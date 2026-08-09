module Fpp.Syntax.Parser

open Fpp.Prelude
open Fpp.Syntax

// Error-tolerant recursive-descent parser with a pragmatic offside rule.
//
// Invariants:
//  * every token of the input ends up in the tree exactly once (losslessness),
//    including on arbitrarily broken input — recovery skips tokens into
//    ErrorNodes, it never drops them;
//  * every loop makes progress or breaks — no input can hang the parser.
//
// Offside, v0 rules (deliberately simpler than full F# but compatible with
// the common subset the compiler itself is written in):
//  * a block's column is the column of its first token; block items start on
//    a fresh line at exactly that column;
//  * an expression continues onto a new line only at column > block column —
//    except infix operators, which may sit at column >= block column;
//  * match/DU bars align at column >= the construct's column.

type Diagnostic =
    { Offset : int
      Message : string }

type ParseResult =
    { Root : GreenNode
      Diagnostics : Diagnostic list }

// ---------------------------------------------------------------------------

type private State(src : string, toks : Vec<Token>) =
    let lineStarts =
        let v = vecNew<int> ()
        vecAdd v 0
        let n = strLen src
        for i in 0 .. n - 1 do
            if charAt src i = '\n' then vecAdd v (i + 1)
        v

    let mutable pos = 0
    let mutable diags : Diagnostic list = []

    member _.Diagnostics = List.rev diags

    member _.Cur : Token = vecGet toks pos
    member _.AtEof : bool = (vecGet toks pos).Kind = Eof

    member _.LineOf (offset : int) : int =
        let mutable lo = 0
        let mutable hi = vecLen lineStarts - 1
        while lo < hi do
            let mid = (lo + hi + 1) / 2
            if vecGet lineStarts mid <= offset then lo <- mid else hi <- mid - 1
        lo

    member this.ColOf (t : Token) : int = t.Offset - vecGet lineStarts (this.LineOf t.Offset)
    member this.CurCol : int = this.ColOf this.Cur
    member this.CurLine : int = this.LineOf this.Cur.Offset

    /// Is the current token on the same line as the previous (consumed) token?
    member this.SameLine : bool =
        pos = 0 || this.LineOf (vecGet toks (pos - 1)).Offset = this.CurLine

    /// Is there whitespace/trivia between the previous token and this one?
    member this.GapBefore : bool =
        pos = 0
        || (let p = vecGet toks (pos - 1)
            p.Offset + strLen p.Text < (vecGet toks pos).Offset)

    member _.Mark : int = pos

    /// Token k positions ahead (clamped to Eof).
    member _.Peek (k : int) : Token =
        let i = if pos + k < vecLen toks then pos + k else vecLen toks - 1
        vecGet toks i

    member this.Bump () : Green =
        let t = this.Cur
        if t.Kind <> Eof then pos <- pos + 1
        GToken t

    member this.Diag (msg : string) : unit =
        diags <- { Offset = this.Cur.Offset; Message = msg } :: diags

    member this.Is (k : TokenKind) : bool = this.Cur.Kind = k
    member this.IsText (s : string) : bool = this.Cur.Text = s
    member this.IsOp (s : string) : bool = this.Cur.Kind = Operator && this.Cur.Text = s
    member this.IsKw (s : string) : bool = this.Cur.Kind = Keyword && this.Cur.Text = s

    /// If the current token is a multi-char '>'-run (e.g. ">>" from nested
    /// generics), split off a single ">" so type-argument lists can close.
    /// Both halves keep real text, so losslessness is preserved.
    member this.SplitGt () : unit =
        let t = this.Cur
        if t.Kind = Operator && strLen t.Text > 1 && charAt t.Text 0 = '>' then
            let first = { Kind = Operator; Text = ">"; Leading = t.Leading; Trailing = []; Offset = t.Offset }
            let rest = { Kind = Operator; Text = substr t.Text 1 (strLen t.Text - 1); Leading = []; Trailing = t.Trailing; Offset = t.Offset + 1 }
            vecSet toks pos first
            vecInsert toks (pos + 1) rest

// ---------------------------------------------------------------------------

let private infixPrec (text : string) : int =
    // F#-style: precedence by leading characters. 0 = not an infix operator.
    // quotation brackets are delimiters, never infix — `@>` would otherwise
    // read as the append operator and swallow the closer
    if text = "@>" || text = "<@" then 0
    elif text = "|" || text = "->" then 0
    elif text = ":=" || text = "<-" then 1
    elif text = ".." || text = "..." then 4
    elif strLen text >= 2 && substr text 0 2 = "**" then 9
    else
        match charAt text 0 with
        | '*' | '/' | '%' -> 8
        | '+' | '-' -> 7
        | ':' -> if text = "::" then 6 else 0
        | '^' | '@' -> 5
        // F# spec: = < > | & $ ! ops share ONE left-assoc level
        // (except && and || which sit below it)
        | '=' | '<' | '>' | '$' -> 4
        | '!' -> if strLen text > 1 then 4 else 0
        | '&' -> if text = "&&" then 3 else 4
        | '|' -> if text = "||" then 2 else 4
        | _ -> 0

let private rightAssoc (text : string) : bool =
    text = "::" || charAt text 0 = '^' || charAt text 0 = '@'
    || (strLen text >= 2 && substr text 0 2 = "**")

let private literalKinds = [ IntLit; FloatLit; StringLit; CharLit ]

let parse (src : string) : ParseResult =
    let toks = vecOfList (Lexer.tokenize src)
    let s = State(src, toks)

    // `and` continues whatever major declaration came last (let rec vs type)
    let mutable lastMajor = "let"
    // set while parsing `extern let ...` — suppresses the missing-'=' diag
    let mutable pendingExtern = false

    let isLiteral () = List.contains s.Cur.Kind literalKinds
    let isLiteralKw () = s.IsKw "true" || s.IsKw "false" || s.IsKw "null"

    /// Can the current token start an atomic expression (an application arg)?
    /// Depth of enclosing `<@ ... @>`, so `%` reads as a splice only inside a
    /// quotation — outside one it is the modulo operator and must stay so.
    let mutable quoteDepth = 0

    /// `%x` with NOTHING between them is a splice; `a % b` is modulo. Adjacency
    /// is the same rule F# uses, and it keeps the two unambiguous.
    let isSpliceHere () =
        // adjacency by OFFSET: trivia may hang off the previous token, so an
        // empty Leading list does not mean the two tokens touch
        quoteDepth > 0 && s.Is Operator && s.IsText "%"
        && (s.Peek 1).Offset = s.Cur.Offset + 1

    let canStartAtom () =
        s.Is Ident || isLiteral () || isLiteralKw ()
        // `fixed expr` — the Pinnable pin operator
        || s.IsKw "fixed"
        // a quotation is an atom: `f <@ x @>` applies f to quoted code
        || (s.Is Operator && s.IsText "<@")
        || isSpliceHere ()
        || s.Is LParen || s.Is LBracket || s.Is LBrace
        || (s.IsOp "'" && (s.Peek 1).Kind = Ident)
        // a struct tuple can be an application argument: `f struct(a, b)`
        || (s.IsKw "struct" && (s.Peek 1).Kind = LParen)
        // `base.M()` — the receiver is the same object, the member is the
        // one the BASE declares
        || s.IsKw "base"

    /// Can the current token start an expression at statement position?
    let canStartExpr () =
        canStartAtom () || s.IsKw "fun" || s.IsKw "if" || s.IsKw "match"
        || (s.IsKw "struct" && (s.Peek 1).Kind = LParen)
        || s.IsKw "function" || s.IsKw "not" || s.IsKw "lazy" || s.IsKw "new"
        || s.IsKw "assert"
        || s.IsKw "downcast" || s.IsKw "upcast"
        || s.IsKw "for" || s.IsKw "while" || s.IsKw "try"
        || (s.Is Operator && (s.IsText "-" || s.IsText "+" || s.IsText "!" || s.IsText "~~~"))
        // `&x` — an address, for a byref argument
        || (s.IsText "&" && (let n = s.Peek 1 in
                             List.isEmpty n.Leading && (n.Kind = Ident || n.Kind = LParen)))
        // `?pattern = p` — naming an optional parameter at a call
        || (s.IsText "?" && (s.Peek 1).Kind = Ident && (s.Peek 2).Text = "=")
        // quotations and splices come through canStartAtom

    /// Anything that can open a statement BLOCK. `yield` and `return` mean
    /// something only inside a computation expression, but a block body is
    /// exactly where they appear, and the shapes that reject them here are
    /// the ones that used to swallow `while c do yield x`.
    let canStartBlock () =
        canStartExpr () || s.IsKw "let" || s.IsKw "use" || s.IsKw "do"
        || s.IsKw "yield" || s.IsKw "return"

    /// `instance` is CONTEXTUAL. F# does not reserve it and real code binds
    /// it — `static let instance = ...` is how a type holds a singleton of
    /// itself, and FSharp.Data.Adaptive writes exactly that. So it is an
    /// ordinary identifier everywhere except at declaration position with a
    /// class name after it, which is the only place the declaration can
    /// appear.
    let atInstanceDecl () =
        s.Is Ident && s.IsText "instance" && (s.Peek 1).Kind = Ident

    let isDirectiveHere () =
        s.IsOp "#" && (s.Peek 1).Kind = Ident
        && List.contains (s.Peek 1).Text
            [ "nowarn"; "light"; "line"; "load"; "r"; "I"; "time"; "help"; "quit" ]

    let canStartDecl () =
        isDirectiveHere ()
        || s.IsKw "let" || s.IsKw "type" || s.IsKw "open" || s.IsKw "module"
        || s.IsKw "namespace" || s.IsKw "and" || s.IsKw "do" || s.IsKw "exception"
        || s.IsKw "extern" || atInstanceDecl ()
        // `class` also opens an F#-style `type X = class ... end`, which F++
        // does not have, so at declaration position it is always a typeclass
        || s.IsKw "class"
        || canStartExpr ()
        || (s.Is LBracket)   // attribute lists

    /// Keywords that close an inner block regardless of indentation.
    let isBlockStopKw () =
        s.IsKw "then" || s.IsKw "else" || s.IsKw "elif" || s.IsKw "with"
        || s.IsKw "end" || s.IsKw "in" || s.IsKw "done" || s.IsKw "to" || s.IsKw "downto"
        || s.IsKw "finally"

    let isCloser () = s.Is RParen || s.Is RBracket || s.Is RBrace || s.Is Comma || s.Is Semicolon

    /// `(+)` in name position: three tokens with nothing between them. They
    /// fuse into ONE identifier token spelled "(+)", so every downstream pass
    /// sees an operator member as an ordinary name. Concatenation still
    /// reproduces the source exactly, which is what losslessness requires —
    /// hence the no-inner-trivia rule (`( + )` is not a name).
    let atOperatorName () =
        s.Is LParen && List.isEmpty s.Cur.Trailing
        && (s.Peek 1).Kind = Operator
        && List.isEmpty (s.Peek 1).Leading && List.isEmpty (s.Peek 1).Trailing
        && (s.Peek 2).Kind = RParen && List.isEmpty (s.Peek 2).Leading

    /// `(|Add|Rem|)` — a multi-case ACTIVE PATTERN name. Seven adjacent
    /// tokens, all of them fused into one identifier, the way `(+)` is.
    let activePatternCases () : string list =
        if not (s.Is LParen && List.isEmpty s.Cur.Trailing) then []
        else
            let mutable i = 1
            let mutable names = []
            let mutable ok = true
            let mutable fin = false
            // ( | Name | Name | )
            while ok && not fin do
                let bar = s.Peek i
                if bar.Kind = Operator && bar.Text = "|" && List.isEmpty bar.Trailing then
                    let nm = s.Peek (i + 1)
                    if nm.Kind = Ident && List.isEmpty nm.Leading && List.isEmpty nm.Trailing then
                        names <- names @ [ nm.Text ]
                        i <- i + 2
                    elif nm.Kind = RParen && not (List.isEmpty names) then
                        fin <- true
                    else ok <- false
                else ok <- false
            if ok && fin && List.length names >= 2 && List.length names <= 4 then names else []

    let atActivePatternName () = not (List.isEmpty (activePatternCases ()))

    /// The function an active pattern becomes, and the choice case each of
    /// its cases becomes. Recorded as the definition is parsed, and read at
    /// every later use — which is why a definition has to precede its uses,
    /// as it does in F#.
    let apFunctionOf = dictNew<string, string> ()      // case -> function
    let apIndexOf = dictNew<string, string> ()         // case -> choice case

    /// Rename identifiers through a parsed subtree. Used only for the
    /// active-pattern desugar, where a case name has to become the choice
    /// case it compiles to.
    let rec renameIdents (m : Dict<string, string>) (g : Green) : Green =
        match g with
        | GToken t when t.Kind = Ident ->
            (match dictTryFind m t.Text with
             | Some r -> GToken { t with Text = r }
             | None -> g)
        | GToken _ -> g
        | GNode n -> Green.node n.NodeKind (n.Children |> List.map (renameIdents m))

    /// Every case of every active pattern seen so far, mapped to the choice
    /// case it becomes.
    let apRenames () : Dict<string, string> = apIndexOf

    let bumpActivePatternName () : Green =
        let names = activePatternCases ()
        let l = s.Cur
        let fname = "$ap$" + String.concat "$" names
        let n = List.length names
        names |> List.iteri (fun i c ->
            dictSet apFunctionOf c fname
            dictSet apIndexOf c ("Choice" + string n + "Of" + string (i + 1)))
        // ( |A |B ... |) — a bar and a name per case, one closing bar, two
        // parens: 2n + 3 tokens
        let mutable k = 0
        while k < 2 * n + 3 do
            s.Bump () |> ignore
            k <- k + 1
        GToken { Kind = Ident; Text = fname
                 Leading = l.Leading; Trailing = []; Offset = l.Offset }

    let bumpOperatorName () : Green =
        let l = s.Cur
        let op = s.Peek 1
        let r = s.Peek 2
        s.Bump () |> ignore
        s.Bump () |> ignore
        s.Bump () |> ignore
        GToken { Kind = Ident; Text = "(" + op.Text + ")"
                 Leading = l.Leading; Trailing = r.Trailing; Offset = l.Offset }

    /// A new line has begun and the current token sits at or left of `col`.
    // Inside brackets the offside rule is suspended: the closing bracket
    // delimits the group, so a continuation line may sit at any column.
    let mutable bracketDepth = 0
    /// The columns an UNDENTED clause list must still stay right of,
    /// innermost first. F# lets `f (x, function` put its clauses left of the
    /// `function` keyword — the bracket delimits the group, so the offside
    /// line is the enclosing statement's, not the keyword's. What it may NOT
    /// undent past is a clause list or a block that encloses it, or
    ///
    ///     (match x with
    ///      | A -> match y with
    ///             | B -> 1
    ///      | C -> 2)
    ///
    /// would give the inner `match` the outer's last clause.
    ///
    /// A -1 is the bracket's own immediate content, which constrains
    /// nothing: `parseBlock` on the inside of a paren starts at whatever
    /// column the first argument happens to sit at, and that column is an
    /// artifact of the layout rather than a bound anyone wrote.
    let mutable guardCols : int list = []
    let mutable pendingBracketBlock = false
    let undentGuard () =
        let rec first (cs : int list) =
            match cs with
            | c :: rest -> if c >= 0 then c else first rest
            | [] -> -1
        first guardCols

    let inBrackets (f : unit -> Green) : Green =
        bracketDepth <- bracketDepth + 1
        let saved = pendingBracketBlock
        pendingBracketBlock <- true
        let r = f ()
        pendingBracketBlock <- saved
        bracketDepth <- bracketDepth - 1
        r
    let offside (col : int) = bracketDepth = 0 && not s.SameLine && s.CurCol <= col

    // ---- error recovery ---------------------------------------------------

    /// Skip tokens into an ErrorNode until something that can plausibly start
    /// a fresh item at column <= col appears (or a closer, or eof).
    let errorUntilRecovery (col : int) (msg : string) : Green =
        s.Diag msg
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())
        let mutable go = true
        while go && not s.AtEof do
            if isCloser () || isBlockStopKw () then go <- false
            elif not s.SameLine && s.CurCol <= col && canStartDecl () then go <- false
            else vecAdd acc (s.Bump ())
        Green.node ErrorNode (vecToList acc)

    // ---- types ------------------------------------------------------------

    let rec parseType (ctx : int) : Green =
        parseFunType ctx

    and parseFunType (ctx : int) : Green =
        let lhs = parseTupleType ctx
        if s.IsOp "->" && not (offside ctx) then
            let arrow = s.Bump ()
            let rhs = parseFunType ctx
            Green.node FunType [ lhs; arrow; rhs ]
        else lhs

    and parseTupleType (ctx : int) : Green =
        let first = parsePostfixType ctx
        if s.IsOp "*" && not (offside ctx) then
            let acc = vecNew<Green> ()
            vecAdd acc first
            while s.IsOp "*" && not (offside ctx) do
                vecAdd acc (s.Bump ())
                vecAdd acc (parsePostfixType ctx)
            Green.node TupleType (vecToList acc)
        else first

    /// a union case's payload: components may carry LABELS —
    /// `of name : string * value : 'a` — which are documentation (F#'s
    /// rule); the tokens stay in the tree, the types drive everything.
    and parseCasePayload (ctx : int) : Green =
        let labelled (acc : Vec<Green>) =
            if s.Is Ident && (s.Peek 1).Text = ":" then
                vecAdd acc (s.Bump ())
                vecAdd acc (s.Bump ())
        let pre = vecNew<Green> ()
        labelled pre
        let first = parsePostfixType ctx
        if s.IsOp "*" && not (offside ctx) then
            let acc = vecNew<Green> ()
            for x in vecToList pre do vecAdd acc x
            vecAdd acc first
            while s.IsOp "*" && not (offside ctx) do
                vecAdd acc (s.Bump ())
                labelled acc
                vecAdd acc (parsePostfixType ctx)
            Green.node TupleType (vecToList acc)
        elif vecLen pre > 0 then
            Green.node ParenType (vecToList pre @ [ first ])
        else first

    and parsePostfixType (ctx : int) : Green =
        // `int list`, `'a option`, `int[]` — postfix applications
        let mutable t = parseAppType ctx
        let mutable go = true
        while go do
            if s.Is Ident && s.SameLine then
                t <- Green.node PostfixType [ t; s.Bump () ]
            elif s.Is LBracket && s.SameLine && (s.Peek 1).Kind = RBracket then
                t <- Green.node PostfixType [ t; s.Bump (); s.Bump () ]
            else go <- false
        t

    and parseAppType (ctx : int) : Green =
        let atom = parseAtomType ctx
        if s.IsOp "<" && s.SameLine then
            Green.node AppType (atom :: parseAngleArgs ctx)
        else atom

    /// `<` typeArgs `>`, tolerant of `when`-constraints and `_` holes; splits
    /// a `>>` run so nested generics close correctly.
    and parseAngleArgs (ctx : int) : Green list =
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())   // '<'
        let mutable go = true
        while go && not s.AtEof do
            s.SplitGt ()
            if not s.SameLine then go <- false   // angle lists never span lines
            elif s.IsOp ">" then
                vecAdd acc (s.Bump ())
                go <- false
            elif s.Is Comma then vecAdd acc (s.Bump ())
            elif canStartTypeAtom () then vecAdd acc (parseType ctx)
            elif s.IsKw "when" then
                // F#'s INLINE constraint: `type MapExt<'Key, 'Value when 'Key
                // : comparison>`. Its own node, so that the tokens are still
                // there (the parse stays lossless) but the identifiers in it
                // are not mistaken for type PARAMETERS — that is how MapExt
                // came to have four.
                let cons = vecNew<Green> ()
                let mutable depth = 0
                let mutable more = true
                while more && not s.AtEof && s.SameLine do
                    s.SplitGt ()
                    if s.IsOp "<" then depth <- depth + 1; vecAdd cons (s.Bump ())
                    elif s.IsOp ">" && depth > 0 then depth <- depth - 1; vecAdd cons (s.Bump ())
                    elif s.IsOp ">" then more <- false
                    else vecAdd cons (s.Bump ())
                vecAdd acc (Green.node WhenDecl (vecToList cons))
            else
                // anything else we do not model yet: absorb tokens verbatim
                vecAdd acc (s.Bump ())
        vecToList acc

    and canStartTypeAtom () =
        s.Is Ident || s.IsOp "'" || s.IsOp "^" || s.Is LParen || s.IsOp "#"
        // `: %t` — a spliced TYPE, inside a quotation only
        || isSpliceHere ()
        || (s.IsKw "struct" && (s.Peek 1).Kind = LParen)

    and parseAtomType (ctx : int) : Green =
        if isSpliceHere () then
            // the spliced name is an ordinary IdentExpr, so the resolver binds
            // it like any other use and lowering can just lower it
            let pct = s.Bump ()
            let name = s.Bump ()
            Green.node SpliceType [ pct; Green.node IdentExpr [ name ] ]
        elif s.IsOp "#" then
            // flexible type `#seq<'a>` — "some subtype of". Argument
            // positions already widen, so the constraint adds nothing here.
            let h = s.Bump ()
            (match parseAtomType ctx with
             | GNode inner -> Green.node inner.NodeKind (h :: inner.Children)
             | g -> g)
        elif s.IsKw "struct" && (s.Peek 1).Kind = LParen then
            // `struct('K * 'V)` names the generic struct StructTuple2<'K,'V>
            let kw = s.Bump ()
            Green.node StructTupleType [ kw; parseAtomType ctx ]
        elif s.IsOp "'" || s.IsOp "^" then
            // `^T` is F#'s STATICALLY RESOLVED type parameter. Here it is an
            // ordinary one: what F# resolves by member constraint, F++
            // resolves by typeclass, so the two spellings mean the same
            // thing and the caret is only a different sigil.
            let q = s.Bump ()
            if s.Is Ident then Green.node VarType [ q; s.Bump () ]
            else Green.node VarType [ q ]
        elif s.Is Ident then
            if s.IsText "_" then Green.node AnonType [ s.Bump () ]
            else
                // dotted name A.B.C
                let acc = vecNew<Green> ()
                vecAdd acc (s.Bump ())
                while s.IsOp "." && s.SameLine do
                    vecAdd acc (s.Bump ())
                    if s.Is Ident then vecAdd acc (s.Bump ())
                Green.node NamedType (vecToList acc)
        elif s.Is LParen then
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            if canStartTypeAtom () then vecAdd acc (parseType ctx)
            if s.Is RParen then vecAdd acc (s.Bump ()) else s.Diag "expected ')'"
            Green.node ParenType (vecToList acc)
        else
            s.Diag "expected a type"
            Green.node ErrorNode [ s.Bump () ]

    // ---- patterns ---------------------------------------------------------

    let rec parsePat (ctx : int) : Green =
        let first = parseConsPat ctx
        let p =
            if s.Is Comma && not (offside ctx) then
                let acc = vecNew<Green> ()
                vecAdd acc first
                while s.Is Comma && not (offside ctx) do
                    vecAdd acc (s.Bump ())
                    vecAdd acc (parseConsPat ctx)
                Green.node TuplePat (vecToList acc)
            else first
        parseAsSuffix p

    /// `pat as name` — binds loosest of all pattern forms.
    and parseAsSuffix (p : Green) : Green =
        if s.IsKw "as" then
            let kw = s.Bump ()
            if s.Is Ident then
                let name = Green.node IdentPat [ s.Bump () ]
                Green.node AsPat [ p; kw; name ]
            else
                s.Diag "expected a name after 'as'"
                Green.node AsPat [ p; kw ]
        else p

    and parseConsPat (ctx : int) : Green =
        let lhs = parseAppPat ctx
        if s.IsOp "::" && not (offside ctx) then
            let op = s.Bump ()
            let rhs = parseConsPat ctx
            Green.node ConsPat [ lhs; op; rhs ]
        else lhs

    and parseAppPat (ctx : int) : Green =
        let head = parseAtomPat ctx
        if canStartAtomPat () && s.SameLine then
            let acc = vecNew<Green> ()
            vecAdd acc head
            while canStartAtomPat () && s.SameLine do
                vecAdd acc (parseAtomPat ctx)
            Green.node AppPat (vecToList acc)
        else head

    and canStartAtomPat () =
        s.Is Ident || isLiteral () || isLiteralKw () || s.Is LParen || s.Is LBracket
        // `| %p ->` — a spliced PATTERN, inside a quotation only
        || isSpliceHere ()
        || (s.IsKw "struct" && (s.Peek 1).Kind = LParen) || s.IsOp ":?"
        || (s.IsOp "-" && (let n = s.Peek 1 in n.Kind = IntLit || n.Kind = FloatLit))

    and parseAtomPat (ctx : int) : Green =
        if isSpliceHere () then
            let pct = s.Bump ()
            let name = s.Bump ()
            Green.node SplicePat [ pct; Green.node IdentExpr [ name ] ]
        elif s.IsOp ":?" then
            // type-test pattern: `| :? HashSet<'K> as o ->`
            let op = s.Bump ()
            // the tested type may be a generic application: `:? HashSet<'K>`
            Green.node TypeTestPat [ op; parseAppType ctx ]
        elif s.IsKw "struct" && (s.Peek 1).Kind = LParen then
            let kw = s.Bump ()
            Green.node StructTuplePat [ kw; parseAtomPat ctx ]
        elif s.Is Ident then
            if s.IsText "_" then Green.node WildcardPat [ s.Bump () ]
            else
                // dotted constructor name, e.g. Lexer.Some
                let acc = vecNew<Green> ()
                vecAdd acc (s.Bump ())
                while s.IsOp "." && s.SameLine do
                    vecAdd acc (s.Bump ())
                    if s.Is Ident then vecAdd acc (s.Bump ())
                Green.node IdentPat (vecToList acc)
        elif isLiteral () || isLiteralKw () then
            Green.node LiteralPat [ s.Bump () ]
        elif s.IsOp "-" then
            // negative literal pattern: `| -1 -> ...`
            Green.node LiteralPat [ s.Bump (); s.Bump () ]
        elif s.Is LParen then
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            if s.Is Operator && not (s.IsOp "'") && (s.Peek 1).Kind = RParen then
                vecAdd acc (s.Bump ())   // operator name `(+)`
            else
                // comma-separated patterns, each optionally ascribed:
                // (x), (x : int), (a, b), (src : string, toks : Vec<Token>)
                // `?retires : int` — an OPTIONAL parameter. The `?` rides in
                // the tree as its own token so inference can see which
                // parameter it belongs to and give that one an option type.
                let optHere () =
                    s.IsOp "?" && (s.Peek 1).Kind = Ident && s.SameLine
                let mutable go = canStartAtomPat () || optHere ()
                while go do
                    if optHere () then vecAdd acc (s.Bump ())
                    vecAdd acc (parseAsSuffix (parseConsPat ctx))
                    // parenthesized or-pattern: ("&&" | "||")
                    while s.IsOp "|" && not s.AtEof do
                        vecAdd acc (s.Bump ())
                        vecAdd acc (parseConsPat ctx)
                    if s.IsOp ":" then
                        vecAdd acc (s.Bump ())
                        vecAdd acc (parseType ctx)
                    if s.Is Comma then
                        vecAdd acc (s.Bump ())
                        go <- canStartAtomPat () || optHere ()
                    else go <- false
            if s.Is RParen then vecAdd acc (s.Bump ()) else s.Diag "expected ')' in pattern"
            Green.node ParenPat (vecToList acc)
        elif s.Is LBracket then
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            let mutable go = true
            while go && not s.AtEof && not (s.Is RBracket) do
                let mark = s.Mark
                if s.Is Semicolon then vecAdd acc (s.Bump ())
                elif canStartAtomPat () then vecAdd acc (parsePat ctx)
                else vecAdd acc (s.Bump ())
                if s.Mark = mark then go <- false
            if s.Is RBracket then vecAdd acc (s.Bump ())
            Green.node ListPat (vecToList acc)
        else
            s.Diag "expected a pattern"
            Green.node ErrorNode [ s.Bump () ]

    // ---- expressions ------------------------------------------------------

    let rec parseExpr (ctx : int) : Green =
        let first = parseBinary ctx 1
        if s.Is Comma && not (offside ctx) then
            let acc = vecNew<Green> ()
            vecAdd acc first
            while s.Is Comma && not (offside ctx) do
                vecAdd acc (s.Bump ())
                if canStartExpr () then vecAdd acc (parseBinary ctx 1)
            Green.node TupleExpr (vecToList acc)
        else first

    and parseBinary (ctx : int) (minPrec : int) : Green =
        let mutable lhs = parseApp ctx
        let mutable go = true
        while go do
            // operators may sit at exactly the block column on a fresh line
            let allowed = s.SameLine || s.CurCol >= ctx || bracketDepth > 0
            // A CAST binds looser than `|>`: F# reads `x |> f :> obj` as
            // `(x |> f) :> obj`, and taking the cast unconditionally made it
            // `x |> (f :> obj)` — a function upcast to obj. Level 4 is the
            // band `|>` and `=` share, and left association puts the cast
            // outside them, which is what the spec's ordering amounts to.
            if (s.IsOp ":>" || s.IsOp ":?>") && allowed && minPrec <= 4 then
                let op = s.Bump ()
                lhs <- Green.node CastExpr [ lhs; op; parseType ctx ]
            elif s.IsOp ":?" && allowed then
                // a type TEST still binds tightly, as in F#
                let op = s.Bump ()
                lhs <- Green.node CastExpr [ lhs; op; parseType ctx ]
            elif s.Is Operator && allowed && not (s.IsOp "|") && not (s.IsOp "->") then
                let prec = infixPrec s.Cur.Text
                // an adjacent `%x` inside a quotation is a SPLICE, never the
                // modulo operator continuing the expression on the line above
                if prec >= minPrec && prec > 0 && not (isSpliceHere ()) then
                    let opText = s.Cur.Text
                    let op = s.Bump ()
                    let nextMin = if rightAssoc opText then prec else prec + 1
                    let rhs =
                        // `x <- \n  let k = ... \n  k + 1` — an assignment
                        // may take a whole BLOCK, and only an assignment
                        // does: everywhere else a `let` on the right of an
                        // operator is a syntax error in F# too
                        if (opText = "<-" || opText = ":=")
                           && canStartBlock () && not (canStartExpr ()) then parseBlock ctx
                        else parseBinary ctx nextMin
                    lhs <- Green.node BinaryExpr [ lhs; op; rhs ]
                else go <- false
            else go <- false
        lhs

    and parseApp (ctx : int) : Green =
        // F#'s ADJACENT-PREFIX rule: in argument position, a `-` with
        // whitespace before it and none after negates what follows — `f -1`
        // and `f -x` both pass one argument, where `f - x` subtracts. The
        // spacing IS the disambiguation, and F# code relies on it:
        // `sprintf "Rem%d(%A)" -cnt value` passes -cnt, and reading that as
        // subtraction makes a nonsense of the whole application.
        let isNegArg () =
            s.IsOp "-" && s.GapBefore
            && (let n = s.Peek 1 in
                n.Offset = s.Cur.Offset + 1
                && (n.Kind = IntLit || n.Kind = FloatLit || n.Kind = Ident || n.Kind = LParen))
        // `f &x` — an ADDRESS as a curried argument, by the same adjacency
        // rule as the negation above
        let isAddrArg () =
            s.IsOp "&" && (let n = s.Peek 1 in
                           List.isEmpty n.Leading && (n.Kind = Ident || n.Kind = LParen))
        let parseArg () =
            if isNegArg () || isAddrArg () then
                let op = s.Bump ()
                Green.node PrefixExpr [ op; parsePostfix ctx ]
            else parsePostfix ctx
        let head = parsePostfix ctx
        if (canStartAtom () || isNegArg () || isAddrArg ()) && (s.SameLine || s.CurCol > ctx) then
            let acc = vecNew<Green> ()
            vecAdd acc head
            while (canStartAtom () || isNegArg () || isAddrArg ()) && (s.SameLine || s.CurCol > ctx) do
                vecAdd acc (parseArg ())
            Green.node AppExpr (vecToList acc)
        else head

    and parsePostfix (ctx : int) : Green =
        let mutable e = parseAtom ctx
        let mutable go = true
        while go do
            if s.IsOp "." && s.SameLine then
                let dot = s.Bump ()
                // `Add.(+)` names a class' operator member — the same fused
                // identifier the declaration used
                if atOperatorName () then e <- Green.node DotExpr [ e; dot; bumpOperatorName () ]
                elif s.Is Ident then e <- Green.node DotExpr [ e; dot; s.Bump () ]
                elif s.Is LBracket then e <- Green.node DotExpr [ e; dot; parseAtom ctx ]   // x.[i]
                else
                    s.Diag "expected member name after '.'"
                    e <- Green.node DotExpr [ e; dot ]
            elif s.IsOp "<" && isAdjacentTo e && looksLikeTypeArgs () then
                // explicit generic application: GetValue<string>, vecNew<Green>
                e <- Green.node AppExpr [ e; Green.node TyParams (parseAngleArgs ctx) ]
            elif s.Is LParen && isAdjacentTo e then
                // F#'s high-precedence application: an atom IMMEDIATELY
                // followed by `(` binds tighter than juxtaposition, so
                // `C(1).Get()` chains the dot onto the call — without this
                // the postfix loop never saw past the constructor
                e <- Green.node AppExpr [ e; parseAtom ctx ]
            elif s.Is LBrace && s.SameLine && isNameExpr e
                 && not ((s.Peek 1).Kind = Keyword && (s.Peek 1).Text = "new")
                 && not (looksLikeRecordExpr ()) then
                // `builder { ... }`. A record or object expression in the
                // same position is an ARGUMENT, so both are excluded first.
                // The builder has to be a NAME: F# allows any expression,
                // but a brace after an arbitrary atom is far more often an
                // argument — `test "name" { ... }` reads as a computation
                // expression only because Expecto says so, and guessing
                // wrong turns a body the parser cannot see into one it can,
                // with every construct inside newly exposed.
                e <- Green.node CompExpr [ e; parseCeBody ctx ]
            else go <- false
        e

    /// A plain name — `seq`, `Foo.bar`, `x.builder` — and nothing else.
    and isNameExpr (e : Green) : bool =
        match e with
        | GNode n -> n.NodeKind = IdentExpr || n.NodeKind = DotExpr
        | GToken _ -> false

    /// The braced body of a computation expression: an ordinary statement
    /// block — the bang forms are `let`/`do` with a `!` glued on — closed by
    /// `}`. Indentation governs it exactly as it governs any other block.
    and parseCeBody (ctx : int) : Green =
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())   // {
        if canStartBlock () then vecAdd acc (parseBlock ctx)
        if s.Is RBrace then vecAdd acc (s.Bump ()) else s.Diag "expected '}'"
        Green.node BraceExpr (vecToList acc)

    /// The `<` begins immediately after the expression (F#'s disambiguator
    /// between generic application and comparison).
    and isAdjacentTo (e : Green) : bool =
        match Green.tokens e |> List.tryLast with
        | Some t -> t.Offset + strLen t.Text = s.Cur.Offset
        | None -> false

    /// Lookahead from a `<`: only type-shaped tokens until a matching `>`
    /// on the same line.
    and looksLikeTypeArgs () : bool =
        let line = s.CurLine
        let rec scan (k : int) (depth : int) : bool =
            let t = s.Peek k
            if t.Kind = Eof then false
            elif s.LineOf t.Offset <> line then false
            else
                match t.Kind with
                | Operator ->
                    if t.Text = "<" then scan (k + 1) (depth + 1)
                    elif charAt t.Text 0 = '>' then
                        // only the LEADING run of '>' closes levels: the
                        // lexer glues trailing symbols on, so `>.Instance`
                        // arrives as the single operator ">."
                        let mutable run = 0
                        while run < strLen t.Text && charAt t.Text run = '>' do run <- run + 1
                        let closed = depth - run
                        if closed < 0 then false
                        elif closed = 0 then true
                        else scan (k + 1) closed
                    elif t.Text = "'" || t.Text = "^" || t.Text = "." || t.Text = "*" || t.Text = "->" then scan (k + 1) depth
                    else false
                | Ident -> scan (k + 1) depth
                // `zeroCreate<struct('K * 'V)>` — a struct-tuple type
                | Keyword when t.Text = "struct" -> scan (k + 1) depth
                | Comma -> scan (k + 1) depth
                | LBracket | RBracket -> scan (k + 1) depth   // int[]
                | LParen | RParen -> scan (k + 1) depth       // (string * int) list
                | _ -> false
        scan 1 1

    and parseAtom (ctx : int) : Green =
        if s.IsKw "fixed" then
            // `fixed expr` — the keyword acts as the Pinnable pin operator;
            // the token rides in an IdentExpr so the pipeline treats it
            // like the (unresolvable) name it dispatches on
            let kw = s.Bump ()
            let t = match kw with GToken tk -> GToken { tk with Kind = Ident } | g -> g
            Green.node IdentExpr [ t ]
        elif s.Is Operator && s.Cur.Text = "<@" then
            // the quoted body is parsed as ORDINARY syntax — that is what
            // makes it resolve, type check and hover like real code
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            // the body gets its OWN block context, starting at its column, so a
            // quoted `let` sequence spanning lines parses like any other block
            // instead of being cut off at the enclosing expression's context
            quoteDepth <- quoteDepth + 1
            // a quotation may hold a DECLARATION as readily as an expression:
            // `type`, and `member` for the shape a deriving plugin emits
            if s.IsKw "type" then vecAdd acc (parseTypeDecl ctx)
            elif s.IsKw "member" then vecAdd acc (parseMember ())
            else vecAdd acc (parseBlock ctx)
            quoteDepth <- quoteDepth - 1
            if s.Is Operator && s.Cur.Text = "@>" then vecAdd acc (s.Bump ())
            else s.Diag "expected '@>' to close the quotation"
            Green.node QuoteExpr (vecToList acc)
        elif s.IsOp "&" && (let n = s.Peek 1 in
                            List.isEmpty n.Leading && (n.Kind = Ident || n.Kind = LParen)) then
            // `&x` — the ADDRESS of a mutable location, for a byref
            // parameter. Adjacency is what distinguishes it from the
            // bitwise operators, which are `&&&` and `&&`.
            let amp = s.Bump ()
            Green.node PrefixExpr [ amp; parsePostfix ctx ]
        elif isSpliceHere () then
            // a splice: `%x` names code to drop in here
            let pct = s.Bump ()
            let inner = parseAtom ctx
            Green.node SpliceExpr [ pct; inner ]
        elif s.Is Ident then Green.node IdentExpr [ s.Bump () ]
        elif isLiteral () || isLiteralKw () then Green.node LiteralExpr [ s.Bump () ]
        elif s.Is LParen then
            let lp = s.Bump ()
            if s.Is RParen then Green.node ParenExpr [ lp; s.Bump () ]   // unit
            elif s.Is Operator && not (s.IsOp "'") && infixPrec s.Cur.Text > 0
                 // `(+)` and `(-)` too: a lone operator before `)` is a
                 // section even when the operator could start a prefix expr
                 && ((s.Peek 1).Kind = RParen || not (canStartExpr ())) then
                // operator section (+)
                let op = s.Bump ()
                let acc = vecNew<Green> ()
                vecAdd acc lp
                vecAdd acc op
                if s.Is RParen then vecAdd acc (s.Bump ()) else s.Diag "expected ')'"
                Green.node ParenExpr (vecToList acc)
            else
                let acc = vecNew<Green> ()
                vecAdd acc lp
                if canStartBlock () then vecAdd acc (inBrackets (fun () -> parseBlock ctx))
                elif s.Is Operator then vecAdd acc (s.Bump ())   // section like (+) with odd op
                if s.IsOp ":" then
                    vecAdd acc (s.Bump ())
                    vecAdd acc (parseType ctx)
                if s.Is RParen then vecAdd acc (s.Bump ()) else s.Diag "expected ')'"
                Green.node ParenExpr (vecToList acc)
        elif s.Is LBracket && (s.Peek 1).Kind = Operator && ((s.Peek 1).Text = "|" || (s.Peek 1).Text = "||") then
            // array literal [| ... |]
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())   // [
            vecAdd acc (s.Bump ())   // | (or || when empty)
            let mutable go = true
            while go && not s.AtEof && not (s.Is RBracket) && not (s.IsOp "|") do
                let mark = s.Mark
                if s.Is Semicolon then vecAdd acc (s.Bump ())
                // Each ELEMENT is parsed at its OWN column, so a sibling on
                // the next line is a new element and only a deeper
                // continuation belongs to this one. Against the enclosing
                // context the next line became an ARGUMENT of the one
                // before — a leading block comment is what exposed it, by
                // moving the elements right, past the outer column, so
                // `[| 7 \n 13 |]` read as `7 13`.
                elif canStartExpr () then vecAdd acc (parseExpr s.CurCol)
                else vecAdd acc (s.Bump ())
                if s.Mark = mark then go <- false
            if s.IsOp "|" then vecAdd acc (s.Bump ())
            if s.Is RBracket then vecAdd acc (s.Bump ()) else s.Diag "expected '|]'"
            Green.node ArrayExpr (vecToList acc)
        elif s.Is LBracket then
            // list: contents as `;`- or newline-separated expressions
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            let mutable go = true
            while go && not s.AtEof && not (s.Is RBracket) do
                let mark = s.Mark
                if s.Is Semicolon then vecAdd acc (s.Bump ())
                elif s.IsOp "|" then vecAdd acc (s.Bump ())
                elif canStartBlock () then vecAdd acc (parseBlock ctx)
                else vecAdd acc (s.Bump ())
                if s.Mark = mark then go <- false
            if s.Is RBracket then vecAdd acc (s.Bump ()) else s.Diag "expected ']'"
            Green.node ListExpr (vecToList acc)
        elif s.Is LBrace then
            if s.IsKw "new" || ((s.Peek 1).Kind = Keyword && (s.Peek 1).Text = "new") then
                // object expression: `{ new IFace with member ... }` — an
                // anonymous class, the natural way to hand over a dictionary
                let acc = vecNew<Green> ()
                vecAdd acc (s.Bump ())   // {
                if s.IsKw "new" then vecAdd acc (s.Bump ())
                vecAdd acc (parseType ctx)
                // `{ new Base(args) with ... }` — an object expression over a
                // CLASS passes its base constructor arguments here, where an
                // interface has none to pass
                if s.Is LParen && s.SameLine then vecAdd acc (parseAtom ctx)
                if s.IsKw "with" then vecAdd acc (s.Bump ())
                bracketDepth <- bracketDepth + 1
                let mutable go = true
                while go && not s.AtEof && not (s.Is RBrace) && isMemberStart () do
                    let mark = s.Mark
                    vecAdd acc (parseMember ())
                    if s.Mark = mark then go <- false
                bracketDepth <- bracketDepth - 1
                if s.Is RBrace then vecAdd acc (s.Bump ()) else s.Diag "expected '}'"
                Green.node ObjExpr (vecToList acc)
            elif looksLikeRecordExpr () then parseRecordExpr ctx
            else
                // sequences and computation bodies: balanced token soup —
                // lossless, structured when CEs are modeled
                let acc = vecNew<Green> ()
                vecAdd acc (s.Bump ())
                let mutable depth = 1
                while depth > 0 && not s.AtEof do
                    if s.Is LBrace then depth <- depth + 1
                    elif s.Is RBrace then depth <- depth - 1
                    vecAdd acc (s.Bump ())
                Green.node BraceExpr (vecToList acc)
        elif s.IsKw "fun" then
            let acc = vecNew<Green> ()
            let funCol = s.CurCol
            vecAdd acc (s.Bump ())
            while canStartAtomPat () && s.SameLine do
                vecAdd acc (parseAtomPat ctx)
            if s.IsOp "->" then vecAdd acc (s.Bump ()) else s.Diag "expected '->' in lambda"
            vecAdd acc (parseBlock funCol)
            Green.node LambdaExpr (vecToList acc)
        elif s.IsKw "if" then parseIf ctx
        elif s.IsKw "match" then parseMatch ctx
        elif s.IsKw "function" then
            let acc = vecNew<Green> ()
            let col = s.CurCol
            vecAdd acc (s.Bump ())
            parseClauses acc col
            Green.node MatchExpr (vecToList acc)
        elif s.IsKw "for" then
            let acc = vecNew<Green> ()
            let fcol = s.CurCol
            vecAdd acc (s.Bump ())
            vecAdd acc (parsePat fcol)
            if s.IsKw "in" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseExpr fcol)
            elif s.IsOp "=" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseExpr fcol)
                if s.IsKw "to" || s.IsKw "downto" then
                    vecAdd acc (s.Bump ())
                    vecAdd acc (parseExpr fcol)
            else s.Diag "expected 'in' or '=' in for loop"
            // `do body` or comprehension arrow `-> expr`
            if s.IsKw "do" || s.IsOp "->" then vecAdd acc (s.Bump ())
            else s.Diag "expected 'do'"
            if canStartBlock () then vecAdd acc (parseBlock fcol)
            Green.node ForExpr (vecToList acc)
        elif s.IsKw "try" then
            let acc = vecNew<Green> ()
            let tcol = s.CurCol
            vecAdd acc (s.Bump ())
            if canStartBlock () then vecAdd acc (parseBlock tcol)
            if s.IsKw "with" then
                vecAdd acc (s.Bump ())
                parseClauses acc tcol
            elif s.IsKw "finally" then
                // `try B finally F`: the finalizer is a BLOCK, not a clause
                // list, and the `finally` keyword in the node is what tells
                // the two shapes apart downstream
                vecAdd acc (s.Bump ())
                if canStartBlock () then vecAdd acc (parseBlock tcol)
            else s.Diag "expected 'with' or 'finally' in try"
            Green.node TryExpr (vecToList acc)
        elif s.IsKw "while" then
            let acc = vecNew<Green> ()
            let wcol = s.CurCol
            vecAdd acc (s.Bump ())
            vecAdd acc (parseExpr wcol)
            if s.IsKw "do" then vecAdd acc (s.Bump ()) else s.Diag "expected 'do'"
            if canStartBlock () then vecAdd acc (parseBlock wcol)
            Green.node WhileExpr (vecToList acc)
        elif s.IsKw "base" then
            // an ordinary receiver as far as the tree is concerned; what the
            // keyword changes is which type its members are looked up on
            Green.node IdentExpr [ s.Bump () ]
        elif s.IsOp "?" && (s.Peek 1).Kind = Ident && (s.Peek 2).Text = "=" then
            // `?pattern = p` at a CALL: the argument names an optional
            // parameter and passes the option itself, not a value to wrap.
            // The `?` rides inside the name so the `= p` still reads as the
            // ordinary named-argument shape.
            Green.node IdentExpr [ s.Bump (); s.Bump () ]
        elif s.IsOp "'" && (s.Peek 1).Kind = Ident then
            // type variable in expression position (e.g. `unbox<'a>` soup)
            Green.node IdentExpr [ s.Bump (); s.Bump () ]
        elif s.IsKw "struct" && (s.Peek 1).Kind = LParen then
            // struct tuple: a value, not a heap allocation
            let kw = s.Bump ()
            Green.node StructTupleExpr [ kw; parseAtom ctx ]
        elif s.IsKw "downcast" || s.IsKw "upcast" then
            // the target type comes from the context, so the node carries
            // only the operator and the operand
            let kw = s.Bump ()
            let arg = parseApp ctx
            Green.node CastExpr [ kw; arg ]
        elif s.IsKw "assert" then
            // `assert e`. F# elides it outside DEBUG; here it is a real
            // check, because a wasm module has no debugger attached to
            // notice the difference and a silent assertion is worth nothing.
            // the operand is a whole EXPRESSION, not an application:
            // `assert n > 0` asserts the comparison, as F# reads it
            let kw = s.Bump ()
            Green.node PrefixExpr [ kw; parseExpr ctx ]
        elif s.IsKw "not" && (let k = (s.Peek 1).Kind in
                              k = RParen || k = RBracket || k = RBrace
                              || k = Comma || k = Semicolon || k = Eof) then
            // `f >> not` — `not` as a VALUE. It is a keyword here and a
            // function in F#, so with nothing to apply it to the node keeps
            // only the keyword, and lowering makes the function out of it.
            Green.node PrefixExpr [ s.Bump () ]
        elif s.IsKw "not" || s.IsKw "lazy" || s.IsKw "new" then
            let kw = s.Bump ()
            let arg = parseApp ctx
            Green.node PrefixExpr [ kw; arg ]
        elif s.Is Operator && (s.IsText "-" || s.IsText "+" || s.IsText "!" || s.IsText "~~~") then
            let op = s.Bump ()
            let arg = parsePostfix ctx
            Green.node PrefixExpr [ op; arg ]
        else
            errorUntilRecovery ctx "expected an expression"

    /// At a `{`: a record expression starts with `Ident (. Ident)*` followed
    /// by `=`, or `Ident ... with` (copy-and-update). Anything else (seq
    /// ranges, CE bodies, object expressions) stays brace-soup.
    and looksLikeRecordExpr () : bool =
        let rec scan (k : int) =
            let t = s.Peek k
            if t.Kind = Ident then
                let n = s.Peek (k + 1)
                if n.Kind = Operator && n.Text = "." then scan (k + 2)
                elif n.Kind = Operator && n.Text = "=" then true
                elif n.Kind = Keyword && n.Text = "with" then true
                else false
            else false
        scan 1

    and parseRecordExpr (ctx : int) : Green =
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())   // '{'
        // copy-and-update base: `{ expr with ... }`
        let isWith =
            let rec scan (k : int) =
                let t = s.Peek k
                if t.Kind = Ident then
                    let n = s.Peek (k + 1)
                    if n.Kind = Operator && n.Text = "." then scan (k + 2)
                    else n.Kind = Keyword && n.Text = "with"
                else false
            scan 0
        if isWith then
            vecAdd acc (parseExpr ctx)
            if s.IsKw "with" then vecAdd acc (s.Bump ())
        let mutable go = true
        while go && not s.AtEof && not (s.Is RBrace) do
            let mark = s.Mark
            if s.Is Semicolon then vecAdd acc (s.Bump ())
            elif s.Is Ident || (s.IsOp "?" && (s.Peek 1).Kind = Ident) then
                let f = vecNew<Green> ()
                let fieldCol = s.CurCol
                // `?Name = e` hands the OPTION itself to an optional field,
                // exactly as `?x = e` does for an optional argument
                if s.IsOp "?" then vecAdd f (s.Bump ())
                vecAdd f (s.Bump ())
                while s.IsOp "." && s.SameLine && (s.Peek 1).Kind = Ident do
                    vecAdd f (s.Bump ())
                    vecAdd f (s.Bump ())
                if s.IsOp "=" then
                    vecAdd f (s.Bump ())
                    if canStartExpr () then vecAdd f (parseExpr fieldCol)
                    else s.Diag "expected a field value"
                else s.Diag "expected '=' in record field"
                vecAdd acc (Green.node RecordExprField (vecToList f))
            else vecAdd acc (s.Bump ())
            if s.Mark = mark then go <- false
        if s.Is RBrace then vecAdd acc (s.Bump ()) else s.Diag "expected '}'"
        Green.node RecordExpr (vecToList acc)

    and parseIf (ctx : int) : Green =
        let acc = vecNew<Green> ()
        let ifCol = s.CurCol
        vecAdd acc (s.Bump ())   // if / elif
        vecAdd acc (parseExpr ifCol)
        if s.IsKw "then" then vecAdd acc (s.Bump ()) else s.Diag "expected 'then'"
        // `yield`/`return` start a body too: inside a comprehension the
        // branch IS a yield, and without this it escaped the `if` and became
        // a sibling — which would yield unconditionally
        if canStartExpr () || s.IsKw "let" || s.IsKw "yield" || s.IsKw "return" then
            vecAdd acc (parseBlock ifCol)
        let mutable go = true
        while go do
            if s.IsKw "elif" && s.CurCol >= ifCol then
                vecAdd acc (parseIf ctx)
                go <- false   // nested elif consumed the rest of the chain
            elif s.IsKw "else" && s.CurCol >= ifCol then
                vecAdd acc (s.Bump ())
                if canStartExpr () || s.IsKw "let" || s.IsKw "if" || s.IsKw "yield" || s.IsKw "return" then
                    vecAdd acc (parseBlock ifCol)
                go <- false
            else go <- false
        Green.node IfExpr (vecToList acc)

    and parseMatch (ctx : int) : Green =
        let acc = vecNew<Green> ()
        let matchCol = s.CurCol
        let kwTok = s.Cur
        let kw = s.Bump ()
        vecAdd acc kw
        let scrutinee = parseExpr matchCol
        vecAdd acc scrutinee
        if s.IsKw "with" then vecAdd acc (s.Bump ()) else s.Diag "expected 'with'"
        let clauses = vecNew<Green> ()
        parseClauses clauses matchCol
        // `match e with | Add (c, v) -> ...` where Add is an active
        // pattern's case: the scrutinee goes THROUGH the pattern's function
        // first, and the case becomes the choice case it compiles to. The
        // whole clause set has to agree — one case of one active pattern is
        // what says this match is that pattern's, and a name that merely
        // collides with a real union case elsewhere never gets rewritten.
        let clauseHeads =
            vecToList clauses
            |> List.collect (fun c ->
                match c with
                | GNode n when n.NodeKind = MatchClause ->
                    // the clause's FIRST identifier is its case head
                    (match Green.tokens c |> List.tryFind (fun t -> t.Kind = Ident) with
                     | Some t -> [ t.Text ]
                     | None -> [])
                | _ -> [])
        let apFns =
            clauseHeads |> List.choose (fun h -> dictTryFind apFunctionOf h) |> List.distinct
        match apFns with
        | [ fn ] when clauseHeads |> List.forall (fun h -> (dictTryFind apFunctionOf h).IsSome || h = "_") ->
            let acc2 = vecNew<Green> ()
            vecAdd acc2 kw
            let call =
                Green.node AppExpr
                    [ Green.node IdentExpr
                        // a SYNTHETIC offset: every table downstream is
                        // keyed by it, and sharing the scrutinee's would make
                        // two different things one
                        [ GToken { Kind = Ident; Text = fn; Leading = []; Trailing = []
                                   Offset = 80000000 + kwTok.Offset } ]
                      scrutinee ]
            vecAdd acc2 call
            for i in 2 .. vecLen acc - 1 do vecAdd acc2 (vecGet acc i)
            for c in vecToList clauses do vecAdd acc2 (renameIdents (apRenames ()) c)
            Green.node MatchExpr (vecToList acc2)
        | _ ->
            for c in vecToList clauses do vecAdd acc c
            Green.node MatchExpr (vecToList acc)

    and parseClauses (acc : Vec<Green>) (col : int) : unit =
        let finishClause (c : Vec<Green>) (barCol : int) : unit =
            vecAdd c (parsePat barCol)
            // or-pattern alternatives: bars before `->`/`when` extend the pattern
            while s.IsOp "|" && not s.AtEof && (s.SameLine || s.CurCol >= col) do
                vecAdd c (s.Bump ())
                vecAdd c (parsePat barCol)
            if s.IsKw "when" then
                vecAdd c (s.Bump ())
                vecAdd c (parseExpr barCol)
            if s.IsOp "->" then vecAdd c (s.Bump ()) else s.Diag "expected '->' in match clause"
            // the clause's own bar column guards anything nested in its body.
            // Every statement keyword a BLOCK accepts must be accepted here
            // too — `use` was missing, and an arm body starting with
            // `use x = new T(...)` fell out of the clause entirely
            guardCols <- barCol :: guardCols
            if canStartExpr () || s.IsKw "let" || s.IsKw "use" || s.IsKw "do"
               || s.IsKw "yield" || s.IsKw "return" then
                vecAdd c (parseBlock barCol)
            guardCols <- List.tail guardCols
            vecAdd acc (Green.node MatchClause (vecToList c))
        // first clause may omit the bar: `match x with null -> ...`
        if not (s.IsOp "|") && canStartAtomPat () && s.SameLine then
            let c = vecNew<Green> ()
            finishClause c s.CurCol
        let barHere () =
            s.IsOp "|"
            && (s.SameLine || s.CurCol >= col
                || (bracketDepth > 0 && s.CurCol > undentGuard ()))
        let mutable go = true
        while go && barHere () do
            let mark = s.Mark
            let barCol = s.CurCol
            let c = vecNew<Green> ()
            vecAdd c (s.Bump ())
            finishClause c barCol
            if s.Mark = mark then go <- false

    /// A sequence of statements sharing a column. Returns a single expression
    /// unmodified; wraps multiple items in BlockExpr.
    and parseBlock (outerCtx : int) : Green =
        let blockCol = s.CurCol
        let isBracketContent = pendingBracketBlock
        pendingBracketBlock <- false
        guardCols <- (if isBracketContent then -1 else blockCol) :: guardCols
        let r = parseBlockInner outerCtx blockCol
        guardCols <- List.tail guardCols
        pendingBracketBlock <- isBracketContent
        r

    and parseBlockInner (outerCtx : int) (blockCol : int) : Green =
        let acc = vecNew<Green> ()
        let canStartItem () =
            canStartExpr () || s.IsKw "let" || s.IsKw "use" || s.IsKw "do"
            || s.IsKw "and" || s.IsKw "yield" || s.IsKw "return"
        let mutable go = true
        while go && not s.AtEof do
            let mark = s.Mark
            if s.IsKw "let" || s.IsKw "use" || s.IsKw "and" then vecAdd acc (parseLet blockCol)
            elif s.IsKw "do" then
                let kids = vecNew<Green> ()
                vecAdd kids (s.Bump ())
                if s.IsOp "!" && s.SameLine then vecAdd kids (s.Bump ())
                vecAdd kids (if canStartExpr () then parseBlock blockCol else Green.node ErrorNode [])
                vecAdd acc (Green.node BlockExpr (vecToList kids))
            elif s.IsKw "yield" || s.IsKw "return" then
                let kids = vecNew<Green> ()
                vecAdd kids (s.Bump ())
                if s.IsOp "!" && s.SameLine then vecAdd kids (s.Bump ())
                if canStartExpr () then vecAdd kids (parseExpr blockCol)
                vecAdd acc (Green.node PrefixExpr (vecToList kids))
            elif canStartExpr () then vecAdd acc (parseExpr blockCol)
            else go <- false
            if s.Mark = mark then go <- false
            // same-line `;` sequencing: `a <- 1; b <- 2`
            elif s.Is Semicolon && s.SameLine then vecAdd acc (s.Bump ())
            elif s.AtEof || isBlockStopKw () || isCloser () then go <- false
            // next item: fresh line, exactly at block column
            elif not s.SameLine && s.CurCol = blockCol && canStartItem () then ()
            else go <- false
        match vecToList acc with
        | [ single ] -> single
        | items -> Green.node BlockExpr items

    // ---- declarations -----------------------------------------------------

    and parseLet (ctx : int) : Green =
        lastMajor <- "let"
        let acc = vecNew<Green> ()
        // `static let` binds at the column of `static`, so its body may be
        // indented relative to that rather than to `let`
        let letCol = s.CurCol
        if s.IsKw "static" then vecAdd acc (s.Bump ())
        vecAdd acc (s.Bump ())   // let / use / and
        // `let!`, `use!`, `and!` — the bang is a separate token, and only a
        // computation expression gives it meaning
        if s.IsOp "!" && s.SameLine then vecAdd acc (s.Bump ())
        while s.IsKw "rec" || s.IsKw "inline" || s.IsKw "mutable" || s.IsKw "private" || s.IsKw "internal" || s.IsKw "public" do
            vecAdd acc (s.Bump ())
        // binding name / pattern. `let (|Add|Rem|) x = ...` binds a name the
        // pattern parser cannot read; it becomes the function the active
        // pattern compiles to, and the cases are recorded for its uses.
        let mutable isActivePattern = false
        if atActivePatternName () then
            isActivePattern <- true
            vecAdd acc (Green.node IdentPat [ bumpActivePatternName () ])
        // `let (+++) a b = ...` — an OPERATOR defined as an ordinary
        // binding. The name fuses into one identifier, as it does everywhere
        // else; parsed as a pattern it came out as a parenthesised operator
        // section and the binding had no name at all.
        elif atOperatorName () then
            vecAdd acc (Green.node IdentPat [ bumpOperatorName () ])
        else
            vecAdd acc (parseAtomPat letCol)
        if s.Is Comma then
            // tuple destructuring: `let leading, p = scanLeading pos`
            while s.Is Comma && s.SameLine do
                vecAdd acc (s.Bump ())
                vecAdd acc (parseConsPat letCol)
        else
            // explicit type parameters: `let inline vecNew<'a> () = ...`
            if s.IsOp "<" && s.SameLine && (s.Peek 1).Text = "'" then
                vecAdd acc (Green.node TyParams (parseAngleArgs letCol))
            // curried parameters
            while canStartAtomPat () && (s.SameLine || s.CurCol > letCol) do
                vecAdd acc (parseAtomPat letCol)
        if s.IsOp ":" then
            vecAdd acc (s.Bump ())
            vecAdd acc (parseType letCol)
            // declared constraints: `let solve ... : Vector<'a> when Fractional<'a> = ...`
            while s.IsKw "when" && (s.SameLine || s.CurCol > letCol) do
                vecAdd acc (parseWhen false letCol)
        if s.IsOp "=" then
            vecAdd acc (s.Bump ())
            if s.AtEof || (not s.SameLine && s.CurCol <= letCol) then s.Diag "expected a binding body"
            else
                let body = parseBlock letCol
                // in an active pattern's own body, `Add (x, y)` CONSTRUCTS
                // the case: rename it to the choice case the pattern
                // compiles to
                vecAdd acc (if isActivePattern then renameIdents (apRenames ()) body else body)
        elif not pendingExtern then s.Diag "expected '=' in binding"
        pendingExtern <- false
        if s.IsKw "in" && s.SameLine then
            vecAdd acc (s.Bump ())
            vecAdd acc (parseBlock letCol)
        Green.node LetDecl (vecToList acc)

    and parseTypeDecl (ctx : int) : Green =
        lastMajor <- "type"
        let acc = vecNew<Green> ()
        let typeCol = s.CurCol
        vecAdd acc (s.Bump ())   // type / and
        while s.IsKw "private" || s.IsKw "internal" || s.IsKw "public" || s.IsKw "rec" do
            vecAdd acc (s.Bump ())
        // `and [<Struct>] Name(...)`: attributes may sit after the keyword
        while s.Is LBracket && (s.Peek 1).Kind = Operator && (s.Peek 1).Text = "<" do
            vecAdd acc (parseAttributeList ())
            while s.IsKw "private" || s.IsKw "internal" || s.IsKw "public" || s.IsKw "rec" do
                vecAdd acc (s.Bump ())
        if s.Is Ident then
            vecAdd acc (s.Bump ())
            // a DOTTED name: `type System.Threading.Interlocked with ...`
            // extends a type named by its full path. The last segment IS the
            // type — the spine is namespaces — so the earlier segments are
            // consumed and the name that remains is the one members hang on.
            while s.IsOp "." && s.SameLine && (s.Peek 1).Kind = Ident do
                s.Bump () |> ignore
                let seg = s.Bump ()
                // replace the accumulated name with the deeper segment
                let rest = vecToList acc |> List.filter (fun g ->
                                match g with
                                | GToken t -> t.Kind <> Ident
                                | _ -> true)
                vecClear acc
                for g in rest do vecAdd acc g
                vecAdd acc seg
        else s.Diag "expected a type name"
        if s.IsOp "<" && s.SameLine then
            vecAdd acc (Green.node TyParams (parseAngleArgs typeCol))
        // primary-constructor parameters: `type State(src : string) =`,
        // optionally with an access modifier: `type HashSet<'K> internal(...)`
        while (s.IsKw "private" || s.IsKw "internal" || s.IsKw "public") && s.SameLine
              && (s.Peek 1).Kind = LParen do
            vecAdd acc (s.Bump ())
        if s.Is LParen && s.SameLine then
            vecAdd acc (parseAtomPat typeCol)
        // `type C(args) as this =` — a name for the object under
        // construction. The tokens are kept so the parse stays lossless;
        // what the name MEANS is the same question `base` asks.
        if s.IsKw "as" && s.SameLine then
            vecAdd acc (s.Bump ())
            if s.Is Ident then vecAdd acc (s.Bump ())
        // declared class constraints: `type Box<'a> when Ordered<'a> = ...`,
        // the same `when C<'a>` a let signature carries
        while s.IsKw "when" && (s.SameLine || s.CurCol > typeCol) do
            vecAdd acc (parseWhen false typeCol)
        // `type X with member ... ` — an INTRINSIC TYPE EXTENSION: members
        // for a type declared elsewhere, and no representation of its own.
        // The `with` in place of `=` is what says so, and it is the whole
        // marker: a TypeDecl carrying no representation is an extension.
        if s.IsKw "with" then
            vecAdd acc (s.Bump ())
            parseTypeBody acc typeCol
        elif s.IsOp "=" then
            vecAdd acc (s.Bump ())
            // F#'s VERBOSE form: `type X = class ... end`, and the same for
            // struct and interface. The keyword and its `end` are pure
            // delimiters — what is between them is the ordinary body — so
            // they are consumed and dropped.
            // `interface` is ambiguous: it opens the verbose form, but it
            // also opens an interface IMPLEMENTATION as the first thing in
            // an ordinary body (`type Rng(n) =` / `interface IEnumerable<int>
            // with`). A type NAME after it means the latter.
            if s.IsKw "class" || s.IsKw "struct"
               || (s.IsKw "interface" && (s.Peek 1).Kind <> Ident) then
                s.Bump () |> ignore
                parseTypeBody acc typeCol
                if s.IsKw "end" then s.Bump () |> ignore
            elif isTypeBodyStart () && not s.SameLine && s.CurCol > typeCol then
                ()   // class/interface body only — handled below
            elif s.IsOp "|" then parseUnionCases acc typeCol
            elif s.Is LBrace then vecAdd acc (parseRecordRepr typeCol)
            elif looksLikeInlineUnion () then parseUnionCases acc typeCol
            elif canStartTypeAtom () then vecAdd acc (parseType typeCol)
            else s.Diag "expected a type representation"
            // members may follow any representation (or be the whole body)
            parseTypeBody acc typeCol
        // nested `let`s in the body reset this, but a following `and`
        // continues the TYPE, not those lets
        lastMajor <- "type"
        Green.node TypeDecl (vecToList acc)

    and isMemberStart () =
        // `static let` is a BINDING, not a member — one shared cell, which is
        // exactly how a type holds a singleton of itself
        (s.IsKw "static" && not ((s.Peek 1).Kind = Keyword && ((s.Peek 1).Text = "let" || (s.Peek 1).Text = "do")))
        || s.IsKw "member" || s.IsKw "abstract" || s.IsKw "override"
        || s.IsKw "default" || s.IsKw "interface" || s.IsKw "inherit" || s.IsKw "val"
        || s.IsKw "new"
        // an access modifier may lead: `internal new(...)`, `private val ...`
        || ((s.IsKw "private" || s.IsKw "internal" || s.IsKw "public")
            && (let k = s.Peek 1 in
                k.Kind = Keyword
                && (k.Text = "member" || k.Text = "static" || k.Text = "abstract"
                    || k.Text = "override" || k.Text = "default" || k.Text = "val"
                    || k.Text = "new" || k.Text = "inline" || k.Text = "mutable")))

    and isTypeBodyStart () =
        isMemberStart () || s.IsKw "let" || s.IsKw "do" || s.IsKw "use" || s.IsKw "static"
        // a member may carry attributes: `[<MethodImpl(...)>] member ...`
        || (s.Is LBracket && (s.Peek 1).Kind = Operator && (s.Peek 1).Text = "<")

    and parseTypeBody (acc : Vec<Green>) (typeCol : int) : unit =
        // a member may sit on the same line as `with`, or on its own line
        // indented past the construct
        let mutable go = true
        while go && not s.AtEof && (s.SameLine || (s.CurCol > typeCol)) && isTypeBodyStart () do
            let mark = s.Mark
            if s.Is LBracket then vecAdd acc (parseAttributeList ())
            elif s.IsKw "static" && (s.Peek 1).Kind = Keyword && (s.Peek 1).Text = "let" then
                // `static let`: a binding on the type, not on an instance
                vecAdd acc (parseLet typeCol)
            elif s.IsKw "let" || s.IsKw "use"
                 || (s.IsKw "static" && (s.Peek 1).Kind = Keyword && (s.Peek 1).Text = "let") then
                vecAdd acc (parseLet typeCol)
            elif s.IsKw "do" then
                let d = s.Bump ()
                let body = if canStartExpr () then parseBlock typeCol else Green.node ErrorNode []
                vecAdd acc (Green.node BlockExpr [ d; body ])
            elif s.IsKw "interface" then vecAdd acc (parseInterfaceImpl ())
            elif s.IsKw "inherit" then
                // `inherit Base` or `inherit Base(args)`: the base type, then
                // the base constructor's arguments
                let a = vecNew<Green> ()
                vecAdd a (s.Bump ())
                // parse the base type by hand: a full parseType would eat the
                // constructor arguments as a parenthesised type
                if s.Is Ident then
                    // a QUALIFIED base: `inherit Inner.Base(s)`. The spine is
                    // modules and the LAST segment names the type, so the
                    // dots are walked here rather than left to parseType,
                    // which would eat the constructor arguments as a
                    // parenthesised type.
                    // every token stays in the tree — the resolver binds the
                    // qualified path, and the parse stays lossless — while
                    // the readers take the LAST segment as the type's name
                    let parts = vecNew<Green> ()
                    vecAdd parts (s.Bump ())
                    while s.IsOp "." && s.SameLine && (s.Peek 1).Kind = Ident do
                        vecAdd parts (s.Bump ())
                        vecAdd parts (s.Bump ())
                    if s.IsOp "<" && s.SameLine then
                        vecAdd a (Green.node AppType (Green.node NamedType (vecToList parts) :: parseAngleArgs typeCol))
                    else vecAdd a (Green.node NamedType (vecToList parts))
                else vecAdd a (parseType typeCol)
                if s.Is LParen && s.SameLine then vecAdd a (parseAtom typeCol)
                vecAdd acc (Green.node InheritDecl (vecToList a))
            else vecAdd acc (parseMember ())
            if s.Mark = mark then go <- false

    and parseInterfaceImpl () : Green =
        let acc = vecNew<Green> ()
        let icol = s.CurCol
        vecAdd acc (s.Bump ())   // interface
        vecAdd acc (parseType icol)
        // implementation constraints: `interface Functor<C<'f,'g>> when 'f : Functor with`
        if s.IsKw "when" then
            vecAdd acc (s.Bump ())
            while not s.AtEof && not (s.IsKw "with") && (s.SameLine || s.CurCol > icol) do
                vecAdd acc (s.Bump ())
        if s.IsKw "with" then vecAdd acc (s.Bump ())
        parseTypeBody acc icol
        Green.node InterfaceImpl (vecToList acc)

    and parseMember () : Green =
        let acc = vecNew<Green> ()
        let mcol = s.CurCol
        while s.IsKw "static" || s.IsKw "member" || s.IsKw "abstract" || s.IsKw "override"
              || s.IsKw "default" || s.IsKw "private" || s.IsKw "internal" || s.IsKw "public"
              || s.IsKw "inline" || s.IsKw "val" || s.IsKw "mutable" do
            vecAdd acc (s.Bump ())
        if s.IsKw "type" then
            // associated type: declared `type Result`, bound in an instance
            // by `type Result = int`
            vecAdd acc (s.Bump ())
            if s.Is Ident then vecAdd acc (s.Bump ())
            if s.IsOp "=" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseType mcol)
        elif s.IsKw "new" then
            // an explicit constructor: `new(args) = { Field = ... }`
            vecAdd acc (s.Bump ())
            while canStartAtomPat () && (s.SameLine || s.CurCol > mcol) do
                vecAdd acc (parseAtomPat mcol)
            if s.IsOp ":" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseType mcol)
            if s.IsOp "=" then
                vecAdd acc (s.Bump ())
                if not (s.AtEof || (not s.SameLine && s.CurCol <= mcol)) then
                    vecAdd acc (parseBlock mcol)
        else
            // [self .] name
            if atOperatorName () then vecAdd acc (bumpOperatorName ())
            elif s.IsOp "'" && (s.Peek 1).Kind = Ident then
                // a TYPECLASS member anchored on a class parameter:
                // `member 'v.ScaledBy : 's -> 'v` — the receiver is the
                // parameter the dot-call dispatches on
                vecAdd acc (s.Bump ())
                vecAdd acc (s.Bump ())
                if s.IsOp "." && s.SameLine then
                    vecAdd acc (s.Bump ())
                    if s.Is Ident then vecAdd acc (s.Bump ())
                    else s.Diag "expected a member name"
            elif s.Is Ident then
                vecAdd acc (s.Bump ())
                if s.IsOp "." && s.SameLine then
                    vecAdd acc (s.Bump ())
                    if atOperatorName () then vecAdd acc (bumpOperatorName ())
                    elif s.Is Ident then vecAdd acc (s.Bump ())
            else s.Diag "expected a member name"
            if s.IsOp "<" && s.SameLine && (s.Peek 1).Text = "'" then
                vecAdd acc (Green.node TyParams (parseAngleArgs mcol))
            while canStartAtomPat () && (s.SameLine || s.CurCol > mcol) do
                vecAdd acc (parseAtomPat mcol)
            if s.IsOp ":" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseType mcol)
                // trailing constraints: `... : int when Pinnable<'a>` — the
                // same WhenDecl a let signature carries, so the member's
                // walk can skip the node and constraintOf can read it. Left
                // as bare tokens, `Pinnable` and `'a` land among the
                // pre-`=` identifiers and the member loses its NAME.
                while s.IsKw "when" && (s.SameLine || s.CurCol > mcol) do
                    if (s.Peek 1).Kind = Ident then vecAdd acc (parseWhen false mcol)
                    else
                        // F#-style variable constraint (`when 'm : Monad`):
                        // its tokens, in their own node
                        let cons = vecNew<Green> ()
                        vecAdd cons (s.Bump ())
                        while not s.AtEof && not (s.IsOp "=") && not (s.IsKw "when")
                              && (s.SameLine || s.CurCol > mcol) do
                            vecAdd cons (s.Bump ())
                        vecAdd acc (Green.node WhenDecl (vecToList cons))
            if s.IsKw "with"
               && (let p = s.Peek 1 in
                   p.Text = "get" || p.Text = "set" || p.Text = "inline"
                   || p.Text = "private" || p.Text = "internal" || p.Text = "public") then
                // property accessors: `member x.P with get() = ... and set v = ...`
                vecAdd acc (s.Bump ())   // with
                let mutable more = true
                while more && not s.AtEof do
                    let mark = s.Mark
                    let a2 = vecNew<Green> ()
                    while s.IsKw "inline" || s.IsKw "private" || s.IsKw "internal" || s.IsKw "public" do
                        vecAdd a2 (s.Bump ())
                    if s.Is Ident && (s.Cur.Text = "get" || s.Cur.Text = "set") then
                        vecAdd a2 (s.Bump ())
                        while canStartAtomPat () && (s.SameLine || s.CurCol > mcol) do
                            vecAdd a2 (parseAtomPat mcol)
                        if s.IsOp ":" then
                            vecAdd a2 (s.Bump ())
                            vecAdd a2 (parseType mcol)
                        if s.IsOp "=" then
                            vecAdd a2 (s.Bump ())
                            if not (s.AtEof || (not s.SameLine && s.CurCol <= mcol)) then
                                vecAdd a2 (parseBlock mcol)
                        vecAdd acc (Green.node AccessorDecl (vecToList a2))
                        // `and` between WRITTEN accessors, a comma between
                        // DECLARED ones: `abstract member Tag : obj with
                        // get, set` names the two slots and gives neither a
                        // body
                        if s.IsKw "and" then vecAdd acc (s.Bump ())
                        elif s.Is Comma then vecAdd acc (s.Bump ())
                        else more <- false
                    else
                        for g in vecToList a2 do vecAdd acc g
                        more <- false
                    if s.Mark = mark then more <- false
            elif s.IsOp "=" then
                vecAdd acc (s.Bump ())
                if s.AtEof || (not s.SameLine && s.CurCol <= mcol) then s.Diag "expected a member body"
                else vecAdd acc (parseBlock mcol)
        Green.node MemberDecl (vecToList acc)

    /// `type T = A | B of int` — an identifier directly followed by `|`/`of`.
    and looksLikeInlineUnion () : bool =
        s.Is Ident && (let n = s.Peek 1 in n.Text = "of" || n.Text = "|")

    and parseUnionCases (acc : Vec<Green>) (typeCol : int) : unit =
        // optional first case without a leading bar: `type T = A | B`
        if s.Is Ident then
            let c = vecNew<Green> ()
            vecAdd c (s.Bump ())
            if s.IsKw "of" then
                vecAdd c (s.Bump ())
                vecAdd c (parseCasePayload typeCol)
            vecAdd acc (Green.node UnionCase (vecToList c))
        let mutable go = true
        while go && s.IsOp "|" && (s.SameLine || s.CurCol > typeCol) do
            let mark = s.Mark
            let c = vecNew<Green> ()
            let barCol = s.CurCol
            vecAdd c (s.Bump ())
            if s.Is Ident then vecAdd c (s.Bump ()) else s.Diag "expected a union case name"
            // the GADT form: `| Lit of value : int -> E<int>` — the
            // constructor IS a function, and the top-level arrow names its
            // result instantiation (function PAYLOADS parenthesize, as F#
            // already requires). A payload-less refined case ascribes:
            // `| Nil : E<unit>`.
            let caseWhens () =
                while s.IsKw "when" do
                    if (s.Peek 1).Text = "'" && (s.Peek 3).Text = ":>" then
                        let acc = vecNew<Green> ()
                        vecAdd acc (s.Bump ())   // when
                        vecAdd acc (s.Bump ())   // '
                        vecAdd acc (s.Bump ())   // var
                        vecAdd acc (s.Bump ())   // :>
                        vecAdd acc (parseType barCol)
                        vecAdd c (Green.node WhenDecl (vecToList acc))
                    else vecAdd c (parseWhen false barCol)
            if s.IsKw "of" then
                vecAdd c (s.Bump ())
                vecAdd c (parseCasePayload barCol)
                if s.IsOp "->" then
                    vecAdd c (s.Bump ())
                    vecAdd c (parsePostfixType barCol)
                caseWhens ()
            elif s.IsOp ":" then
                vecAdd c (s.Bump ())
                vecAdd c (parsePostfixType barCol)
                caseWhens ()
            elif s.IsOp "=" then
                // enum case: `| Leaf = 0uy`
                vecAdd c (s.Bump ())
                if isLiteral () then vecAdd c (Green.node LiteralExpr [ s.Bump () ])
                else s.Diag "expected an enum value"
            vecAdd acc (Green.node UnionCase (vecToList c))
            if s.Mark = mark then go <- false

    and parseRecordRepr (typeCol : int) : Green =
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())   // '{'
        let mutable go = true
        while go && not s.AtEof && not (s.Is RBrace) do
            let mark = s.Mark
            if s.Is Semicolon then vecAdd acc (s.Bump ())
            elif s.IsKw "mutable" || s.Is Ident || (s.IsOp "?" && (s.Peek 1).Kind = Ident) then
                let f = vecNew<Green> ()
                if s.IsKw "mutable" then vecAdd f (s.Bump ())
                // `?Name : T` — an OPTIONAL field: the type becomes
                // option<T> and a literal may leave it out (None)
                if s.IsOp "?" then vecAdd f (s.Bump ())
                if s.Is Ident then vecAdd f (s.Bump ())
                if s.IsOp ":" then
                    vecAdd f (s.Bump ())
                    vecAdd f (parseType typeCol)
                else s.Diag "expected ':' in record field"
                vecAdd acc (Green.node RecordField (vecToList f))
            else vecAdd acc (s.Bump ())
            if s.Mark = mark then go <- false
        if s.Is RBrace then vecAdd acc (s.Bump ()) else s.Diag "expected '}'"
        Green.node RecordRepr (vecToList acc)

    and parseAttributeList () : Green =
        // `[< ... >]` — balanced, verbatim
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())   // '['
        let mutable go = true
        while go && not s.AtEof do
            if s.Is RBracket then
                vecAdd acc (s.Bump ())
                go <- false
            else
                s.SplitGt ()
                vecAdd acc (s.Bump ())
        Green.node AttributeList (vecToList acc)

    and parseModule (ctx : int) : Green =
        let acc = vecNew<Green> ()
        let modCol = s.CurCol
        vecAdd acc (s.Bump ())   // module / namespace
        while s.IsKw "rec" || s.IsKw "private" || s.IsKw "internal" || s.IsKw "public" do
            vecAdd acc (s.Bump ())
        // dotted name
        if s.Is Ident then
            vecAdd acc (s.Bump ())
            while s.IsOp "." && s.SameLine do
                vecAdd acc (s.Bump ())
                if s.Is Ident then vecAdd acc (s.Bump ())
        else s.Diag "expected a module name"
        if s.IsOp "=" then
            vecAdd acc (s.Bump ())
            // nested module: indented declaration block
            let mutable go = true
            while go && not s.AtEof do
                if not s.SameLine && s.CurCol <= modCol then go <- false
                elif canStartDecl () then
                    let mark = s.Mark
                    vecAdd acc (parseDecl (modCol + 1))
                    if s.Mark = mark then go <- false
                else go <- false
            Green.node ModuleDef (vecToList acc)
        else Green.node ModuleHeader (vecToList acc)

    and parseOpen () : Green =
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())
        if s.Is Ident then
            vecAdd acc (s.Bump ())
            while s.IsOp "." && s.SameLine do
                vecAdd acc (s.Bump ())
                if s.Is Ident then vecAdd acc (s.Bump ())
        else s.Diag "expected a module path"
        Green.node OpenDecl (vecToList acc)

    /// `Name<...>` in class-head position. Parsed by hand rather than through
    /// parseType so a following `with` or `=` is not swallowed.
    and parseClassHead (col : int) : Green =
        if s.Is Ident then
            let idt = s.Bump ()
            if s.IsOp "<" && s.SameLine then
                Green.node AppType (Green.node NamedType [ idt ] :: parseAngleArgs col)
            else Green.node NamedType [ idt ]
        else
            s.Diag "expected a class name"
            Green.node ErrorNode [ s.Bump () ]

    /// One constraint: `when C<'a>`, `when C<'a> with Result = 'a`, or the
    /// single-associated-type shorthand `when C<'a> = 'a`.
    /// `allowEq` is off in a `let`, where a trailing `=` opens the body
    /// rather than fixing an associated type. `with Result = 'a` still
    /// works there, and is unambiguous.
    and parseWhen (allowEq : bool) (col : int) : Green =
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())   // when
        vecAdd acc (parseClassHead col)
        let mutable sawWith = false
        if s.IsKw "with" then
            sawWith <- true
            vecAdd acc (s.Bump ())
            if s.Is Ident then vecAdd acc (s.Bump ())
        if s.IsOp "=" && (allowEq || sawWith) then
            vecAdd acc (s.Bump ())
            vecAdd acc (parseType col)
        Green.node WhenDecl (vecToList acc)

    /// `class C<'a,'b>` / `instance C<int,int>` — head, context, then a body
    /// of associated types and members. Both shapes are identical; only the
    /// keyword and what the body means differ.
    and parseClassLike (kind : NodeKind) : Green =
        let acc = vecNew<Green> ()
        let col = s.CurCol
        vecAdd acc (s.Bump ())   // class / instance
        vecAdd acc (parseClassHead col)
        while s.IsKw "when" && (s.SameLine || s.CurCol > col) do
            vecAdd acc (parseWhen true col)
        if s.IsOp "=" then vecAdd acc (s.Bump ())
        let mutable go = true
        while go && not s.AtEof && not s.SameLine && s.CurCol > col do
            let mark = s.Mark
            // `type Result` declares (or binds) an associated type; inside a
            // class body it needs no `static abstract` ceremony
            if s.IsKw "when" then vecAdd acc (parseWhen true col)
            elif s.IsKw "type" || isMemberStart () then vecAdd acc (parseMember ())
            else go <- false
            if s.Mark = mark then go <- false
        Green.node kind (vecToList acc)

    and parseDecl (ctx : int) : Green =
        if s.IsKw "extern" then
            // `extern let name : type` — a foreign import declaration
            let ext = s.Bump ()
            pendingExtern <- true
            (match parseLet ctx with
             | GNode n -> Green.node LetDecl (ext :: n.Children)
             | t -> t)
        elif s.IsKw "module" || s.IsKw "namespace" then parseModule ctx
        elif s.IsKw "open" then parseOpen ()
        elif s.IsKw "let" || s.IsKw "use" then parseLet ctx
        elif s.IsKw "and" then
            // mutually-recursive continuation of whichever came last
            if lastMajor = "type" then parseTypeDecl ctx else parseLet ctx
        elif s.IsKw "type" then parseTypeDecl ctx
        elif s.IsKw "class" then parseClassLike ClassDecl
        elif atInstanceDecl () then parseClassLike InstanceDecl
        elif s.IsKw "exception" then
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            if s.Is Ident then vecAdd acc (s.Bump ())
            if s.IsKw "of" then
                vecAdd acc (s.Bump ())
                // the payload may be LABELLED — `exception E of level : int`
                // — and the label is documentation, not part of the type
                let mutable go = true
                while go do
                    if s.Is Ident && (s.Peek 1).Kind = Operator && (s.Peek 1).Text = ":" then
                        s.Bump () |> ignore
                        s.Bump () |> ignore
                    vecAdd acc (parseType ctx)
                    if s.Is Comma || (s.IsOp "*" && s.SameLine) then s.Bump () |> ignore
                    else go <- false
            Green.node TypeDecl (vecToList acc)
        elif isDirectiveHere () then
            // a COMPILER DIRECTIVE: `#nowarn "7331"`, `#light`. It addresses
            // the compiler, not the program, and every one of them is either
            // about warnings F++ does not raise or about a script host it
            // does not have. Consumed to the end of its line.
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            while not s.AtEof && s.SameLine do vecAdd acc (s.Bump ())
            Green.node BlockExpr (vecToList acc)
        elif s.Is LBracket then parseAttributeList ()
        elif s.IsKw "do" then
            let d = s.Bump ()
            let body = if canStartExpr () then parseBlock ctx else Green.node ErrorNode []
            Green.node BlockExpr [ d; body ]
        elif canStartExpr () then parseExpr s.CurCol
        else errorUntilRecovery ctx "unexpected token"

    // ---- file -------------------------------------------------------------

    let items = vecNew<Green> ()
    let mutable go = true
    while go && not s.AtEof do
        let mark = s.Mark
        if canStartDecl () then vecAdd items (parseDecl 0)
        else vecAdd items (errorUntilRecovery -1 "unexpected token at top level")
        if s.Mark = mark then
            // absolute progress backstop — never hang
            vecAdd items (Green.node ErrorNode [ s.Bump () ])

    // the Eof token carries any trailing trivia of the file
    vecAdd items (s.Bump ())

    let root =
        match Green.node File (vecToList items) with
        | GNode n -> n
        | GToken _ -> { NodeKind = File; Children = []; Width = 0 }

    { Root = root; Diagnostics = s.Diagnostics }

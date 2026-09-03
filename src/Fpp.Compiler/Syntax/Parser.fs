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

/// One ACTIVE-PATTERN definition, for cross-file seeding: case name, the
/// `$ap$...` function name, the case's index, the case count, partial?, and
/// how many EXTRA parameters a use supplies before the matched value.
type ApDef =
    { ApCase : string
      ApFn : string
      ApIndex : int
      ApCount : int
      ApPartial : bool
      ApParams : int }

let parseSeeded (apSeed : ApDef list) (src : string) : ParseResult =
    let toks = vecOfList (Lexer.tokenize src)
    let s = State(src, toks)

    // `and` continues whatever major declaration came last (let rec vs type)
    let mutable lastMajor = "let"
    // set while parsing `extern let ...` — suppresses the missing-'=' diag
    let mutable pendingExtern = false

    let isLiteral () = List.contains s.Cur.Kind literalKinds
    /// the token AFTER the current one — the enum-case arm looks past its `=`
    let isLiteral2 () = List.contains (s.Peek 1).Kind literalKinds
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
    /// SPACES are allowed around the operator: `( * )` and `( *** )` have to
    /// be written that way, since `(*` opens a comment. A NEWLINE inside is
    /// still not an operator name.
    let spacesOnly (ts : Trivia list) =
        ts |> List.forall (fun t -> t.TriviaKind = Whitespace)
    let atOperatorName () =
        s.Is LParen && spacesOnly s.Cur.Trailing
        && (s.Peek 1).Kind = Operator
        && spacesOnly (s.Peek 1).Leading && spacesOnly (s.Peek 1).Trailing
        && (s.Peek 2).Kind = RParen && spacesOnly (s.Peek 2).Leading

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
            // `(|Pos|_|)` — a PARTIAL active pattern: the trailing `_` case is
            // the "no match" one, and the function answers an option
            if ok && fin && List.length names >= 1 && List.length names <= 5 then names else []

    let atActivePatternName () = not (List.isEmpty (activePatternCases ()))

    /// The function an active pattern becomes, and the choice case each of
    /// its cases becomes. Recorded as the definition is parsed, and read at
    /// every later use — which is why a definition has to precede its uses,
    /// as it does in F#.
    /// A union case's NAMED fields, in declaration order — `| Rectangle of
    /// Width : float * Height : float`. F# lets those names be used at the
    /// construction (`Rectangle (Width = 4.0, Height = 5.0)`) and in a
    /// pattern (`Rectangle (Width = w)`); both are rewritten POSITIONALLY
    /// here, so nothing downstream needs to know the names. Recorded as the
    /// declaration is parsed, like the active-pattern tables below, so a
    /// declaration has to precede its uses — as it does in F#.
    let ucFieldNames = dictNew<string, string list> ()
    /// the case whose ARGUMENT patterns are being parsed, "" outside one
    let mutable curCasePat = ""

    let apFunctionOf = dictNew<string, string> ()      // case -> function
    let apIndexOf = dictNew<string, string> ()         // case -> choice case
    let apCaseIndex = dictNew<string, int> ()          // case -> 0-based index
    let apCaseCount = dictNew<string, int> ()          // case -> how many cases
    let apIsPartial = dictNew<string, bool> ()         // case -> answers an option?
    let apParamCount = dictNew<string, int> ()         // case -> extra args the USE gives
    // cross-file uses: the workspace seeds every project file's (and every
    // linked library's) active-pattern definitions, because this rewrite is
    // PARSE-time and these dicts are otherwise per-file. Unseeded, a
    // consumer's `PairP (n, _)` stayed an ordinary pattern: a total case was
    // at least an unknown-case error, but a partial one matched with a
    // GARBAGE binding, and a tuple payload silently missed (fpp.base #32).
    // A local definition simply overwrites its seed row with the same truth.
    do
        for d in apSeed do
            dictSet apFunctionOf d.ApCase d.ApFn
            dictSet apCaseIndex d.ApCase d.ApIndex
            dictSet apCaseCount d.ApCase d.ApCount
            dictSet apIsPartial d.ApCase d.ApPartial
            dictSet apParamCount d.ApCase d.ApParams
            if d.ApCount > 1 then
                dictSet apIndexOf d.ApCase ("Choice" + string d.ApCount + "Of" + string (d.ApIndex + 1))

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

    /// A match CLAUSE of an active pattern. The case name becomes its choice
    /// case, and a case matched with NO sub-pattern gains a wildcard: the
    /// choice case carries a payload (unit, for a nullary case), and without
    /// the wildcard the pattern was read as the constructor FUNCTION.
    let rec renameApClause (m : Dict<string, string>) (g : Green) : Green =
        let caseOf (h : GreenNode) : string option =
            if h.NodeKind <> IdentPat then None
            else
                match Green.tokens (GNode h) with
                | [ t ] when t.Kind = Ident -> dictTryFind m t.Text
                | _ -> None
        let renamedHead (h : GreenNode) (r : string) : Green =
            match Green.tokens (GNode h) with
            | [ t ] -> Green.node IdentPat [ GToken { t with Text = r } ]
            | _ -> GNode h
        match g with
        | GToken t when t.Kind = Ident ->
            (match dictTryFind m t.Text with
             | Some r -> GToken { t with Text = r }
             | None -> g)
        | GToken _ -> g
        | GNode n when n.NodeKind = AppPat ->
            (match n.Children with
             | GNode h :: rest when (caseOf h).IsSome ->
                 Green.node AppPat (renamedHead h (caseOf h).Value :: List.map (renameApClause m) rest)
             | kids -> Green.node AppPat (List.map (renameApClause m) kids))
        | GNode n when n.NodeKind = IdentPat && (caseOf n).IsSome ->
            let off =
                match Green.tokens (GNode n) |> List.tryHead with
                | Some t -> t.Offset + 91000000
                | None -> 0
            let wild = Green.node WildcardPat [ GToken { Kind = Ident; Text = "_"; Leading = []; Trailing = []; Offset = off } ]
            Green.node AppPat [ renamedHead n (caseOf n).Value; wild ]
        | GNode n -> Green.node n.NodeKind (n.Children |> List.map (renameApClause m))

    /// The BODY of an active pattern, with each case name replaced by the
    /// choice case it compiles to. A case used with no argument (`Even`, the
    /// nullary shape) becomes `Choice2Of1 ()` — the choice case carries a
    /// payload, so left bare it was the CONSTRUCTOR FUNCTION and the match
    /// tested tags against a closure.
    let rec renameApBody (m : Dict<string, string>) (g : Green) : Green =
        let caseOf (h : GreenNode) : string option =
            if h.NodeKind <> IdentExpr then None
            else
                match Green.tokens (GNode h) with
                | [ t ] when t.Kind = Ident -> dictTryFind m t.Text
                | _ -> None
        let renamedHead (h : GreenNode) (r : string) : Green =
            match Green.tokens (GNode h) with
            | [ t ] -> Green.node IdentExpr [ GToken { t with Text = r } ]
            | _ -> GNode h
        match g with
        | GToken _ -> g
        | GNode n when n.NodeKind = AppExpr ->
            (match n.Children with
             | GNode h :: rest when (caseOf h).IsSome ->
                 Green.node AppExpr (renamedHead h (caseOf h).Value :: List.map (renameApBody m) rest)
             | kids -> Green.node AppExpr (List.map (renameApBody m) kids))
        | GNode n when (match n.NodeKind with IdentExpr -> true | _ -> false) && (caseOf n).IsSome ->
            let off =
                match Green.tokens (GNode n) |> List.tryHead with
                | Some t -> t.Offset + 90000000
                | None -> 0
            let unit_ =
                Green.node ParenExpr
                    [ GToken { Kind = LParen; Text = "("; Leading = []; Trailing = []; Offset = off }
                      GToken { Kind = RParen; Text = ")"; Leading = []; Trailing = []; Offset = off + 1 } ]
            Green.node AppExpr [ renamedHead n (caseOf n).Value; unit_ ]
        | GNode n -> Green.node n.NodeKind (n.Children |> List.map (renameApBody m))

    /// The clauses of a match (or a `function`) that mention an ACTIVE
    /// PATTERN, as a chain: each clause becomes its own match over the
    /// already-bound scrutinee, with the rest of the chain as its
    /// fallthrough. That is what lets a PARTIAL pattern fail into the next
    /// clause, several different patterns share one match, and an active
    /// pattern sit beside ordinary ones.
    /// Synthetic offsets for the active-pattern desugar. One counter, so two
    /// synthesised nodes never share an offset — every table downstream is
    /// keyed by it.
    let mutable apSynthNext = 86000000
    let apTok (k : TokenKind) (txt : string) : Green =
        apSynthNext <- apSynthNext + 1
        GToken { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = apSynthNext }

    /// The NAMES a case payload declares, one per slot ("" where the slot is
    /// unnamed). `Radius : float` and `W : float * H : float` both read off
    /// the payload node's direct children: a name, its colon, its type.
    let payloadFieldNames (g : Green) : string list =
        let isTypeNode (k : NodeKind) =
            k = NamedType || k = VarType || k = AnonType || k = TupleType
            || k = StructTupleType || k = FunType || k = AppType || k = PostfixType
            || k = ParenType
        match g with
        | GNode n ->
            let names = vecNew<string> ()
            let mutable pending = ""
            for ch in n.Children do
                match ch with
                | GToken t when t.Kind = Ident -> pending <- t.Text
                | GToken _ -> ()
                | GNode m when isTypeNode m.NodeKind ->
                    vecAdd names pending
                    pending <- ""
                | GNode _ -> ()
            vecToList names
        | GToken _ -> []

    /// The `name = value` pairs a parenthesised argument list spells, or None
    /// when any element is something else. Works for both trees: the elements
    /// of an expression list are `BinaryExpr =` nodes, and a pattern list
    /// carries the name and `=` as loose tokens beside the element.
    let namedExprPairs (inner : Green list) : (string * Green) list option =
        let out = vecNew<string * Green> ()
        let mutable ok = true
        for g in inner do
            match g with
            | GNode n when n.NodeKind = BinaryExpr ->
                (match n.Children with
                 | [ GNode l; GToken op; (GNode _ as v) ] when
                       op.Kind = Operator && op.Text = "=" && l.NodeKind = IdentExpr ->
                     (match l.Children with
                      | [ GToken nt ] when nt.Kind = Ident -> vecAdd out (nt.Text, v)
                      | _ -> ok <- false)
                 | _ -> ok <- false)
            | GNode n when n.NodeKind = TupleExpr ->
                ok <- false   // handled by the caller, which flattens first
            | GToken t when t.Kind = Comma || t.Kind = LParen || t.Kind = RParen -> ()
            | _ -> ok <- false
        if ok && vecLen out > 0 then Some (vecToList out) else None

    /// `Rectangle (Width = 4.0, Height = 5.0)` — a union case applied to
    /// NAMED arguments, rebuilt in the declaration's order. Anything that is
    /// not exactly one parenthesised list of `Field = value` over a KNOWN
    /// case is left alone, so an ordinary `f (x = 1)` comparison is
    /// untouched.
    let rec fixNamedCaseApp (g : Green) : Green =
        match g with
        | GNode n when n.NodeKind = AppExpr ->
            (match n.Children with
             | [ GNode h; GNode par ] when h.NodeKind = IdentExpr && par.NodeKind = ParenExpr ->
                 let caseName =
                     match h.Children with
                     | [ GToken t ] when t.Kind = Ident -> t.Text
                     | _ -> ""
                 (match dictTryFind ucFieldNames caseName with
                  | Some declared ->
                      // the elements: one BinaryExpr, or a TupleExpr of them
                      let elems =
                          par.Children
                          |> List.collect (fun c ->
                              match c with
                              | GNode m when m.NodeKind = TupleExpr -> m.Children
                              | GNode m when m.NodeKind = BinaryExpr -> [ c ]
                              | _ -> [])
                      (match namedExprPairs elems with
                       | Some pairs when
                             List.length pairs = List.length declared
                             && pairs |> List.forall (fun (nm, _) -> List.contains nm declared) ->
                           let ordered =
                               declared
                               |> List.map (fun d -> pairs |> List.find (fun (nm, _) -> nm = d) |> snd)
                           let inner =
                               match ordered with
                               | [ one ] -> [ one ]
                               | many ->
                                   let acc = vecNew<Green> ()
                                   many |> List.iteri (fun i v ->
                                       if i > 0 then vecAdd acc (apTok Comma ",")
                                       vecAdd acc v)
                                   [ Green.node TupleExpr (vecToList acc) ]
                           Green.node AppExpr
                               [ GNode h
                                 Green.node ParenExpr ((apTok LParen "(") :: inner @ [ apTok RParen ")" ]) ]
                       | _ -> g)
                  | None -> g)
             | _ -> g)
        | _ -> g

    /// `let (Split (n, s)) = e` — an active pattern in a BINDING. The pattern
    /// becomes the payload it matches and the right-hand side goes through the
    /// pattern's function, which is the same rewrite a match clause gets.
    let apLetRewrite (pat : Green) (rhs : Green) : (Green * Green) option =
        let isPatNode (k : Green) =
            match k with
            | GNode m ->
                (match m.NodeKind with
                 | IdentPat | WildcardPat | LiteralPat | TuplePat | StructTuplePat
                 | ConsPat | AppPat | ParenPat | ListPat | ArrayPat | AndPat | AsPat
                 | TypeTestPat | RecordPat -> true
                 | _ -> false)
            | GToken _ -> false
        // the pattern may be parenthesised: `let (Split (n, s)) = …`
        let rec inner (p : Green) : Green =
            match p with
            | GNode m when m.NodeKind = ParenPat ->
                (match m.Children |> List.filter isPatNode with
                 | [ one ] -> inner one
                 | _ -> p)
            | _ -> p
        let p0 = inner pat
        let head =
            match p0 with
            | GNode m when m.NodeKind = IdentPat ->
                (match Green.tokens p0 with [ t ] when t.Kind = Ident -> Some (t.Text, []) | _ -> None)
            | GNode m when m.NodeKind = AppPat ->
                (match m.Children with
                 | GNode h :: rest when h.NodeKind = IdentPat ->
                     (match Green.tokens (GNode h) with
                      | [ t ] when t.Kind = Ident -> Some (t.Text, rest |> List.filter isPatNode)
                      | _ -> None)
                 | _ -> None)
            | _ -> None
        match head with
        | Some (h, args) when (dictTryFind apFunctionOf h).IsSome ->
            let fn = (dictTryFind apFunctionOf h).Value
            let n = match dictTryFind apCaseCount h with Some c -> c | None -> 1
            let i = match dictTryFind apCaseIndex h with Some c -> c | None -> 0
            let partial = (dictTryFind apIsPartial h) = Some true
            let payload = if List.isEmpty args then [ Green.node WildcardPat [ apTok Ident "_" ] ] else args
            let choice =
                if n > 1 then
                    Green.node ParenPat
                        [ Green.node AppPat (Green.node IdentPat [ apTok Ident ("Choice" + string n + "Of" + string (i + 1)) ] :: payload) ]
                else (match payload with [ one ] -> one | many -> Green.node AppPat many)
            let pat2 =
                if partial then Green.node AppPat [ Green.node IdentPat [ apTok Ident "Some" ]; choice ] else choice
            // NOT re-parenthesised: an extra ParenPat hides the tuple's comma
            // from the destructure test, and the binding then took just its
            // first name
            Some (pat2, Green.node AppExpr [ Green.node IdentExpr [ apTok Ident fn ]; rhs ])
        | _ -> None

    /// Does a clause's PATTERN mention an active-pattern case — at the head
    /// or nested inside another pattern (`Some (Pos v)`)? The body is not
    /// scanned: a value there may share a case's name.
    let clauseUsesAp (c : Green) : bool =
        let isPatNode (k : Green) =
            match k with
            | GNode m ->
                (match m.NodeKind with
                 | IdentPat | WildcardPat | LiteralPat | TuplePat | StructTuplePat
                 | ConsPat | AppPat | ParenPat | ListPat | ArrayPat | AndPat | AsPat
                 | TypeTestPat | RecordPat -> true
                 | _ -> false)
            | GToken _ -> false
        match c with
        | GNode cn when cn.NodeKind = MatchClause ->
            (match cn.Children |> List.tryFind isPatNode with
             | Some p ->
                 Green.tokens p
                 |> List.exists (fun t -> t.Kind = Ident && (dictTryFind apFunctionOf t.Text).IsSome)
             | None -> false)
        | _ -> false

    let apChain (baseOff0 : int) (scrutName : string) (clauses : Green list) : Green =
        let mutable synth = baseOff0
        let fresh () = synth <- synth + 1; synth
        let tok (k : TokenKind) (txt : string) : Green =
            GToken { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = fresh () }
        let identE (nm : string) = Green.node IdentExpr [ tok Ident nm ]
        let identP (nm : string) = Green.node IdentPat [ tok Ident nm ]
        let wildP () = Green.node WildcardPat [ tok Ident "_" ]
        let unitE () = Green.node ParenExpr [ tok LParen "("; tok RParen ")" ]
        let unitP () = Green.node ParenPat [ tok LParen "("; tok RParen ")" ]
        let failE () =
            Green.node AppExpr
                [ identE "failwith"; Green.node LiteralExpr [ tok StringLit "match failure" ] ]
        let isPat (k : Green) =
            match k with
            | GNode m ->
                (match m.NodeKind with
                 | IdentPat | WildcardPat | LiteralPat | TuplePat | StructTuplePat
                 | ConsPat | AppPat | ParenPat | ListPat | ArrayPat | AndPat | AsPat
                 | TypeTestPat | RecordPat -> true
                 | _ -> false)
            | GToken _ -> false
        let isExprNode (k : Green) =
            match k with
            | GNode m ->
                (match m.NodeKind with
                 | IdentExpr | LiteralExpr | AppExpr | ParenExpr | BinaryExpr | MatchExpr
                 | IfExpr | LambdaExpr | BlockExpr | ListExpr | ArrayExpr | RecordExpr
                 | DotExpr | TupleExpr | PrefixExpr | LetDecl | CastExpr -> true
                 | _ -> false)
            | GToken _ -> false
        /// a pattern used as an ARGUMENT of a parameterized pattern is an
        /// EXPRESSION in F#: only the literal and identifier shapes cross over
        let patAsExpr (p : Green) : Green option =
            match p with
            | GNode m when m.NodeKind = LiteralPat -> Some (Green.node LiteralExpr (Green.tokens p |> List.map GToken))
            | GNode m when m.NodeKind = IdentPat -> Some (Green.node IdentExpr (Green.tokens p |> List.map GToken))
            | GNode m when m.NodeKind = ParenPat ->
                (match Green.tokens p |> List.filter (fun t -> t.Kind = Ident || t.Kind = IntLit
                                                               || t.Kind = StringLit || t.Kind = FloatLit) with
                 | [ t ] when t.Kind = Ident -> Some (Green.node IdentExpr [ GToken t ])
                 | [ t ] -> Some (Green.node LiteralExpr [ GToken t ])
                 | _ -> None)
            | _ -> None
        /// the head name and arguments of a pattern, when it has one
        let headOfPat (p : Green) : (string * Green list) option =
            match p with
            | GNode m when m.NodeKind = IdentPat ->
                (match Green.tokens p with
                 | [ t ] when t.Kind = Ident -> Some (t.Text, [])
                 | _ -> None)
            | GNode m when m.NodeKind = AppPat ->
                (match m.Children with
                 | GNode h :: rest when h.NodeKind = IdentPat ->
                     (match Green.tokens (GNode h) with
                      | [ t ] when t.Kind = Ident -> Some (t.Text, rest |> List.filter isPat)
                      | _ -> None)
                 | _ -> None)
            | _ -> None
        /// the pattern the payload of case `h` matches against
        let payloadPattern (h : string) (payload : Green list) : Green =
            let n = match dictTryFind apCaseCount h with Some c -> c | None -> 1
            let i = match dictTryFind apCaseIndex h with Some c -> c | None -> 0
            let partial = (dictTryFind apIsPartial h) = Some true
            let args = if List.isEmpty payload then [ wildP () ] else payload
            let choice =
                if n > 1 then
                    Green.node ParenPat [ Green.node AppPat (identP ("Choice" + string n + "Of" + string (i + 1)) :: args) ]
                else (match args with [ one ] -> one | many -> Green.node AppPat many)
            if partial then Green.node AppPat [ identP "Some"; choice ] else choice
        /// PEEL every active-pattern use out of a pattern, at any depth: each
        /// becomes a fresh binder, and the test it stands for is recorded so
        /// the clause can run it after the ordinary pattern has matched.
        let rec peel (peeled : Vec<string * string * Green list * Green>) (p : Green) : Green =
            match headOfPat p with
            | Some (h, args0) when (dictTryFind apFunctionOf h).IsSome ->
                let fn = (dictTryFind apFunctionOf h).Value
                let np = match dictTryFind apParamCount h with Some k -> k | None -> 0
                let take = min np (List.length args0)
                let extra = args0 |> List.truncate take |> List.choose patAsExpr
                let payload = args0 |> List.skip take |> List.map (peel peeled)
                let binder = "__apV" + string (fresh ())
                vecAdd peeled (binder, fn, extra, payloadPattern h payload)
                identP binder
            | _ ->
                (match p with
                 | GNode m when m.NodeKind = AppPat || m.NodeKind = ParenPat || m.NodeKind = TuplePat
                                || m.NodeKind = ConsPat || m.NodeKind = ListPat || m.NodeKind = ArrayPat
                                || m.NodeKind = AndPat || m.NodeKind = AsPat || m.NodeKind = RecordPat ->
                     Green.node m.NodeKind (m.Children |> List.map (fun c -> if isPat c then peel peeled c else c))
                 | _ -> p)
        let rec chain (cs : Green list) : Green =
            match cs with
            | [] -> failE ()
            | c :: rest ->
                match c with
                | GNode cn when cn.NodeKind = MatchClause ->
                    let kids = cn.Children
                    let patIdx = kids |> List.mapi (fun i k -> i, k) |> List.tryPick (fun (i, k) -> if isPat k then Some i else None)
                    (match patIdx with
                     | None -> chain rest
                     | Some pi ->
                         let pat = List.item pi kids
                         let guard =
                             kids |> List.mapi (fun i k -> i, k)
                                  |> List.tryPick (fun (i, k) ->
                                        match k with
                                        | GToken t when t.Kind = Keyword && t.Text = "when" ->
                                            kids |> List.skip (i + 1) |> List.tryFind isExprNode
                                        | _ -> None)
                         let body =
                             match kids |> List.filter isExprNode |> List.rev with
                             | b :: _ when guard.IsNone || (match guard with Some g -> not (System.Object.ReferenceEquals (g, b)) | None -> true) -> b
                             | _ -> unitE ()
                         let peeled = vecNew<string * string * Green list * Green> ()
                         let pat2 = peel peeled pat
                         let hasTests = vecLen peeled > 0 || guard.IsSome
                         // the rest of the chain, behind a join point when a
                         // failed TEST (not just a failed pattern) has to
                         // reach it — otherwise it would be duplicated once
                         // per test
                         let joinName = "__apJ" + string (fresh ())
                         let needJoin = hasTests && not (List.isEmpty rest)
                         let fallthrough () =
                             if List.isEmpty rest then failE ()
                             elif needJoin then Green.node AppExpr [ identE joinName; unitE () ]
                             else chain rest
                         let inner0 = if guard.IsSome then
                                        Green.node IfExpr
                                            [ tok Keyword "if"; guard.Value; tok Keyword "then"; body
                                              tok Keyword "else"; fallthrough () ]
                                      else body
                         let mutable inner = inner0
                         for k in (vecLen peeled - 1) .. -1 .. 0 do
                             let (binder, fn, extra, casePat) = vecGet peeled k
                             let call = Green.node AppExpr ([ identE fn ] @ extra @ [ identE binder ])
                             inner <-
                                 Green.node MatchExpr
                                     [ tok Keyword "match"; call; tok Keyword "with"
                                       Green.node MatchClause [ tok Operator "|"; casePat; tok Operator "->"; inner ]
                                       Green.node MatchClause [ tok Operator "|"; wildP (); tok Operator "->"; fallthrough () ] ]
                         let outer =
                             let tail =
                                 if List.isEmpty rest && not hasTests then []
                                 else [ Green.node MatchClause [ tok Operator "|"; wildP (); tok Operator "->"; fallthrough () ] ]
                             Green.node MatchExpr
                                 ([ tok Keyword "match"; identE scrutName; tok Keyword "with"
                                    Green.node MatchClause [ tok Operator "|"; pat2; tok Operator "->"; inner ] ] @ tail)
                         if needJoin then
                             Green.node LetDecl
                                 [ tok Keyword "let"; identP joinName; unitP (); tok Operator "="
                                   chain rest; tok Keyword "in"; outer ]
                         else outer)
                | _ -> chain rest
        chain clauses

    let bumpActivePatternName () : Green =
        let names0 = activePatternCases ()
        let l = s.Cur
        // a trailing `_` case marks a PARTIAL pattern: the function answers
        // an OPTION, and a `None` falls through to the next clause
        let partial = (match List.tryLast names0 with Some "_" -> true | _ -> false)
        let names = if partial then names0 |> List.filter (fun c -> c <> "_") else names0
        let fname = "$ap$" + String.concat "$" names0
        let n = List.length names
        // A MULTI-CASE PARTIAL is not a thing: `(|A|B|_|)`. A total pattern
        // answers which case (a Choice), a partial one answers whether it
        // matched (an option), and no return type says both. F# rejects it
        // and so must this — accepted, the cases here rode a Choice while
        // callers read an option.
        if partial && n > 1 then
            s.Diag "multi-case partial active patterns are not supported"
        names |> List.iteri (fun i c ->
            dictSet apFunctionOf c fname
            dictSet apCaseIndex c i
            dictSet apCaseCount c n
            dictSet apIsPartial c partial
            // ONE case carries its payload bare; several ride a choice union
            if n > 1 then dictSet apIndexOf c ("Choice" + string n + "Of" + string (i + 1)))
        // ( |A |B ... |) — a bar and a name per case, one closing bar, two
        // parens: 2n + 3 tokens, counting the partial pattern's `_` case
        let n0 = List.length names0
        let mutable k = 0
        while k < 2 * n0 + 3 do
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
    /// The column of the BINDING a block belongs to. An infix operator may
    /// start a continuation line left of the expression it continues, as long
    /// as it stays right of this — F#'s offside exception for infix tokens.
    let mutable outerCols : int list = []
    let outerCol () = match outerCols with c :: _ -> c | [] -> 0 - 1
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
        parseAsSuffix (parseAndSuffix p)

    /// `p1 & p2` — BOTH sides must match, and both sets of binders come into
    /// scope. Binds tighter than `as` and looser than everything else, as in
    /// F#; it is what a parameterized partial pattern is usually combined
    /// with (`DivisibleByTwo & DivisibleByX 3`).
    and parseAndSuffix (p : Green) : Green =
        if s.IsText "&" && s.Is Operator then
            let op = s.Bump ()
            let rhs = parseAndSuffix (parseConsPat 0)
            Green.node AndPat [ p; op; rhs ]
        else p

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
            let outer = curCasePat
            curCasePat <-
                (match head with
                 | GNode h when h.NodeKind = IdentPat ->
                     (match h.Children with
                      | [ GToken t ] when t.Kind = Ident && (dictTryFind ucFieldNames t.Text).IsSome -> t.Text
                      | _ -> "")
                 | _ -> "")
            let caseHere = curCasePat
            while canStartAtomPat () && s.SameLine do
                vecAdd acc (parseAtomPat ctx)
            curCasePat <- outer
            fixNamedCasePat caseHere (Green.node AppPat (vecToList acc))
        else head

    /// The named-field pattern list, rebuilt POSITIONALLY: each declared
    /// slot takes the pattern its name was given, and a slot no name
    /// mentioned takes a wildcard (F# allows a partial list).
    and fixNamedCasePat (caseName : string) (g : Green) : Green =
        if caseName = "" then g
        else
        match dictTryFind ucFieldNames caseName, g with
        | Some declared, GNode n when n.NodeKind = AppPat ->
            (match n.Children with
             | [ hd; GNode par ] when par.NodeKind = ParenPat ->
                 // collect `Ident = pat` triples; anything else means the
                 // list is ordinary and stays as written
                 let pairs = vecNew<string * Green> ()
                 let mutable ok = true
                 let mutable i = 0
                 let kids = par.Children
                 let count = List.length kids
                 while ok && i < count do
                     match List.item i kids with
                     | GToken t when t.Kind = LParen || t.Kind = RParen || t.Kind = Comma -> i <- i + 1
                     | GToken t when t.Kind = Ident && i + 2 < count ->
                         (match List.item (i + 1) kids with
                          | GToken eq when eq.Kind = Operator && eq.Text = "=" ->
                              vecAdd pairs (t.Text, List.item (i + 2) kids)
                              i <- i + 3
                          | _ -> ok <- false)
                     | _ -> ok <- false
                 if not ok || vecLen pairs = 0 then g
                 else
                     let given = vecToList pairs
                     if given |> List.exists (fun (nm, _) -> not (List.contains nm declared)) then g
                     else
                         let ordered =
                             declared
                             |> List.map (fun d ->
                                 match given |> List.tryFind (fun (nm, _) -> nm = d) with
                                 | Some (_, v) -> v
                                 | None -> Green.node WildcardPat [ apTok Ident "_" ])
                         let acc = vecNew<Green> ()
                         vecAdd acc (apTok LParen "(")
                         ordered |> List.iteri (fun k v ->
                             if k > 0 then vecAdd acc (apTok Comma ",")
                             vecAdd acc v)
                         vecAdd acc (apTok RParen ")")
                         Green.node AppPat [ hd; Green.node ParenPat (vecToList acc) ]
             | _ -> g)
        | _ -> g

    and canStartAtomPat () =
        s.Is Ident || isLiteral () || isLiteralKw () || s.Is LParen || s.Is LBracket || s.Is LBrace
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
                // `Circle (Radius = r)` — a NAMED field pattern. Only inside
                // the argument list of a case that declares that name, so an
                // ordinary parenthesised pattern is never misread; the name
                // and its `=` ride as loose tokens and parseAppPat reorders
                // the whole list positionally.
                let namedHere () =
                    curCasePat <> "" && s.Is Ident && (s.Peek 1).Kind = Operator
                    && (s.Peek 1).Text = "="
                    && (match dictTryFind ucFieldNames curCasePat with
                        | Some ns -> List.contains s.Cur.Text ns
                        | None -> false)
                let mutable go = canStartAtomPat () || optHere ()
                while go do
                    if optHere () then vecAdd acc (s.Bump ())
                    if namedHere () then
                        vecAdd acc (s.Bump ())   // field name
                        vecAdd acc (s.Bump ())   // =

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
        // `[| p; q |]` — an ARRAY pattern, spelled the way the literal is.
        // Read as a LIST pattern (the bar just another token to skip) it
        // typed the scrutinee as a list and every array match was an error.
        elif s.Is LBracket && (s.Peek 1).Kind = Operator && ((s.Peek 1).Text = "|" || (s.Peek 1).Text = "||") then
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())   // [
            vecAdd acc (s.Bump ())   // | (or || when empty)
            let mutable go = true
            while go && not s.AtEof && not (s.Is RBracket) && not (s.IsOp "|") do
                let mark = s.Mark
                if s.Is Semicolon then vecAdd acc (s.Bump ())
                elif canStartAtomPat () then vecAdd acc (parsePat ctx)
                else vecAdd acc (s.Bump ())
                if s.Mark = mark then go <- false
            if s.IsOp "|" then vecAdd acc (s.Bump ())
            if s.Is RBracket then vecAdd acc (s.Bump ()) else s.Diag "expected '|]' in pattern"
            Green.node ArrayPat (vecToList acc)
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
        elif s.Is LBrace then
            // record pattern: `{ F1 = p1; F2 = p2 }` — each field is an
            // IdentPat (the NAME), the `=`, and the field's own pattern
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            let mutable go = true
            while go && not s.AtEof && not (s.Is RBrace) do
                let mark = s.Mark
                if s.Is Semicolon then vecAdd acc (s.Bump ())
                elif s.Is Ident then
                    vecAdd acc (Green.node IdentPat [ s.Bump () ])
                    (if s.IsOp "=" then vecAdd acc (s.Bump ()) else s.Diag "expected '=' in record pattern")
                    vecAdd acc (parseAsSuffix (parseConsPat ctx))
                else vecAdd acc (s.Bump ())
                if s.Mark = mark then go <- false
            if s.Is RBrace then vecAdd acc (s.Bump ()) else s.Diag "expected '}' in record pattern"
            Green.node RecordPat (vecToList acc)
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
            // operators may sit at exactly the block column on a fresh line —
            // or LEFT of it, down to the binding's own column: `let z =    x`
            // then `        -- 1` continues the expression, which is F#'s
            // offside exception for an infix token
            let allowed =
                s.SameLine || s.CurCol >= ctx || bracketDepth > 0
                || (s.Is Operator && s.CurCol > outerCol () && infixPrec s.Cur.Text > 0)
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
                    // `a.[lo..]` — an OPEN range: the `..` is there and the
                    // upper bound is not. Left as an error the whole slice
                    // form was unusable; the one-sided node is the marker
                    // lowering fills in the array's length for.
                    if opText = ".." && s.Is RBracket then
                        lhs <- Green.node BinaryExpr [ lhs; op ]
                    else
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
        // `f !x` — a DEREF as a curried argument, same adjacency rule
        // (`max !x 3` passes the cell's value; `!` is never binary in F#)
        let isDerefArg () =
            s.IsOp "!" && s.GapBefore
            && (let n = s.Peek 1 in
                n.Offset = s.Cur.Offset + 1 && (n.Kind = Ident || n.Kind = LParen))
        let parseArg () =
            if isNegArg () || isAddrArg () || isDerefArg () then
                let op = s.Bump ()
                Green.node PrefixExpr [ op; parsePostfix ctx ]
            else parsePostfix ctx
        let head = parsePostfix ctx
        if (canStartAtom () || isNegArg () || isAddrArg () || isDerefArg ()) && (s.SameLine || s.CurCol > ctx) then
            let acc = vecNew<Green> ()
            vecAdd acc head
            while (canStartAtom () || isNegArg () || isAddrArg () || isDerefArg ()) && (s.SameLine || s.CurCol > ctx) do
                vecAdd acc (parseArg ())
            fixNamedCaseApp (Green.node AppExpr (vecToList acc))
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
            elif s.IsOp "?" && isAdjacentTo e && s.SameLine && (s.Peek 1).Kind = Ident then
                // DYNAMIC ACCESS: `scope?Alpha` is `(?) scope "Alpha"` — the
                // member name becomes a STRING and the user-defined `(?)`
                // operator is an ordinary binary application (FShade's
                // custom-uniform spelling, fpp-shader-hooks request 4). The
                // rewrite is a BinaryExpr on the fused name, which is exactly
                // the let-bound-operator shape Infer and Lower already
                // handle. Adjacency required, as for `a[i]` — `a ? b` with
                // spaces stays an error rather than quietly meaning this.
                let q = s.Bump ()
                let nm = s.Bump ()
                (match nm with
                 | GToken nt ->
                     let str = { Kind = StringLit; Text = "\"" + nt.Text + "\""; Leading = []; Trailing = nt.Trailing; Offset = nt.Offset }
                     e <- Green.node BinaryExpr [ e; q; Green.node LiteralExpr [ GToken str ] ]
                 | _ -> ())
            elif s.IsOp "<" && isAdjacentTo e && looksLikeTypeArgs () then
                // A LITERAL cannot take type arguments. `5.0<m>` is F#'s
                // units-of-measure spelling, and there are no measures here —
                // no part of this compiler knows the word. The suffix was
                // parsed and DISCARDED, so `1.0<m> + 2.0<s>` answered 3 where
                // F# rejects it, and `5.0<zzz>` was accepted with zzz
                // declared nowhere. Rejected rather than silently ignored.
                (match e with
                 | GNode le when le.NodeKind = LiteralExpr ->
                     s.Diag "units of measure are not supported: a numeric literal cannot take type arguments"
                 | _ -> ())
                // explicit generic application: GetValue<string>, vecNew<Green>
                e <- Green.node AppExpr [ e; Green.node TyParams (parseAngleArgs ctx) ]
            elif s.Is LBracket && isAdjacentTo e && s.SameLine
                 && not ((s.Peek 1).Kind = Operator && ((s.Peek 1).Text = "|" || (s.Peek 1).Text = "||"))
                 && not ((s.Peek 1).Kind = Operator && (s.Peek 1).Text = "<") then
                // F# 6 INDEXING WITHOUT THE DOT: `a[i]` means `a.[i]` when the
                // bracket is adjacent to what it indexes. With a space it is
                // still application (`List.map f [1; 2]`), which is the rule
                // F# uses and the only thing separating the two.
                //
                // A synthetic dot keeps the tree IDENTICAL to the `a.[i]`
                // form, so nothing downstream learns this spelling exists —
                // the index paths in Infer and Lower key on DotExpr with a
                // bracket child, and a two-child node would have missed both.
                // Excluded: `[|` and `[<`, which open an array literal and an
                // attribute list.
                let br = s.Cur
                let dot = { Kind = Operator; Text = "."; Leading = []; Trailing = []; Offset = br.Offset }
                e <- Green.node DotExpr [ e; GToken dot; parseAtom ctx ]
            elif s.Is LParen && isAdjacentTo e then
                // F#'s high-precedence application: an atom IMMEDIATELY
                // followed by `(` binds tighter than juxtaposition, so
                // `C(1).Get()` chains the dot onto the call — without this
                // the postfix loop never saw past the constructor
                e <- fixNamedCaseApp (Green.node AppExpr [ e; parseAtom ctx ])
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

    /// A plain name — `seq`, `Foo.bar`, `x.builder` — or a PARENTHESISED
    /// expression, which F# also allows as a builder (`(List.head bs) { … }`).
    /// A bare atom is still refused: a brace after one is far more often an
    /// argument, and the parenthesis is the author saying otherwise. A record
    /// or object expression in the brace is excluded before this is asked.
    and isNameExpr (e : Green) : bool =
        match e with
        | GNode n -> n.NodeKind = IdentExpr || n.NodeKind = DotExpr || n.NodeKind = ParenExpr
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
            let fnTok = s.Cur
            vecAdd acc (s.Bump ())
            parseClauses acc col
            let clauses = vecToList acc |> List.filter (fun c -> match c with GNode m -> m.NodeKind = MatchClause | _ -> false)
            let heads =
                clauses |> List.collect (fun c ->
                    match Green.tokens c |> List.tryFind (fun t -> t.Kind = Ident) with
                    | Some t -> [ t.Text ]
                    | None -> [])
            if clauses |> List.exists clauseUsesAp then
                // `function | Even -> …` is a lambda over the same chain a
                // `match` gets — without this the case names reached the
                // union resolver and were "unknown case"
                let scrutName = "__apF" + string fnTok.Offset
                let tk (k : TokenKind) (txt : string) (off : int) : Green =
                    GToken { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = off }
                Green.node LambdaExpr
                    [ tk Keyword "fun" (84000000 + fnTok.Offset)
                      Green.node IdentPat [ tk Ident scrutName (84100000 + fnTok.Offset) ]
                      tk Operator "->" (84200000 + fnTok.Offset)
                      apChain (84300000 + fnTok.Offset) scrutName clauses ]
            else Green.node MatchExpr (vecToList acc)
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
            // the operand is a whole APPLICATION: F# reads `-f x` as
            // `-(f x)` — prefix minus binds looser than application (the
            // syntax test's `-R 3` shape). Argument-position minus
            // (`f -x`, parsed elsewhere) keeps the tight postfix operand.
            let wide = s.IsText "-" || s.IsText "+"
            let op = s.Bump ()
            let arg = if wide then parseApp ctx else parsePostfix ctx
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
        // `use` and `do` start a branch body exactly as `let` does — the same
        // list the block-start predicate above carries. Missing here, `use x
        // = e` opening a `then` typed as unit and one opening an `else` did
        // not parse at all, both a long way from the branch that caused it.
        if canStartExpr () || s.IsKw "let" || s.IsKw "use" || s.IsKw "do"
           || s.IsKw "yield" || s.IsKw "return" then
            vecAdd acc (parseBlock ifCol)
        let mutable go = true
        while go do
            if s.IsKw "elif" && s.CurCol >= ifCol then
                vecAdd acc (parseIf ctx)
                go <- false   // nested elif consumed the rest of the chain
            elif s.IsKw "else" && s.CurCol >= ifCol then
                vecAdd acc (s.Bump ())
                if canStartExpr () || s.IsKw "let" || s.IsKw "use" || s.IsKw "do"
                   || s.IsKw "if" || s.IsKw "yield" || s.IsKw "return" then
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
        // the FAST path: one TOTAL, multi-case pattern owns every clause, so
        // one call to it dispatches them all. Anything else (a partial
        // pattern, a one-case pattern, a mix) takes the chain below.
        | [ fn ] when (clauseHeads |> List.forall (fun h -> (dictTryFind apFunctionOf h).IsSome || h = "_"))
                      && (clauseHeads |> List.forall (fun h ->
                              h = "_" || ((dictTryFind apIsPartial h) <> Some true
                                          && (match dictTryFind apCaseCount h with Some c -> c > 1 | None -> false)))) ->
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
            for c in vecToList clauses do vecAdd acc2 (renameApClause (apRenames ()) c)
            Green.node MatchExpr (vecToList acc2)
        | _ when vecToList clauses |> List.exists clauseUsesAp ->
            // an ACTIVE PATTERN among the clauses: the scrutinee is evaluated
            // ONCE, by an outer clause that binds it, and the clauses become a
            // chain (see apChain)
            let scrutName = "__apS" + string kwTok.Offset
            let tk (k : TokenKind) (txt : string) (off : int) : Green =
                GToken { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = off }
            Green.node MatchExpr
                [ tk Keyword "match" (83000000 + kwTok.Offset); scrutinee; tk Keyword "with" (83100000 + kwTok.Offset)
                  Green.node MatchClause
                    [ tk Operator "|" (83200000 + kwTok.Offset)
                      Green.node IdentPat [ tk Ident scrutName (83300000 + kwTok.Offset) ]
                      tk Operator "->" (83400000 + kwTok.Offset)
                      apChain (82000000 + kwTok.Offset) scrutName (vecToList clauses) ] ]
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
        outerCols <- outerCtx :: outerCols
        let r = parseBlockInner outerCtx blockCol
        outerCols <- List.tail outerCols
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
        let mutable apDefCases : string list = []
        if atActivePatternName () then
            isActivePattern <- true
            apDefCases <- activePatternCases () |> List.filter (fun c -> c <> "_")
            vecAdd acc (Green.node IdentPat [ bumpActivePatternName () ])
        // `let (+++) a b = ...` — an OPERATOR defined as an ordinary
        // binding. The name fuses into one identifier, as it does everywhere
        // else; parsed as a pattern it came out as a parenthesised operator
        // section and the binding had no name at all.
        elif atOperatorName () then
            vecAdd acc (Green.node IdentPat [ bumpOperatorName () ])
        else
            // `let (x, y) as whole = e`: an as-pattern binds the WHOLE value
            // beside its parts. It binds loosest, so it WRAPS the pattern —
            // left as a sibling it read as a curried parameter named `as`.
            vecAdd acc (parseAsSuffix (parseAtomPat letCol))
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
            let beforeParams = vecLen acc
            while canStartAtomPat () && (s.SameLine || s.CurCol > letCol) do
                vecAdd acc (parseAtomPat letCol)
            // a PARAMETERIZED active pattern (`let (|Mul|) k x = ...`): every
            // parameter but the last is given at the USE site, before the
            // value being matched
            if not (List.isEmpty apDefCases) then
                let extra = vecLen acc - beforeParams - 1
                for c in apDefCases do dictSet apParamCount c (max 0 extra)
        if s.IsOp ":" then
            vecAdd acc (s.Bump ())
            vecAdd acc (parseType letCol)
            // declared constraints: `let solve ... : Vector<'a> when Fractional<'a> = ...`
            while s.IsKw "when" && (s.SameLine || s.CurCol > letCol) do
                for w__ in parseWhen false letCol do vecAdd acc w__
        if s.IsOp "=" then
            vecAdd acc (s.Bump ())
            if s.AtEof || (not s.SameLine && s.CurCol <= letCol) then s.Diag "expected a binding body"
            else
                let body = parseBlock letCol
                // in an active pattern's own body, `Add (x, y)` CONSTRUCTS
                // the case: rename it to the choice case the pattern
                // compiles to
                vecAdd acc (if isActivePattern then renameApBody (apRenames ()) body else body)
        elif not pendingExtern then s.Diag "expected '=' in binding"
        pendingExtern <- false
        if s.IsKw "in" && s.SameLine then
            vecAdd acc (s.Bump ())
            vecAdd acc (parseBlock letCol)
        // `let (Split (n, s)) = e`: the binding pattern goes through the
        // active pattern's function. Only a VALUE binding — a function's
        // parameters are patterns of their own.
        let kids = vecToList acc
        let isPatNode (k : Green) =
            match k with
            | GNode m ->
                (match m.NodeKind with
                 | IdentPat | WildcardPat | LiteralPat | TuplePat | StructTuplePat
                 | ConsPat | AppPat | ParenPat | ListPat | ArrayPat | AndPat | AsPat
                 | TypeTestPat | RecordPat -> true
                 | _ -> false)
            | GToken _ -> false
        let pats = kids |> List.filter isPatNode
        let eqIdx = kids |> List.mapi (fun i k -> i, k)
                         |> List.tryPick (fun (i, k) -> match k with
                                                        | GToken t when t.Kind = Operator && t.Text = "=" -> Some i
                                                        | _ -> None)
        match pats, eqIdx with
        | [ p ], Some ei when not isActivePattern ->
            let rhsIdx = kids |> List.mapi (fun i k -> i, k)
                              |> List.tryPick (fun (i, k) -> if i > ei && (match k with GNode _ -> true | _ -> false) then Some i else None)
            (match rhsIdx with
             | Some ri ->
                 (match apLetRewrite p (List.item ri kids) with
                  | Some (p2, rhs2) ->
                      let pi = kids |> List.mapi (fun i k -> i, k) |> List.pick (fun (i, k) -> if isPatNode k then Some i else None)
                      Green.node LetDecl
                          (kids |> List.mapi (fun i k -> if i = pi then p2 elif i = ri then rhs2 else k))
                  | None -> Green.node LetDecl kids)
             | None -> Green.node LetDecl kids)
        | _ -> Green.node LetDecl kids

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
        let mutable classSelf = ""
        if s.IsKw "as" && s.SameLine then
            vecAdd acc (s.Bump ())
            if s.Is Ident then
                classSelf <- s.Cur.Text
                vecAdd acc (s.Bump ())
        // declared class constraints: `type Box<'a> when Ordered<'a> = ...`,
        // the same `when C<'a>` a let signature carries
        while s.IsKw "when" && (s.SameLine || s.CurCol > typeCol) do
            for w__ in parseWhen false typeCol do vecAdd acc w__
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
            // members may follow any representation (or be the whole body),
            // optionally introduced by `with` (`type R = { ... } with
            // member ...`) and closed by a matching `end`
            let hadWith = s.IsKw "with" && (s.SameLine || s.CurCol > typeCol)
            if hadWith then vecAdd acc (s.Bump ())
            parseTypeBody acc typeCol
            if hadWith && s.IsKw "end" && s.CurCol > typeCol then s.Bump () |> ignore
        // nested `let`s in the body reset this, but a following `and`
        // continues the TYPE, not those lets
        lastMajor <- "type"
        // `type C(x) as self = ...` — the name of the object under
        // construction. Each member already binds a self of its own (`this`,
        // or `_` for none), so the class-level name is bound THROUGH it: a
        // member without one takes this name, and a member with one has this
        // name renamed to it inside its body.
        if classSelf <> "" then
            let rec bindSelf (g : Green) : Green =
                match g with
                | GNode n when n.NodeKind = MemberDecl ->
                    // the self token is the Ident right before the `.` that
                    // introduces the member's name
                    let kids = n.Children
                    let mutable selfIdx = 0 - 1
                    let mutable k = 0
                    while k + 1 < List.length kids do
                        (match List.item k kids, List.item (k + 1) kids with
                         | GToken a, GToken b when (a.Kind = Ident || (a.Kind = Operator && a.Text = "_"))
                                                   && b.Kind = Operator && b.Text = "." && selfIdx < 0 ->
                             selfIdx <- k
                         | _ -> ())
                        k <- k + 1
                    if selfIdx < 0 then g
                    else
                        match List.item selfIdx kids with
                        | GToken t when t.Text = "_" ->
                            Green.node MemberDecl
                                (kids |> List.mapi (fun i c ->
                                    if i = selfIdx then GToken { t with Kind = Ident; Text = classSelf } else c))
                        | GToken t ->
                            let mine = t.Text
                            let rec ren (x : Green) : Green =
                                match x with
                                | GToken tk when tk.Kind = Ident && tk.Text = classSelf -> GToken { tk with Text = mine }
                                | GToken _ -> x
                                | GNode m -> Green.node m.NodeKind (m.Children |> List.map ren)
                            Green.node MemberDecl
                                (kids |> List.mapi (fun i c -> if i <= selfIdx then c else ren c))
                        | _ -> g
                | GNode n -> Green.node n.NodeKind (n.Children |> List.map bindSelf)
                | GToken _ -> g
            Green.node TypeDecl (vecToList acc |> List.map bindSelf)
        else
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
            let newTok = s.Cur
            vecAdd acc (s.Bump ())
            while canStartAtomPat () && (s.SameLine || s.CurCol > mcol) do
                vecAdd acc (parseAtomPat mcol)
            // `new (args) as x = <delegate> then <body>`: the delegation
            // builds the object, `as x` names it, and `then` runs against the
            // finished instance. It DESUGARS here, to
            //     new (args) = let x = <delegate> in (<body>; x)
            // which every later stage already handles — Resolve binds the
            // let, Infer types x as the delegate's result, and Lower emits an
            // ELet. Nothing downstream needs to know the form existed.
            let asBinder =
                if s.IsKw "as" && (s.Peek 1).Kind = Ident then
                    s.Bump () |> ignore
                    let t = s.Cur
                    s.Bump () |> ignore
                    Some t
                else None
            if s.IsOp ":" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseType mcol)
            if s.IsOp "=" then
                vecAdd acc (s.Bump ())
                if not (s.AtEof || (not s.SameLine && s.CurCol <= mcol)) then
                    let delegated = parseBlock mcol
                    // the `then` body, if any. `then` ends the block above:
                    // it is one of the keywords isBlockEnd stops at.
                    let thenBlk =
                        if s.IsKw "then" then
                            s.Bump () |> ignore
                            Some (parseBlock mcol)
                        else None
                    match asBinder, thenBlk with
                    | Some bt, Some tb ->
                        let mutable synth = 83000000 + newTok.Offset
                        let fresh () = synth <- synth + 1; synth
                        let tok2 (k : TokenKind) (txt : string) : Green =
                            GToken { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = fresh () }
                        // the binder's DEFINITION keeps the real token, so a
                        // hover or a diagnostic points at the source; the
                        // trailing USE gets a synthetic offset, since a
                        // definition and a use at one offset confuse defsAt
                        let useE = Green.node IdentExpr [ tok2 Ident bt.Text ]
                        let cont =
                            match tb with
                            | GNode b when b.NodeKind = BlockExpr ->
                                Green.node BlockExpr (b.Children @ [ useE ])
                            | other -> Green.node BlockExpr [ other; useE ]
                        vecAdd acc
                            (Green.node LetDecl
                                [ tok2 Keyword "let"; Green.node IdentPat [ GToken bt ]
                                  tok2 Operator "="; delegated; tok2 Keyword "in"; cont ])
                    | _ ->
                        vecAdd acc delegated
                        (match thenBlk with
                         | Some tb -> vecAdd acc tb
                         | None -> ())
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
            // The ascription and the constraints ALTERNATE. F# accepts both
            // orders — `: 'a when Num<'a>` and `when Num<'a> : 'a` — and this
            // took the ascription once, then the constraints, and stopped; a
            // return type written AFTER the constraints was left for the
            // top-level loop, which reported "unexpected token" four times on
            // one member (KNOWN-ISSUES #7).
            //
            // The constraints are the same WhenDecl a let signature carries,
            // so the member's walk can skip the node and constraintOf can read
            // it. Left as bare tokens, `Pinnable` and `'a` land among the
            // pre-`=` identifiers and the member loses its NAME.
            let mutable sigMore = true
            while sigMore do
                sigMore <- false
                if s.IsOp ":" then
                    vecAdd acc (s.Bump ())
                    vecAdd acc (parseType mcol)
                    sigMore <- true
                while s.IsKw "when" && (s.SameLine || s.CurCol > mcol) do
                    sigMore <- true
                    if (s.Peek 1).Kind = Ident then (for w__ in parseWhen false mcol do vecAdd acc w__)
                    else
                        // F#-style variable constraint (`when 'm : Monad`):
                        // its tokens, in their own node. It ends at the `=`, at
                        // the next `when` — or at a `:` that starts the RETURN
                        // type, which is why the ascription can follow.
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
                // `member val P = init with get, set`: accessor NAMES after
                // an auto-property initializer — names only, no bodies; the
                // member-val desugar reads them off
                if s.IsKw "with"
                   && (let p = s.Peek 1 in p.Text = "get" || p.Text = "set") then
                    vecAdd acc (s.Bump ())
                    let mutable moreAcc = true
                    while moreAcc && s.Is Ident && (s.Cur.Text = "get" || s.Cur.Text = "set") do
                        vecAdd acc (Green.node AccessorDecl [ s.Bump () ])
                        if s.Is Comma || s.IsKw "and" then vecAdd acc (s.Bump ())
                        else moreAcc <- false
        Green.node MemberDecl (vecToList acc)

    /// `type T = A | B of int` — an identifier directly followed by `|`/`of`.
    /// An ENUM writes its first case the same way, with a value instead:
    /// `type E = A = 1 | B = 2`. Without the `=` arm that read as the
    /// ABBREVIATION `type E = A` and the value after it was a syntax error at
    /// top level, so the one-line enum form did not parse at all. The literal
    /// is what tells the two apart — `type T = A` really is an abbreviation.
    and looksLikeInlineUnion () : bool =
        s.Is Ident
        && (let n = s.Peek 1 in
            n.Text = "of" || n.Text = "|"
            || (n.Text = "=" && List.contains (s.Peek 2).Kind literalKinds))

    and parseUnionCases (acc : Vec<Green>) (typeCol : int) : unit =
        // optional first case without a leading bar: `type T = A | B`
        if s.Is Ident then
            let c = vecNew<Green> ()
            let nameTok = s.Cur.Text
            vecAdd c (s.Bump ())
            if s.IsKw "of" then
                vecAdd c (s.Bump ())
                let payload = parseCasePayload typeCol
                let fns = payloadFieldNames payload
                if fns |> List.exists (fun x -> x <> "") then dictSet ucFieldNames nameTok fns
                vecAdd c payload
            elif s.IsOp "=" && isLiteral2 () then
                // the leading ENUM case, the barless twin of `| A = 1` below
                vecAdd c (s.Bump ())
                vecAdd c (Green.node LiteralExpr [ s.Bump () ])
            vecAdd acc (Green.node UnionCase (vecToList c))
        let mutable go = true
        while go && s.IsOp "|" && (s.SameLine || s.CurCol > typeCol) do
            let mark = s.Mark
            let c = vecNew<Green> ()
            let barCol = s.CurCol
            vecAdd c (s.Bump ())
            let caseName = if s.Is Ident then s.Cur.Text else ""
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
                    else for w__ in parseWhen false barCol do vecAdd c w__
            if s.IsKw "of" then
                vecAdd c (s.Bump ())
                let payload = parseCasePayload barCol
                let fns = payloadFieldNames payload
                if caseName <> "" && (fns |> List.exists (fun x -> x <> "")) then
                    dictSet ucFieldNames caseName fns
                vecAdd c payload
                if s.IsOp "->" then
                    vecAdd c (s.Bump ())
                    vecAdd c (parsePostfixType barCol)
                caseWhens ()
            elif s.IsOp ":" then
                vecAdd c (s.Bump ())
                vecAdd c (parsePostfixType barCol)
                caseWhens ()
            elif s.IsOp "=" then
                // enum case: `| Leaf = 0uy` — and a NEGATIVE member,
                // `| Debug = -1`, fused into one literal token so the value
                // reader downstream sees a single number (fpp.base #35's
                // side note; FShade's ShaderStage starts at -1)
                vecAdd c (s.Bump ())
                if s.IsOp "-" && List.contains (s.Peek 1).Kind literalKinds then
                    let neg = s.Bump ()
                    (match s.Bump () with
                     | GToken lt ->
                         (match neg with
                          | GToken ngt ->
                              // spelled out, never `with`-copied: the copy
                              // resolves its record by FIELD NAME under the
                              // self-host, and Text/Offset live on several
                              vecAdd c (Green.node LiteralExpr
                                            [ GToken { Kind = lt.Kind; Text = "-" + lt.Text
                                                       Leading = lt.Leading; Trailing = lt.Trailing
                                                       Offset = ngt.Offset } ])
                          | _ -> ())
                     | _ -> ())
                elif isLiteral () then vecAdd c (Green.node LiteralExpr [ s.Bump () ])
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
            elif s.IsKw "mutable" || s.Is Ident || (s.IsOp "?" && (s.Peek 1).Kind = Ident)
                 // `[<Semantic "...">] pos : V4` — an attribute on the FIELD
                 // (FShade vertex records carry one per field)
                 || (s.Is LBracket && (let p = s.Peek 1 in p.Kind = Operator && p.Text = "<")) then
                let f = vecNew<Green> ()
                if s.Is LBracket && (let p = s.Peek 1 in p.Kind = Operator && p.Text = "<") then
                    vecAdd f (parseAttributeList ())
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
            // `module Ab = Inner` — an ABBREVIATION, not a nested module. The
            // target is an identifier on the SAME line; a nested module's
            // body always starts on the next one. Without this the body loop
            // below found no declaration, produced an empty module, and left
            // `Inner` behind as a stray top-level expression — so every later
            // `Ab.x` was an unresolved variable.
            if s.Is Ident && s.SameLine then
                vecAdd acc (s.Bump ())
                while s.IsOp "." && s.SameLine do
                    vecAdd acc (s.Bump ())
                    if s.Is Ident then vecAdd acc (s.Bump ())
                Green.node ModuleAbbrev (vecToList acc)
            else
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
    /// One WhenDecl per constraint HEAD: `when A<'a> and B<'a>` is two
    /// nodes, each carrying its keyword token (`when`, then `and`), so
    /// constraintOf reads every head and the leaves still round-trip.
    and parseWhen (allowEq : bool) (col : int) : Green list =
        let out = vecNew<Green> ()
        let one (kw : Green) : unit =
            let acc = vecNew<Green> ()
            vecAdd acc kw
            // F#'s OWN spellings — `when 'a : comparison`, `when 'a :> IFace`
            // — are absorbed verbatim and read back by Infer's constraintOf,
            // which already understands both (fsharpInlineConstraint and the
            // subtype-bound scan). Demanding a class name here rejected, in
            // `let` position only, a form the rest of the compiler handles
            // and the type-parameter position accepts.
            if s.IsOp "'" then
                vecAdd acc (s.Bump ())                        // '
                if s.Is Ident then vecAdd acc (s.Bump ())     // the variable
                if s.IsOp ":" || s.IsOp ":>" then
                    vecAdd acc (s.Bump ())
                    if s.Is Ident then
                        vecAdd acc (s.Bump ())
                        while s.IsOp "." && s.SameLine do     // a dotted name
                            vecAdd acc (s.Bump ())
                            if s.Is Ident then vecAdd acc (s.Bump ())
            else
                vecAdd acc (parseClassHead col)
            let mutable sawWith = false
            if s.IsKw "with" then
                sawWith <- true
                vecAdd acc (s.Bump ())
                if s.Is Ident then vecAdd acc (s.Bump ())
            if s.IsOp "=" && (allowEq || sawWith) then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseType col)
            vecAdd out (Green.node WhenDecl (vecToList acc))
        one (s.Bump ())   // when
        while s.IsKw "and" && (s.SameLine || s.CurCol > col)
              && ((s.Peek 1).Kind = Ident || (s.Peek 1).Text = "'") do
            one (s.Bump ())   // and
        vecToList out

    /// `class C<'a,'b>` / `instance C<int,int>` — head, context, then a body
    /// of associated types and members. Both shapes are identical; only the
    /// keyword and what the body means differ.
    and parseClassLike (kind : NodeKind) : Green =
        let acc = vecNew<Green> ()
        let col = s.CurCol
        vecAdd acc (s.Bump ())   // class / instance
        vecAdd acc (parseClassHead col)
        while s.IsKw "when" && (s.SameLine || s.CurCol > col) do
            for w__ in parseWhen true col do vecAdd acc w__
        if s.IsOp "=" then vecAdd acc (s.Bump ())
        let mutable go = true
        while go && not s.AtEof && not s.SameLine && s.CurCol > col do
            let mark = s.Mark
            // `type Result` declares (or binds) an associated type; inside a
            // class body it needs no `static abstract` ceremony
            if s.IsKw "when" then (for w__ in parseWhen true col do vecAdd acc w__)
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
            // `exception E of T` DECLARES A CASE OF `exn`. Spelled as one —
            // a TypeDecl naming `exn` whose child is E's UnionCase — it rides
            // the rule that a user type of a prelude type's name MERGES with
            // it (CLAUDE.md), so E becomes a constructor and a pattern with
            // no special handling anywhere downstream. The `exn` identifier
            // is synthesized at the keyword's own offset, so a diagnostic
            // still points at the declaration.
            let kw = s.Bump ()
            let kwOffset = (match kw with GToken t -> t.Offset | _ -> 0)
            let c = vecNew<Green> ()
            if s.Is Ident then vecAdd c (s.Bump ())
            if s.IsKw "of" then
                vecAdd c (s.Bump ())
                // the payload may be LABELLED — `exception E of level : int`
                // — and the label is documentation, not part of the type
                let mutable go = true
                while go do
                    if s.Is Ident && (s.Peek 1).Kind = Operator && (s.Peek 1).Text = ":" then
                        s.Bump () |> ignore
                        s.Bump () |> ignore
                    vecAdd c (parseType ctx)
                    if s.Is Comma || (s.IsOp "*" && s.SameLine) then s.Bump () |> ignore
                    else go <- false
            let exnTok =
                GToken { Kind = Ident; Text = "exn"; Leading = []; Trailing = []; Offset = kwOffset }
            Green.node TypeDecl [ kw; exnTok; Green.node UnionCase (vecToList c) ]
        elif isDirectiveHere () then
            // a COMPILER DIRECTIVE: `#nowarn "7331"`, `#light`. It addresses
            // the compiler, not the program, and every one of them is either
            // about warnings F++ does not raise or about a script host it
            // does not have. Consumed to the end of its line.
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            while not s.AtEof && s.SameLine do vecAdd acc (s.Bump ())
            Green.node BlockExpr (vecToList acc)
        // only `[<` opens an attribute list — a bare `[` at declaration
        // position is a LIST-LITERAL statement (`[ ... ] |> List.iter ...`),
        // which used to die as "unexpected token at top level"
        elif s.Is LBracket && (let p = s.Peek 1 in p.Kind = Operator && p.Text = "<") then parseAttributeList ()
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

let parse (src : string) : ParseResult = parseSeeded [] src

/// Token-level prescan of one file's ACTIVE-PATTERN definitions — the rows
/// the workspace seeds every other file's parse with. Reads the raw token
/// stream so it needs no parse (and the seed memo therefore cannot cycle
/// with the parses that depend on it). The parameter count mirrors the
/// parser's own rule: every atom between `|)` and the `=` (or a return
/// ascription's `:`) but the LAST is given at the use site.
let scanActivePatterns (src : string) : ApDef list =
    let toks = Lexer.tokenize src |> List.filter (fun t -> t.Kind <> Eof) |> vecOfList
    let n = vecLen toks
    let out = vecNew<ApDef> ()
    let tokAt (i : int) : Token = vecGet toks i
    let isTx (i : int) (txt : string) = i < n && (tokAt i).Text = txt
    let mutable i = 0
    while i < n do
        if (tokAt i).Kind = Keyword && (tokAt i).Text = "let" then
            let mutable j = i + 1
            while j < n && (tokAt j).Kind = Keyword
                  && List.contains (tokAt j).Text [ "rec"; "inline"; "mutable"; "private"; "internal"; "public" ] do
                j <- j + 1
            if isTx j "(" && isTx (j + 1) "|" then
                // ( | A | B | ) — names between bars; a trailing `_` marks partial
                let names0 = vecNew<string> ()
                let mutable k = j + 1
                // `( (| name)* | )` — names while a bar is FOLLOWED by one;
                // the final bar is followed by the closing paren
                while isTx k "|" && (k + 1 < n && ((tokAt (k + 1)).Kind = Ident || (tokAt (k + 1)).Text = "_")) do
                    vecAdd names0 (tokAt (k + 1)).Text
                    k <- k + 2
                if isTx k "|" && isTx (k + 1) ")" && vecLen names0 > 0 then
                    let k = k + 1
                    let all = vecToList names0
                    let partial = (match List.tryLast all with Some "_" -> true | _ -> false)
                    let names = all |> List.filter (fun c -> c <> "_")
                    let count = List.length names
                    // parameter ATOMS after `)` up to `=` / `:` — idents,
                    // literals, or balanced groups, each one atom
                    let mutable p = k + 1
                    let mutable atoms = 0
                    let mutable stop = false
                    while not stop && p < n do
                        let t = tokAt p
                        if t.Text = "=" || t.Text = ":" then stop <- true
                        elif t.Text = "(" || t.Text = "[" then
                            let closing = if t.Text = "(" then ")" else "]"
                            let opening = t.Text
                            let mutable depth = 1
                            p <- p + 1
                            while depth > 0 && p < n do
                                (if (tokAt p).Text = opening then depth <- depth + 1
                                 elif (tokAt p).Text = closing then depth <- depth - 1)
                                p <- p + 1
                            atoms <- atoms + 1
                        elif t.Kind = Ident || List.contains t.Kind literalKinds then
                            atoms <- atoms + 1
                            p <- p + 1
                        else stop <- true
                    let extra = if atoms > 1 then atoms - 1 else 0
                    let fname = "$ap$" + String.concat "$" all
                    names |> List.iteri (fun ix c ->
                        vecAdd out
                            { ApCase = c; ApFn = fname; ApIndex = ix
                              ApCount = count; ApPartial = partial; ApParams = extra })
                    i <- p - 1
        i <- i + 1
    vecToList out

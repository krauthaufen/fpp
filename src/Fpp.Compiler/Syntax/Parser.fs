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
    if text = "|" || text = "->" then 0
    elif text = ":=" || text = "<-" then 1
    elif text = ".." || text = "..." then 4
    elif strLen text >= 2 && substr text 0 2 = "**" then 9
    else
        match charAt text 0 with
        | '*' | '/' | '%' -> 8
        | '+' | '-' -> 7
        | ':' -> if text = "::" then 6 else 0
        | '^' | '@' -> 5
        | '=' | '<' | '>' | '$' -> 4
        | '!' -> if strLen text > 1 then 4 else 0
        | '&' -> 3
        | '|' -> 2
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
    let canStartAtom () =
        s.Is Ident || isLiteral () || isLiteralKw ()
        || s.Is LParen || s.Is LBracket || s.Is LBrace
        || (s.IsOp "'" && (s.Peek 1).Kind = Ident)

    /// Can the current token start an expression at statement position?
    let canStartExpr () =
        canStartAtom () || s.IsKw "fun" || s.IsKw "if" || s.IsKw "match"
        || s.IsKw "function" || s.IsKw "not" || s.IsKw "lazy" || s.IsKw "new"
        || s.IsKw "for" || s.IsKw "while"
        || (s.Is Operator && (s.IsText "-" || s.IsText "+" || s.IsText "!" || s.IsText "~~~"))

    let canStartDecl () =
        s.IsKw "let" || s.IsKw "type" || s.IsKw "open" || s.IsKw "module"
        || s.IsKw "namespace" || s.IsKw "and" || s.IsKw "do" || s.IsKw "exception"
        || s.IsKw "extern"
        || canStartExpr ()
        || (s.Is LBracket)   // attribute lists

    /// Keywords that close an inner block regardless of indentation.
    let isBlockStopKw () =
        s.IsKw "then" || s.IsKw "else" || s.IsKw "elif" || s.IsKw "with"
        || s.IsKw "end" || s.IsKw "in" || s.IsKw "done" || s.IsKw "to" || s.IsKw "downto"

    let isCloser () = s.Is RParen || s.Is RBracket || s.Is RBrace || s.Is Comma || s.Is Semicolon

    /// A new line has begun and the current token sits at or left of `col`.
    let offside (col : int) = not s.SameLine && s.CurCol <= col

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
            else
                // constraints (`when 'm : Monad`) and anything else we do not
                // model yet: absorb tokens verbatim
                vecAdd acc (s.Bump ())
        vecToList acc

    and canStartTypeAtom () =
        s.Is Ident || s.IsOp "'" || s.Is LParen

    and parseAtomType (ctx : int) : Green =
        if s.IsOp "'" then
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
        || (s.IsOp "-" && (let n = s.Peek 1 in n.Kind = IntLit || n.Kind = FloatLit))

    and parseAtomPat (ctx : int) : Green =
        if s.Is Ident then
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
                let mutable go = canStartAtomPat ()
                while go do
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
                        go <- canStartAtomPat ()
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
            let allowed = s.SameLine || s.CurCol >= ctx
            if s.Is Operator && allowed && not (s.IsOp "|") && not (s.IsOp "->") then
                let prec = infixPrec s.Cur.Text
                if prec >= minPrec && prec > 0 then
                    let opText = s.Cur.Text
                    let op = s.Bump ()
                    let nextMin = if rightAssoc opText then prec else prec + 1
                    let rhs = parseBinary ctx nextMin
                    lhs <- Green.node BinaryExpr [ lhs; op; rhs ]
                else go <- false
            else go <- false
        lhs

    and parseApp (ctx : int) : Green =
        // F#'s prefix-minus rule: `f -1` (space before the minus, none after
        // a numeric literal) is application of a negative literal
        let isNegLitArg () =
            s.IsOp "-" && s.GapBefore
            && (let n = s.Peek 1 in
                (n.Kind = IntLit || n.Kind = FloatLit) && n.Offset = s.Cur.Offset + 1)
        let parseArg () =
            if isNegLitArg () then Green.node PrefixExpr [ s.Bump (); s.Bump () ]
            else parsePostfix ctx
        let head = parsePostfix ctx
        if (canStartAtom () || isNegLitArg ()) && (s.SameLine || s.CurCol > ctx) then
            let acc = vecNew<Green> ()
            vecAdd acc head
            while (canStartAtom () || isNegLitArg ()) && (s.SameLine || s.CurCol > ctx) do
                vecAdd acc (parseArg ())
            Green.node AppExpr (vecToList acc)
        else head

    and parsePostfix (ctx : int) : Green =
        let mutable e = parseAtom ctx
        let mutable go = true
        while go do
            if s.IsOp "." && s.SameLine then
                let dot = s.Bump ()
                if s.Is Ident then e <- Green.node DotExpr [ e; dot; s.Bump () ]
                elif s.Is LBracket then e <- Green.node DotExpr [ e; dot; parseAtom ctx ]   // x.[i]
                else
                    s.Diag "expected member name after '.'"
                    e <- Green.node DotExpr [ e; dot ]
            elif s.IsOp "<" && isAdjacentTo e && looksLikeTypeArgs () then
                // explicit generic application: GetValue<string>, vecNew<Green>
                e <- Green.node AppExpr [ e; Green.node TyParams (parseAngleArgs ctx) ]
            else go <- false
        e

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
                        // a run of > closes that many levels
                        let closed = depth - strLen t.Text
                        if closed < 0 then false
                        elif closed = 0 then true
                        else scan (k + 1) closed
                    elif t.Text = "'" || t.Text = "." || t.Text = "*" || t.Text = "->" then scan (k + 1) depth
                    else false
                | Ident -> scan (k + 1) depth
                | Comma -> scan (k + 1) depth
                | LBracket | RBracket -> scan (k + 1) depth   // int[]
                | LParen | RParen -> scan (k + 1) depth       // (string * int) list
                | _ -> false
        scan 1 1

    and parseAtom (ctx : int) : Green =
        if s.Is Ident then Green.node IdentExpr [ s.Bump () ]
        elif isLiteral () || isLiteralKw () then Green.node LiteralExpr [ s.Bump () ]
        elif s.Is LParen then
            let lp = s.Bump ()
            if s.Is RParen then Green.node ParenExpr [ lp; s.Bump () ]   // unit
            elif s.Is Operator && not (s.IsOp "'") && infixPrec s.Cur.Text > 0 && not (canStartExpr ()) then
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
                if canStartExpr () || s.IsKw "let" then vecAdd acc (parseBlock ctx)
                elif s.Is Operator then vecAdd acc (s.Bump ())   // section like (+) with odd op
                if s.IsOp ":" then
                    vecAdd acc (s.Bump ())
                    vecAdd acc (parseType ctx)
                if s.Is RParen then vecAdd acc (s.Bump ()) else s.Diag "expected ')'"
                Green.node ParenExpr (vecToList acc)
        elif s.Is LBracket then
            // list / array: contents as `;`- or newline-separated expressions;
            // stray `|` (array brackets) absorbed verbatim
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            let mutable go = true
            while go && not s.AtEof && not (s.Is RBracket) do
                let mark = s.Mark
                if s.Is Semicolon then vecAdd acc (s.Bump ())
                elif s.IsOp "|" then vecAdd acc (s.Bump ())
                elif canStartExpr () || s.IsKw "for" || s.IsKw "yield" || s.IsKw "let" then vecAdd acc (parseBlock ctx)
                else vecAdd acc (s.Bump ())
                if s.Mark = mark then go <- false
            if s.Is RBracket then vecAdd acc (s.Bump ()) else s.Diag "expected ']'"
            Green.node ListExpr (vecToList acc)
        elif s.Is LBrace then
            if looksLikeRecordExpr () then parseRecordExpr ctx
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
            if canStartExpr () || s.IsKw "let" || s.IsKw "yield" then vecAdd acc (parseBlock fcol)
            Green.node ForExpr (vecToList acc)
        elif s.IsKw "while" then
            let acc = vecNew<Green> ()
            let wcol = s.CurCol
            vecAdd acc (s.Bump ())
            vecAdd acc (parseExpr wcol)
            if s.IsKw "do" then vecAdd acc (s.Bump ()) else s.Diag "expected 'do'"
            if canStartExpr () || s.IsKw "let" then vecAdd acc (parseBlock wcol)
            Green.node WhileExpr (vecToList acc)
        elif s.IsOp "'" && (s.Peek 1).Kind = Ident then
            // type variable in expression position (e.g. `unbox<'a>` soup)
            Green.node IdentExpr [ s.Bump (); s.Bump () ]
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
            elif s.Is Ident then
                let f = vecNew<Green> ()
                let fieldCol = s.CurCol
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
        if canStartExpr () || s.IsKw "let" then vecAdd acc (parseBlock ifCol)
        let mutable go = true
        while go do
            if s.IsKw "elif" && s.CurCol >= ifCol then
                vecAdd acc (parseIf ctx)
                go <- false   // nested elif consumed the rest of the chain
            elif s.IsKw "else" && s.CurCol >= ifCol then
                vecAdd acc (s.Bump ())
                if canStartExpr () || s.IsKw "let" || s.IsKw "if" then vecAdd acc (parseBlock ifCol)
                go <- false
            else go <- false
        Green.node IfExpr (vecToList acc)

    and parseMatch (ctx : int) : Green =
        let acc = vecNew<Green> ()
        let matchCol = s.CurCol
        vecAdd acc (s.Bump ())
        vecAdd acc (parseExpr matchCol)
        if s.IsKw "with" then vecAdd acc (s.Bump ()) else s.Diag "expected 'with'"
        parseClauses acc matchCol
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
            if canStartExpr () || s.IsKw "let" then vecAdd c (parseBlock barCol)
            vecAdd acc (Green.node MatchClause (vecToList c))
        // first clause may omit the bar: `match x with null -> ...`
        if not (s.IsOp "|") && canStartAtomPat () && s.SameLine then
            let c = vecNew<Green> ()
            finishClause c s.CurCol
        let mutable go = true
        while go && s.IsOp "|" && (s.SameLine || s.CurCol >= col) do
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
        let acc = vecNew<Green> ()
        let canStartItem () =
            canStartExpr () || s.IsKw "let" || s.IsKw "use" || s.IsKw "do"
            || s.IsKw "and" || s.IsKw "yield" || s.IsKw "return"
        let mutable go = true
        while go && not s.AtEof do
            let mark = s.Mark
            if s.IsKw "let" || s.IsKw "use" || s.IsKw "and" then vecAdd acc (parseLet blockCol)
            elif s.IsKw "do" then
                let d = s.Bump ()
                let body = if canStartExpr () then parseBlock blockCol else Green.node ErrorNode []
                vecAdd acc (Green.node BlockExpr [ d; body ])
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
        let letCol = s.CurCol
        vecAdd acc (s.Bump ())   // let / use / and
        while s.IsKw "rec" || s.IsKw "inline" || s.IsKw "mutable" || s.IsKw "private" || s.IsKw "internal" || s.IsKw "public" do
            vecAdd acc (s.Bump ())
        // binding name / pattern
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
        if s.IsOp "=" then
            vecAdd acc (s.Bump ())
            if s.AtEof || (not s.SameLine && s.CurCol <= letCol) then s.Diag "expected a binding body"
            else vecAdd acc (parseBlock letCol)
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
        if s.Is Ident then vecAdd acc (s.Bump ()) else s.Diag "expected a type name"
        if s.IsOp "<" && s.SameLine then
            vecAdd acc (Green.node TyParams (parseAngleArgs typeCol))
        // primary-constructor parameters: `type State(src : string) =`
        if s.Is LParen && s.SameLine then
            vecAdd acc (parseAtomPat typeCol)
        if s.IsOp "=" then
            vecAdd acc (s.Bump ())
            if isTypeBodyStart () && not s.SameLine && s.CurCol > typeCol then
                ()   // class/interface body only — handled below
            elif s.IsOp "|" then parseUnionCases acc typeCol
            elif s.Is LBrace then vecAdd acc (parseRecordRepr typeCol)
            elif looksLikeInlineUnion () then parseUnionCases acc typeCol
            elif canStartTypeAtom () then vecAdd acc (parseType typeCol)
            else s.Diag "expected a type representation"
            // members may follow any representation (or be the whole body)
            parseTypeBody acc typeCol
        Green.node TypeDecl (vecToList acc)

    and isMemberStart () =
        s.IsKw "member" || s.IsKw "static" || s.IsKw "abstract" || s.IsKw "override"
        || s.IsKw "default" || s.IsKw "interface" || s.IsKw "inherit" || s.IsKw "val"
        || s.IsKw "new"

    and isTypeBodyStart () =
        isMemberStart () || s.IsKw "let" || s.IsKw "do" || s.IsKw "use"

    and parseTypeBody (acc : Vec<Green>) (typeCol : int) : unit =
        let mutable go = true
        while go && not s.AtEof && not s.SameLine && s.CurCol > typeCol && isTypeBodyStart () do
            let mark = s.Mark
            if s.IsKw "let" || s.IsKw "use" then vecAdd acc (parseLet typeCol)
            elif s.IsKw "do" then
                let d = s.Bump ()
                let body = if canStartExpr () then parseBlock typeCol else Green.node ErrorNode []
                vecAdd acc (Green.node BlockExpr [ d; body ])
            elif s.IsKw "interface" then vecAdd acc (parseInterfaceImpl ())
            elif s.IsKw "inherit" then
                let a = vecNew<Green> ()
                vecAdd a (s.Bump ())
                vecAdd a (parseType typeCol)
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
            // associated type: `static abstract type State`
            vecAdd acc (s.Bump ())
            if s.Is Ident then vecAdd acc (s.Bump ())
        else
            // [self .] name
            if s.Is Ident then
                vecAdd acc (s.Bump ())
                if s.IsOp "." && s.SameLine then
                    vecAdd acc (s.Bump ())
                    if s.Is Ident then vecAdd acc (s.Bump ())
            else s.Diag "expected a member name"
            if s.IsOp "<" && s.SameLine && (s.Peek 1).Text = "'" then
                vecAdd acc (Green.node TyParams (parseAngleArgs mcol))
            while canStartAtomPat () && (s.SameLine || s.CurCol > mcol) do
                vecAdd acc (parseAtomPat mcol)
            if s.IsOp ":" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseType mcol)
                // trailing constraints: `... -> 't<'m, 'a> when 'm : Monad`
                if s.IsKw "when" then
                    vecAdd acc (s.Bump ())
                    while not s.AtEof && not (s.IsOp "=") && (s.SameLine || s.CurCol > mcol) do
                        vecAdd acc (s.Bump ())
            if s.IsOp "=" then
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
                vecAdd c (parseType typeCol)
            vecAdd acc (Green.node UnionCase (vecToList c))
        let mutable go = true
        while go && s.IsOp "|" && (s.SameLine || s.CurCol > typeCol) do
            let mark = s.Mark
            let c = vecNew<Green> ()
            let barCol = s.CurCol
            vecAdd c (s.Bump ())
            if s.Is Ident then vecAdd c (s.Bump ()) else s.Diag "expected a union case name"
            if s.IsKw "of" then
                vecAdd c (s.Bump ())
                vecAdd c (parseType barCol)
            elif s.IsOp ":" then
                // GADT-style per-case signature
                vecAdd c (s.Bump ())
                vecAdd c (parseType barCol)
            vecAdd acc (Green.node UnionCase (vecToList c))
            if s.Mark = mark then go <- false

    and parseRecordRepr (typeCol : int) : Green =
        let acc = vecNew<Green> ()
        vecAdd acc (s.Bump ())   // '{'
        let mutable go = true
        while go && not s.AtEof && not (s.Is RBrace) do
            let mark = s.Mark
            if s.Is Semicolon then vecAdd acc (s.Bump ())
            elif s.IsKw "mutable" || s.Is Ident then
                let f = vecNew<Green> ()
                if s.IsKw "mutable" then vecAdd f (s.Bump ())
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
        elif s.IsKw "exception" then
            let acc = vecNew<Green> ()
            vecAdd acc (s.Bump ())
            if s.Is Ident then vecAdd acc (s.Bump ())
            if s.IsKw "of" then
                vecAdd acc (s.Bump ())
                vecAdd acc (parseType ctx)
            Green.node TypeDecl (vecToList acc)
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

module Fpp.Syntax.Lexer

open Fpp.Prelude
open Fpp.Syntax

// Trivia-preserving lexer for the F#/F++ surface. Coarse token kinds; the
// parser refines by text. Invariant (tested): rendering the token stream
// reproduces the input byte-for-byte, including on malformed input — error
// tolerance must never lose text.

let private isIdentStart (c : char) = isLetter c || c = '_'
let private isIdentCont (c : char) = isLetter c || isDigit c || c = '_' || c = '\''

let private isSymbolic (c : char) =
    match c with
    | '!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | '<' | '>'
    | '=' | '?' | '@' | '^' | '|' | '~' | ':' | '#' -> true
    | _ -> false

let rec tokenize (src : string) : Token list =
    let n = strLen src
    let peek (i : int) = if i < n then charAt src i else '\000'
    let text (a : int) (b : int) = substr src a (b - a)

    // ---- trivia -----------------------------------------------------------

    /// One piece of trivia at `pos`, or None if a real token starts here.
    let triviaOne (pos : int) : (Trivia * int) option =
        let c = peek pos
        if c = '\r' then
            let e = if peek (pos + 1) = '\n' then pos + 2 else pos + 1
            Some ({ TriviaKind = Newline; TriviaText = text pos e }, e)
        elif c = '\n' then
            Some ({ TriviaKind = Newline; TriviaText = text pos (pos + 1) }, pos + 1)
        elif c = ' ' || c = '\t' then
            let mutable i = pos
            while peek i = ' ' || peek i = '\t' do i <- i + 1
            Some ({ TriviaKind = Whitespace; TriviaText = text pos i }, i)
        elif c = '/' && peek (pos + 1) = '/' then
            let mutable i = pos
            while i < n && peek i <> '\n' && peek i <> '\r' do i <- i + 1
            Some ({ TriviaKind = LineComment; TriviaText = text pos i }, i)
        // `(*)` is the multiplication operator, not an unterminated comment —
        // the same carve-out F# makes. Only this exact three-character run.
        elif c = '(' && peek (pos + 1) = '*' && peek (pos + 2) <> ')' then
            let mutable i = pos + 2
            let mutable depth = 1
            while i < n && depth > 0 do
                if peek i = '(' && peek (i + 1) = '*' then depth <- depth + 1; i <- i + 2
                elif peek i = '*' && peek (i + 1) = ')' then depth <- depth - 1; i <- i + 2
                else i <- i + 1
            Some ({ TriviaKind = BlockComment; TriviaText = text pos i }, i)
        else None

    /// All trivia from `pos` (used for leading trivia).
    let scanLeading (pos : int) : Trivia list * int =
        let rec go acc p =
            match triviaOne p with
            | Some (t, p2) -> go (t :: acc) p2
            | None -> List.rev acc, p
        go [] pos

    /// Trivia up to and including the first newline (Roslyn convention for
    /// trailing trivia); anything after belongs to the next token's leading.
    let scanTrailing (pos : int) : Trivia list * int =
        let rec go acc p =
            match triviaOne p with
            | Some (t, p2) ->
                if t.TriviaKind = Newline then List.rev (t :: acc), p2
                else go (t :: acc) p2
            | None -> List.rev acc, p
        go [] pos

    // ---- tokens -----------------------------------------------------------

    let scanIdent (pos : int) : TokenKind * int =
        let mutable i = pos
        while i < n && isIdentCont (peek i) do i <- i + 1
        let k = if Keywords.isKeyword (text pos i) then Keyword else Ident
        k, i

    /// ``arbitrary identifier`` — delimiters included in the token text.
    let scanBacktickIdent (pos : int) : int =
        let mutable i = pos + 2
        while i < n && not (peek i = '`' && peek (i + 1) = '`') do i <- i + 1
        if i < n then i + 2 else n

    let scanNumber (pos : int) : TokenKind * int =
        let mutable i = pos
        let mutable isFloat = false
        let c1 = peek (pos + 1)
        if peek pos = '0' && (c1 = 'x' || c1 = 'X' || c1 = 'b' || c1 = 'B' || c1 = 'o' || c1 = 'O') then
            i <- pos + 2
            while isHexDigit (peek i) || peek i = '_' do i <- i + 1
        else
            while isDigit (peek i) || peek i = '_' do i <- i + 1
            // consume '.' unless what follows makes it an OPERATOR: another
            // '.' is a range (`1..10`), a letter or '_' is a member access
            // (`1.ToString()`). A bare trailing dot IS a float in F# —
            // `100. * 101. / 2.` is ordinary arithmetic there, and rejecting
            // it was a lexer divergence the Seq conformance port tripped on.
            if peek i = '.' && peek (i + 1) <> '.'
               && not (isAsciiLetter (peek (i + 1))) && peek (i + 1) <> '_' then
                isFloat <- true
                i <- i + 1
                while isDigit (peek i) || peek i = '_' do i <- i + 1
            if peek i = 'e' || peek i = 'E' then
                let s = if peek (i + 1) = '+' || peek (i + 1) = '-' then i + 2 else i + 1
                if isDigit (peek s) then
                    isFloat <- true
                    i <- s
                    while isDigit (peek i) do i <- i + 1
        // suffix letters (y, uy, L, UL, n, f, m, ...) ride along with the literal
        let sufStart = i
        while isAsciiLetter (peek i) do i <- i + 1
        let suf = text sufStart i
        let floatSuf = suf = "f" || suf = "F" || suf = "m" || suf = "M" || suf = "lf" || suf = "LF"
        (if isFloat || floatSuf then FloatLit else IntLit), i

    let scanString (pos : int) : int =
        if peek (pos + 1) = '"' && peek (pos + 2) = '"' then
            // """triple-quoted"""
            let mutable i = pos + 3
            while i < n && not (peek i = '"' && peek (i + 1) = '"' && peek (i + 2) = '"') do i <- i + 1
            if i < n then i + 3 else n
        else
            let mutable i = pos + 1
            let mutable fin = false
            while not fin && i < n do
                if peek i = '\\' then i <- i + 2
                elif peek i = '"' then i <- i + 1; fin <- true
                else i <- i + 1
            i

    /// @"verbatim", "" escapes a quote.
    let scanVerbatimString (pos : int) : int =
        let mutable i = pos + 2
        let mutable fin = false
        while not fin && i < n do
            if peek i = '"' && peek (i + 1) = '"' then i <- i + 2
            elif peek i = '"' then i <- i + 1; fin <- true
            else i <- i + 1
        i

    /// pos is at a `'`. Char literal, or a lone quote (type variable prefix).
    let scanQuote (pos : int) : TokenKind * int =
        if peek (pos + 1) = '\\' then
            // the escaped char is consumed unconditionally, so '\'' works
            let mutable i = pos + 3
            while i < n && peek i <> '\'' && peek i <> '\n' && peek i <> '\r' do i <- i + 1
            CharLit, (if peek i = '\'' then i + 1 else i)
        elif peek (pos + 1) <> '\000' && peek (pos + 2) = '\'' then
            CharLit, pos + 3
        else
            Operator, pos + 1

    let scanOperator (pos : int) : int =
        let mutable i = pos
        let mutable stop = false
        while not stop && i < n && isSymbolic (peek i) do
            // a comment start terminates a symbolic run: `1 +// rest`
            if (peek i = '/' && peek (i + 1) = '/') || (peek i = '(' && peek (i + 1) = '*') then stop <- true
            // `#` stands ALONE. It opens a compiler directive and a FLEXIBLE
            // type, and neither is an operator — gluing it to the run made
            // `aval<#seq<'a>>` lex its `<#` as one token, so the generic
            // argument list was never entered and the type would not parse.
            // No operator in this language contains one.
            elif peek i = '#' then
                if i = pos then i <- i + 1
                stop <- true
            else i <- i + 1
        i

    /// Returns (kind, endPos); token text is src[pos .. endPos).
    let scanToken (pos : int) : TokenKind * int =
        let c = peek pos
        if isIdentStart c then scanIdent pos
        elif isDigit c then scanNumber pos
        elif c = '"' then
            let e = scanString pos
            // byte-string suffix "..."B
            StringLit, (if peek e = 'B' then e + 1 else e)
        elif c = '@' && peek (pos + 1) = '"' then StringLit, scanVerbatimString pos
        elif c = '\'' then scanQuote pos
        elif c = '`' && peek (pos + 1) = '`' then Ident, scanBacktickIdent pos
        elif c = '(' then LParen, pos + 1
        elif c = ')' then RParen, pos + 1
        elif c = '[' then LBracket, pos + 1
        elif c = ']' then RBracket, pos + 1
        elif c = '{' then LBrace, pos + 1
        elif c = '}' then RBrace, pos + 1
        elif c = ',' then Comma, pos + 1
        elif c = ';' then Semicolon, pos + 1
        elif isSymbolic c then Operator, scanOperator pos
        else Unknown, pos + 1

    let rec loop (pos : int) (acc : Token list) : Token list =
        let leading, p = scanLeading pos
        if p >= n then
            let eof = { Kind = Eof; Text = ""; Leading = leading; Trailing = []; Offset = p }
            List.rev (eof :: acc)
        else
            let kind, e = scanToken p
            let trailing, p3 = scanTrailing e
            let tok = { Kind = kind; Text = text p e; Leading = leading; Trailing = trailing; Offset = p }
            loop p3 (tok :: acc)

    let toks = loop 0 []

    // ---- interpolated strings ---------------------------------------------
    //
    // `$"a{e}b"` lexes as the operator `$` beside an ordinary string, so it is
    // expanded HERE into tokens the parser already reads:
    //
    //     ( "a" + string ( e ) + "b" )
    //
    // The hole's own text is tokenised recursively and its tokens keep their
    // REAL file offsets — every later pass keys tables by offset, so a hole's
    // names resolve, and its operators get their kinds, exactly as if they had
    // been written outside the string. `{{` and `}}` are literal braces.
    //
    // NOT supported: a .NET format specifier (`{x:N2}`) — the `:` would read as
    // a type annotation — and `$$"""…"""`.
    let expandInterp (ts : Token list) : Token list =
        let syn (k : TokenKind) (txt : string) (off : int) : Token =
            { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = off }
        let synL (k : TokenKind) (txt : string) (off : int) (lead : Trivia list) : Token =
            { Kind = k; Text = txt; Leading = lead; Trailing = []; Offset = off }
        let synT (k : TokenKind) (txt : string) (off : int) (trail : Trivia list) : Token =
            { Kind = k; Text = txt; Leading = []; Trailing = trail; Offset = off }
        // split a literal BODY into pieces: each is (isLiteral, text, start in
        // the body). Kept as three parallel vectors — the compiler's own
        // sources stay inside the subset it can parse, and a tuple as a
        // generic argument is not in it.
        let pieceIsLit = vecNew<bool> ()
        let pieceText = vecNew<string> ()
        let pieceAt = vecNew<int> ()
        let pieces (body : string) : unit =
            vecClear pieceIsLit; vecClear pieceText; vecClear pieceAt
            let bn = strLen body
            let mutable lit = ""
            let mutable litStart = 0
            let mutable i = 0
            while i < bn do
                let c = charAt body i
                if c = '{' && i + 1 < bn && charAt body (i + 1) = '{' then
                    lit <- lit + "{"; i <- i + 2
                elif c = '}' && i + 1 < bn && charAt body (i + 1) = '}' then
                    lit <- lit + "}"; i <- i + 2
                elif c = '{' then
                    vecAdd pieceIsLit true; vecAdd pieceText lit; vecAdd pieceAt litStart
                    lit <- ""
                    // scan to the matching close brace, counting nesting so a
                    // record inside the hole survives
                    let mutable depth = 1
                    let mutable j = i + 1
                    let holeStart = j
                    while j < bn && depth > 0 do
                        let d = charAt body j
                        if d = '{' then depth <- depth + 1
                        elif d = '}' then depth <- depth - 1
                        if depth > 0 then j <- j + 1
                    vecAdd pieceIsLit false; vecAdd pieceText (substr body holeStart (j - holeStart)); vecAdd pieceAt holeStart
                    i <- j + 1
                    litStart <- i
                else
                    lit <- lit + string c; i <- i + 1
            vecAdd pieceIsLit true; vecAdd pieceText lit; vecAdd pieceAt litStart
        let rec go (ts : Token list) (acc : Token list) : Token list =
            match ts with
            | d :: str :: rest when d.Kind = Operator && d.Text = "$" && str.Kind = StringLit
                                    && d.Offset + 1 = str.Offset && List.isEmpty d.Trailing
                                    && strLen str.Text >= 2 && charAt str.Text 0 = '"' ->
                let body = substr str.Text 1 (strLen str.Text - 2)
                let bodyOff = str.Offset + 1
                pieces body
                let o = d.Offset
                let out = vecNew<Token> ()
                vecAdd out (synL LParen "(" o d.Leading)
                let mutable first = true
                for k in 0 .. vecLen pieceIsLit - 1 do
                    let isLit = vecGet pieceIsLit k
                    let txt = vecGet pieceText k
                    let at = vecGet pieceAt k
                    if isLit then
                        if txt <> "" then
                            if not first then vecAdd out (syn Operator "+" o)
                            vecAdd out (syn StringLit ("\"" + txt + "\"") (bodyOff + at))
                            first <- false
                    else
                        // every `+` may share the `$`'s offset (they are all
                        // string concatenation, so one kind entry serves), but
                        // each `string` needs its OWN: kinds are keyed by
                        // offset, and sharing one with the `+` overwrote it —
                        // the conversion then rendered nothing at all. The
                        // hole's `{` is a position no real token occupies.
                        if not first then vecAdd out (syn Operator "+" o)
                        vecAdd out (syn Ident "string" (bodyOff + at - 1))
                        vecAdd out (syn LParen "(" (bodyOff + at - 1))
                        for ht in tokenizeAt (bodyOff + at) txt do
                            if ht.Kind <> Eof then vecAdd out ht
                        vecAdd out (syn RParen ")" (bodyOff + at + strLen txt))
                        first <- false
                if first then vecAdd out (syn StringLit "\"\"" bodyOff)
                vecAdd out (synT RParen ")" (str.Offset + strLen str.Text - 1) str.Trailing)
                go rest (List.rev (vecToList out) @ acc)
            | t :: rest -> go rest (t :: acc)
            | [] -> List.rev acc
        go ts []
    if (toks |> List.exists (fun t -> t.Kind = Operator && t.Text = "$")) then expandInterp toks else toks

/// `tokenize`, with every offset shifted by `base0` — an interpolation hole
/// is lexed on its own text but has to report the offsets it really occupies.
and tokenizeAt (base0 : int) (src : string) : Token list =
    tokenize src |> List.map (fun t -> { t with Offset = t.Offset + base0 })

/// Inverse of tokenize — the lossless-ness witness.
let render (tokens : Token list) : string =
    let triviaText (ts : Trivia list) = List.map (fun t -> t.TriviaText) ts
    tokens
    |> List.collect (fun t -> triviaText t.Leading @ [ t.Text ] @ triviaText t.Trailing)
    |> String.concat ""

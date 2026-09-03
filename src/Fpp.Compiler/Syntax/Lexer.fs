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
            // source arrives LATIN-1 (offsets are byte offsets), so a
            // non-ASCII char literal is a UTF-8 RUN between the quotes —
            // `'日'` is five bytes, not three. Only a well-formed run
            // counts, so `'a,'b` (two type variables) is still an operator.
            let u = int (peek (pos + 1))
            let cont (k : int) = int (peek k) >= 0x80 && int (peek k) < 0xC0
            let width =
                if u >= 0xC2 && u < 0xE0 && cont (pos + 2) then 2
                elif u >= 0xE0 && u < 0xF0 && cont (pos + 2) && cont (pos + 3) then 3
                elif u >= 0xF0 && u < 0xF5 && cont (pos + 2) && cont (pos + 3) && cont (pos + 4) then 4
                else 0
            if width > 0 && peek (pos + 1 + width) = '\'' then CharLit, pos + 2 + width
            else Operator, pos + 1

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
    // A PRINTF SPECIFIER binds to the hole that follows it: `$"n=%d{x}"` is
    //
    //     ( "n=" + sprintf "%d" ( x ) )
    //
    // rather than `string`. Routing it through sprintf is what makes the
    // specifier both FORMAT and TYPE-CHECK — `%.2f` pads and `%d` refuses a
    // string — for free, since printf is already complete. Left as literal
    // text it printed itself: `$"%d{x}"` rendered `%d42`, a wrong answer with
    // no diagnostic anywhere.
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
        /// the printf specifier a hole inherits from the literal before it
        /// ("" when it has none). Parallel to the three above.
        let pieceSpec = vecNew<string> ()
        // `System.Char.IsDigit` is OUT of the self-hosting subset (it stubs,
        // and stage-1 then traps) — this file is compiler source.
        let isDig (c : char) : bool = c >= '0' && c <= '9'
        let isConv (c : char) : bool =
            c = 'd' || c = 'i' || c = 'u' || c = 'x' || c = 'X' || c = 'o'
            || c = 'b' || c = 's' || c = 'c' || c = 'f' || c = 'F' || c = 'e'
            || c = 'E' || c = 'g' || c = 'G' || c = 'M' || c = 'O' || c = 'A'
        /// The trailing printf specifier of a literal piece, or "". Scans
        /// BACKWARDS from the end: `%` flags width `.` precision conversion,
        /// and the `%` must not itself be escaped (`%%` is a literal percent,
        /// so `$"100%%{x}"` keeps its text and the hole stays a `string`).
        let trailingSpec (txt : string) : string =
            let n = strLen txt
            if n < 2 then ""
            elif not (isConv (charAt txt (n - 1))) then ""
            else
                let mutable i = n - 2
                let mutable ok = true
                while ok && i >= 0 && (isDig (charAt txt i) || charAt txt i = '.'
                                       || charAt txt i = '+' || charAt txt i = '-'
                                       || charAt txt i = ' ' || charAt txt i = '0') do
                    i <- i - 1
                if i < 0 || charAt txt i <> '%' then ""
                // an ESCAPED percent is not a specifier: count the run of `%`
                // ending here, and an even-length run is all literal pairs
                else
                    let mutable j = i
                    let mutable runs = 0
                    while j >= 0 && charAt txt j = '%' do
                        runs <- runs + 1
                        j <- j - 1
                    if runs % 2 = 0 then "" else substr txt i (n - i)
        let pieces (body : string) : unit =
            vecClear pieceIsLit; vecClear pieceText; vecClear pieceAt; vecClear pieceSpec
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
        /// Move each hole's specifier off the END of the literal before it.
        /// Runs after `pieces`, so it can see both sides.
        /// `%%` is one literal percent, because an interpolated string IS a
        /// printf format in F#. The literal pieces here become ORDINARY string
        /// literals, which no formatter ever sees, so the pair survived and
        /// `$"100%%{x}"` printed `100%%42`.
        let collapsePct (txt : string) : string =
            let n = strLen txt
            let mutable outp = ""
            let mutable i = 0
            while i < n do
                if charAt txt i = '%' && i + 1 < n && charAt txt (i + 1) = '%' then
                    outp <- outp + "%"; i <- i + 2
                else
                    outp <- outp + string (charAt txt i); i <- i + 1
            outp
        let bindSpecs () : unit =
            vecClear pieceSpec
            for _ in 0 .. vecLen pieceIsLit - 1 do vecAdd pieceSpec ""
            for k in 0 .. vecLen pieceIsLit - 1 do
                if not (vecGet pieceIsLit k) && k > 0 && vecGet pieceIsLit (k - 1) then
                    let prev = vecGet pieceText (k - 1)
                    let sp = trailingSpec prev
                    if sp <> "" then
                        vecSet pieceSpec k sp
                        vecSet pieceText (k - 1) (substr prev 0 (strLen prev - strLen sp))
            // AFTER the specifiers are taken: `trailingSpec` counts the run of
            // `%` to tell a specifier from an escaped pair, and collapsing
            // first would turn `%%d{x}` — a literal `%d` — into one that reads
            // as a specifier and eats the hole
            for k in 0 .. vecLen pieceIsLit - 1 do
                if vecGet pieceIsLit k then
                    vecSet pieceText k (collapsePct (vecGet pieceText k))
        let rec go (ts : Token list) (acc : Token list) : Token list =
            match ts with
            | d :: str :: rest when d.Kind = Operator && d.Text = "$" && str.Kind = StringLit
                                    && d.Offset + 1 = str.Offset && List.isEmpty d.Trailing
                                    && strLen str.Text >= 2 && charAt str.Text 0 = '"' ->
                let body = substr str.Text 1 (strLen str.Text - 2)
                let bodyOff = str.Offset + 1
                pieces body
                bindSpecs ()
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
                        let spec = vecGet pieceSpec k
                        if spec = "" then
                            vecAdd out (syn Ident "string" (bodyOff + at - 1))
                        else
                            // the format literal takes the specifier's OWN
                            // source position — unique (offsets key the kind
                            // tables) and honest, since that is where it is
                            vecAdd out (syn Ident "sprintf" (bodyOff + at - 1))
                            vecAdd out (syn StringLit ("\"" + spec + "\"") (bodyOff + at - 1 - strLen spec))
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
    // ---- anonymous records ------------------------------------------------
    //
    // `{| X = 1; Y = "s" |}` is F#'s STRUCTURAL record and everything here is
    // nominal, so it expands to an ordinary record of a SYNTHESIZED type, one
    // per distinct field-name set:
    //
    //     ({ X = 1; Y = "s" } : $anon$X$Y<_, _>)
    //
    // with `type $anon$X$Y<'a, 'b> = { X : 'a; Y : 'b }` injected after the
    // module header. GENERIC, so two literals with the same labels and
    // different value types are different types the way F# has them; SORTED,
    // so writing the fields in another order does not make another type.
    //
    // The ascription is not decoration. A record literal resolves by
    // field-name SET, so a nominal `type P = { X : int; Y : string }` in the
    // same program would capture `{| X = 1; Y = "s" |}` — the expected type
    // is what pins the owner, and that rule already exists for F#'s sake.
    //
    // `{| r with X = 2 |}` needs NO ascription: copy-and-update takes its
    // type from the base expression, which already has one.
    let expandAnon (srcLen : int) (ts : Token list) : Token list =
        let arr = vecNew<Token> ()
        for t in ts do vecAdd arr t
        let n = vecLen arr
        // synthetic offsets live PAST the end of the source: unique in this
        // file, so no table keyed by `path:offset` can confuse one with a
        // real token, and never negative or absurd
        let mutable synth = srcLen + 8
        // laid out by TEXT LENGTH, not one apart: `Name<int>` only reads as
        // type arguments when the `<` TOUCHES the name, and the parser tests
        // that with `offset + length`. Spaced by one, every synthetic `<`
        // read as less-than instead
        let syn (k : TokenKind) (txt : string) : Token =
            let at = synth
            synth <- synth + strLen txt
            { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = at }
        /// A synthetic token AT a real position. The type form mixes
        /// synthesized brackets with the user's own type tokens, and
        /// `looksLikeTypeArgs` refuses a `<...>` whose tokens are not all on
        /// ONE LINE — past-EOF offsets all report the file's last line, so a
        /// `{| N : int |}` written anywhere else was read as less-than and
        /// the annotation ended at the name. Anchoring to the `{` that is
        /// being dropped puts them back on the right line; nothing keys on
        /// these offsets, since only the type NAME is an identifier.
        let synAt (at : int) (k : TokenKind) (txt : string) : Token =
            { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = at }
        let tokAt (i : int) : Token = vecGet arr i
        let isOpenAt (i : int) : bool =
            i + 1 < n && (tokAt i).Kind = LBrace
            && (tokAt (i + 1)).Kind = Operator && (tokAt (i + 1)).Text = "|"
            && (tokAt (i + 1)).Offset = (tokAt i).Offset + 1
        let isCloseAt (i : int) : bool =
            i + 1 < n && (tokAt i).Kind = Operator && (tokAt i).Text = "|"
            && (tokAt (i + 1)).Kind = RBrace
            && (tokAt (i + 1)).Offset = (tokAt i).Offset + 1
        let opens (k : TokenKind) = k = LBrace || k = LParen || k = LBracket
        let closes (k : TokenKind) = k = RBrace || k = RParen || k = RBracket
        /// index just past the `|}` matching the `{|` that starts at `i`
        let matchEnd (i : int) : int =
            let mutable j = i + 2
            let mutable depth = 0
            let mutable stop = -1
            while stop < 0 && j < n do
                if isOpenAt j then depth <- depth + 1; j <- j + 2
                elif isCloseAt j && depth = 0 then stop <- j
                elif isCloseAt j then depth <- depth - 1; j <- j + 2
                else
                    (if opens (tokAt j).Kind then depth <- depth + 1
                     elif closes (tokAt j).Kind then depth <- depth - 1)
                    j <- j + 1
            if stop < 0 then n else stop
        let splitOn (sep : char) (txt : string) : string list =
            let acc = vecNew<string> ()
            let mutable cur = ""
            let ln = strLen txt
            let mutable i = 0
            while i < ln do
                (if charAt txt i = sep then (vecAdd acc cur; cur <- "")
                 else cur <- cur + string (charAt txt i))
                i <- i + 1
            vecAdd acc cur
            vecToList acc
        // every distinct field-name set the file uses, as "X,Y" (sorted)
        let shapes = vecNew<string> ()
        let joinLabels (ls : string list) : string = String.concat "," (List.sort ls)
        let nameOfShape (key : string) : string =
            "$anon$" + String.concat "$" (splitOn ',' key)
        /// the labels of one anon record, from its INNER token range
        let labelsIn (lo : int) (hi : int) : string list =
            let acc = vecNew<string> ()
            let mutable depth = 0
            let mutable atFieldStart = true
            let mutable j = lo
            while j < hi do
                let t = tokAt j
                if isOpenAt j then depth <- depth + 1; j <- j + 2; atFieldStart <- false
                elif isCloseAt j then depth <- depth - 1; j <- j + 2; atFieldStart <- false
                else
                    (if opens t.Kind then depth <- depth + 1
                     elif closes t.Kind then depth <- depth - 1)
                    (if depth = 0 && t.Kind = Semicolon then atFieldStart <- true
                     elif depth = 0 && t.Kind = Ident && atFieldStart
                          && j + 1 < hi
                          && (tokAt (j + 1)).Kind = Operator
                          && ((tokAt (j + 1)).Text = "=" || (tokAt (j + 1)).Text = ":") then
                        vecAdd acc t.Text
                        atFieldStart <- false
                     elif t.Kind <> Semicolon then atFieldStart <- false)
                    j <- j + 1
            vecToList acc
        /// is this a TYPE (`{| X : int |}`) rather than a value? A field is
        /// introduced by `=` in one and `:` in the other, and a `:` inside a
        /// value sits under a paren, so depth 0 tells them apart.
        let isTypeForm (lo : int) (hi : int) : bool =
            let mutable depth = 0
            let mutable sawEq = false
            let mutable sawColon = false
            let mutable j = lo
            while j < hi do
                let t = tokAt j
                (if opens t.Kind then depth <- depth + 1
                 elif closes t.Kind then depth <- depth - 1
                 elif depth = 0 && t.Kind = Operator && t.Text = "=" then sawEq <- true
                 elif depth = 0 && t.Kind = Operator && t.Text = ":" then sawColon <- true)
                j <- j + 1
            not sawEq && sawColon
        /// does this range use `with` (copy-and-update) at depth 0?
        let hasWith (lo : int) (hi : int) : bool =
            let mutable depth = 0
            let mutable found = false
            let mutable j = lo
            while j < hi do
                let t = tokAt j
                (if opens t.Kind then depth <- depth + 1
                 elif closes t.Kind then depth <- depth - 1
                 elif depth = 0 && t.Kind = Keyword && t.Text = "with" then found <- true)
                j <- j + 1
            found
        let rec expandRange (lo : int) (hi : int) : Token list =
            let out = vecNew<Token> ()
            let mutable i = lo
            while i < hi do
                if isOpenAt i then
                    let e = matchEnd i
                    let inner = expandRange (i + 2) e
                    let labels = labelsIn (i + 2) e
                    if isTypeForm (i + 2) e then
                        // `{| X : int; Y : string |}` names the same
                        // synthesized type its literals do, with the field
                        // TYPES as its arguments — in sorted label order, so
                        // the written order cannot make a second type
                        let key = joinLabels labels
                        if not (List.contains key (vecToList shapes)) then vecAdd shapes key
                        // each field's type tokens, kept as index ranges
                        let flab = vecNew<string> ()
                        let flo = vecNew<int> ()
                        let fhi = vecNew<int> ()
                        let mutable depth = 0
                        let mutable j = i + 2
                        let mutable cur = -1
                        while j < e do
                            let t = tokAt j
                            if depth = 0 && t.Kind = Semicolon then
                                (if cur >= 0 then vecAdd fhi j)
                                cur <- -1
                                j <- j + 1
                            elif depth = 0 && cur < 0 && t.Kind = Ident
                                 && j + 1 < e && (tokAt (j + 1)).Kind = Operator
                                 && (tokAt (j + 1)).Text = ":" then
                                vecAdd flab t.Text
                                vecAdd flo (j + 2)
                                cur <- 1
                                j <- j + 2
                            else
                                (if opens t.Kind then depth <- depth + 1
                                 elif closes t.Kind then depth <- depth - 1)
                                j <- j + 1
                        if cur >= 0 then vecAdd fhi e
                        let anchor = (tokAt i).Offset
                        vecAdd out (synAt anchor Ident (nameOfShape key))
                        vecAdd out (synAt anchor Operator "<")
                        let ls = List.sort labels
                        List.iteri (fun k (l : string) ->
                            if k > 0 then vecAdd out (synAt anchor Comma ",")
                            let mutable found = -1
                            for m in 0 .. vecLen flab - 1 do
                                if found < 0 && vecGet flab m = l then found <- m
                            if found >= 0 && found < vecLen fhi then
                                for q in vecGet flo found .. vecGet fhi found - 1 do
                                    vecAdd out (tokAt q)) ls
                        vecAdd out (synAt anchor Operator ">")
                    elif hasWith (i + 2) e then
                        // the base expression carries the type already
                        vecAdd out (syn LParen "(")
                        vecAdd out (syn LBrace "{")
                        for t in inner do vecAdd out t
                        vecAdd out (syn RBrace "}")
                        vecAdd out (syn RParen ")")
                        // a GAP, so this `)` is not adjacent to the next
                        // expansion's `(`: adjacency is F#'s high-precedence
                        // application, and `f {| .. |} {| .. |}` became the
                        // first argument APPLIED to the second
                        synth <- synth + 1
                    else
                        let key = joinLabels labels
                        if not (List.contains key (vecToList shapes)) then vecAdd shapes key
                        vecAdd out (syn LParen "(")
                        vecAdd out (syn LBrace "{")
                        for t in inner do vecAdd out t
                        vecAdd out (syn RBrace "}")
                        vecAdd out (syn Operator ":")
                        vecAdd out (syn Ident (nameOfShape key))
                        vecAdd out (syn Operator "<")
                        let ls = List.sort labels
                        List.iteri (fun k _ ->
                            if k > 0 then vecAdd out (syn Comma ",")
                            vecAdd out (syn Ident "_")) ls
                        vecAdd out (syn Operator ">")
                        vecAdd out (syn RParen ")")
                        // a GAP, so this `)` is not adjacent to the next
                        // expansion's `(`: adjacency is F#'s high-precedence
                        // application, and `f {| .. |} {| .. |}` became the
                        // first argument APPLIED to the second
                        synth <- synth + 1
                    i <- e + 2
                else
                    vecAdd out (tokAt i)
                    i <- i + 1
            vecToList out
        let body = expandRange 0 n
        if vecLen shapes = 0 then body
        else
            // the declarations go after the module or namespace HEADER: a
            // type cannot precede it, and everything else may follow it
            let decls = vecNew<Token> ()
            for k in 0 .. vecLen shapes - 1 do
                let ls = splitOn ',' (vecGet shapes k)
                vecAdd decls (syn Keyword "type")
                vecAdd decls (syn Ident (nameOfShape (vecGet shapes k)))
                vecAdd decls (syn Operator "<")
                List.iteri (fun j _ ->
                    if j > 0 then vecAdd decls (syn Comma ",")
                    vecAdd decls (syn Operator "'")
                    vecAdd decls (syn Ident ("anon" + string j))) ls
                vecAdd decls (syn Operator ">")
                vecAdd decls (syn Operator "=")
                vecAdd decls (syn LBrace "{")
                List.iteri (fun j (l : string) ->
                    if j > 0 then vecAdd decls (syn Semicolon ";")
                    vecAdd decls (syn Ident l)
                    vecAdd decls (syn Operator ":")
                    vecAdd decls (syn Operator "'")
                    vecAdd decls (syn Ident ("anon" + string j))) ls
                vecAdd decls (syn RBrace "}")
            let outv = vecNew<Token> ()
            let barr = vecNew<Token> ()
            for t in body do vecAdd barr t
            let bn = vecLen barr
            // past `module`/`namespace`, its dotted name and an optional `=`
            let mutable cut = 0
            let mutable j = 0
            let mutable seen = false
            while j < bn && not seen do
                let t = vecGet barr j
                if t.Kind = Keyword && (t.Text = "module" || t.Text = "namespace") then
                    seen <- true
                    let mutable k = j + 1
                    while k < bn && ((vecGet barr k).Kind = Ident
                                     || ((vecGet barr k).Kind = Operator && (vecGet barr k).Text = ".")
                                     || ((vecGet barr k).Kind = Keyword && (vecGet barr k).Text = "rec")) do
                        k <- k + 1
                    if k < bn && (vecGet barr k).Kind = Operator && (vecGet barr k).Text = "=" then k <- k + 1
                    cut <- k
                else j <- j + 1
            for k in 0 .. cut - 1 do vecAdd outv (vecGet barr k)
            for t in vecToList decls do vecAdd outv t
            for k in cut .. bn - 1 do vecAdd outv (vecGet barr k)
            vecToList outv
    let toks2 =
        if (toks |> List.exists (fun t -> t.Kind = Operator && t.Text = "$")) then expandInterp toks else toks
    if (toks2 |> List.exists (fun t -> t.Kind = LBrace)) then expandAnon (strLen src) toks2 else toks2

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

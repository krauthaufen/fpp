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

let tokenize (src : string) : Token list =
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
        elif c = '(' && peek (pos + 1) = '*' then
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
            // consume '.' only when followed by a digit, so `1..10` and
            // `1.ToString()` lex as int-then-operator
            if peek i = '.' && isDigit (peek (i + 1)) then
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

    loop 0 []

/// Inverse of tokenize — the lossless-ness witness.
let render (tokens : Token list) : string =
    let triviaText (ts : Trivia list) = List.map (fun t -> t.TriviaText) ts
    tokens
    |> List.collect (fun t -> triviaText t.Leading @ [ t.Text ] @ triviaText t.Trailing)
    |> String.concat ""

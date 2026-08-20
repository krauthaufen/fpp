module Fpp.Backend.StrLit

open Fpp.Prelude

// String-literal decoding, shared by every backend: the three spellings
// (triple-quoted, verbatim, ordinary) and the escape table. It lived in the
// wasm-GC driver until that backend was deleted; nothing here is
// backend-specific.

// unescape for string literals — the full three-spelling logic, ported from
// the retired text emitter: triple-quoted is literal, verbatim folds `""`,
// ordinary processes named/decimal/hex/unicode escapes into BYTES
let private escapeAt (s : string) (i : int) : int * int =
    let at k = if i + k < strLen s then charAt s (i + k) else '\000'
    let hexVal (c : char) =
        if c >= '0' && c <= '9' then int c - 48
        elif c >= 'a' && c <= 'f' then int c - 87
        elif c >= 'A' && c <= 'F' then int c - 55
        else -1
    let hexRun (start : int) (count : int) =
        let mutable v = 0
        let mutable k = 0
        let mutable ok = true
        while ok && k < count do
            let d = hexVal (at (start + k))
            if d < 0 then ok <- false else v <- v * 16 + d
            k <- k + 1
        if ok then Some v else None
    match at 1 with
    | 'n' -> 10, 2
    | 't' -> 9, 2
    | 'r' -> 13, 2
    | 'a' -> 7, 2
    | 'b' -> 8, 2
    | 'f' -> 12, 2
    | 'v' -> 11, 2
    | '\\' -> 92, 2
    | '"' -> 34, 2
    | '\'' -> 39, 2
    | 'x' -> (match hexRun 2 2 with Some v -> v, 4 | None -> int (at 1), 2)
    | 'u' -> (match hexRun 2 4 with Some v -> v, 6 | None -> int (at 1), 2)
    | 'U' -> (match hexRun 2 8 with Some v -> v, 10 | None -> int (at 1), 2)
    | c when c >= '0' && c <= '9' ->
        if isDigit (at 2) && isDigit (at 3) then
            ((int (at 1) - 48) * 100 + (int (at 2) - 48) * 10 + (int (at 3) - 48)) % 256, 4
        elif c = '0' then 0, 2
        else int c, 2
    | c -> int c, 2

let unescape (raw : string) : byte[] =
    // UTF-16 UNITS, serialized little-endian for the data segment (the
    // array.new_data COUNT is in ELEMENTS — internStr halves the length).
    // Each source char IS one unit (charAt walks the lexer's UTF-16 string,
    // surrogate pairs arrive as two chars and stay two units); `\u` names
    // one unit, `\U` beyond the BMP becomes a surrogate pair, and
    // `\xHH`/`\DDD` name one unit under 256.
    let raw = if strLen raw > 1 && charAt raw (strLen raw - 1) = 'B' then substr raw 0 (strLen raw - 1) else raw
    let isTriple =
        strLen raw >= 6 && charAt raw 0 = '"' && charAt raw 1 = '"' && charAt raw 2 = '"'
    let isVerbatim = strLen raw >= 3 && charAt raw 0 = '@'
    let units = vecNew<int> ()
    if isTriple then
        // no escape processing at all: the text IS the value
        let inner = substr raw 3 (strLen raw - 6)
        for k in 0 .. strLen inner - 1 do vecAdd units (int (charAt inner k))
    elif isVerbatim then
        // `""` is the only escape a verbatim string has
        let inner = substr raw 2 (strLen raw - 3)
        let mutable i = 0
        while i < strLen inner do
            if charAt inner i = '"' && i + 1 < strLen inner && charAt inner (i + 1) = '"' then
                vecAdd units 34
                i <- i + 2
            else
                vecAdd units (int (charAt inner i))
                i <- i + 1
    else
        let inner = if strLen raw >= 2 then substr raw 1 (strLen raw - 2) else raw
        let mutable i = 0
        while i < strLen inner do
            let c = charAt inner i
            if c = '\\' && i + 1 < strLen inner then
                let code, width = escapeAt inner i
                if code > 0xFFFF then
                    // beyond the BMP: the pair, exactly as .NET stores it
                    let v = code - 0x10000
                    vecAdd units (0xD800 ||| (v / 1024))
                    vecAdd units (0xDC00 ||| (v % 1024))
                else vecAdd units code
                i <- i + width
            else
                vecAdd units (int c)
                i <- i + 1
    // The CLI reads source as LATIN-1 (offsets are byte offsets), so a
    // UTF-8 é arrives as the two chars C3 A9 — fold valid UTF-8 runs back
    // into code points. Chars over 255 (an LSP host hands REAL strings)
    // are already decoded and pass through; so does anything that does not
    // shape up as UTF-8 (a `\xE9` escape followed by ASCII stays itself).
    let folded = vecNew<int> ()
    let raw = vecToList units |> List.toArray
    let cont (k : int) = k < raw.Length && raw.[k] >= 0x80 && raw.[k] < 0xC0
    let mutable i = 0
    while i < raw.Length do
        let u = raw.[i]
        if u >= 0xC2 && u < 0xE0 && cont (i + 1) then
            vecAdd folded (((u - 0xC0) * 64) + (raw.[i + 1] - 0x80))
            i <- i + 2
        elif u >= 0xE0 && u < 0xF0 && cont (i + 1) && cont (i + 2) then
            vecAdd folded (((u - 0xE0) * 4096) + ((raw.[i + 1] - 0x80) * 64)
                           + (raw.[i + 2] - 0x80))
            i <- i + 3
        elif u >= 0xF0 && u < 0xF5 && cont (i + 1) && cont (i + 2) && cont (i + 3) then
            let cp = ((u - 0xF0) * 262144) + ((raw.[i + 1] - 0x80) * 4096)
                     + ((raw.[i + 2] - 0x80) * 64) + (raw.[i + 3] - 0x80)
            let v = cp - 0x10000
            vecAdd folded (0xD800 ||| (v / 1024))
            vecAdd folded (0xDC00 ||| (v % 1024))
            i <- i + 4
        else
            vecAdd folded u
            i <- i + 1
    let out = vecNew<byte> ()
    for u in vecToList folded do
        vecAdd out (byte (u % 256))
        vecAdd out (byte ((u / 256) % 256))
    vecToArray out

/// a char literal is ONE code point; reading it out of the unescaped BYTES
/// would take only the first byte of a multi-byte escape
let charCode (raw : string) : int =
    let inner = if strLen raw >= 2 then substr raw 1 (strLen raw - 2) else raw
    if strLen inner > 1 && charAt inner 0 = '\\' then fst (escapeAt inner 0)
    else
        let bs = unescape raw
        if bs.Length > 1 then int bs.[0] + 256 * int bs.[1] else 0


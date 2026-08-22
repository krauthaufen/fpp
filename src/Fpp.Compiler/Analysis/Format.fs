module Fpp.Analysis.Format

open Fpp.Prelude

// The printf family is COMPILE-TIME: the format string is a literal, so its
// holes are parsed once, typed during inference, and expanded to string
// concatenation during lowering. Nothing survives to runtime but the pieces.
//
// Supported: %d %i %u %s %c %b %x %X %o %f %e %E %g %G %A %O and %%, each
// with the `-`, `0` and `+` flags, a width, and a precision. %e/%g and
// precision waited for the prelude's exact decimal buffer (FloatFmt): a
// format that prints ALMOST what F# prints is worse than none, and only an
// exact expansion plus round-half-to-even reproduces .NET digit for digit.

type Seg =
    /// literal text, RAW (escape sequences unexpanded — the emitter owns
    /// unescaping, exactly as for any other string literal)
    | Text of string
    /// one conversion: specifier, minimum width (0 = none), pad with zero,
    /// left-justify, precision (-1 = none), always-sign
    | Hole of char * int * bool * bool * int * bool

/// Split a raw format (without the surrounding quotes) into segments.
/// Returns an error message for anything unsupported.
let parse (raw : string) : Result<Seg list, string> =
    let segs = vecNew<Seg> ()
    // chunks joined once at the end: appending to a string would be
    // quadratic, and a builder is not part of the seam
    let text = vecNew<string> ()
    let flush () =
        if vecLen text > 0 then
            vecAdd segs (Text (String.concat "" (vecToList text)))
            vecClear text
    let mutable i = 0
    let mutable error = None
    while error.IsNone && i < raw.Length do
        let c = raw.[i]
        if c = '%' then
            if i + 1 >= raw.Length then error <- Some "the format ends inside a specifier"
            elif raw.[i + 1] = '%' then
                vecAdd text "%"
                i <- i + 2
            else
                // flags, then width, then the specifier
                let mutable j = i + 1
                let mutable zero = false
                let mutable left = false
                let mutable plus = false
                while j < raw.Length && (raw.[j] = '0' || raw.[j] = '-' || raw.[j] = '+') do
                    (if raw.[j] = '0' then zero <- true
                     elif raw.[j] = '+' then plus <- true
                     else left <- true)
                    j <- j + 1
                let mutable width = 0
                while j < raw.Length && raw.[j] >= '0' && raw.[j] <= '9' do
                    width <- width * 10 + int raw.[j] - int '0'
                    j <- j + 1
                // the precision: `.N`, and a bare `.` means zero
                let mutable prec = -1
                if j < raw.Length && raw.[j] = '.' then
                    j <- j + 1
                    prec <- 0
                    while j < raw.Length && raw.[j] >= '0' && raw.[j] <= '9' do
                        prec <- prec * 10 + int raw.[j] - int '0'
                        j <- j + 1
                if j >= raw.Length then error <- Some "the format ends inside a specifier"
                else
                    let sp = raw.[j]
                    if String.exists (fun k -> k = sp) "diuscbxXofeEgGAO" then
                        flush ()
                        vecAdd segs (Hole (sp, width, zero, left, prec, plus))
                    else
                        error <- Some ("unsupported format specifier %" + string sp)
                    i <- j + 1
        else
            vecAdd text (string c)
            i <- i + 1
    flush ()
    match error with
    | Some e -> Error e
    | None -> Ok (vecToList segs)

let holes (segs : Seg list) : (char * int * bool * bool * int * bool) list =
    segs |> List.choose (fun s -> match s with Hole (c, w, z, l, p, pl) -> Some (c, w, z, l, p, pl) | Text _ -> None)

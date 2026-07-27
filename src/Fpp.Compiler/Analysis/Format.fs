module Fpp.Analysis.Format

// The printf family is COMPILE-TIME: the format string is a literal, so its
// holes are parsed once, typed during inference, and expanded to string
// concatenation during lowering. Nothing survives to runtime but the pieces.
//
// Supported: %d %i %u %s %c %b %x %X %o %f %A and %%. Deliberately absent:
// %e and %g (their .NET renderings are not reproducible bit-for-bit without
// shortest-roundtrip formatting, and a format that prints ALMOST the same
// thing as F# is worse than none) and precision (.N). Width with the 0/-
// flags is in, because %02x is everywhere bytes are.

type Seg =
    /// literal text, RAW (escape sequences unexpanded — the emitter owns
    /// unescaping, exactly as for any other string literal)
    | Text of string
    /// one conversion: specifier, minimum width (0 = none), pad with zero,
    /// left-justify
    | Hole of char * int * bool * bool

/// Split a raw format (without the surrounding quotes) into segments.
/// Returns an error message for anything unsupported.
let parse (raw : string) : Result<Seg list, string> =
    let segs = System.Collections.Generic.List<Seg>()
    let text = System.Text.StringBuilder()
    let flush () =
        if text.Length > 0 then
            segs.Add (Text (text.ToString ()))
            text.Clear () |> ignore
    let mutable i = 0
    let mutable error = None
    while error.IsNone && i < raw.Length do
        let c = raw.[i]
        if c = '%' then
            if i + 1 >= raw.Length then error <- Some "the format ends inside a specifier"
            elif raw.[i + 1] = '%' then
                text.Append '%' |> ignore
                i <- i + 2
            else
                // flags, then width, then the specifier
                let mutable j = i + 1
                let mutable zero = false
                let mutable left = false
                while j < raw.Length && (raw.[j] = '0' || raw.[j] = '-') do
                    (if raw.[j] = '0' then zero <- true else left <- true)
                    j <- j + 1
                let mutable width = 0
                while j < raw.Length && raw.[j] >= '0' && raw.[j] <= '9' do
                    width <- width * 10 + int raw.[j] - int '0'
                    j <- j + 1
                if j >= raw.Length then error <- Some "the format ends inside a specifier"
                else
                    let sp = raw.[j]
                    if "diuscbxXofA".IndexOf sp >= 0 then
                        flush ()
                        segs.Add (Hole (sp, width, zero, left))
                    else
                        error <- Some ("unsupported format specifier %" + string sp)
                    i <- j + 1
        else
            text.Append c |> ignore
            i <- i + 1
    flush ()
    match error with
    | Some e -> Error e
    | None -> Ok (List.ofSeq segs)

let holes (segs : Seg list) : (char * int * bool * bool) list =
    segs |> List.choose (fun s -> match s with Hole (c, w, z, l) -> Some (c, w, z, l) | Text _ -> None)

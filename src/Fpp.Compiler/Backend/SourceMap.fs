module Fpp.Backend.SourceMap

open Fpp.Prelude

// A source map for wasm, in the shape browsers already read: one generated
// "line" (the module), with COLUMNS as absolute byte offsets into the .wasm.
// Chrome resolves a frame's byte offset through this to a file, line and
// column, which is what makes a breakpoint land in a .fpp file rather than in
// disassembled wasm.

let private b64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

/// base64-VLQ, the encoding source maps use for their deltas
let vlq (value : int) : string =
    let mutable v = if value < 0 then ((-value) <<< 1) ||| 1 else value <<< 1
    let mutable out = ""
    let mutable go = true
    while go do
        let mutable digit = v &&& 31
        v <- v >>> 5
        if v > 0 then digit <- digit ||| 32
        out <- out + string b64.[digit]
        go <- v > 0
    out

/// line and column (both 0-based) of a character offset in a text
let lineColOf (text : string) (offset : int) : int * int =
    let cut = if offset < text.Length then offset else text.Length
    let mutable line = 0
    let mutable col = 0
    let mutable i = 0
    while i < cut do
        if text.[i] = '\n' then
            line <- line + 1
            col <- 0
        else col <- col + 1
        i <- i + 1
    line, col

let private jsonString (s : string) : string =
    let mutable out = ""
    for ch in s do
        if ch = '"' then out <- out + "\\\""
        elif ch = '\\' then out <- out + "\\\\"
        elif ch = '\n' then out <- out + "\\n"
        elif ch = '\r' then out <- out + "\\r"
        elif ch = '\t' then out <- out + "\\t"
        elif int ch < 32 then out <- out + "\\u" + (int ch).ToString "x4"
        else out <- out + string ch
    "\"" + out + "\""

/// Build the map. `positions` are (absolute byte offset in the module, source
/// path, source offset); `sources` supplies each file's text, both to turn an
/// offset into a line and column and to EMBED the text, so a debugger shows the
/// real code without needing the files on disk.
let build (file : string) (positions : (int * string * int) list) (sources : (string * string) list) : string =
    let paths = sources |> List.map fst
    let indexOf (p : string) = paths |> List.findIndex (fun x -> x = p)
    let known = positions |> List.filter (fun (_, p, _) -> List.contains p paths)
    // one generated line, so segments are ordered by generated column. One
    // mapping per byte offset: several IR nodes can begin at the same
    // instruction, and a debugger only wants the first.
    let ordered =
        known
        |> List.sortBy (fun (gen, _, _) -> gen)
        |> List.fold
            (fun acc (gen, p, off) ->
                match acc with
                | (g0, _, _) :: _ when g0 = gen -> acc
                | _ -> (gen, p, off) :: acc)
            []
        |> List.rev
    let mutable prevGen = 0
    let mutable prevSrc = 0
    let mutable prevLine = 0
    let mutable prevCol = 0
    let segs = vecNew<string> ()
    for gen, path, off in ordered do
        let text = sources |> List.pick (fun (p, t) -> if p = path then Some t else None)
        let line, col = lineColOf text off
        let si = indexOf path
        vecAdd segs (vlq (gen - prevGen) + vlq (si - prevSrc) + vlq (line - prevLine) + vlq (col - prevCol))
        prevGen <- gen
        prevSrc <- si
        prevLine <- line
        prevCol <- col
    "{\"version\":3,\"file\":" + jsonString file
    + ",\"sources\":[" + String.concat "," (List.map jsonString paths) + "]"
    + ",\"sourcesContent\":[" + String.concat "," (List.map (fun (_, t) -> jsonString t) sources) + "]"
    + ",\"names\":[],\"mappings\":\"" + String.concat "," (vecToList segs) + "\"}"

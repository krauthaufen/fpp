module Fpp.Bootstrap.CompileDrive

// The BINARY twin of compiledrive.fpp: same corpus protocol, but the answer
// is the direct LINEAR .wasm BYTES from EmitProgramWasmLinearWith true rather than .wat text.
// `print` writes the string byte-for-byte (a string IS its bytes here), so
// stage-1's stdout is the module the wasm-hosted compiler emitted — and it
// must equal stage-0's bytes exactly.

open Fpp.Prelude
open Fpp

/// Read by the harness out of this file, so the two stages cannot disagree
/// about what the corpus is. One path per line, comma-separated.
let corpusList = "fpp:corpus"

let ws = Workspace()

let rec loadAll (paths : string list) : int =
    match paths with
    | [] -> 0
    | p :: rest ->
        match hostReadText p with
        | Some t ->
            ws.SetFileText p t
            1 + loadAll rest
        | None ->
            print ("MISSING " + p)
            loadAll rest

/// The corpus is whatever the host serves under these names. The harness
/// writes the same list into the generated host module.
let corpus = [ "corpus.fpp" ]

let loaded = loadAll corpus

let result = ws.EmitProgramWasmReactor ()

let bytes = fst result

let errs = snd result

let report =
    if List.isEmpty errs then
        // CHUNKED: one 11MB module as a single string overflowed the
        // string machinery under self-host; 64K slices print the same bytes
        let mutable i = 0
        while i < bytes.Length do
            let n = min 65536 (bytes.Length - i)
            printRaw (bytesString (Array.sub bytes i n))
            i <- i + n
    else print ("ERRORS " + string (List.length errs) + " " + String.concat " | " errs)

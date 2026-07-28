module Fpp.Bootstrap.CompileDrive

// Driver for PHASE 2: the compiler the compiler emitted, compiling.
//
// Stage-0 (the dotnet-built compiler) emits this driver together with the
// compiler's own 20 sources; the result IS stage-1. Running stage-1 prints
// the .wat it produces for a corpus, and that text must be byte-identical to
// what stage-0 produces for the same corpus. Two hosts, one compiler, one
// answer — anything else is a miscompilation of the compiler by itself.
//
// The corpus arrives through the four host imports, served by a generated
// preload module (tests/bootstrap/fixpoint.fsx). Only the PATHS live here:
// baking the text in would let the two stages compile different bytes and
// still agree, which is exactly the weak gate this phase exists to avoid.

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

let result = ws.EmitProgram ()

let wat = fst result

let errs = snd result

let report =
    if List.isEmpty errs then print wat
    else print ("ERRORS " + string (List.length errs) + " " + String.concat " | " errs)

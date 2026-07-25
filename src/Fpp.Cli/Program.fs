module Fpp.Cli.Program

open Fpp

// `fpp check <files>` — batch diagnostics. Deliberately a second thin client
// of the same Workspace the LSP server uses.

let private check (files : string list) : int =
    let ws = Workspace()
    let mutable errors = 0
    for f in files do
        let text = System.IO.File.ReadAllText f
        ws.SetFileText f text
        for d in ws.Diagnostics f do
            errors <- errors + 1
            printfn "%s:%d:%d: error: %s" d.Path (d.Line + 1) (d.Col + 1) d.Message
    if errors = 0 then 0 else 1

[<EntryPoint>]
let main argv =
    match List.ofArray argv with
    | "check" :: files when not (List.isEmpty files) -> check files
    | _ ->
        eprintfn "usage: fpp check <file>..."
        2

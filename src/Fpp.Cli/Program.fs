module Fpp.Cli.Program

open Fpp

// `fpp check <files>` — batch diagnostics. Deliberately a second thin client
// of the same Workspace the LSP server uses.

let private check (files : string list) : int =
    let ws = Workspace()
    // argument order is the compile order — exports flow forward
    for f in files do
        ws.SetFileText f (System.IO.File.ReadAllText f)
    let mutable errors = 0
    for f in files do
        for d in ws.Diagnostics f do
            errors <- errors + 1
            printfn "%s:%d:%d: error: %s" d.Path (d.Line + 1) (d.Col + 1) d.Message
    if errors = 0 then 0 else 1

let private build (out : string) (files : string list) : int =
    let ws = Workspace()
    for f in files do
        ws.SetFileText f (System.IO.File.ReadAllText f)
    let wat, errors = ws.EmitProgram ()
    if not (List.isEmpty errors) then
        for e in errors do eprintfn "error: %s" e
        1
    else
        System.IO.File.WriteAllText(out, wat)
        0

[<EntryPoint>]
let main argv =
    match List.ofArray argv with
    | "check" :: files when not (List.isEmpty files) -> check files
    | "build" :: "-o" :: out :: files when not (List.isEmpty files) -> build out files
    | _ ->
        eprintfn "usage: fpp check <file>... | fpp build -o out.wat <file>..."
        2

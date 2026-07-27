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

let private buildLib (out : string) (files : string list) : int =
    let ws = Workspace()
    for f in files do
        ws.SetFileText f (System.IO.File.ReadAllText f)
    let lib, errors = ws.BuildLibrary ()
    if not (List.isEmpty errors) then
        for e in errors do eprintfn "error: %s" e
        1
    else
        System.IO.File.WriteAllText(out, lib)
        0

let private build (out : string) (files : string list) : int =
    let ws = Workspace()
    let libs = files |> List.filter (fun f -> f.EndsWith ".fppir")
    let srcs = files |> List.filter (fun f -> not (f.EndsWith ".fppir"))
    for l in libs do
        ws.AddLibrary l (System.IO.File.ReadAllText l)
    for f in srcs do
        ws.SetFileText f (System.IO.File.ReadAllText f)
    let wat, errors = ws.EmitProgram ()
    if not (List.isEmpty errors) then
        for e in errors do eprintfn "error: %s" e
        1
    else
        System.IO.File.WriteAllText(out, wat)
        0

/// A project names its sources in compile order and its output, so `check`
/// and `build` take one argument instead of a hand-ordered file list.
let private withProject (proj : string) (f : string list -> string list -> string -> int) : int =
    let r = Project.read proj
    if not (List.isEmpty r.Errors) then
        for line, msg in r.Errors do eprintfn "%s:%d: error: %s" proj line msg
        1
    else
        let dir = System.IO.Path.GetDirectoryName r.Loaded.Path
        f r.Loaded.Libs r.Loaded.Sources (System.IO.Path.Combine (dir, r.Loaded.Out))

let private isProject (f : string) = f.EndsWith Project.extension

[<EntryPoint>]
let main argv =
    match List.ofArray argv with
    | [ "check"; proj ] when isProject proj ->
        withProject proj (fun libs srcs _ -> check (libs @ srcs))
    | [ "build"; proj ] when isProject proj ->
        withProject proj (fun libs srcs out -> build out (libs @ srcs))
    | [ "build"; proj; "-o"; out ] when isProject proj ->
        withProject proj (fun libs srcs _ -> build out (libs @ srcs))
    | "check" :: files when not (List.isEmpty files) -> check files
    | "build" :: "-o" :: out :: files when not (List.isEmpty files) -> build out files
    | "lib" :: "-o" :: out :: files when not (List.isEmpty files) -> buildLib out files
    | _ ->
        eprintfn "usage:"
        eprintfn "  fpp check <project.fppproj> | fpp check <file>..."
        eprintfn "  fpp build <project.fppproj> [-o out.wat] | fpp build -o out.wat <file>..."
        eprintfn "  fpp lib -o out.fppir <file>..."
        2

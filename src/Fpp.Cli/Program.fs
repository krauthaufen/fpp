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
/// Returns None once it has reported a bad manifest.
let private openProject (proj : string) : (string list * string) option =
    let r = Project.read proj
    if not (List.isEmpty r.Errors) then
        for line, msg in r.Errors do eprintfn "%s:%d: error: %s" proj line msg
        None
    else
        let dir = System.IO.Path.GetDirectoryName r.Loaded.Path
        let out = System.IO.Path.Combine (dir, r.Loaded.Out)
        Some (r.Loaded.Libs @ r.Loaded.Sources, out)

let private isProject (f : string) = f.EndsWith Project.extension

[<EntryPoint>]
let main argv =
    match List.ofArray argv with
    | [ "check"; proj ] when isProject proj ->
        (match openProject proj with
         | Some (files, _) -> check files
         | None -> 1)
    | [ "build"; proj ] when isProject proj ->
        (match openProject proj with
         | Some (files, out) -> build out files
         | None -> 1)
    | [ "build"; proj; "-o"; out ] when isProject proj ->
        (match openProject proj with
         | Some (files, _) -> build out files
         | None -> 1)
    | "check" :: files when not (List.isEmpty files) -> check files
    | "build" :: "-o" :: out :: files when not (List.isEmpty files) -> build out files
    | "lib" :: "-o" :: out :: files when not (List.isEmpty files) -> buildLib out files
    | _ ->
        eprintfn "usage:"
        eprintfn "  fpp check <project.fppproj> | fpp check <file>..."
        eprintfn "  fpp build <project.fppproj> [-o out.wat] | fpp build -o out.wat <file>..."
        eprintfn "  fpp lib -o out.fppir <file>..."
        2

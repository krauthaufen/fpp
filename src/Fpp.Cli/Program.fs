module Fpp.Cli.Program

open Fpp

/// Source is BYTES: every offset the compiler records is a byte offset, and
/// decoding UTF-8 into .NET chars renumbers everything after the first
/// non-ASCII character. Same reader the compiler's own host services use.
let private readSource (path : string) : string =
    System.Text.Encoding.Latin1.GetString (System.IO.File.ReadAllBytes path)

// `fpp check <files>` — batch diagnostics. Deliberately a second thin client
// of the same Workspace the LSP server uses.

let private check (strict : bool) (files : string list) : int =
    let ws = Workspace()
    // argument order is the compile order — exports flow forward
    for f in files do
        ws.SetFileText f (readSource f)
    let mutable errors = 0
    for f in files do
        for d in ws.Diagnostics f do
            errors <- errors + 1
            printfn "%s:%d:%d: error: %s" d.Path (d.Line + 1) (d.Col + 1) d.Message
    if errors > 0 then 1
    elif not strict then 0
    else
        // --strict: also emit (to memory) and refuse stubs — a function
        // the backend cannot compile traps if reached, and a clean check
        // that hands over a trapping binary was this project's most
        // repeated bug shape
        let _bytes, eerrs = ws.EmitProgramWasm ()
        for e in eerrs do eprintfn "error: %s" e
        let stubs = ws.EmitWarnings |> List.filter (fun w -> w.StartsWith "stubbed ")
        for st in stubs do eprintfn "error (strict): %s" st
        if List.isEmpty eerrs && List.isEmpty stubs then 0 else 1

let private picks (files : string list) : int =
    // every instance selection over concrete arguments, one line each —
    // input for tests/tooling/verify/check-picks.py, which re-derives the
    // winner independently and diffs
    let ws = Workspace()
    ws.RecordPicks ()
    for f in files do
        ws.SetFileText f (readSource f)
    let mutable errors = 0
    for f in files do
        for d in ws.Diagnostics f do
            errors <- errors + 1
            eprintfn "%s:%d:%d: error: %s" d.Path (d.Line + 1) (d.Col + 1) d.Message
    for line in ws.InstancePicks do
        printfn "%s" line
    if errors = 0 then 0 else 1

let private buildLib (out : string) (files : string list) : int =
    let ws = Workspace()
    for f in files do
        ws.SetFileText f (readSource f)
    let lib, errors = ws.BuildLibrary ()
    if not (List.isEmpty errors) then
        for e in errors do eprintfn "error: %s" e
        1
    else
        System.IO.File.WriteAllText(out, lib)
        0

let private build (strict : bool) (out : string) (files : string list) : int =
    let ws = Workspace()
    let libs = files |> List.filter (fun f -> f.EndsWith ".fppir")
    let srcs = files |> List.filter (fun f -> not (f.EndsWith ".fppir"))
    for l in libs do
        ws.AddLibrary l (readSource l)
    for f in srcs do
        ws.SetFileText f (readSource f)
    // --strict: a stub is a function that TRAPS if reached. Warning and
    // handing over the binary anyway is right for the porting workflow
    // (unreached surface stubs are routine there) and wrong for a program
    // someone intends to ship — this flag draws that line.
    let failOnStubs (bytes : byte[]) : int =
        let stubs = ws.EmitWarnings |> List.filter (fun w -> w.StartsWith "stubbed ")
        if strict && not (List.isEmpty stubs) then
            for s in stubs do eprintfn "error (strict): %s" s
            eprintfn "error (strict): %d function(s) would trap if reached" (List.length stubs)
            1
        else
            System.IO.File.WriteAllBytes(out, bytes)
            0
    // an `-o something.c` selects the C backend (fpprt runtime); anything
    // else is the wasm-GC module
    if out.EndsWith ".c" then
        let text, errors = ws.EmitProgramC ()
        if not (List.isEmpty errors) then
            for e in errors do eprintfn "error: %s" e
            1
        else
            System.IO.File.WriteAllText(out, text)
            0
    else
        let bytes, errors = ws.EmitProgramWasm ()
        if not (List.isEmpty errors) then
            for e in errors do eprintfn "error: %s" e
            1
        else failOnStubs bytes

// `fpp exe` — a platform executable. The module is compiled to machine code at
// BUILD time and linked into a launcher that embeds wasmtime, so the result
// runs like any other program: no runtime to install, and nothing to compile
// when it starts.

/// Where the wasmtime C API lives. It is a separate download from the CLI, so
/// the path is configuration rather than a guess.
let private capiRoot () : string option =
    match System.Environment.GetEnvironmentVariable "FPP_WASMTIME_CAPI" with
    | null | "" ->
        let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
        let guess = System.IO.Path.Combine (home, ".wasmtime", "c-api")
        if System.IO.Directory.Exists (System.IO.Path.Combine (guess, "include")) then Some guess else None
    | p -> Some p

let private run (exe : string) (args : string list) : int * string =
    let psi = System.Diagnostics.ProcessStartInfo (exe)
    for a in args do psi.ArgumentList.Add a
    psi.RedirectStandardError <- true
    psi.RedirectStandardOutput <- true
    use p = System.Diagnostics.Process.Start psi
    let err = p.StandardError.ReadToEnd ()
    let out = p.StandardOutput.ReadToEnd ()
    p.WaitForExit ()
    p.ExitCode, (out + err)

/// the module's bytes as a C array the launcher links against
let private moduleData (bytes : byte[]) : string =
    let sb = System.Text.StringBuilder ()
    sb.Append("const unsigned char FPP_MODULE[] = {\n") |> ignore
    bytes
    |> Array.iteri (fun i b ->
        sb.Append(string (int b)).Append(',') |> ignore
        if i % 20 = 19 then sb.Append('\n') |> ignore)
    sb.Append("};\nconst unsigned int FPP_MODULE_LEN = ") |> ignore
    sb.Append(bytes.Length).Append(";\n") |> ignore
    sb.ToString ()

let private buildExe (out : string) (files : string list) : int =
    match capiRoot () with
    | None ->
        eprintfn "error: the wasmtime C API is needed to link an executable."
        eprintfn "  download the `c-api` archive for your platform from"
        eprintfn "  https://github.com/bytecodealliance/wasmtime/releases and either"
        eprintfn "  unpack it to ~/.wasmtime/c-api or set FPP_WASMTIME_CAPI to it."
        1
    | Some capi ->
    let here = System.IO.Path.GetDirectoryName (System.Reflection.Assembly.GetExecutingAssembly().Location)
    let native = System.IO.Path.Combine (here, "native")
    let launcher = System.IO.Path.Combine (native, "launcher.c")
    let aot = System.IO.Path.Combine (native, "aot.c")
    if not (System.IO.File.Exists launcher) then
        eprintfn "error: launcher sources are missing from %s" native
        1
    else
    let ws = Workspace()
    let libs = files |> List.filter (fun f -> f.EndsWith ".fppir")
    let srcs = files |> List.filter (fun f -> not (f.EndsWith ".fppir"))
    for l in libs do ws.AddLibrary l (readSource l)
    for f in srcs do ws.SetFileText f (readSource f)
    let bytes, errors = ws.EmitProgramWasm ()
    if not (List.isEmpty errors) then
        for e in errors do eprintfn "error: %s" e
        1
    else
    let tmp = System.IO.Path.Combine (System.IO.Path.GetTempPath (), "fpp-exe-" + string (System.Diagnostics.Process.GetCurrentProcess().Id))
    System.IO.Directory.CreateDirectory tmp |> ignore
    let wasmPath = System.IO.Path.Combine (tmp, "module.wasm")
    let cwasmPath = System.IO.Path.Combine (tmp, "module.cwasm")
    let dataPath = System.IO.Path.Combine (tmp, "module_data.c")
    let aotExe = System.IO.Path.Combine (tmp, "fppaot")
    System.IO.File.WriteAllBytes (wasmPath, bytes)
    let inc = "-I" + System.IO.Path.Combine (capi, "include")
    let lib = System.IO.Path.Combine (capi, "lib", "libwasmtime.a")
    // 1. a helper that compiles the module with the SAME engine settings the
    //    launcher uses — a precompiled module only loads into an engine
    //    configured exactly like the one that produced it
    let rc1, log1 = run "gcc" [ "-O2"; "-o"; aotExe; aot; inc; lib; "-lpthread"; "-ldl"; "-lm" ]
    if rc1 <> 0 then eprintfn "error: building the precompiler failed:\n%s" log1; 1
    else
    let rc2, log2 = run aotExe [ wasmPath; cwasmPath ]
    if rc2 <> 0 then eprintfn "error: precompiling failed:\n%s" log2; 1
    else
    System.IO.File.WriteAllText (dataPath, moduleData (System.IO.File.ReadAllBytes cwasmPath))
    let rc3, log3 =
        run "gcc" [ "-O2"; "-DFPP_PRECOMPILED"; "-o"; out; launcher; dataPath; inc; lib; "-lpthread"; "-ldl"; "-lm" ]
    if rc3 <> 0 then eprintfn "error: linking failed:\n%s" log3; 1
    else
        try System.IO.Directory.Delete (tmp, true) with _ -> ()
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
    let argl0 = List.ofArray argv
    let strict = argl0 |> List.exists (fun a -> a = "--strict")
    match argl0 |> List.filter (fun a -> a <> "--strict") with
    | [ "check"; proj ] when isProject proj ->
        (match openProject proj with
         | Some (files, _) -> check strict files
         | None -> 1)
    | [ "build"; proj ] when isProject proj ->
        (match openProject proj with
         | Some (files, out) -> build strict out files
         | None -> 1)
    | [ "build"; proj; "-o"; out ] when isProject proj ->
        (match openProject proj with
         | Some (files, _) -> build strict out files
         | None -> 1)
    | "check" :: files when not (List.isEmpty files) -> check strict files
    | "picks" :: files when not (List.isEmpty files) -> picks files
    | "build" :: "-o" :: out :: files when not (List.isEmpty files) -> build strict out files
    | "lib" :: "-o" :: out :: files when not (List.isEmpty files) -> buildLib out files
    | [ "exe"; proj; "-o"; out ] when isProject proj ->
        (match openProject proj with
         | Some (files, _) -> buildExe out files
         | None -> 1)
    | "exe" :: "-o" :: out :: files when not (List.isEmpty files) -> buildExe out files
    | _ ->
        eprintfn "usage:"
        eprintfn "  fpp check [--strict] <project.fppproj> | fpp check [--strict] <file>..."
        eprintfn "  fpp build [--strict] <project.fppproj> [-o out.wasm] | fpp build [--strict] -o out.wasm <file>..."
        eprintfn "      --strict: fail when any function had to be stubbed (would trap if reached)"
        eprintfn "  fpp lib -o out.fppir <file>..."
        eprintfn "  fpp exe -o app <file>... | fpp exe <project.fppproj> -o app"
        2

module Fpp.Cli.Program

open Fpp

/// Source is BYTES: every offset the compiler records is a byte offset, and
/// decoding UTF-8 into .NET chars renumbers everything after the first
/// non-ASCII character. Same reader the compiler's own host services use.
let private readSource (path : string) : string =
    System.Text.Encoding.Latin1.GetString (System.IO.File.ReadAllBytes path)

// `fpp check <files>` — batch diagnostics. Deliberately a second thin client
// of the same Workspace the LSP server uses.

/// The stubs that could actually TRAP. An unstamped template (`EUnknown
/// $class:...`) cannot: every call of a generic class member goes through
/// a stamped copy, and the template survives only as an artifact — so a
/// generic member the program never USES must not fail a strict build.
let private strictStubs (ws : Workspace) : string list =
    ws.EmitWarnings
    |> List.filter (fun w -> w.StartsWith "stubbed " && not (w.Contains "EUnknown $class:"))

let private check (strict : bool) (defines : string list) (files : string list) : int =
    let ws = Workspace()
    // `check` sees the ORACLE's view of conditional code
    ws.Defines <- "WASM" :: defines
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
        let stubs = strictStubs ws
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

let mutable private linearBackend = false
let mutable private lowirBackend = false

let private build (strict : bool) (defines : string list) (out : string) (files : string list) : int =
    let ws = Workspace()
    // the target IS the configuration: `#if WASM` code exists only in wasm
    // builds, `#if NATIVE` only in C builds — nothing compiles to a trap
    ws.Defines <- (if out.EndsWith ".c" then "NATIVE" else "WASM") :: defines
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
        let stubs = strictStubs ws
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
    elif linearBackend then
        // --linear: the direct wasm-LINEAR module, no C compiler in the path.
        // --lowir additionally routes supported functions through the shared
        // LowIR (Core/LowIR.fs) rather than the hand-lowering.
        let bytes, errors = ws.EmitProgramWasmLinearWith lowirBackend
        if not (List.isEmpty errors) then
            for e in errors |> List.distinct do eprintfn "error: %s" e
            1
        else
            System.IO.File.WriteAllBytes(out, bytes)
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
    ws.Defines <- [ "WASM" ]
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
// ---- packages -------------------------------------------------------------
// A registry is a directory or a static http(s) base:
//   <base>/<name>/versions              one semver per line
//   <base>/<name>/<name>-<v>.fpkg       the archive (zip: fpkg manifest + fppirs)
// The cache is ~/.fpp/pkg/<name>/<version>/, the archive extracted.
// `fpp restore` solves against the registries and writes fpp.lock next to
// the project; build/check consume the LOCK and the CACHE only — the
// network is touched by restore alone.

let private cacheRoot () : string =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    System.IO.Path.Combine (home, ".fpp", "pkg")

let private cacheDir (name : string) (v : string) : string =
    System.IO.Path.Combine (cacheRoot (), name, v)

let private isUrl (s : string) = s.StartsWith "http://" || s.StartsWith "https://"

let private http = lazy (new System.Net.Http.HttpClient ())

/// registry read: None on a miss (a package absent from one registry may
/// live in the next)
let private regFetch (reg : string) (rel : string) : byte[] option =
    if isUrl reg then
        try
            let url = reg.TrimEnd '/' + "/" + rel
            let resp = http.Value.GetAsync(url).Result
            if resp.IsSuccessStatusCode then Some (resp.Content.ReadAsByteArrayAsync().Result)
            else None
        with _ -> None
    else
        let p = System.IO.Path.Combine (reg, rel.Replace ("/", string System.IO.Path.DirectorySeparatorChar))
        if System.IO.File.Exists p then Some (System.IO.File.ReadAllBytes p) else None

let private fpkgFile (name : string) (v : string) = name + "-" + v + ".fpkg"

/// Pull one package version into the cache (idempotent). Returns its
/// manifest, or the error.
let private fetchToCache (regs : string list) (name : string) (v : string) : Result<Pkg.PkgManifest, string> =
    let dir = cacheDir name v
    let manifestPath = System.IO.Path.Combine (dir, "fpkg")
    let fetched =
        if System.IO.File.Exists manifestPath then Ok ()
        else
            match regs |> List.tryPick (fun r -> regFetch r (name + "/" + fpkgFile name v)) with
            | None -> Error ("package " + name + " " + v + " is in no registry")
            | Some bytes ->
                let tmp = System.IO.Path.GetTempFileName ()
                System.IO.File.WriteAllBytes (tmp, bytes)
                System.IO.Directory.CreateDirectory dir |> ignore
                System.IO.Compression.ZipFile.ExtractToDirectory (tmp, dir, true)
                System.IO.File.Delete tmp
                Ok ()
    match fetched with
    | Error e -> Error e
    | Ok () ->
        if System.IO.File.Exists manifestPath then
            Pkg.parseManifest (System.IO.File.ReadAllText manifestPath)
        else Error ("package " + name + " " + v + ": archive carries no fpkg manifest")

/// Build the solver's universe by walking out from the roots: versions
/// list per name, then each candidate version's own requires (read from
/// its cached archive — fetching it is how its edges become known).
let private buildUniverse (regs : string list) (roots : (string * Pkg.Range) list) : Result<Pkg.Universe, string> =
    let u = Pkg.newUniverse ()
    let seen = System.Collections.Generic.HashSet<string> ()
    let queue = System.Collections.Generic.Queue<string> ()
    for n, _ in roots do
        if seen.Add n then queue.Enqueue n
    let mutable err = ""
    while err = "" && queue.Count > 0 do
        let name = queue.Dequeue ()
        match regs |> List.tryPick (fun r -> regFetch r (name + "/versions")) with
        | None -> err <- "no registry knows package " + name
        | Some bytes ->
            let text = System.Text.Encoding.UTF8.GetString bytes
            let versions =
                text.Replace("\r\n", "\n").Split '\n'
                |> Array.toList
                |> List.map (fun l -> l.Trim ())
                |> List.filter (fun l -> l <> "" && not (l.StartsWith "#"))
                |> List.choose Pkg.parseVersion
            Fpp.Prelude.dictSet u.Versions name versions
            for v in versions do
                if err = "" then
                    match fetchToCache regs name (Pkg.versionString v) with
                    | Error e -> err <- e
                    | Ok m ->
                        Fpp.Prelude.dictSet u.Requires (name, Pkg.versionString v) m.Requires
                        for dn, _ in m.Requires do
                            if seen.Add dn then queue.Enqueue dn
    if err = "" then Ok u else Error err

let private lockPath (projPath : string) : string =
    System.IO.Path.Combine (System.IO.Path.GetDirectoryName projPath, "fpp.lock")

let private readLock (path : string) : (string * string) list =
    if System.IO.File.Exists path then
        System.IO.File.ReadAllLines path
        |> Array.toList
        |> List.choose (fun l ->
            match l.Trim().Split ' ' |> Array.toList |> List.filter (fun p -> p <> "") with
            | [ "package"; n; v ] -> Some (n, v)
            | _ -> None)
    else []

/// The lock's picks as flavor-correct fppir paths, dependency order.
/// Errors rather than guessing when the lock is missing, stale against
/// the manifest, or names something not cached.
let private lockedLibs (proj : Project.Project) (flavor : string) : Result<string list, string> =
    if List.isEmpty proj.Packages then Ok []
    else
        let lp = lockPath proj.Path
        let locked = readLock lp
        if List.isEmpty locked then Error ("project uses packages but has no lock — run: fpp restore " + proj.Path)
        else
            let ranges = proj.Packages |> List.map (fun (n, r) -> n, (Pkg.parseRange r).Value)
            let stale =
                ranges |> List.tryPick (fun (n, r) ->
                    match locked |> List.tryFind (fun (ln, _) -> ln = n) with
                    | None -> Some (n + " is not in fpp.lock")
                    | Some (_, lv) ->
                        match Pkg.parseVersion lv with
                        | Some v when Pkg.satisfies r v -> None
                        | _ -> Some (n + " " + lv + " no longer satisfies " + r.String))
            match stale with
            | Some s -> Error ("fpp.lock is stale (" + s + ") — run: fpp restore " + proj.Path)
            | None ->
                let mutable err = ""
                let libs =
                    locked |> List.map (fun (n, v) ->
                        let dir = cacheDir n v
                        let mp = System.IO.Path.Combine (dir, "fpkg")
                        if not (System.IO.File.Exists mp) then
                            err <- "package " + n + " " + v + " is not cached — run: fpp restore " + proj.Path
                            ""
                        else
                            match Pkg.parseManifest (System.IO.File.ReadAllText mp) with
                            | Error e -> err <- n + " " + v + ": " + e; ""
                            | Ok m ->
                                match m.Libs |> List.tryFind (fun (f, _) -> f = flavor) with
                                | Some (_, file) -> System.IO.Path.Combine (dir, file)
                                | None ->
                                    err <- "package " + n + " " + v + " has no " + flavor + " flavor"
                                    ""
                    )
                if err <> "" then Error err else Ok libs

let private restore (projPath : string) : int =
    let r = Project.read projPath
    if not (List.isEmpty r.Errors) then
        for line, msg in r.Errors do eprintfn "%s:%d: error: %s" projPath line msg
        1
    elif List.isEmpty r.Loaded.Packages then
        printfn "nothing to restore: project declares no packages"
        0
    elif List.isEmpty r.Loaded.Registries then
        eprintfn "error: project declares packages but no `registry`"
        1
    else
        let roots = r.Loaded.Packages |> List.map (fun (n, rg) -> n, (Pkg.parseRange rg).Value)
        match buildUniverse r.Loaded.Registries roots with
        | Error e -> eprintfn "error: %s" e; 1
        | Ok u ->
            match Pkg.solve u roots with
            | Error e -> eprintfn "error: %s" e; 1
            | Ok sol ->
                let lines =
                    [ "# generated by fpp restore — do not edit" ]
                    @ (sol.Picks |> List.map (fun (n, v) -> "package " + n + " " + Pkg.versionString v))
                System.IO.File.WriteAllText (lockPath projPath, String.concat "\n" lines + "\n")
                for n, v in sol.Picks do printfn "%s %s" n (Pkg.versionString v)
                0

let private pack (projPath : string) (out : string) : int =
    let r = Project.read projPath
    if not (List.isEmpty r.Errors) then
        for line, msg in r.Errors do eprintfn "%s:%d: error: %s" projPath line msg
        1
    elif r.Loaded.Version = "" then
        eprintfn "error: `fpp pack` needs a `version` line in the project"
        1
    else
        let p = r.Loaded
        let tmp = System.IO.Path.Combine (System.IO.Path.GetTempPath (), "fpp-pack-" + string (System.Diagnostics.Process.GetCurrentProcess().Id))
        if System.IO.Directory.Exists tmp then System.IO.Directory.Delete (tmp, true)
        System.IO.Directory.CreateDirectory tmp |> ignore
        let mutable failed = false
        let libLines = Fpp.Prelude.vecNew<string * string> ()
        for flavor, define in [ "wasm", "WASM"; "native", "NATIVE" ] do
            if not failed then
                match lockedLibs p flavor with
                | Error e -> eprintfn "error: %s" e; failed <- true
                | Ok deps ->
                    let ws = Workspace()
                    ws.Defines <- define :: p.Defines
                    for l in deps @ p.Libs do
                        ws.AddLibrary l (readSource l)
                    for f in p.Sources do
                        ws.SetFileText f (readSource f)
                    let lib, errors = ws.BuildLibrary ()
                    if not (List.isEmpty errors) then
                        for e in errors do eprintfn "error (%s): %s" flavor e
                        failed <- true
                    else
                        let file = p.Name + "-" + flavor + ".fppir"
                        System.IO.File.WriteAllText (System.IO.Path.Combine (tmp, file), lib)
                        Fpp.Prelude.vecAdd libLines (flavor, file)
        if failed then 1
        else
            let manifest : Pkg.PkgManifest =
                { Name = p.Name
                  Version = (Pkg.parseVersion p.Version).Value
                  Requires = p.Packages |> List.map (fun (n, rg) -> n, (Pkg.parseRange rg).Value)
                  Libs = Fpp.Prelude.vecToList libLines }
            System.IO.File.WriteAllText (System.IO.Path.Combine (tmp, "fpkg"), Pkg.manifestText manifest)
            if System.IO.File.Exists out then System.IO.File.Delete out
            System.IO.Compression.ZipFile.CreateFromDirectory (tmp, out)
            System.IO.Directory.Delete (tmp, true)
            printfn "packed %s %s -> %s" p.Name p.Version out
            0

/// the manifest out of an archive — name and version live there
let private fpkgManifest (fpkg : string) : Result<Pkg.PkgManifest, string> =
    use z = System.IO.Compression.ZipFile.OpenRead fpkg
    let entry = z.Entries |> Seq.tryFind (fun e -> e.FullName = "fpkg")
    match entry with
    | None -> Error (fpkg + " carries no fpkg manifest")
    | Some e ->
        let rd = new System.IO.StreamReader (e.Open ())
        let text = rd.ReadToEnd ()
        rd.Dispose ()
        Pkg.parseManifest text

let private publish (fpkg : string) (reg : string) : int =
    match fpkgManifest fpkg with
    | Error e -> eprintfn "error: %s" e; 1
    | Ok m ->
            let v = Pkg.versionString m.Version
            if isUrl reg then
                // a writable static host (PUT): the archive, then the
                // refreshed versions file
                let baseUrl = reg.TrimEnd '/' + "/" + m.Name
                let put (rel : string) (bytes : byte[]) : bool =
                    let resp = http.Value.PutAsync(baseUrl + "/" + rel, new System.Net.Http.ByteArrayContent (bytes)).Result
                    resp.IsSuccessStatusCode
                let existing =
                    match regFetch reg (m.Name + "/versions") with
                    | Some b -> System.Text.Encoding.UTF8.GetString b
                    | None -> ""
                let versions =
                    (existing.Replace("\r\n", "\n").Split '\n'
                     |> Array.toList |> List.map (fun l -> l.Trim ()) |> List.filter (fun l -> l <> ""))
                    @ [ v ] |> List.distinct
                if put (fpkgFile m.Name v) (System.IO.File.ReadAllBytes fpkg)
                   && put "versions" (System.Text.Encoding.UTF8.GetBytes (String.concat "\n" versions + "\n")) then
                    printfn "published %s %s -> %s" m.Name v reg
                    0
                else
                    eprintfn "error: the registry refused the upload (PUT %s)" baseUrl
                    1
            else
                let dir = System.IO.Path.Combine (reg, m.Name)
                System.IO.Directory.CreateDirectory dir |> ignore
                System.IO.File.Copy (fpkg, System.IO.Path.Combine (dir, fpkgFile m.Name v), true)
                let vf = System.IO.Path.Combine (dir, "versions")
                let existing = if System.IO.File.Exists vf then System.IO.File.ReadAllLines vf |> Array.toList else []
                let versions = (existing |> List.map (fun l -> l.Trim ()) |> List.filter (fun l -> l <> "")) @ [ v ] |> List.distinct
                System.IO.File.WriteAllLines (vf, Array.ofList versions)
                printfn "published %s %s -> %s" m.Name v reg
                0

let private openProject (proj : string) : (string list * string * string list) option =
    let r = Project.read proj
    if not (List.isEmpty r.Errors) then
        for line, msg in r.Errors do eprintfn "%s:%d: error: %s" proj line msg
        None
    else
        let dir = System.IO.Path.GetDirectoryName r.Loaded.Path
        let out = System.IO.Path.Combine (dir, r.Loaded.Out)
        // package dependencies join ahead of explicit libs, in solved
        // dependency order, at the flavor the OUT selects
        let flavor = if out.EndsWith ".c" then "native" else "wasm"
        match lockedLibs r.Loaded flavor with
        | Error e ->
            eprintfn "error: %s" e
            None
        | Ok pkgLibs ->
            Some (pkgLibs @ r.Loaded.Libs @ r.Loaded.Sources, out, r.Loaded.Defines)

let private isProject (f : string) = f.EndsWith Project.extension

[<EntryPoint>]
let main argv =
    let argl0 = List.ofArray argv
    let strict = argl0 |> List.exists (fun a -> a = "--strict")
    lowirBackend <- argl0 |> List.exists (fun a -> a = "--lowir")
    linearBackend <- (argl0 |> List.exists (fun a -> a = "--linear")) || lowirBackend
    match argl0 |> List.filter (fun a -> a <> "--strict" && a <> "--linear" && a <> "--lowir") with
    | [ "check"; proj ] when isProject proj ->
        (match openProject proj with
         | Some (files, _, defs) -> check strict defs files
         | None -> 1)
    | [ "build"; proj ] when isProject proj ->
        (match openProject proj with
         | Some (files, out, defs) -> build strict defs out files
         | None -> 1)
    | [ "build"; proj; "-o"; out ] when isProject proj ->
        (match openProject proj with
         | Some (files, _, defs) -> build strict defs out files
         | None -> 1)
    | "check" :: files when not (List.isEmpty files) -> check strict [] files
    | "picks" :: files when not (List.isEmpty files) -> picks files
    | "build" :: "-o" :: out :: files when not (List.isEmpty files) -> build strict [] out files
    | "lib" :: "-o" :: out :: files when not (List.isEmpty files) -> buildLib out files
    | [ "pack"; proj; "-o"; out ] when isProject proj -> pack proj out
    | [ "restore"; proj ] when isProject proj -> restore proj
    | [ "publish"; fpkg; reg ] when fpkg.EndsWith ".fpkg" -> publish fpkg reg
    | [ "exe"; proj; "-o"; out ] when isProject proj ->
        (match openProject proj with
         | Some (files, _, _) -> buildExe out files
         | None -> 1)
    | "exe" :: "-o" :: out :: files when not (List.isEmpty files) -> buildExe out files
    | _ ->
        eprintfn "usage:"
        eprintfn "  fpp check [--strict] <project.fppproj> | fpp check [--strict] <file>..."
        eprintfn "  fpp build [--strict] [--linear] <project.fppproj> [-o out.wasm] | fpp build [--strict] -o out.wasm <file>..."
        eprintfn "      --strict: fail when any function had to be stubbed (would trap if reached)"
        eprintfn "  fpp lib -o out.fppir <file>..."
        eprintfn "  fpp pack <project.fppproj> -o out.fpkg      (needs a `version` line)"
        eprintfn "  fpp publish <pkg.fpkg> <registry-dir-or-url>"
        eprintfn "  fpp restore <project.fppproj>               (solves `package` lines, writes fpp.lock)"
        eprintfn "  fpp exe -o app <file>... | fpp exe <project.fppproj> -o app"
        2

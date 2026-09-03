module Fpp.Cli.Web

// The BROWSER story: scaffold a project, serve it while you edit it, and
// emit a directory a static host can take.
//
// Nothing here is a build system. `fpp dev` compiles the one wasm module the
// page loads and serves the directory around it; a browser already knows how
// to do the rest, because ES modules are native. That is why a project with
// no npm dependency needs NO Node and no bundler at all — the "bundle" step
// is a copy. Node enters only when npm packages do, and then only as `npm`
// to install and `esbuild` to flatten them into one file the page can
// import.
//
// F++ reaches JavaScript the way it already did: `extern let f : ...`
// declares the import, and the page supplies it in the `jsx` object. So an
// npm package is consumed from the GLUE, not from F++ directly, and needed
// no compiler change.

open System
open System.IO
open System.Net
open System.Text

let private home () =
    Environment.GetFolderPath Environment.SpecialFolder.UserProfile

/// The JS loader that instantiates a module and wires WASI + the jsx
/// imports. Resolved like the reactor is: beside the binary first, then the
/// dev checkout, so a shipped `fpp` and this repo both work.
let jsRuntimePath () : string option =
    [ Path.Combine (AppContext.BaseDirectory, "fpp-js.mjs")
      Path.Combine (AppContext.BaseDirectory, "stdlib", "fpp-js.mjs")
      home () + "/projects/fpp-lowir/stdlib/fpp-js.mjs" ]
    |> List.tryFind File.Exists

// ---- scaffolding ---------------------------------------------------------

// NOT sprintf: a multi-line triple-quoted format silently collapses to its
// first specifier (F# warns it is a partially-applied function), so the
// generated project file was the name alone. Substitution, not formatting.
let private projTemplate = """name $NAME$
out  web/app.wasm
src  src/Main.fpp
"""
let private projFile (name : string) = projTemplate.Replace ("$NAME$", name)

let private mainFpp = """module Main

// Every JS function the page hands over is declared here and supplied in
// `jsx` on the other side. The types are the contract: this one takes two
// strings and answers an int, because a JS extern always answers something.
//
// [<JsImport>] is what makes it a JAVASCRIPT extern. Without it the import
// is the plain C one (module "env", raw ABI) and the page cannot satisfy it
// — the browser reports "env: module is not an object or function".
[<JsImport>]
extern let setText : string -> string -> int

let greet (who : string) : string =
    "hello, " + who + "!"

let mutable clicks = 0

// [<Export>] is what puts it in the module's exports under its own name. A
// top-level function is NOT exported by default — without this the page gets
// "mod.onClick is not a function", and only after it has already run.
[<Export>]
let onClick () : int =
    clicks <- clicks + 1
    setText "count" (string clicks) |> ignore
    0

setText "greeting" (greet "world") |> ignore
"""

let private indexTemplate = """<!doctype html>
<meta charset="utf-8">
<title>$NAME$</title>
<style>
  body { font-family: ui-sans-serif, system-ui, sans-serif; margin: 3rem auto; max-width: 40rem; }
  button { font: inherit; padding: .4rem .9rem; }
  code { background: #f4f4f5; padding: .1rem .3rem; border-radius: 3px; }
</style>
<h1 id="greeting">…</h1>
<p>Clicked <b id="count">0</b> times.</p>
<button id="go">Click me</button>
<p>Edit <code>src/Main.fpp</code> and save — the page reloads itself.</p>
<script type="module" src="./main.js"></script>
"""
let private indexHtml (name : string) = indexTemplate.Replace ("$NAME$", name)

let private mainJs = """// The GLUE. It owns the DOM and hands F++ the few functions it declared
// `extern`; F++ owns the logic. An npm package imported here is available to
// F++ through exactly this object.
import { instantiateLinear } from "./fpp-js.mjs";

const mod = await instantiateLinear("./app.wasm", {
  sink: s => console.log(s),
  jsx: {
    setText: (id, text) => {
      const el = document.getElementById(id);
      if (el) el.textContent = text;
      return 0;
    },
  },
});

// Top-level effects in Main.fpp run here.
mod._start();

document.getElementById("go").addEventListener("click", () => mod.onClick());
"""

let private gitignore = """web/app.wasm
dist/
node_modules/
"""

/// `fpp new <name>`: a project that builds to the browser and runs.
let scaffold (name : string) : int =
    if Directory.Exists name then
        eprintfn "error: '%s' already exists" name
        1
    else
        let write (rel : string) (text : string) =
            let p = Path.Combine (name, rel)
            Directory.CreateDirectory (Path.GetDirectoryName p) |> ignore
            File.WriteAllText (p, text)
        Directory.CreateDirectory name |> ignore
        write "app.fppproj" (projFile name)
        write "src/Main.fpp" mainFpp
        write "web/index.html" (indexHtml name)
        write "web/main.js" mainJs
        write ".gitignore" gitignore
        printfn "created %s" name
        printfn "  cd %s && fpp dev" name
        0

// ---- building ------------------------------------------------------------

/// Where a project's wasm goes, from its `out` line. The scaffold points it
/// into `web/` so the page can fetch it beside itself.
let private outputOf (projPath : string) : string =
    let dir = Path.GetDirectoryName (Path.GetFullPath projPath)
    let line =
        File.ReadAllLines projPath
        |> Array.tryFind (fun l -> l.TrimStart().StartsWith "out ")
    match line with
    | Some l -> Path.Combine (dir, (l.Trim().Substring 4).Trim())
    | None -> Path.Combine (dir, "web", "app.wasm")

let private findProject (dir : string) : string option =
    Directory.GetFiles (dir, "*.fppproj") |> Array.sortBy id |> Array.tryHead

/// Copy the JS loader in beside the page. It is one file and it belongs to
/// the compiler, so it is COPIED rather than imported from somewhere the
/// page cannot reach — a static host has no idea where `fpp` lives.
let private placeRuntime (webDir : string) : bool =
    match jsRuntimePath () with
    | Some src ->
        Directory.CreateDirectory webDir |> ignore
        File.Copy (src, Path.Combine (webDir, "fpp-js.mjs"), true)
        true
    | None ->
        eprintfn "error: fpp-js.mjs not found beside the compiler"
        false

// ---- npm -----------------------------------------------------------------

let private hasNodeModules (dir : string) = Directory.Exists (Path.Combine (dir, "node_modules"))

let private run (exe : string) (args : string list) (cwd : string) : int =
    let psi = Diagnostics.ProcessStartInfo (exe)
    for a in args do psi.ArgumentList.Add a
    psi.WorkingDirectory <- cwd
    psi.UseShellExecute <- false
    try
        use p = Diagnostics.Process.Start psi
        p.WaitForExit ()
        p.ExitCode
    with _ ->
        eprintfn "error: '%s' not found — install Node.js to use npm packages" exe
        127

/// `fpp npm <args...>`: npm, in the project directory. Thin on purpose —
/// npm is a better npm than anything wrapped around it, and the only thing
/// this adds is the working directory and a readable failure when Node is
/// not installed.
let npm (dir : string) (args : string list) : int =
    let code = run "npm" args dir
    if code = 0 && not (List.isEmpty args) then
        printfn "note: import it in web/main.js and expose what F++ needs through `jsx`"
    code

/// When the project has npm packages, `main.js` imports them and the browser
/// cannot resolve a bare specifier — so it is flattened with esbuild. With
/// no node_modules the file is already loadable as it stands, and is copied.
let private emitMainJs (projDir : string) (webDir : string) (outDir : string) : bool =
    let src = Path.Combine (webDir, "main.js")
    let dst = Path.Combine (outDir, "main.js")
    if not (File.Exists src) then true
    elif not (hasNodeModules projDir) then
        File.Copy (src, dst, true)
        true
    else
        let code =
            run "npx" [ "--yes"; "esbuild"; src; "--bundle"; "--format=esm"
                        "--external:./fpp-js.mjs"; "--outfile=" + dst ] projDir
        if code <> 0 then
            eprintfn "error: esbuild failed — it bundles the npm imports in web/main.js"
        code = 0

// ---- dev server ----------------------------------------------------------

let private mime (path : string) =
    match Path.GetExtension(path).ToLowerInvariant () with
    | ".html" -> "text/html; charset=utf-8"
    | ".js" | ".mjs" -> "text/javascript; charset=utf-8"
    | ".wasm" -> "application/wasm"
    | ".css" -> "text/css; charset=utf-8"
    | ".json" -> "application/json"
    | ".svg" -> "image/svg+xml"
    | ".png" -> "image/png"
    | _ -> "application/octet-stream"

/// Injected into every served HTML page: one EventSource, and a reload when
/// the build says so. Not hot module replacement — a wasm module has no
/// meaningful partial update, and a reload is honest about that.
let private reloadScript = "\
<script>
new EventSource(\"/__fpp/reload\").onmessage = e => { if (e.data === \"reload\") location.reload(); };
</script>
"

/// The dev server. One build, one listener, one watcher; a change rebuilds
/// and every open page reloads.
///
/// `buildOnce` is passed in rather than called here so this file never
/// depends on the compiler driver — the CLI owns how a project is built,
/// and this owns when.
let dev (projDir : string) (port : int) (buildOnce : unit -> bool) : int =
    let webDir = Path.Combine (projDir, "web")
    if not (placeRuntime webDir) then 1 else

    let mutable ok = buildOnce ()
    if not ok then eprintfn "(serving anyway — fix the error and save)"

    // every connected page, so a rebuild can wake all of them
    let clients = Collections.Concurrent.ConcurrentDictionary<int, StreamWriter> ()
    let mutable nextId = 0

    let listener = new HttpListener ()
    let prefix = sprintf "http://localhost:%d/" port
    listener.Prefixes.Add prefix
    try listener.Start ()
    with _ ->
        eprintfn "error: cannot listen on %s — is the port taken?" prefix
        exit 1

    let notifyAll () =
        for kv in clients do
            try
                kv.Value.Write "data: reload\n\n"
                kv.Value.Flush ()
            with _ -> clients.TryRemove kv.Key |> ignore

    // debounce: an editor writes a file more than once per save, and a
    // rebuild per write would queue builds behind each other
    let mutable pending = false
    let gate = obj ()
    let rebuild () =
        lock gate (fun () ->
            if not pending then
                pending <- true
                async {
                    do! Async.Sleep 120
                    lock gate (fun () -> pending <- false)
                    printfn "rebuilding…"
                    ok <- buildOnce ()
                    if ok then printfn "ok" else eprintfn "build failed"
                    notifyAll ()
                } |> Async.Start)

    let watchers =
        [ for sub in [ "src"; "web" ] do
            let d = Path.Combine (projDir, sub)
            if Directory.Exists d then
                let w = new FileSystemWatcher (d)
                w.IncludeSubdirectories <- true
                w.NotifyFilter <- NotifyFilters.LastWrite ||| NotifyFilters.FileName
                // the OUTPUT lives under web/: rebuilding on it would loop
                w.Changed.Add (fun e -> if not (e.FullPath.EndsWith ".wasm") then rebuild ())
                w.Created.Add (fun e -> if not (e.FullPath.EndsWith ".wasm") then rebuild ())
                w.EnableRaisingEvents <- true
                yield w ]

    printfn "serving %s on %s" webDir prefix
    printfn "watching src/ and web/ — Ctrl-C to stop"

    let serve (ctx : HttpListenerContext) =
        let path = Uri.UnescapeDataString (ctx.Request.Url.AbsolutePath)
        if path = "/__fpp/reload" then
            // server-sent events: held open for the life of the page
            ctx.Response.ContentType <- "text/event-stream"
            ctx.Response.Headers.Add ("Cache-Control", "no-cache")
            ctx.Response.SendChunked <- true
            let w = new StreamWriter (ctx.Response.OutputStream)
            let id = Threading.Interlocked.Increment (&nextId)
            w.Write ": hello\n\n"
            w.Flush ()
            clients.[id] <- w
        else
            let rel = if path = "/" then "index.html" else path.TrimStart '/'
            let full = Path.GetFullPath (Path.Combine (webDir, rel))
            // never serve outside the directory, whatever the path says
            if not (full.StartsWith (Path.GetFullPath webDir)) || not (File.Exists full) then
                ctx.Response.StatusCode <- 404
                ctx.Response.Close ()
            else
                ctx.Response.ContentType <- mime full
                ctx.Response.Headers.Add ("Cache-Control", "no-store")
                let bytes =
                    if full.EndsWith ".html" then
                        Encoding.UTF8.GetBytes (File.ReadAllText full + reloadScript)
                    else File.ReadAllBytes full
                ctx.Response.ContentLength64 <- int64 bytes.Length
                ctx.Response.OutputStream.Write (bytes, 0, bytes.Length)
                ctx.Response.Close ()

    while true do
        let ctx = listener.GetContext ()
        // each request on its own thread: the SSE ones never return
        Threading.ThreadPool.QueueUserWorkItem (fun _ ->
            try serve ctx with _ -> ()) |> ignore
    0

/// `fpp bundle`: the directory a static host wants. The wasm, the page, the
/// loader, and `main.js` — flattened through esbuild only if npm packages
/// are in play.
let bundle (projDir : string) (outDir : string) (buildOnce : unit -> bool) : int =
    let webDir = Path.Combine (projDir, "web")
    if not (placeRuntime webDir) then 1
    elif not (buildOnce ()) then 1
    else
        Directory.CreateDirectory outDir |> ignore
        for f in Directory.GetFiles webDir do
            let name = Path.GetFileName f
            if name <> "main.js" then File.Copy (f, Path.Combine (outDir, name), true)
        if not (emitMainJs projDir webDir outDir) then 1
        else
            let total =
                Directory.GetFiles (outDir, "*", SearchOption.AllDirectories)
                |> Array.sumBy (fun f -> (FileInfo f).Length)
            printfn "bundled %s (%d files, %d KB)" outDir
                    (Directory.GetFiles (outDir, "*", SearchOption.AllDirectories)).Length
                    (total / 1024L |> int)
            printfn "  serve it with any static host"
            0

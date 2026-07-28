// PHASE 2: the stage-0/stage-1 fixpoint.
//
//   dotnet fsi tests/bootstrap/fixpoint.fsx              # the default corpus
//   dotnet fsi tests/bootstrap/fixpoint.fsx path.fpp     # one file instead
//
// Stage-0 is the dotnet-built compiler. It emits TWO things:
//
//   * the expected answer — stage-0's own .wat for the corpus;
//   * stage-1 — the compiler's 20 sources plus compiledrive.fpp, as wasm.
//
// Stage-1 then runs under wasmtime and compiles the same corpus, reading it
// through the four host imports served by a generated preload module. The two
// .wat texts must be byte-identical. A difference is a miscompilation of the
// compiler by itself, and the script bisects it to the first differing byte
// and names the emitted function it falls inside.
//
// The corpus is served, never baked in: if the driver carried the text, the
// two stages could compile DIFFERENT bytes and still agree, which is the weak
// gate this phase exists to close.

#r "../../src/Fpp.Compiler/bin/Release/net10.0/Fpp.Compiler.dll"

open Fpp

let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
let scratch = System.IO.Path.Combine (System.IO.Path.GetTempPath (), "fpp-fixpoint")
System.IO.Directory.CreateDirectory scratch |> ignore

let wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

// ---- the compiler's own sources, with the seam substituted ---------------

let compilerFiles =
    let proj = root + "/src/Fpp.Compiler/Fpp.Compiler.fsproj"
    System.IO.File.ReadAllLines proj
    |> Array.choose (fun line ->
        let m = System.Text.RegularExpressions.Regex.Match(line, "Compile Include=\"(.+?)\"")
        if m.Success then Some (root + "/src/Fpp.Compiler/" + m.Groups.[1].Value.Replace('\\', '/'))
        else None)
    |> Array.toList
    |> List.map (fun f -> if f.EndsWith "/Prelude.fs" then root + "/stdlib/bootstrap.fpp" else f)

// ---- the corpus ----------------------------------------------------------
// Bootstrap drivers first — small, and already gated at stage 0 — then the
// acceptance file, which is the largest real program the compiler has.

let defaultCorpus =
    [ root + "/tests/bootstrap/fixcorpus.fpp" ]

let corpus =
    match System.Environment.GetCommandLineArgs () |> Array.tryLast with
    | Some a when a.EndsWith ".fpp" || a.EndsWith ".txt" ->
        [ if System.IO.Path.IsPathRooted a then a else root + "/" + a ]
    | _ -> defaultCorpus

/// The corpus is served under STABLE names: the path a file is known by ends
/// up in the .wat (diagnostics, symbol prefixes), so stage-0 and stage-1 must
/// use the same one or every byte after the first name differs for no reason.
let servedName (path : string) = System.IO.Path.GetFileName path

// ---- the generated host --------------------------------------------------
// What a real host looks like from the module's side: a preloaded in-memory
// map, which is the case the host-import surface was designed for. Paths are
// matched exactly, as the compiler asks for them; a miss answers null, which
// the seam turns into None.

let escape (bytes : byte[]) =
    let sb = System.Text.StringBuilder()
    for b in bytes do
        if b = 34uy then sb.Append "\\22" |> ignore
        elif b = 92uy then sb.Append "\\5c" |> ignore
        elif b >= 32uy && b < 127uy then sb.Append (char b) |> ignore
        else sb.Append("\\").Append(b.ToString "x2") |> ignore
    sb.ToString ()

/// Source is BYTES. Reading it as UTF-8 text gives .NET char offsets, and
/// stage-1 — which sees the same file as bytes — then numbers every node
/// after the first non-ASCII character differently. Latin-1 is the identity
/// byte->char map, so both stages index the same way.
let readSource (path : string) : string =
    System.Text.Encoding.Latin1.GetString (System.IO.File.ReadAllBytes path)

/// The prelude source the host hands to stage-1 — the SAME text stage-0
/// compiled against, read from the file the build embeds.
let preludeText : string =
    readSource (root + "/stdlib/prelude.fpp")

let generateHost (files : (string * string) list) : string =
    let sb = System.Text.StringBuilder()
    let app (s : string) = sb.Append(s).Append('\n') |> ignore
    app "(module"
    app "  (type $str (array (mut i8)))"
    files |> List.iteri (fun i (p, c) ->
        app (sprintf "  (data $p%d \"%s\")" i (escape (System.Text.Encoding.UTF8.GetBytes p)))
        app (sprintf "  (data $c%d \"%s\")" i (escape (System.Text.Encoding.Latin1.GetBytes c))))
    app (sprintf "  (data $prelude \"%s\")" (escape (System.Text.Encoding.Latin1.GetBytes preludeText)))
    app "  (func $eq (param $a (ref $str)) (param $b (ref $str)) (result i32)"
    app "    (local $i i32)"
    app "    (if (i32.ne (array.len (local.get $a)) (array.len (local.get $b))) (then (return (i32.const 0))))"
    app "    (block $done (loop $next"
    app "      (br_if $done (i32.ge_u (local.get $i) (array.len (local.get $a))))"
    app "      (if (i32.ne (array.get_u $str (local.get $a) (local.get $i))"
    app "                  (array.get_u $str (local.get $b) (local.get $i)))"
    app "        (then (return (i32.const 0))))"
    app "      (local.set $i (i32.add (local.get $i) (i32.const 1)))"
    app "      (br $next)))"
    app "    (i32.const 1))"
    app "  (func $which (param $p anyref) (result i32)"
    app "    (local $s (ref null $str))"
    app "    (if (i32.eqz (ref.test (ref $str) (local.get $p))) (then (return (i32.const -1))))"
    app "    (local.set $s (ref.cast (ref $str) (local.get $p)))"
    files |> List.iteri (fun i (p, _) ->
        let n = System.Text.Encoding.UTF8.GetByteCount p
        app (sprintf "    (if (call $eq (ref.cast (ref $str) (local.get $s)) (array.new_data $str $p%d (i32.const 0) (i32.const %d)))" i n)
        app (sprintf "      (then (return (i32.const %d))))" i))
    app "    (i32.const -1))"
    app "  (func (export \"readTextRaw\") (param $p anyref) (result anyref)"
    app "    (local $k i32)"
    app "    (local.set $k (call $which (local.get $p)))"
    files |> List.iteri (fun i (_, c) ->
        let n = System.Text.Encoding.UTF8.GetByteCount c
        app (sprintf "    (if (i32.eq (local.get $k) (i32.const %d))" i)
        app (sprintf "      (then (return (array.new_data $str $c%d (i32.const 0) (i32.const %d)))))" i n))
    app "    (ref.null any))"
    app "  (func (export \"existsRaw\") (param $p anyref) (result i32)"
    app "    (i32.ne (call $which (local.get $p)) (i32.const -1)))"
    app "  (func (export \"listDirRaw\") (param $p anyref) (result anyref) (ref.null any))"
    app "  (func (export \"canonicalizeRaw\") (param $p anyref) (result anyref) (local.get $p))"
    // the prelude's own text is a host service too: stage-1 gets EXACTLY the
    // string stage-0 compiled against, which is what makes the two stages
    // comparable rather than merely similar
    app "  (func (export \"preludeSourceRaw\") (param $p anyref) (result anyref)"
    app (sprintf "    (array.new_data $str $prelude (i32.const 0) (i32.const %d)))"
                 (System.Text.Encoding.Latin1.GetByteCount preludeText))
    app ")"
    sb.ToString ()

// ---- the two stages ------------------------------------------------------

let emit (label : string) (files : (string * string) list) : string =
    let ws = Workspace()
    for path, text in files do ws.SetFileText path text
    let wat, errs = ws.EmitProgram ()
    if not (List.isEmpty errs) then
        printfn "%s: %d emit errors" label errs.Length
        errs
        |> List.countBy (fun (e : string) ->
            let i = e.IndexOf ": "
            let m = if i >= 0 then e.Substring (i + 2) else e
            String.concat " " (m.Split ' ' |> Array.truncate 6))
        |> List.sortByDescending snd
        |> List.truncate 12
        |> List.iter (fun (m, c) -> printfn "   %3d  %s" c m)
        exit 1
    wat

let run (exe : string) (args : string) =
    let psi = System.Diagnostics.ProcessStartInfo(exe, args)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    // BOTH pipes drained concurrently. Reading stdout to the end FIRST
    // deadlocks the moment the child fills the stderr buffer: the child
    // waits for stderr to drain, the parent waits for stdout to end, and
    // stage-1 sits there burning no CPU at all.
    let ot = p.StandardOutput.ReadToEndAsync ()
    let et = p.StandardError.ReadToEndAsync ()
    p.WaitForExit()
    ot.Result, et.Result, p.ExitCode

// ---- the bisector --------------------------------------------------------
// A difference is only useful if it names the emission site, so report the
// first differing byte with its line, its column, and the function it is in.

let enclosingFunc (text : string) (offset : int) =
    let upto = text.Substring (0, min offset text.Length)
    let i = upto.LastIndexOf "(func $"
    if i < 0 then "<before the first function>"
    else
        let rest = upto.Substring (i + 6)
        let cut = rest.IndexOfAny [| ' '; '\n'; '(' |]
        if cut < 0 then rest else rest.Substring (0, cut)

let report (expected : string) (actual : string) =
    if expected = actual then
        printfn "FIXPOINT: stage-1 reproduces stage-0 byte for byte (%d bytes)" expected.Length
        0
    else
        let n = min expected.Length actual.Length
        let mutable i = 0
        while i < n && expected.[i] = actual.[i] do i <- i + 1
        let line = 1 + (expected.Substring (0, i) |> Seq.filter (fun c -> c = '\n') |> Seq.length)
        let lineStart = expected.LastIndexOf ('\n', max 0 (i - 1)) + 1
        printfn "DIFFERS at byte %d (line %d, column %d) of %d/%d"
            i line (i - lineStart + 1) expected.Length actual.Length
        printfn "  in stage-0 function: %s" (enclosingFunc expected i)
        printfn "  in stage-1 function: %s" (enclosingFunc actual i)
        let window (s : string) =
            let a = max 0 (i - 60)
            let b = min s.Length (i + 60)
            s.Substring(a, b - a).Replace("\n", "\\n")
        printfn "  stage-0: %s" (window expected)
        printfn "  stage-1: %s" (window actual)
        1

// ---- go ------------------------------------------------------------------

let corpusFiles = corpus |> List.map (fun p -> servedName p, readSource p)

printfn "corpus: %s" (String.concat ", " (corpusFiles |> List.map fst))

let expected = emit "stage-0" corpusFiles
printfn "stage-0 answer: %d bytes" expected.Length

// `stage0` stops here: emitting stage-1 is the whole compiler and costs
// minutes and gigabytes, which is too much to pay just to see the answer
// this run is comparing against.
if System.Environment.GetCommandLineArgs () |> Array.contains "stage0" then exit 0

let stage1Source =
    (compilerFiles |> List.map (fun f -> f, readSource f))
    @ [ let d = root + "/tests/bootstrap/compiledrive.fpp"
        // the driver names the corpus; keep it and the host in step
        let text = readSource d
        let names = corpusFiles |> List.map (fun (n, _) -> "\"" + n + "\"")
        d, text.Replace ("let corpus = [ \"corpus.fpp\" ]",
                         "let corpus = [ " + String.concat "; " names + " ]") ]

let stage1 = emit "stage-1" stage1Source
let stage1Path = scratch + "/stage1.wat"
System.IO.File.WriteAllText (stage1Path, stage1)
printfn "stage-1: %d bytes of wat" stage1.Length

// the host serves the corpus AND the prelude the compiler reads at startup
let hostPath = scratch + "/env.wat"
System.IO.File.WriteAllText (hostPath,
    generateHost (corpusFiles @ [ "prelude.fpp", readSource (root + "/stdlib/prelude.fpp") ]))

// 64 MB of wasm stack: the compiler is recursive-descent throughout (parser,
// type walks, emission), and wasmtime's 1 MB default is not a statement about
// the program — a native build gets far more.
let out, err, code =
    run wasmtime ("run -W exceptions=y,gc=y,max-wasm-stack=67108864 --preload env=" + hostPath + " " + stage1Path)
if code <> 0 then
    printfn "stage-1 failed to run (exit %d)" code
    printfn "%s" (err.Substring (0, min 2000 err.Length))
    exit 1

// `print` appends a newline; the compared text is what the compiler produced
let actual = if out.EndsWith "\n" then out.Substring (0, out.Length - 1) else out
exit (report expected actual)

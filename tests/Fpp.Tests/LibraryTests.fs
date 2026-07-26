module Fpp.Tests.LibraryTests

open Expecto
open Fpp

// The library gate: the patricia-trie HashMap core ported from
// FSharp.Data.Adaptive (examples/hashmap.fpp) must compile, run, and
// match F# byte-for-byte — real algorithmic code as the conformance bar.

let private oracleFile (relPath : string) (stripPrefix : string) =
    let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
    let src = System.IO.File.ReadAllText (root + "/" + relPath)
    let ws = Workspace()
    ws.SetFileText relPath src
    let wat, errs = ws.EmitProgram ()
    Expect.isEmpty errs "compiles"
    let run (exe : string) (args : string) =
        let psi = System.Diagnostics.ProcessStartInfo(exe, args)
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        use p = System.Diagnostics.Process.Start psi
        let o = p.StandardOutput.ReadToEnd()
        p.StandardError.ReadToEnd() |> ignore
        p.WaitForExit()
        o
    let tmp = System.IO.Path.GetTempFileName() + ".wat"
    System.IO.File.WriteAllText(tmp, wat)
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    let actual = run (home + "/.wasmtime/bin/wasmtime") ("-W exceptions=y " + tmp)
    System.IO.File.Delete tmp
    let body =
        src.Split '\n'
        |> Array.filter (fun l -> not (l.StartsWith stripPrefix))
        |> String.concat "\n"
    let prelude =
        "let print (x : obj) =\n"
        + "    match x with\n"
        + "    | :? string as s -> printfn \"%s\" s\n"
        + "    | :? int as i -> printfn \"%d\" i\n"
        + "    | other -> printfn \"%O\" other\n"
    let fsx = System.IO.Path.GetTempFileName() + ".fsx"
    System.IO.File.WriteAllText(fsx, prelude + body)
    let expected = run "dotnet" ("fsi " + fsx)
    System.IO.File.Delete fsx
    Expect.equal actual expected ("F++ matches F# on " + relPath)

[<Tests>]
let stdlibTests =
    testList "stdlib" [
        test "List module (F++ source) matches F#" {
            oracleFile "stdlib/list.fpp" "module Stdlib"
        }
        test "MapExt Map + Set (AVL tree, 62 assertions incl. randomised model diff) match F#" {
            oracleFile "stdlib/mapext.fpp" "module Stdlib"
        }
        test "Map/Set modules (patricia trie, F++ source) match F#" {
            oracleFile "stdlib/map.fpp" "module Stdlib"
        }
    ]

[<Tests>]
let libraryTests =
    testList "library: hashmap port" [
        test "FSharp.Data.Adaptive hashmap core runs and matches F#" {
            let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
            let src = System.IO.File.ReadAllText (root + "/examples/hashmap.fpp")
            let ws = Workspace()
            ws.SetFileText "hashmap.fpp" src
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "compiles"
            let tmp = System.IO.Path.GetTempFileName() + ".wat"
            System.IO.File.WriteAllText(tmp, wat)
            let run (exe : string) (args : string) =
                let psi = System.Diagnostics.ProcessStartInfo(exe, args)
                psi.RedirectStandardOutput <- true
                psi.RedirectStandardError <- true
                use p = System.Diagnostics.Process.Start psi
                let o = p.StandardOutput.ReadToEnd()
                p.StandardError.ReadToEnd() |> ignore
                p.WaitForExit()
                o
            let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
            let actual = run (home + "/.wasmtime/bin/wasmtime") ("-W exceptions=y " + tmp)
            System.IO.File.Delete tmp
            let body =
                src.Split '\n'
                |> Array.filter (fun l -> not (l.StartsWith "module "))
                |> String.concat "\n"
            let prelude =
                "let print (x : obj) =\n"
                + "    match x with\n"
                + "    | :? string as s -> printfn \"%s\" s\n"
                + "    | :? int as i -> printfn \"%d\" i\n"
                + "    | other -> printfn \"%O\" other\n"
            let fsx = System.IO.Path.GetTempFileName() + ".fsx"
            System.IO.File.WriteAllText(fsx, prelude + body)
            let expected = run "dotnet" ("fsi " + fsx)
            System.IO.File.Delete fsx
            Expect.equal actual expected "F++ matches F# on the hashmap"
        }
    ]

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
    let bytes, errs = ws.EmitProgramWasm ()
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
    let tmp = System.IO.Path.GetTempFileName() + ".wasm"
    System.IO.File.WriteAllBytes(tmp, bytes)
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    let actual = run (home + "/.wasmtime/bin/wasmtime") ("run -W gc=y,exceptions=y " + tmp)
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
        test "Array module (int/float flavours) matches F#" {
            oracleFile "stdlib/array.fpp" "module Stdlib"
        }
        test "Check: property/fuzzing library (generators + forAll) matches F#" {
            oracleFile "stdlib/check.fpp" "module Stdlib"
        }
        test "MapExt Map + Set (AVL tree, 62 assertions incl. randomised model diff) match F#" {
            oracleFile "stdlib/mapext.fpp" "module Stdlib"
        }
        test "HashMap + HashSet (patricia trie, 44 assertions incl. randomised model diff) match F#" {
            oracleFile "stdlib/hashmap.fpp" "module Stdlib"
        }
        test "the .NET surface (ResizeArray, Dictionary, HashSet, StringBuilder, Math) matches F#" {
            oracleFile "stdlib/dotnet.fpp" "module Stdlib"
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
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "compiles"
            let tmp = System.IO.Path.GetTempFileName() + ".wasm"
            System.IO.File.WriteAllBytes(tmp, bytes)
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
            let actual = run (home + "/.wasmtime/bin/wasmtime") ("run -W gc=y,exceptions=y " + tmp)
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

// The acceptance gate: the UNPORTED FSharp.Data.Adaptive HashCollections
// source (4000+ lines, class hierarchies, bit-packed base state, struct
// tuples, static creators) compiles AND its collections work at runtime.

[<Tests>]
let acceptanceTests =
    testList "acceptance: HashCollections" [
        test "reference HashCollections source runs HashSet and HashMap" {
            let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
            let src = System.IO.File.ReadAllText (root + "/tests/reference-HashCollections.ported.fs.txt")
            let usage =
                String.concat "\n" [
                    ""
                    "let s1 = HashSet.OfList [ 1; 2; 3; 4; 5 ]"
                    "let p1 = print s1.Count"
                    "let s2 = s1.Add 6"
                    "let p2 = print s2.Count"
                    "let p3 = print (if s2.Contains 6 then 1 else 0)"
                    "let p4 = print (if s1.Contains 6 then 1 else 0)"
                    "let s3 = s2.Remove 1"
                    "let p5 = print s3.Count"
                    "let p6 = print (if s1.IsSubsetOf s2 then 1 else 0)"
                    "let p7 = print (if s2.IsProperSubsetOf s1 then 1 else 0)"
                    "let inter = s1.IntersectWith (HashSet.OfList [ 4; 5; 6; 7 ])"
                    "let p8 = print inter.Count"
                    "let m1 = HashMap.OfList [ (1, \"one\"); (2, \"two\"); (3, \"three\") ]"
                    "let p9 = print m1.Count"
                    "let p10 = print (match m1.TryFind 2 with Some v -> v | None -> \"?\")"
                    "let m2 = m1.Add(4, \"four\")"
                    "let p11 = print m2.Count"
                    "let m3 = m2.Remove 1"
                    "let p12 = print (match m3.TryFind 1 with Some v -> v | None -> \"gone\")"
                    "let p13 = print (m1.Fold((fun s k v -> s + k), 0))"
                    "let sum = HashSet.OfList [ 10; 20; 30 ]"
                    "let p14 = print (sum.Fold((fun s k -> s + k), 0))"
                    "let evens = s1.Filter (fun k -> k % 2 = 0)"
                    "let p15 = print evens.Count"
                    "let mapped = m1.Map (fun k v -> String.length v)"
                    "let p16 = print (match mapped.TryFind 3 with Some n -> n | None -> -1)"
                    "let p17 = print (if s1.SetEquals (HashSet.OfArray [| 5; 4; 3; 2; 1 |]) then 1 else 0)"
                    "let p18 = print (if s1.Overlaps ([ 5; 9 ] :> seq<int>) then 1 else 0)"
                    "" ]
            let ws = Workspace()
            ws.SetFileText "HashCollections.fpp" (src + usage)
            Expect.isEmpty (ws.Diagnostics "HashCollections.fpp") "type-checks"
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "compiles"
            let tmp = System.IO.Path.GetTempFileName() + ".wasm"
            System.IO.File.WriteAllBytes(tmp, bytes)
            let psi =
                let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
                System.Diagnostics.ProcessStartInfo(home + "/.wasmtime/bin/wasmtime", "run -W gc=y,exceptions=y " + tmp)
            psi.RedirectStandardOutput <- true
            psi.RedirectStandardError <- true
            let actual, err, code =
                use p = System.Diagnostics.Process.Start psi
                let o = p.StandardOutput.ReadToEnd()
                let e = p.StandardError.ReadToEnd()
                p.WaitForExit()
                o, e, p.ExitCode
            System.IO.File.Delete tmp
            Expect.equal code 0 ("runs without trapping: " + err)
            let expected =
                String.concat "\n"
                    [ "5"; "6"; "1"; "0"; "5"; "1"; "0"; "2"
                      "3"; "two"; "4"; "gone"; "6"; "60"; "2"; "5"; "1"; "1"; "" ]
            Expect.equal (actual.Replace("\r\n", "\n")) expected "HashSet and HashMap answer correctly"
        }
    ]

module Fpp.Tests.OracleTests

open Expecto
open Fpp

// The oracle harness: the shared subset is real F#, so every program can run
// twice — under dotnet fsi and under fpp+wasmtime — and the outputs must
// match. A machine-checked conformance suite for the inherited semantics.

let private wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let private run (exe : string) (args : string) : string * int =
    let psi = System.Diagnostics.ProcessStartInfo(exe, args)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd()
    p.StandardError.ReadToEnd() |> ignore
    p.WaitForExit()
    out, p.ExitCode

let private fppRun (src : string) : string =
    let ws = Workspace()
    ws.SetFileText "prog.fpp" src
    let wat, errors = ws.EmitProgram ()
    Expect.isEmpty errors "emission errors"
    let tmp = System.IO.Path.GetTempFileName() + ".wat"
    System.IO.File.WriteAllText(tmp, wat)
    let out, code = run wasmtime tmp
    System.IO.File.Delete tmp
    Expect.equal code 0 "wasmtime failed"
    out

let private fsiRun (src : string) : string =
    // strip the module header; provide the F# side of `print`
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
    let tmp = System.IO.Path.GetTempFileName() + ".fsx"
    System.IO.File.WriteAllText(tmp, prelude + body)
    let out, code = run "dotnet" ("fsi " + tmp)
    System.IO.File.Delete tmp
    Expect.equal code 0 "fsi failed"
    out

let private oracle (name : string) (srcLines : string list) =
    test name {
        let src = String.concat "\n" ("module M" :: srcLines) + "\n"
        let expected = fsiRun src
        let actual = fppRun src
        Expect.equal actual expected "F++ output must match F# (the oracle)"
    }

[<Tests>]
let oracleTests =
    testList "oracle: F# vs F++" [
        oracle "factorial including beyond-i31 range" [
            "let rec fact n ="
            "    if n <= 1 then 1"
            "    else n * fact (n - 1)"
            "let a = print (fact 10)"
            "let b = print (fact 13)"   // 1932053504 — needs full int32
            "let c = print \"done\""
        ]
        oracle "lists, matches, recursion" [
            "let rec sum xs ="
            "    match xs with"
            "    | h :: t -> h + sum t"
            "    | [] -> 0"
            "let rec rev acc xs ="
            "    match xs with"
            "    | h :: t -> rev (h :: acc) t"
            "    | [] -> acc"
            "let a = print (sum [1; 2; 3; 4; 5])"
            "let b = print (sum (rev [] [10; 20; 30]))"
        ]
        oracle "tuples, guards, negatives, arithmetic" [
            "let classify t ="
            "    match t with"
            "    | a, b when a > b -> \"first\""
            "    | a, b when a < b -> \"second\""
            "    | _ -> \"same\""
            "let x = print (classify (2, 1))"
            "let y = print (classify (1, 2))"
            "let z = print (0 - 42)"
            "let w = print ((0 - 7) * (0 - 6))"
            "let v = print (100000 * 30000)"   // int32 wraparound semantics
        ]
    ]

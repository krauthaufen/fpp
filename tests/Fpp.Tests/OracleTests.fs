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
        oracle "tail recursion at depth 1000000" [
            "let rec loop i acc ="
            "    if i = 0 then acc"
            "    else loop (i - 1) (acc + 1)"
            "let a = print (loop 1000000 0)"
        ]
        oracle "imperative: while, range-for, mutables" [
            "let sumTo n ="
            "    let mutable acc = 0"
            "    let mutable i = 1"
            "    while i <= n do"
            "        acc <- acc + i"
            "        i <- i + 1"
            "    acc"
            "let a = print (sumTo 100)"
            "let countFor () ="
            "    let mutable s = 0"
            "    for i in 1 .. 10 do"
            "        s <- s + i * i"
            "    s"
            "let b = print (countFor ())"
        ]
        oracle "arrays: literals, indexing, mutation, Length" [
            "let xs = [| 10; 20; 30 |]"
            "let a = print (xs.[0] + xs.[2])"
            "let doIt () ="
            "    xs.[1] <- 99"
            "    xs.[1]"
            "let b = print (doIt ())"
            "let c = print (xs.Length)"
            "let d = print (\"hello\".Length)"
            "let sumArr (arr : int[]) ="
            "    let mutable s = 0"
            "    for i in 0 .. arr.Length - 1 do"
            "        s <- s + arr.[i]"
            "    s"
            "let e = print (sumArr [| 1; 2; 3; 4 |])"
        ]
        oracle "string concatenation" [
            "let greet name ="
            "    \"Hello, \" + name + \"!\""
            "let a = print (greet \"F++\")"
            "let b = print (1 + 2 + 3)"
        ]
        oracle "floats: arithmetic, comparison, printing" [
            "let a = print (1.5 + 2.25)"
            "let b = print (10.0 / 4.0)"
            "let c = print (3.5 * 2.0 - 0.5)"
            "let d = print (if 2.5 > 2.25 then 1 else 0)"
            "let area (r : float) = r * r * 3.140625"
            "let e = print (area 2.0)"
        ]
        oracle "int64: wide arithmetic" [
            "let big = 5000000000L"
            "let a = print (big + big)"
            "let b = print (big * 3L)"
            "let c = print (9000000000L / 4L)"
            "let d = print (if 5000000001L > big then 1 else 0)"
        ]
        oracle "float32 arithmetic" [
            "let x = 0.5f + 0.25f"
            "let a = print (x * 2.0f)"
        ]
        oracle "struct V2d: array of structs, field sums" [
            "[<Struct>]"
            "type V2d = { X : float; Y : float }"
            "let pts = [| { X = 1.5; Y = 2.5 }; { X = 3.25; Y = 0.75 }; { X = 10.0; Y = 20.0 } |]"
            "let total ="
            "    let mutable s = 0.0"
            "    for i in 0 .. pts.Length - 1 do"
            "        s <- s + pts.[i].X + pts.[i].Y"
            "    s"
            "let a = print total"
            "let b = print (pts.[2].X * pts.[0].Y)"
            "let dot (u : V2d) (v : V2d) = u.X * v.X + u.Y * v.Y"
            "let c = print (dot pts.[0] pts.[1])"
        ]
        oracle "string equality and chars" [
            "let pick s ="
            "    if s = \"yes\" then 1 else 0"
            "let a = print (pick \"yes\")"
            "let b = print (pick \"no\")"
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

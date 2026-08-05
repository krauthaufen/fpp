module Fpp.Tests.AdaptiveSuiteTests

open Expecto
open Fpp

// The fourth gate: the FSharp.Data.Adaptive port RUNS. The library is
// regenerated from its checkout by the port driver, concatenated with the
// hand-ported test suite, compiled, and executed under wasmtime — the
// suite's own "PASSED n FAILED 0" line is the assertion. This is the gate
// that catches what inference and the fixpoints cannot: a representation
// split, a mis-stamped clone, a closure reading the wrong cell — every one
// of those was found by running, not by checking.
//
// The FSharp.Data.Adaptive checkout is an external input; without it the
// gate SKIPS loudly rather than passing silently.

let private adaptiveRoot =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    home + "/projects/FSharp.Data.Adaptive/src/FSharp.Data.Adaptive"

let private run (exe : string) (args : string) : string * string * int =
    let psi = System.Diagnostics.ProcessStartInfo(exe, args)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let o = p.StandardOutput.ReadToEnd()
    let e = p.StandardError.ReadToEnd()
    p.WaitForExit()
    o, e, p.ExitCode

[<Tests>]
let adaptiveSuiteTests =
    // sequenced: an eight-minute in-process compile sharing the runner with
    // the parallel batch starves it — three unrelated tests flaked when
    // this ran alongside them
    testSequenced <| testList "adaptive suite" [
        if not (System.IO.Directory.Exists adaptiveRoot) then
            ptest "the ported library's test suite runs green (SKIPPED: no FSharp.Data.Adaptive checkout)" { () }
        else
            test "the ported library's test suite runs green" {
                let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
                let tmp = System.IO.Path.GetTempPath() + "fpp-adaptive-gate"
                System.IO.Directory.CreateDirectory tmp |> ignore
                let libPath = tmp + "/lib.fpp"
                let o, e, code =
                    run "python3" (root + "/tests/port-adaptive.py " + adaptiveRoot + " " + libPath)
                Expect.equal code 0 ("port driver runs: " + o + e)
                let suiteSrc =
                    System.IO.File.ReadAllText libPath
                    + System.IO.File.ReadAllText (root + "/tests/adaptive-suite/Tests.fpp")
                let ws = Workspace()
                ws.SetFileText "adaptive-suite.fpp" suiteSrc
                let bytes, errs = ws.EmitProgramWasm ()
                Expect.isEmpty errs "the suite compiles with zero errors"
                let wasmPath = tmp + "/suite.wasm"
                System.IO.File.WriteAllBytes(wasmPath, bytes)
                let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
                let out, err, rc =
                    run (home + "/.wasmtime/bin/wasmtime")
                        ("run -W function-references=y,gc=y,exceptions=y " + wasmPath)
                Expect.equal rc 0 ("the suite runs to exit 0: " + err)
                let last =
                    out.Split '\n'
                    |> Array.filter (fun l -> l.StartsWith "PASSED ")
                    |> Array.tryLast
                match last with
                | Some line ->
                    Expect.stringEnds line "FAILED 0" ("no failures: " + line)
                    let passed =
                        line.Split ' ' |> Array.item 1 |> int
                    Expect.isGreaterThanOrEqual passed 100
                        "the suite has not shrunk below its 100-test baseline"
                | None -> failwithf "no PASSED line in output: %s" out
            }
    ]

module Fpp.Tests.FixpointTests

open Expecto
open Fpp

// PHASE 2: the stage-0/stage-1 fixpoint.
//
// Stage-0 is the dotnet-built compiler. Stage-1 is the compiler AS WASM —
// stage-0's output for the compiler's own 20 sources plus the driver in
// tests/bootstrap/compiledrive.fpp. Both then compile the same corpus, and
// their .wat must agree byte for byte. Anything else is the compiler
// miscompiling itself.
//
// The corpus reaches stage-1 through the four host imports, served by a
// generated preload module — a preloaded in-memory map, which is the case
// the host-import surface was designed for. It is SERVED and never baked
// into the driver: a driver carrying the text could let the two stages
// compile different bytes and still agree, which is precisely the weak gate
// this phase exists to close.
//
// Gating: the whole thing is one wasmtime run over a module the size of the
// compiler, so it is measured before it is trusted. `Fixpoint` runs it;
// without that the test list is empty and says why.

let private root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")

let private enabled =
    match System.Environment.GetEnvironmentVariable "FPP_FIXPOINT" with
    | null | "" | "0" -> false
    | _ -> true

let private run (exe : string) (args : string) =
    let psi = System.Diagnostics.ProcessStartInfo(exe, args)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.WorkingDirectory <- root
    use p = System.Diagnostics.Process.Start psi
    let o = p.StandardOutput.ReadToEnd()
    let e = p.StandardError.ReadToEnd()
    p.WaitForExit()
    o, e, p.ExitCode

[<Tests>]
let fixpointTests =
    testList "phase 2: stage-0/stage-1 fixpoint" [
        if enabled then
            test "stage-1 compiles the corpus to the same bytes as stage-0" {
                let out, err, code = run "dotnet" "fsi tests/bootstrap/fixpoint.fsx"
                // the script names the first differing byte and the function
                // it falls inside; that message IS the failure report
                Expect.equal code 0 (out + "\n" + err)
                Expect.stringContains out "FIXPOINT:" "the script reached the comparison"
            }
        else
            test "the fixpoint is gated off (set FPP_FIXPOINT=1 to run it)" {
                Expect.isTrue (System.IO.File.Exists (root + "/tests/bootstrap/fixpoint.fsx"))
                    "the harness is present even when the gate is off"
            }
    ]

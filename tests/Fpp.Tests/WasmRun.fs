module Fpp.Tests.WasmRun

// Shared runner for reactor-linear test programs: modules emitted with
// EmitProgramWasmPreload import fpprt from the mmc reactor via wasmtime
// --preload — no wasm-merge in the unit-test path. mmc is the product
// collector and the only one that can pin (deriveSerialize blits Array.pin);
// the semi shakeout still runs the conformance/fixpoint gates via FPP_REACTOR.

let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
let wasmtime =
    System.Environment.GetEnvironmentVariable "HOME" + "/.wasmtime/bin/wasmtime"
let reactor = root + "/tests/tooling/gc/fpprt_reactor.wasm"
/// the product collector — the only one that can pin (Array.pin tests)
let reactorMmc = root + "/tests/tooling/gc/fpprt_reactor_mmc.wasm"

/// exitCode, stdout, stderr
let run (bytes : byte[]) : int * string * string =
    let tmp = System.IO.Path.GetTempFileName () + ".wasm"
    System.IO.File.WriteAllBytes (tmp, bytes)
    try
        let psi =
            System.Diagnostics.ProcessStartInfo (
                wasmtime,
                "run -W gc=y,exceptions=y --env FPPRT_HEAP_MB=256 --preload fpprt=" + reactorMmc + " " + tmp)
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        use p = System.Diagnostics.Process.Start psi
        let out = p.StandardOutput.ReadToEnd ()
        let err = p.StandardError.ReadToEnd ()
        p.WaitForExit ()
        p.ExitCode, out, err
    finally
        System.IO.File.Delete tmp

module Fpp.Tests.BinOracleTests

open Expecto

// The binary-backend gate: every oracle program runs through BOTH emitters —
// text (wat, already conformance-checked against F#) and binary (bytes) —
// and the outputs must be identical. The text emitter is the reference here;
// its own fidelity is established by OracleTests against dotnet fsi.

let private wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let private run (exe : string) (args : string) : string * string * int =
    let psi = System.Diagnostics.ProcessStartInfo (exe, args)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd ()
    let err = p.StandardError.ReadToEnd ()
    p.WaitForExit ()
    out, err, p.ExitCode

let private textRun (src : string) : string =
    let ws = Fpp.Workspace ()
    ws.SetFileText "prog.fpp" src
    let wat, errors = ws.EmitProgram ()
    Expect.isEmpty errors "text emission errors"
    let tmp = System.IO.Path.GetTempFileName () + ".wat"
    System.IO.File.WriteAllText (tmp, wat)
    let out, err, code = run wasmtime ("-W exceptions=y " + tmp)
    System.IO.File.Delete tmp
    Expect.equal code 0 (sprintf "text wasmtime failed: %s" err)
    out

let private binaryRun (src : string) : string =
    let ws = Fpp.Workspace ()
    ws.SetFileText "prog.fpp" src
    let bytes, errors = ws.EmitProgramWasm ()
    Expect.isEmpty errors "binary emission errors"
    let tmp = System.IO.Path.GetTempFileName () + ".wasm"
    System.IO.File.WriteAllBytes (tmp, bytes)
    let out, err, code = run wasmtime ("run -W gc=y,exceptions=y " + tmp)
    System.IO.File.Delete tmp
    Expect.equal code 0 (sprintf "binary wasmtime failed: %s" err)
    out

[<Tests>]
let binOracleTests =
    // touching the oracle list forces OracleTests' module init, which is
    // what populates the corpus
    OracleTests.oracleTests |> ignore
    testList "binary oracle: text vs binary" [
        for name, srcLines in List.ofSeq OracleTests.corpus ->
            test name {
                let src = String.concat "\n" ("module M" :: srcLines) + "\n"
                let expected = textRun src
                let actual = binaryRun src
                Expect.equal actual expected "binary output must match the text emitter"
            }
    ]

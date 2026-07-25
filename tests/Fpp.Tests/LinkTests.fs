module Fpp.Tests.LinkTests

open Expecto
open Fpp

[<Tests>]
let linkTests =
    testList "linker" [
        test "separate compilation: lib exports, schemes, DCE, execution" {
            let libWs = Workspace()
            libWs.SetFileText "mathlib.fpp"
                (String.concat "\n" [
                    "module MathLib"
                    "let double x = x * 2"
                    "let unusedHelper x = x + 999"
                    "let rec sumTo n ="
                    "    if n = 0 then 0"
                    "    else n + sumTo (n - 1)"
                    "" ])
            let lib, libErrs = libWs.BuildLibrary ()
            Expect.isEmpty libErrs "library builds"
            let ws = Workspace()
            ws.AddLibrary "mathlib.fppir" lib
            ws.SetFileText "app.fpp"
                (String.concat "\n" [
                    "module App"
                    "open MathLib"
                    "let a = print (double 21)"
                    "let c = print (sumTo 100)"
                    "" ])
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "app links"
            Expect.isFalse (wat.Contains "unusedHelper") "dead code eliminated"
            let tmp = System.IO.Path.GetTempFileName() + ".wat"
            System.IO.File.WriteAllText(tmp, wat)
            let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
            let psi = System.Diagnostics.ProcessStartInfo(home + "/.wasmtime/bin/wasmtime", tmp)
            psi.RedirectStandardOutput <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd()
            p.WaitForExit()
            System.IO.File.Delete tmp
            Expect.equal out "42\n5050\n" "linked program runs"
        }
        test "type errors cross the library boundary" {
            let libWs = Workspace()
            libWs.SetFileText "l.fpp" "module L\nlet shout (s : string) = s\n"
            let lib, _ = libWs.BuildLibrary ()
            let ws = Workspace()
            ws.AddLibrary "l.fppir" lib
            ws.SetFileText "a.fpp" "module A\nopen L\nlet bad = shout 42\n"
            Expect.isNonEmpty (ws.Diagnostics "a.fpp") "int into string param caught across the lib"
        }
    ]

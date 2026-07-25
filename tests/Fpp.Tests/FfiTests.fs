module Fpp.Tests.FfiTests

open Expecto
open Fpp

[<Tests>]
let ffiTests =
    testList "ffi" [
        test "extern let imports cross an i32 C-ABI boundary" {
            let ws = Workspace()
            ws.SetFileText "ffi.fpp"
                (String.concat "\n" [
                    "module Ffi"
                    "extern let mul3 : int -> int"
                    "extern let addmul : int -> int -> int"
                    "let a = print (mul3 14)"
                    "let b = print (addmul 3 4)"
                    "let c = print (mul3 (addmul 1 1) + 1)"
                    "" ])
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "emits"
            Expect.stringContains wat "(import \"env\" \"mul3\"" "import emitted"
            let dir = System.IO.Path.GetTempPath()
            let env = dir + "fppenv.wat"
            let prog = dir + "fppffi.wat"
            System.IO.File.WriteAllText(env,
                "(module\n  (func (export \"mul3\") (param i32) (result i32) (i32.mul (local.get 0) (i32.const 3)))\n  (func (export \"addmul\") (param i32) (param i32) (result i32) (i32.mul (i32.add (local.get 0) (local.get 1)) (i32.const 10))))")
            System.IO.File.WriteAllText(prog, wat)
            let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
            let psi = System.Diagnostics.ProcessStartInfo(home + "/.wasmtime/bin/wasmtime", "run --preload env=" + env + " " + prog)
            psi.RedirectStandardOutput <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd()
            p.WaitForExit()
            Expect.equal out "42\n70\n61\n" "foreign calls compute correctly"
        }
        test "extern types are checked" {
            let ws = Workspace()
            ws.SetFileText "f.fpp" "module F\nextern let mul3 : int -> int\nlet bad = mul3 \"nope\"\n"
            Expect.isNonEmpty (ws.Diagnostics "f.fpp") "string into int extern caught"
        }
    ]

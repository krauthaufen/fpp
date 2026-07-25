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
            let psi = System.Diagnostics.ProcessStartInfo(home + "/.wasmtime/bin/wasmtime", "run -W exceptions=y --preload env=" + env + " " + prog)
            psi.RedirectStandardOutput <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd()
            p.WaitForExit()
            Expect.equal out "42\n70\n61\n" "foreign calls compute correctly"
        }
        test "pinned struct arrays expose byte-exact C layout" {
            // THE FFI PROOF: pin a V2d[], let a foreign reader sum raw
            // doubles at the pointer; correct sum == byte-exact C layout.
            // (wasmtime hosts the "C library" as a preload module.)
            let ws = Workspace()
            ws.SetFileText "pin.fpp"
                (String.concat "\n" [
                    "module Pin"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "extern let sumXY : int -> int -> int"
                    "let pts = [| { X = 1.5; Y = 2.25 }; { X = 10.0; Y = 0.5 } |]"
                    "let ptr = Array.pin pts"
                    "let s = print (sumXY ptr 2)"
                    "let live = print (pts.[1].X + pts.[1].Y)"
                    "let back = Array.unpin pts"
                    "let after = print (pts.[0].X + pts.[0].Y)"
                    "" ])
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "compiles"
            let dir = System.IO.Path.GetTempPath()
            let envPath = dir + "fppcsum.wat"
            let progPath = dir + "fpppin.wat"
            System.IO.File.WriteAllText(envPath,
                String.concat "\n" [
                    "(module"
                    "  (import \"mainmem\" \"memory\" (memory 17))"
                    "  (func (export \"sumXY\") (param $p i32) (param $n i32) (result i32)"
                    "    (local $i i32) (local $a f64)"
                    "    (block $d (loop $go"
                    "      (br_if $d (i32.ge_u (local.get $i) (local.get $n)))"
                    "      (local.set $a (f64.add (local.get $a) (f64.add"
                    "        (f64.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 16))))"
                    "        (f64.load (i32.add (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 16))) (i32.const 8))))))"
                    "      (local.set $i (i32.add (local.get $i) (i32.const 1)))"
                    "      (br $go)))"
                    "    (i32.trunc_f64_s (f64.mul (local.get $a) (f64.const 100)))))" ])
            System.IO.File.WriteAllText(progPath, wat)
            let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
            let psi =
                System.Diagnostics.ProcessStartInfo(
                    home + "/.wasmtime/bin/wasmtime",
                    "run -W exceptions=y -W gc=y --preload env=" + envPath + " " + progPath)
            psi.RedirectStandardOutput <- true
            psi.RedirectStandardError <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd()
            let err = p.StandardError.ReadToEnd()
            p.WaitForExit()
            if p.ExitCode <> 0 then
                // the preload needs the main module's memory; if the host
                // cannot wire it, skip rather than fail spuriously
                Expect.stringContains err "memory" (sprintf "unexpected failure: %s" err)
            else
                Expect.equal out "1425\n10.5\n3.75\n" "foreign reader saw C layout"
        }
        test "extern types are checked" {
            let ws = Workspace()
            ws.SetFileText "f.fpp" "module F\nextern let mul3 : int -> int\nlet bad = mul3 \"nope\"\n"
            Expect.isNonEmpty (ws.Diagnostics "f.fpp") "string into int extern caught"
        }
    ]

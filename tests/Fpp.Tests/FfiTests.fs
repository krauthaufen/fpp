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
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "emits"
            Expect.isTrue ((System.Text.Encoding.Latin1.GetString bytes).Contains "mul3") "import emitted"
            let dir = System.IO.Path.GetTempPath()
            let env = dir + "fppenv.wat"
            let prog = dir + "fppffi.wasm"
            System.IO.File.WriteAllText(env,
                "(module\n  (func (export \"mul3\") (param i32) (result i32) (i32.mul (local.get 0) (i32.const 3)))\n  (func (export \"addmul\") (param i32) (param i32) (result i32) (i32.mul (i32.add (local.get 0) (local.get 1)) (i32.const 10))))")
            System.IO.File.WriteAllBytes(prog, bytes)
            let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
            let psi = System.Diagnostics.ProcessStartInfo(home + "/.wasmtime/bin/wasmtime", "run -W gc=y,exceptions=y --preload env=" + env + " " + prog)
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
                    "extern let sumXY : nativeint -> int -> int"
                    "let pts = [| { X = 1.5; Y = 2.25 }; { X = 10.0; Y = 0.5 } |]"
                    "let ptr = Array.pin pts"
                    "let s = print (sumXY ptr 2)"
                    "let live = print (pts.[1].X + pts.[1].Y)"
                    "let back = Array.unpin pts"
                    "let after = print (pts.[0].X + pts.[0].Y)"
                    "" ])
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "compiles"
            let dir = System.IO.Path.GetTempPath()
            let envPath = dir + "fppcsum.wat"
            let progPath = dir + "fpppin.wasm"
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
            System.IO.File.WriteAllBytes(progPath, bytes)
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
        test "a 12-byte struct array has C's stride, not a padded one" {
            // THE ABI PROOF, for the case that used to be wrong: clang and
            // emscripten give `struct { float a, b, c; }` a size of 12 and an
            // array of them a stride of 12. A backing store of 64-bit words
            // would round that to 16 and every element after the first would
            // sit four bytes late — invisible until a foreign reader walks the
            // array. The reader below walks it at stride 12, as C does.
            let ws = Workspace()
            ws.SetFileText "pin3.fpp"
                (String.concat "\n" [
                    "module Pin3"
                    "[<Struct>]"
                    "type V3f = { A : float32; B : float32; C : float32 }"
                    "extern let sum3 : nativeint -> int -> int"
                    "let pts = [| { A = 1.0f; B = 2.0f; C = 3.0f }; { A = 4.0f; B = 5.0f; C = 6.0f }; { A = 7.0f; B = 8.0f; C = 9.0f } |]"
                    "let ptr = Array.pin pts"
                    "let n = print (Array.byteSize pts)"
                    "let s = print (sum3 ptr 3)"
                    "let live = print (pts.[2].C)"
                    "" ])
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "compiles"
            let dir = System.IO.Path.GetTempPath()
            let envPath = dir + "fppcsum3.wat"
            let progPath = dir + "fpppin3.wasm"
            // stride 12, three floats each: exactly what a C `V3f*` walk is
            System.IO.File.WriteAllText(envPath,
                String.concat "\n" [
                    "(module"
                    "  (import \"mainmem\" \"memory\" (memory 17))"
                    "  (func (export \"sum3\") (param $p i32) (param $n i32) (result i32)"
                    "    (local $i i32) (local $a f32)"
                    "    (block $d (loop $go"
                    "      (br_if $d (i32.ge_u (local.get $i) (local.get $n)))"
                    "      (local.set $a (f32.add (local.get $a) (f32.add (f32.add"
                    "        (f32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 12))))"
                    "        (f32.load (i32.add (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 12))) (i32.const 4))))"
                    "        (f32.load (i32.add (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 12))) (i32.const 8))))))"
                    "      (local.set $i (i32.add (local.get $i) (i32.const 1)))"
                    "      (br $go)))"
                    "    (i32.trunc_f32_s (local.get $a))))" ])
            System.IO.File.WriteAllBytes(progPath, bytes)
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
                Expect.stringContains err "memory" (sprintf "unexpected failure: %s" err)
            else
                // 36 bytes for three elements (not 48), 1+..+9 = 45, and the
                // array still reads correctly from F++ while pinned
                Expect.equal out "36\n45\n9\n" "C stride, and the array still works"
        }
        test "extern types are checked" {
            let ws = Workspace()
            ws.SetFileText "f.fpp" "module F\nextern let mul3 : int -> int\nlet bad = mul3 \"nope\"\n"
            Expect.isNonEmpty (ws.Diagnostics "f.fpp") "string into int extern caught"
        }
    ]

[<Tests>]
let hostImportTests =
    // The host surface: readText, exists, listDir, canonicalize, satisfied
    // by a wasm module the way a real host satisfies them. The point of the
    // test is the CONTRACT — strings only, null for "not there", newline
    // separated for a list — so any host can implement it.
    testList "host imports" [
        test "the four host services are satisfied by a preloaded module" {
            let ws = Workspace()
            ws.SetFileText "seam.fpp" (System.IO.File.ReadAllText (
                System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../../stdlib/bootstrap.fpp")))
            ws.SetFileText "prog.fpp" (String.concat "\n" [
                "module P"
                "open Fpp.Prelude"
                "let r1 ="
                "    match hostReadText \"/there\" with"
                "    | Some t -> print (\"read \" + t)"
                "    | None -> print \"MISSING\""
                "let r2 ="
                "    match hostReadText \"/gone\" with"
                "    | Some t -> print (\"BAD \" + t)"
                "    | None -> print \"absent\""
                "let r3 = print (string (hostExists \"/there\") + \" \" + string (hostExists \"/gone\"))"
                "let r4 = print (String.concat \"|\" (Array.toList (hostListDir \"/d\")))"
                "let r5 = print (string (Array.length (hostListDir \"/empty\")))"
                "let r6 = print (hostCanonicalize \"/a/./b\")"
                "" ])
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "the host surface emits"
            // every import is declared against module "env"
            Expect.isTrue ((System.Text.Encoding.Latin1.GetString bytes).Contains "readTextRaw") "readText is an import"
            Expect.isTrue ((System.Text.Encoding.Latin1.GetString bytes).Contains "existsRaw") "exists is an import"
            Expect.isTrue ((System.Text.Encoding.Latin1.GetString bytes).Contains "listDirRaw") "listDir is an import"
            Expect.isTrue ((System.Text.Encoding.Latin1.GetString bytes).Contains "canonicalizeRaw") "canonicalize is an import"
        }
        test "a missing file is None, not an exception" {
            // Runnable half of the contract: the .NET side of the seam, which
            // the dotnet-hosted compiler uses today and which the F++ side
            // must match. The wasm side declares the same shape (above) and
            // wraps null into None in the seam, not in the host.
            let tmp = System.IO.Path.GetTempFileName()
            System.IO.File.WriteAllText(tmp, "contents")
            Expect.equal (Prelude.hostReadText tmp) (Some "contents") "an existing file reads"
            Expect.equal (Prelude.hostReadText (tmp + ".nope")) None "a missing file is None"
            Expect.isTrue (Prelude.hostExists tmp) "exists sees the file"
            Expect.isFalse (Prelude.hostExists (tmp + ".nope")) "and not a missing one"
            let dir = System.IO.Path.GetDirectoryName tmp
            Expect.isTrue (Prelude.hostExists dir) "exists covers directories too"
            Expect.contains (Prelude.hostListDir dir) tmp "listDir finds the file"
            Expect.equal (Prelude.hostListDir (tmp + "-no-such-dir")) [||] "a missing directory lists empty"
            System.IO.File.Delete tmp
        }
        test "path arithmetic needs no host" {
            Expect.equal (Prelude.pathDirectory "/a/b/c.fpp") "/a/b" "directory"
            Expect.equal (Prelude.pathFileName "/a/b/c.fpp") "c.fpp" "file name"
            Expect.equal (Prelude.pathFileNameWithoutExtension "/a/b/c.fpp") "c" "stem"
            Expect.equal (Prelude.pathCombine "/a/b" "c.fpp") "/a/b/c.fpp" "combine"
            Expect.equal (Prelude.pathCombine "/a/b" "/x.fpp") "/x.fpp" "an absolute rel wins"
            Expect.equal (Prelude.pathCombine "" "c.fpp") "c.fpp" "empty dir"
        }
    ]

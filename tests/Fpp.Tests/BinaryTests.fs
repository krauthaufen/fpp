module Fpp.Tests.BinaryTests

open Expecto
open Fpp.Backend.WasmBinary
open Fpp.Backend.EmitBin

// The byte writer for direct binary emission, proven the only way that
// counts: a module assembled by hand through it RUNS. Encodings are also
// pinned against the classic LEB128 vectors, because an off-by-one here
// would surface as a validation error thousands of bytes downstream.

let private wasmtime =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    home + "/.wasmtime/bin/wasmtime"

[<Tests>]
let binaryWriter =
    testList "binary writer" [
        test "LEB128 encodings match the reference vectors" {
            let enc (f : Bytes -> unit) : int list =
                let b = bytesNew ()
                f b
                bytesToArray b |> Array.toList |> List.map int
            Expect.equal (enc (fun b -> emitU32 b 0)) [ 0x00 ] "u32 0"
            Expect.equal (enc (fun b -> emitU32 b 64)) [ 0x40 ] "u32 64"
            Expect.equal (enc (fun b -> emitU32 b 300)) [ 0xAC; 0x02 ] "u32 300"
            Expect.equal (enc (fun b -> emitU32 b 624485)) [ 0xE5; 0x8E; 0x26 ] "u32 624485"
            Expect.equal (enc (fun b -> emitS32 b -1)) [ 0x7F ] "s32 -1"
            Expect.equal (enc (fun b -> emitS32 b 64)) [ 0xC0; 0x00 ] "s32 64 needs a continuation"
            Expect.equal (enc (fun b -> emitS32 b -123456)) [ 0xC0; 0xBB; 0x78 ] "s32 -123456"
            Expect.equal (enc (fun b -> emitS64 b -1L)) [ 0x7F ] "s64 -1"
        }
        test "labels resolve to relative depths, innermost shadowing" {
            let ls = labelsNew ()
            pushLabel ls "a"
            pushLabel ls "b"
            pushLabel ls "a"
            Expect.equal (labelDepth ls "a") 0 "innermost a"
            Expect.equal (labelDepth ls "b") 1 "b one out"
            popLabel ls
            // stack is [a; b] now: the outer `a` sits one block out
            Expect.equal (labelDepth ls "a") 1 "outer a after pop"
            Expect.equal (labelDepth ls "missing") -1 "unknown label"
        }
        test "a hand-assembled module with patched sizes and a br RUNS" {
            let b = bytesNew ()
            // magic + version
            for v in [ 0x00; 0x61; 0x73; 0x6D; 0x01; 0x00; 0x00; 0x00 ] do emitByte b v
            // type section: one functype [] -> [i32]
            emitByte b 1
            let ts = beginPatch b
            emitU32 b 1
            emitByte b 0x60
            emitU32 b 0
            emitU32 b 1
            emitByte b 0x7F // i32
            endPatch b ts
            // function section: one function of type 0
            emitByte b 3
            let fs = beginPatch b
            emitU32 b 1
            emitU32 b 0
            endPatch b fs
            // export section: "f" -> func 0
            emitByte b 7
            let es = beginPatch b
            emitU32 b 1
            emitVec b [| byte 'f' |]
            emitByte b 0x00
            emitU32 b 0
            endPatch b es
            // code section: block (result i32) i32.const 42 br <a> end end
            emitByte b 10
            let cs = beginPatch b
            emitU32 b 1
            let body = beginPatch b
            emitU32 b 0 // no locals
            let ls = labelsNew ()
            emitByte b 0x02 // block
            emitByte b 0x7F // (result i32)
            pushLabel ls "a"
            emitByte b 0x41 // i32.const
            emitS32 b 42
            emitByte b 0x0C // br
            emitU32 b (labelDepth ls "a")
            emitByte b 0x0B // end (block)
            popLabel ls
            emitByte b 0x0B // end (function)
            endPatch b body
            endPatch b cs
            let path = System.IO.Path.GetTempFileName () + ".wasm"
            System.IO.File.WriteAllBytes (path, bytesToArray b)
            let psi = System.Diagnostics.ProcessStartInfo (wasmtime, "run --invoke f " + path)
            psi.RedirectStandardOutput <- true
            psi.RedirectStandardError <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd ()
            let err = p.StandardError.ReadToEnd ()
            p.WaitForExit ()
            System.IO.File.Delete path
            Expect.equal p.ExitCode 0 (sprintf "wasmtime failed: %s" err)
            Expect.stringContains out "42" "the module computes through the patched sizes and the br"
        }
        test "the EmitBin API builds a GC module that runs" {
            // every encoding in the SDK exercised at once: func/struct/array
            // /sub types, struct.new/get, ref.cast, ref.i31/i31.get_s, a
            // passive data segment through array.new_data (with DataCount),
            // ref.func + call_ref via the declarative elem segment, a
            // mutable global, nested labels, and a direct call. If this
            // runs, transliteration can trust the layer underneath.
            let m = modNew ()
            tyFunc m "$v1" [ "anyref" ] [ "anyref" ]
            tyStruct m "$box" [ fld true "i32" ]
            tyArray m "$bytes" "i8"
            tyStructSub m "$base" "" true [ fld true "anyref" ]
            tyStructSub m "$derived" "$base" false [ fld true "anyref"; fld true "i32" ]
            tyFunc m "$main_t" [] [ "i32" ]
            globalAnyref m "$g"
            dataSeg m "$d0" [| byte 65; byte 66; byte 67 |]
            declFn m "$twice" "$v1"
            declFn m "$main" "$main_t"
            exportFn m "f" "$main"
            // $twice: unbox i31, double, rebox
            let f1 = beginFn m [ "$x" ]
            localsDone f1
            lg f1 "$x"
            gcAbs f1 "ref.cast" "i31"
            i31get f1
            ic f1 2
            ins f1 "i32.mul"
            refI31 f1
            endFn f1
            // $main: 21*2 via call_ref of $twice + struct roundtrip + data
            let f = beginFn m []
            local f "$acc" "i32"
            local f "$s" "anyref"
            localsDone f
            // call_ref through a first-class $twice
            ic f 21
            refI31 f
            rf f "$twice"
            callRef f "$v1"
            gcAbs f "ref.cast" "i31"
            i31get f
            ls f "$acc"
            // struct roundtrip: box 5, read back, add
            ic f 5
            gcT f "struct.new" "$box"
            ls f "$s"
            lg f "$s"
            gcT f "ref.cast" "$box"
            gcTF f "struct.get" "$box" 0
            lg f "$acc"
            ins f "i32.add"
            ls f "$acc"
            // data segment: len "ABC" = 3, via array.new_data
            ic f 0
            ic f 3
            arrNewData f "$bytes" "$d0"
            gci f "array.len"
            lg f "$acc"
            ins f "i32.add"
            ls f "$acc"
            // subtype: derived through base-typed global, cast down, read field
            refNull f "any"
            ic f 9
            gcT f "struct.new" "$derived"
            gs f "$g"
            gg f "$g"
            gcT f "ref.cast" "$derived"
            gcTF f "struct.get" "$derived" 1
            lg f "$acc"
            ins f "i32.add"
            ls f "$acc"
            // labels: skip an addition through a nested br
            blockE f "$outer"
            blockE f "$inner"
            br f "$outer"
            endB f
            ic f 100
            lg f "$acc"
            ins f "i32.add"
            ls f "$acc"
            endB f
            lg f "$acc"
            endFn f
            let bytes = assemble m 1 false
            let path = System.IO.Path.GetTempFileName () + ".wasm"
            System.IO.File.WriteAllBytes (path, bytes)
            let psi = System.Diagnostics.ProcessStartInfo (wasmtime, "run -W gc=y --invoke f " + path)
            psi.RedirectStandardOutput <- true
            psi.RedirectStandardError <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd ()
            let err = p.StandardError.ReadToEnd ()
            p.WaitForExit ()
            System.IO.File.Delete path
            Expect.equal p.ExitCode 0 (sprintf "wasmtime failed: %s" err)
            // 42 + 5 + 3 + 9 = 59, and the br skipped the +100
            Expect.stringContains out "59" "GC types, casts, data, call_ref and labels all encode"
        }
    ]

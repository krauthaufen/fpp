module Fpp.Tests.EmitTests

open Expecto
open Fpp

let private wasmtime =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    home + "/.wasmtime/bin/wasmtime"

let private runProgram (src : string) : string =
    let ws = Workspace()
    ws.SetFileText "prog.fpp" src
    let wat, errors = ws.EmitProgram ()
    Expect.isEmpty errors "emission errors"
    let tmp = System.IO.Path.GetTempFileName() + ".wat"
    System.IO.File.WriteAllText(tmp, wat)
    let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "-W exceptions=y " + tmp)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd()
    let err = p.StandardError.ReadToEnd()
    p.WaitForExit()
    System.IO.File.Delete tmp
    Expect.equal p.ExitCode 0 (sprintf "wasmtime failed: %s" err)
    out

[<Tests>]
let divergenceGate =
    // Entries in DIVERGENCES.md cannot be checked by the oracle: running
    // them under dotnet fsi legitimately disagrees. They are asserted here
    // against OUR stated semantics instead.
    testList "deliberate divergences from F#" [
        test "arrays are compared by reference, not structurally" {
            // F# would print "structural" and "equal-content". An array's
            // contents may change while its identity stays the same, and
            // comparing one is O(n) hidden behind a symbol that looks free.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let a = [| 1; 2; 3 |]"
                    "let b = [| 1; 2; 3 |]"
                    "let c = a"
                    "let x = print (if a = b then \"structural\" else \"reference\")"
                    "let y = print (if a = c then \"same\" else \"different\")"
                    "let m = a.[0] <- 99"
                    "let z = print (if a = c then \"stable\" else \"changed\")"
                    "" ])
            Expect.equal out "reference\nsame\nstable\n"
                "arrays equal only themselves, and stay equal to themselves across mutation"
        }
        test "an array's hash is its length, and survives mutation" {
            // Identity equality only obliges equal values to hash equally,
            // so length is legal — and it is the one thing about an array
            // that writing to its elements cannot change.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let a = [| 1; 2; 3 |]"
                    "let b = [| 9; 9 |]"
                    "let h0 = hash a"
                    "let m = a.[0] <- 99"
                    "let r1 = print (if hash a = h0 then \"stable\" else \"CHANGED\")"
                    "let r2 = print (if hash a = hash b then \"same\" else \"by-length\")"
                    "" ])
            Expect.equal out "stable\nby-length\n"
                "an array's hash does not move when its contents do"
        }
    ]

[<Tests>]
let noBoxGate =
    testList "representation gate" [
        test "vectors and primitive arrays are flat — no generic arrays, no dispatchers" {
            // THE INVARIANT (user requirement): structs and primitives are
            // never boxed into generic arrays; there is no runtime dispatch.
            // This gate fails if either ever creeps back for typed programs.
            let ws = Workspace()
            ws.SetFileText "g.fpp"
                (String.concat "
" [
                    "module G"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let pts = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 } |]"
                    "let more = Array.create 8 { X = 0.0; Y = 0.0 }"
                    "let ints = [| 1; 2; 3 |]"
                    "let go ="
                    "    let mutable s = 0.0"
                    "    for i in 0 .. pts.Length - 1 do"
                    "        s <- s + pts.[i].X"
                    "    print s"
                    "" ])
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "emits"
            Expect.stringContains wat "array.new_fixed $pk" "V2d arrays are C-image packed"
            Expect.isFalse (wat.Contains "$sarr_V2d") "no SoA wrapper for POD structs"
            Expect.stringContains wat "array.new_fixed $parr_i" "int arrays are flat i32"
            Expect.isFalse (wat.Contains "array.new_fixed $arr ") "no generic array construction"
            Expect.isFalse (wat.Contains "$indexv") "no dispatching reader"
            Expect.isFalse (wat.Contains "$setv") "no dispatching writer"
            Expect.isFalse (wat.Contains "$creatv") "no dispatching allocator"
            // THE HOT-LOOP INVARIANT: the vector summation loop performs
            // ZERO allocations — floats live in raw f64 locals, fields
            // read directly from flat SoA arrays
            let loopStart = wat.IndexOf "(loop $cont"
            Expect.isGreaterThan loopStart 0 "loop emitted"
            let loopBody = wat.Substring(loopStart, wat.IndexOf("(br $cont", loopStart) - loopStart)
            for alloc in [ "struct.new $box"; "call $off"; "call $oss"; "call $ofl"; "struct.new $r_V2d" ] do
                Expect.isFalse (loopBody.Contains alloc) (sprintf "allocation '%s' in hot loop" alloc)
        }
    ]

[<Tests>]
let scalarizationGate =
    testList "representation gate: struct scalarization" [
        test "struct params/returns pass as scalars — zero-alloc pipeline" {
            let ws = Workspace()
            ws.SetFileText "sc.fpp"
                (String.concat "\n" [
                    "module Sc"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let dot (a : V2d) (b : V2d) = a.X * b.X + a.Y * b.Y"
                    "let scale (s : float) (v : V2d) = { X = s * v.X; Y = s * v.Y }"
                    "let lenSq (v : V2d) = dot v v"
                    "let pts = [| { X = 3.0; Y = 4.0 }; { X = 1.0; Y = 2.0 } |]"
                    "let total ="
                    "    let mutable acc = 0.0"
                    "    let mutable i = 0"
                    "    while i < pts.Length do"
                    "        acc <- acc + lenSq (scale 2.0 pts.[i])"
                    "        i <- i + 1"
                    "    acc"
                    "let a = print total"
                    "" ])
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "compiles"
            Expect.stringContains wat "(result f64 f64)" "struct return scalarized to leaves"
            Expect.stringContains wat "(param $a0_0 f64) (param $a0_1 f64)" "struct params scalarized"
            let loopStart = wat.IndexOf "(loop $cont"
            let loopBody = wat.Substring(loopStart, wat.IndexOf("(br $cont", loopStart) - loopStart)
            for alloc in [ "struct.new $box"; "struct.new $r_V2d"; "call $off"; "call $oss" ] do
                Expect.isFalse (loopBody.Contains alloc) (sprintf "allocation '%s' in scalarized pipeline" alloc)
        }
    ]

[<Tests>]
let emitTests =
    testList "wasm end-to-end" [
        test "hello and factorial" {
            let out = runProgram "module M\nlet rec fact n =\n    if n <= 1 then 1\n    else n * fact (n - 1)\nlet a = print \"Hello from F++!\"\nlet b = print (fact 10)\n"
            Expect.equal out "Hello from F++!\n3628800\n" "output"
        }
        test "DUs, closures, records, lists, equality" {
            let src =
                String.concat "\n" [
                    "module M"
                    "type Shape ="
                    "    | Dot"
                    "    | Box of int"
                    "let rec total xs ="
                    "    match xs with"
                    "    | Dot :: t -> 1 + total t"
                    "    | Box n :: t -> n + total t"
                    "    | [] -> 0"
                    "let omap f o ="
                    "    match o with"
                    "    | Some v -> Some (f v)"
                    "    | None -> None"
                    "let getOr d o ="
                    "    match o with"
                    "    | Some v -> v"
                    "    | None -> d"
                    "type Point ="
                    "    { X : int"
                    "      Y : int }"
                    "let r1 = print (total [Dot; Box 40; Dot])"
                    "let r2 = print (getOr 0 (omap (fun x -> x * 2) (Some 21)))"
                    "let p = { X = 3; Y = 4 }"
                    "let r4 = print (p.X * p.X + p.Y * p.Y)"
                    "let r6 = if [1; 2] = [1; 2] then print \"eq\" else print \"broken\""
                    "" ]
            let out = runProgram src
            Expect.equal out "42\n42\n25\neq\n" "output"
        }
        test "guards, tuples, negative ints, strings" {
            let src =
                String.concat "\n" [
                    "module M"
                    "let classify t ="
                    "    match t with"
                    "    | a, b when a > b -> \"first\""
                    "    | a, b when a < b -> \"second\""
                    "    | _ -> \"same\""
                    "let x = print (classify (2, 1))"
                    "let y = print (classify (1, 2))"
                    "let z = print (classify (3, 3))"
                    "let n = print (0 - 42)"
                    "" ]
            let out = runProgram src
            Expect.equal out "first\nsecond\nsame\n-42\n" "output"
        }
    ]

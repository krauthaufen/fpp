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
        test "a class instance has its own identity hash" {
            // wasm-GC exposes no address and no identity number of its own
            // (i31 is an immediate, not a heap reference), so the number is
            // handed out on first use and kept in the object.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type C(v : int) ="
                    "    member _.V = v"
                    "type D(v : int) ="
                    "    inherit C(v)"
                    "    member _.W = v * 2"
                    "let a = C(5)"
                    "let b = C(5)"
                    "let d = D(7)"
                    "let r1 = print (if hash a = hash a then \"stable\" else \"UNSTABLE\")"
                    "let r2 = print (if hash a = hash b then \"COLLIDE\" else \"distinct\")"
                    "let r3 = print (if hash d = hash a then \"COLLIDE\" else \"distinct\")"
                    "let m = a.V"
                    "let r4 = print (if hash a = hash a then \"stable\" else \"UNSTABLE\")"
                    "" ])
            Expect.equal out "stable\ndistinct\ndistinct\nstable\n"
                "identity is per object, stable, and survives field access"
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

[<Tests>]
let acceptanceProgressTests =
    testList "acceptance-file mechanisms" [
        test "ctor arguments widen to a declared base, in tuples too" {
            let ws = Fpp.Workspace()
            ws.SetFileText "t.fpp" (String.concat "\n" [
                "module M"
                "type Node<'K>(v : 'K) ="
                "    member x.V = v"
                "type Leaf<'K, 'V>(k : 'K, value : 'V) ="
                "    inherit Node<'K>(k)"
                "type Holder<'K, 'V>(tag : int, root : Node<'K>) ="
                "    member x.Tag = tag"
                "    member x.Root = root"
                "    static member Single(k : 'K, v : 'V) ="
                "        Holder<'K, 'V>(1, Leaf(k, v))"
                "let h = Holder<int, string>.Single(2, \"x\")"
                "let a = print h.Root.V"
                "" ])
            Expect.isEmpty (ws.Diagnostics "t.fpp") "clean"
            let _, errs = ws.EmitProgram ()
            Expect.isEmpty errs "the second tuple slot widened Leaf to Node"
        }
        test "Array.zeroCreate with an explicit struct-tuple type argument" {
            let ws = Fpp.Workspace()
            ws.SetFileText "t.fpp" (String.concat "\n" [
                "module M"
                "let xs = Array.zeroCreate<struct(int * int)> 3"
                "let ints = Array.zeroCreate<int> 4"
                "let a = print xs.Length"
                "let b = print ints.Length"
                "let c = print ints.[2]"
                "" ])
            Expect.isEmpty (ws.Diagnostics "t.fpp") "type application parses, struct included"
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "emits"
            Expect.stringContains wat "array.new_default" "zero fill is the default fill"
        }
    ]

[<Tests>]
let capturedMutableTests =
    // Closure conversion copies the environment by value, so a mutable a
    // closure WRITES to has to be a shared cell. These pin the sharing.
    testList "captured mutable locals" [
        test "a closure keeps writing the cell after the frame is gone" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let makeCounter (start : int) : unit -> int ="
                    "    let mutable n = start"
                    "    fun () ->"
                    "        n <- n + 1"
                    "        n"
                    "let c = makeCounter 10"
                    "let a1 = print (string (c ()))"
                    "let a2 = print (string (c ()))"
                    "let a3 = print (string (c ()))"
                    "" ])
            Expect.equal out "11\n12\n13\n" "the counter counts"
        }
        test "two closures share one cell" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let pair (u : unit) : (int -> unit) * (unit -> int) ="
                    "    let mutable acc = 0"
                    "    (fun k -> acc <- acc + k), (fun () -> acc)"
                    "let ps = pair ()"
                    "let r ="
                    "    match ps with"
                    "    | (add, get) ->"
                    "        add 5"
                    "        add 7"
                    "        print (string (get ()))"
                    "" ])
            Expect.equal out "12\n" "the writer and the reader see the same box"
        }
        test "a lambda handed to a higher-order function writes the frame's local" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let sumOf (xs : int list) : int ="
                    "    let mutable s = 0"
                    "    List.iter (fun x -> s <- s + x) xs"
                    "    s"
                    "let d1 = print (string (sumOf [ 1; 2; 3; 4 ]))"
                    "" ])
            Expect.equal out "10\n" "List.iter accumulates into the caller's mutable"
        }
        test "a mutable nobody captures stays a plain local" {
            // the prelude has captured mutables of its own, so the question
            // is whether THIS program adds a cell — count against a baseline
            let cells (src : string) =
                let ws = Fpp.Workspace()
                ws.SetFileText "t.fpp" src
                let wat, errs = ws.EmitProgram ()
                Expect.isEmpty errs "emits"
                wat.Split([| "struct.new $cell" |], System.StringSplitOptions.None).Length - 1
            let baseline = cells "module M\nlet z = print \"hi\"\n"
            let withLoop =
                cells (String.concat "\n" [
                    "module M"
                    "let plain (n : int) : float ="
                    "    let mutable f = 0.5"
                    "    let mutable i = 0"
                    "    while i < n do"
                    "        f <- f + 1.5"
                    "        i <- i + 1"
                    "    f"
                    "let f1 = print (string (plain 4))"
                    "" ])
            Expect.equal withLoop baseline "no cell where nothing captures"
        }
    ]

[<Tests>]
let mutualRecursionTests =
    // `and` binds a GROUP: every member's body sees every member's name, and
    // an unresolved name is not a diagnostic, so a miss here is silent until
    // emission. Local groups additionally need their knot tied at runtime —
    // each member is built over a marker standing for its siblings.
    testList "mutually recursive bindings" [
        test "a top-level let rec ... and group" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let rec even (k : int) : bool ="
                    "    if k = 0 then true else odd (k - 1)"
                    "and odd (k : int) : bool ="
                    "    if k = 0 then false else even (k - 1)"
                    "let p = print (string (even 10) + \" \" + string (odd 10))"
                    "" ])
            Expect.equal out "True False\n" "the forward reference resolves"
        }
        test "a LOCAL let rec ... and group" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let outer (n : int) : int ="
                    "    let rec even (k : int) : bool ="
                    "        if k = 0 then true else odd (k - 1)"
                    "    and odd (k : int) : bool ="
                    "        if k = 0 then false else even (k - 1)"
                    "    if even n then 1 else 0"
                    "let p = print (string (outer 10) + string (outer 7))"
                    "" ])
            Expect.equal out "10\n" "closures see each other once the knot is tied"
        }
        test "a three-member group closing over the enclosing frame" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let classify (limit : int) (start : int) : string ="
                    "    let tag = \"<\" + string limit + \">\""
                    "    let rec down (k : int) : string ="
                    "        if k <= 0 then \"done\" + tag"
                    "        elif k > limit then down (k - 1)"
                    "        else across k"
                    "    and across (k : int) : string ="
                    "        if k % 2 = 0 then up (k - 1) else down (k - 1)"
                    "    and up (k : int) : string ="
                    "        if k <= 0 then \"up\" + tag else across k"
                    "    down start"
                    "let a = print (classify 3 9)"
                    "" ])
            Expect.equal out "done<3>\n" "every member sees the others and the capture"
        }
        test "a group member used as a value, and nested groups" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let pick (n : int) : int ="
                    "    let rec f (k : int) : int = if k = 0 then 0 else g (k - 1)"
                    "    and g (k : int) : int = if k = 0 then 1 else f (k - 1)"
                    "    let apply (h : int -> int) (x : int) : int = h x"
                    "    apply f n + apply g n"
                    "let nested (n : int) : int ="
                    "    let rec outerA (k : int) : int ="
                    "        let rec innerA (j : int) : int = if j = 0 then 0 else innerB (j - 1) + 1"
                    "        and innerB (j : int) : int = if j = 0 then 100 else innerA (j - 1)"
                    "        if k = 0 then innerA 3 else outerB (k - 1)"
                    "    and outerB (k : int) : int = outerA k"
                    "    outerA n"
                    "let c = print (string (pick 4) + \" \" + string (nested 2))"
                    "" ])
            Expect.equal out "1 102\n" "a member passed as a value is the patched closure"
        }
        test "a group whose members write a captured mutable" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let counts (xs : int list) : string ="
                    "    let mutable evens = 0"
                    "    let mutable odds = 0"
                    "    let rec goE (ys : int list) : unit ="
                    "        match ys with"
                    "        | [] -> ()"
                    "        | _ :: rest ->"
                    "            evens <- evens + 1"
                    "            goO rest"
                    "    and goO (ys : int list) : unit ="
                    "        match ys with"
                    "        | [] -> ()"
                    "        | _ :: rest ->"
                    "            odds <- odds + 1"
                    "            goE rest"
                    "    goE xs"
                    "    string evens + \"/\" + string odds"
                    "let e = print (counts [ 1; 2; 3; 4; 5 ])"
                    "" ])
            Expect.equal out "3/2\n" "cells and the rec-group knot coexist"
        }
    ]

[<Tests>]
let letInScopeTests =
    testList "let ... in scoping" [
        test "the in-body sees the binding" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let f (xs : int list) : bool ="
                    "    match xs with"
                    "    | [] -> false"
                    "    | x :: _ -> (let n = x + 1 in n > 3 && n < 10)"
                    "let a = print (string (f [ 5 ]) + \" \" + string (f [ 1 ]))"
                    "" ])
            Expect.equal out "True False\n" "n is in scope after `in`"
        }
        test "an in-bound function is callable in the body" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let g (y : int) : int ="
                    "    (let h (z : int) : int = z * 2 in h y + h 1)"
                    "let b = print (string (g 5))"
                    "" ])
            Expect.equal out "12\n" "the binding, not its parameters, is what the body sees"
        }
    ]

[<Tests>]
let qualifiedCasePatternTests =
    // A qualified case in PATTERN position is named by its last segment.
    // Getting that wrong typed the pattern off the MODULE name, so the
    // payload binder had no type and everything read out of it was unknown.
    testList "qualified union-case patterns" [
        test "a qualified case pattern types its payload binder" {
            let ws = Fpp.Workspace()
            ws.SetFileText "other.fpp" (String.concat "\n" [
                "module Other"
                "type InstDef = { Head : string; Ctx : string list }"
                "type Outcome ="
                "    | Chose of InstDef"
                "    | NoneFit"
                "" ])
            ws.SetFileText "m.fpp" (String.concat "\n" [
                "module M"
                "open Other"
                "let run (o : Outcome) : int ="
                "    let mutable n = 0"
                "    match o with"
                "    | Other.Chose inst ->"
                // the loop is the witness: without the payload's type the
                // source is not known to be a list and cannot be walked
                "        for c in inst.Ctx do"
                "            n <- n + c.Length"
                "    | Other.NoneFit -> n <- -1"
                "    n"
                "let r = print (string (run (Chose { Head = \"h\"; Ctx = [ \"ab\"; \"cde\" ] })))"
                "" ])
            Expect.isEmpty (ws.Diagnostics "m.fpp") "clean"
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "emits"
            let tmp = System.IO.Path.GetTempFileName() + ".wat"
            System.IO.File.WriteAllText(tmp, wat)
            let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "-W exceptions=y " + tmp)
            psi.RedirectStandardOutput <- true
            psi.RedirectStandardError <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd()
            p.WaitForExit()
            System.IO.File.Delete tmp
            Expect.equal out "5\n" "the payload's list field is walked"
        }
        test "a qualified nullary case still matches" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Flag = | On | Off"
                    "let show (f : Flag) ="
                    "    match f with"
                    "    | M.On -> \"on\""
                    "    | M.Off -> \"off\""
                    "let a = print (show On)"
                    "let b = print (show Off)"
                    "" ])
            Expect.equal out "on\noff\n" "qualified nullary cases select correctly"
        }
    ]

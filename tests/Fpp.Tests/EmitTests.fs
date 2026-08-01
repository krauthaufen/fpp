module Fpp.Tests.EmitTests

open Expecto
open Fpp

let private wasmtime =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    home + "/.wasmtime/bin/wasmtime"

let private runProgram (src : string) : string =
    let ws = Workspace()
    ws.SetFileText "prog.fpp" src
    let bytes, errors = ws.EmitProgramWasm ()
    Expect.isEmpty errors "emission errors"
    let tmp = System.IO.Path.GetTempFileName() + ".wasm"
    System.IO.File.WriteAllBytes(tmp, bytes)
    let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "run -W gc=y,exceptions=y " + tmp)
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

/// the module DISASSEMBLED — the name section names functions and types, so
/// representation assertions read `$parr_i`, not a bare index
let private disassemble (src : string) : string =
    let ws = Workspace()
    ws.SetFileText "prog.fpp" src
    let bytes, errors = ws.EmitProgramWasm ()
    Expect.isEmpty errors "emission errors"
    let tmp = System.IO.Path.GetTempFileName() + ".wasm"
    System.IO.File.WriteAllBytes(tmp, bytes)
    let psi = System.Diagnostics.ProcessStartInfo("wasm-tools", "print " + tmp)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd()
    p.StandardError.ReadToEnd() |> ignore
    p.WaitForExit()
    System.IO.File.Delete tmp
    Expect.equal p.ExitCode 0 "wasm-tools print failed"
    out

[<Tests>]
let noBoxGate =
    testList "representation gate" [
        test "vectors and primitive arrays are packed — no per-element boxing" {
            // THE INVARIANT (user requirement): primitive and POD-struct
            // arrays are never boxed into generic arrays. Asserted against
            // the DISASSEMBLED binary module.
            let src =
                String.concat "\n" [
                    "module G"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let pts = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 } |]"
                    "let more = Array.create 8 { X = 0.0; Y = 0.0 }"
                    "let ints = [| 1; 2; 3 |]"
                    "let floats = [| 1.5; 2.5 |]"
                    "let go ="
                    "    let mutable s = 0.0"
                    "    for i in 0 .. pts.Length - 1 do"
                    "        s <- s + pts.[i].X"
                    "    print s"
                    // read every array: an unused binding whose initializer
                    // has no effect is dead, representation and all
                    "    print ints.[0]"
                    "    print more.Length"
                    "    print floats.Length"
                    "" ]
            let text = disassemble src
            // The backing store is chosen from the struct's fields: a pair of
            // doubles is backed by an f64 ARRAY, so reading a field is the
            // array.get alone. Integer words would mean a load into a general
            // register and a move across to the FPU for every field. The bytes
            // are the same either way, so the C image still holds.
            Expect.stringContains text "array.new_fixed $pf64" "V2d arrays are packed, and backed by floats"
            Expect.stringContains text "array.new_fixed $parr_i" "int arrays are flat i32"
            Expect.stringContains text "array.new_fixed $parr_f" "float arrays are flat f64"
            Expect.isFalse (text.Contains "$sarr_") "no SoA wrapper for POD structs"
            Expect.isFalse (text.Contains "$indexv") "no dispatching reader"
            Expect.isFalse (text.Contains "$setv") "no dispatching writer"
            Expect.isFalse (text.Contains "$creatv") "no dispatching allocator"
            // and the program still computes
            Expect.equal (runProgram src) "4\n1\n8\n2\n" "the packed loop sums X"
        }
        test "the hot loop allocates NOTHING — scalars ride raw rails" {
            // THE HOT-LOOP INVARIANT: summing packed struct fields performs
            // zero allocations per iteration. Rail locals box at reads and
            // unbox at writes; the emit-time peephole cancels every pair, so
            // the loop that remains is loads, adds and stores.
            let src =
                String.concat "\n" [
                    "module H"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let pts = [| { X = 3.0; Y = 4.0 }; { X = 1.0; Y = 2.0 } |]"
                    "let go ="
                    "    let mutable s = 0.0"
                    "    for i in 0 .. pts.Length - 1 do"
                    "        s <- s + pts.[i].X"
                    "    print s"
                    "" ]
            let text = disassemble src
            // find the summation loop (the one reading POD words) and walk
            // to its matching `end` by indentation
            let lines = text.Split '\n'
            let mutable loopSeg = ""
            let mutable i = 0
            while loopSeg = "" && i < lines.Length do
                if lines.[i].TrimStart().StartsWith "loop" then
                    let indent = lines.[i].Length - lines.[i].TrimStart().Length
                    let mutable j = i + 1
                    while j < lines.Length
                          && not (lines.[j].Trim() = "end"
                                  && lines.[j].Length - lines.[j].TrimStart().Length = indent) do
                        j <- j + 1
                    let seg = String.concat "\n" (Array.sub lines i (j - i + 1))
                    // the read is inline AND its base is hoisted out of the
                    // loop, so neither a call nor the handle appears in here;
                    // what remains is the load itself
                    if seg.Contains "array.get" && seg.Contains "f64.add" then loopSeg <- seg
                i <- i + 1
            Expect.isTrue (loopSeg <> "") "the summation loop is found"
            for alloc in [ "call $off"; "call $oss"; "call $ofl"; "call $ofi"
                           "struct.new $box"; "struct.new $r_V2d"; "call $addv" ] do
                Expect.isFalse (loopSeg.Contains alloc) (sprintf "'%s' in the hot loop" alloc)
            Expect.equal (runProgram src) "4\n" "and the sum is right"
        }
        test "a store into an int[] field builds a FLAT array" {
            // `r.Slots <- Array.zeroCreate n` used to build a UNIFORM array:
            // assignment did not unify through a dot target, so nothing
            // pinned the element type, and every later read cast it to
            // $parr_i and trapped. Found in the self-compile (RefMap.Clear).
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type R = { mutable Slots : int[]; mutable Count : int }"
                    "let clear (r : R) : unit ="
                    "    r.Slots <- Array.zeroCreate r.Slots.Length"
                    "    r.Count <- 0"
                    "let r : R = { Slots = Array.zeroCreate 16; Count = 3 }"
                    "let go ="
                    "    clear r"
                    "    r.Slots.[2] <- 7"
                    "    print (string (r.Slots.Length + r.Slots.[2] + r.Count))"
                    "" ])
            Expect.equal out "23\n" "the field holds a flat int array through the store"
        }
        test "`.Length` behind a parked dot is array length, not a like-named field" {
            // `(s.Substring 1).Split ':'` leaves the receiver unknown until
            // the dot fixpoint runs, so `.Length` on it resolved LATE — and
            // the late path had no array case, so it bound to whatever
            // record in scope declares a `Length`. Silently: a field WAS
            // found. This is what trapped the stage-1 compiler.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Definition = { Name : string; Offset : int; Length : int }"
                    "let f (n : string) ="
                    "    let parts = (n.Substring 1).Split ':'"
                    "    match parts.Length with"
                    "    | 3 -> 30"
                    "    | 2 -> 20"
                    "    | _ -> 0"
                    "let d = { Name = \"x\"; Offset = 0; Length = 42 }"
                    "let go ="
                    "    print (string (f \"@a:b:c\"))"
                    "    print (string d.Length)"
                    "" ])
            Expect.equal out "30\n42\n" "array length, and the record field still reads"
        }
        test "conversions FROM a string parse, and nest" {
            // `int s` fell through the conversion table's catch-all identity
            // and handed the STRING to an integer context. The nesting case
            // is the same hazard one level up: a conversion's kind is its
            // TARGET's, and reporting "u" made the outer one an identity too.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let go ="
                    "    print (string (int \"42\"))"
                    "    print (string (int \"-17\"))"
                    "    print (string (int64 \"1234567890123\" |> int))"
                    "    print (string (float \"-2.5e2\"))"
                    "    print (string (float \"1.25E-2\"))"
                    "    print (string (int (char \"A\")))"
                    "" ])
            Expect.equal out "42\n-17\n1912276171\n-250\n0.0125\n65\n"
                "each conversion parses, and the i64 wraps on the way to int"
        }
        test "byte and sbyte order as integers" {
            // `byte` was missing from the operator suffix table, so `<@byte`
            // went looking for an instance member and found the GENERATED
            // `compare` — whose body is that very comparison. It recursed
            // until the stack ran out.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let go ="
                    "    let a = byte 200"
                    "    let b = byte 100"
                    "    print (string (compare a b))"
                    "    print (string (compare b a))"
                    "    print (string (compare a a))"
                    "    print (string (int (max a b)))"
                    "    print (string (compare (sbyte -5) (sbyte 7)))"
                    "" ])
            Expect.equal out "1\n-1\n0\n200\n-1\n" "byte is unsigned, sbyte is signed, neither loops"
        }
        test "the three string literal spellings each carry their own value" {
            // every literal was unescaped as if it were `"..."`: a triple
            // quoted one kept two quotes at each end and still processed
            // backslashes, and a verbatim one kept its doubled quotes.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let a = \"\"\"x\\ny\"\"\""
                    "let b = @\"c:\\p\"\"q\""
                    "let c = \"m\\tn\""
                    "let go ="
                    "    print a"
                    "    print b"
                    "    print c"
                    "" ])
            Expect.equal out "x\\ny\nc:\\p\"q\nm\tn\n"
                "triple quoted is literal, verbatim folds \"\", ordinary escapes"
        }
        test "numeric character escapes name the character they spell" {
            // only the NAMED escapes were decoded, so `'\\000'` came out as
            // '0'. The compiler's own lexer guards end-of-input with exactly
            // that literal, so the compiler compiled its lexer into a test
            // against the digit zero — and then rejected every char literal
            // in its own sources.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let go ="
                    "    print (string (int '\\000'))"
                    "    print (string (int '\\0'))"
                    "    print (string (int '\\065'))"
                    "    print (string (int '\\x41'))"
                    "    print (string (int '\\n'))"
                    "    print \"a\\065b\""
                    "" ])
            Expect.equal out "0\n0\n65\n65\n10\naAb\n" "decimal, hex and named escapes all decode"
        }
        test "joining many pieces is not quadratic" {
            // `String.concat` folded left, so joining n chunks of total
            // length L copied O(n*L) characters. The compiler's own emitter
            // joins a six-megabyte module out of hundreds of thousands of
            // chunks: self-hosting went from not finishing in fifty minutes
            // to ninety-seven seconds when this became a pairwise merge.
            // The GATE here is the answer, not the clock — a left fold gets
            // these right too, and only the bootstrap measures the speed.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let go ="
                    "    print (String.concat \",\" [\"a\"; \"b\"; \"c\"])"
                    "    print (String.concat \"\" [\"x\"; \"y\"])"
                    "    print (String.concat \"-\" [\"solo\"])"
                    "    print (String.concat \"-\" [])"
                    "    print (String.replicate 3 \"ab\")"
                    "    print (String.init 4 (fun i -> string i))"
                    "    print (string (String.length (String.concat \"\" (List.replicate 2000 \"0123456789\"))))"
                    "" ])
            Expect.equal out "a,b,c\nxy\nsolo\n\nababab\n0123\n20000\n"
                "separators land between pieces, in order, at every arity"
        }
        test "tupled arguments are a calling convention, in all three shapes" {
            // `let f (a, b)` compiles to a two-argument function. A literal
            // call passes elements; a call with a tuple VALUE destructures
            // at the call site; a first-class use goes through a shared
            // tupled shim. Over-application (`h (a, b) extra` lowers
            // FLATTENED) must disqualify a function — binding tuple->a,
            // extra->b is how two attempts at this trapped the self-compile.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let f (a, b) = a * b + 1"
                    "let g (a, b, c) = a + b + c"
                    "let h (a, b) = fun c -> a + b + c"
                    "let go ="
                    "    let t = (3, 4)"
                    "    print (string (f (3, 4)))"
                    "    print (string (f t))"
                    "    print (string (g (1, 2, 3)))"
                    "    print (string (List.sum (List.map f [(1, 2); (3, 4)])))"
                    "    print (string (h (1, 2) 3))"
                    "" ])
            Expect.equal out "13\n13\n6\n16\n6\n"
                "literal, value, first-class and over-applied calls all agree"
        }
        test "an as-binding over an or-pattern is written by every alternative" {
            // PAs allocated a FRESH local per or-alternative and the shared
            // body read whichever compiled last, so `(A _ | B _) as x -> x`
            // returned garbage whenever an EARLIER alternative matched. In
            // the self-compile that surfaced as a cyclic expression tree
            // that sent the emitter into infinite recursion — three attempts
            // at the untupling pass were blamed for it before this repro.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type E ="
                    "    | A of int * string"
                    "    | B of int * string * bool"
                    "    | C"
                    "let keep (e : E) : E ="
                    "    match e with"
                    "    | (A (n, _) | B (n, _, _)) as it when n > 2 -> it"
                    "    | _ -> C"
                    "let show (e : E) : string ="
                    "    match e with"
                    "    | A (n, s) -> \"A\" + string n + s"
                    "    | B (n, s, b) -> \"B\" + string n + s + (if b then \"T\" else \"F\")"
                    "    | C -> \"C\""
                    "let go ="
                    "    print (show (keep (A (9, \"z\"))))"
                    "    print (show (keep (B (7, \"q\", true))))"
                    "    print (show (keep (A (1, \"x\"))))"
                    "" ])
            Expect.equal out "A9z\nB7qT\nC\n" "the first alternative binds the same slot the body reads"
        }
    ]

[<Tests>]
let scalarizationGate =
    testList "representation gate: struct scalarization" [
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
            let _, errs = ws.EmitProgramWasm ()
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
            let _, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "emits"
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
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "emits"
            let tmp = System.IO.Path.GetTempFileName() + ".wasm"
            System.IO.File.WriteAllBytes(tmp, bytes)
            let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "run -W gc=y,exceptions=y " + tmp)
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

[<Tests>]
let stringForInTests =
    // `for c in s` walks a string by index, like an array — the emitter's
    // "$str" sentinel is the marker, so no new backend machinery.
    testList "for-in over a string" [
        test "iterating a string yields its characters" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let count (s : string) : int ="
                    "    let mutable n = 0"
                    "    for c in s do"
                    "        if c = 'a' then n <- n + 1"
                    "    n"
                    "let esc (s : string) : string ="
                    "    let mutable acc = \"\""
                    "    for c in s do"
                    "        if c = '\"' then acc <- acc + \"\\\\\" + string c"
                    "        else acc <- acc + string c"
                    "    acc"
                    "let r1 = print (string (count \"banana\"))"
                    "let r2 = print (esc \"say \\\"hi\\\"\")"
                    "let r3 = print (string (count \"\"))"
                    "" ])
            Expect.equal out "3\nsay \\\"hi\\\"\n0\n" "characters in order, empty string safe"
        }
    ]

[<Tests>]
let comprehensionTests =
    // `[ for x in src -> e ]`: the loop lowers by the ordinary rules and its
    // body conses onto an accumulator, which is reversed once at the end.
    testList "list comprehensions (arrow form)" [
        test "over a range, a list, an array, and a destructuring binder" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let squares = [ for i in 1 .. 5 -> i * i ]"
                    "let r1 = print (String.concat \",\" (List.map (fun n -> string n) squares))"
                    "let xs = [ \"a\"; \"bb\"; \"ccc\" ]"
                    "let lens = [ for s in xs -> s.Length ]"
                    "let r2 = print (String.concat \",\" (List.map (fun n -> string n) lens))"
                    "let arr = [| 10; 20; 30 |]"
                    "let doubled = [ for v in arr -> v * 2 ]"
                    "let r3 = print (String.concat \",\" (List.map (fun n -> string n) doubled))"
                    "let ps = [ (1, \"x\"); (2, \"y\") ]"
                    "let names = [ for k, v in ps -> v + string k ]"
                    "let r4 = print (String.concat \",\" names)"
                    "let none = [ for i in 1 .. 0 -> i ]"
                    "let r5 = print (string (List.length none))"
                    "" ])
            Expect.equal out "1,4,9,16,25\n1,2,3\n20,40,60\nx1,y2\n0\n"
                "elements in source order"
        }
        test "a loop INSIDE the yielded expression stays an ordinary loop" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let sums = [ for i in 1 .. 3 -> (let mutable t = 0 in (for j in 1 .. i do t <- t + j); t) ]"
                    "let r = print (String.concat \",\" (List.map (fun n -> string n) sums))"
                    "" ])
            Expect.equal out "1,3,6\n" "the inner loop accumulates nothing"
        }
    ]

[<Tests>]
let wildcardRangeTests =
    testList "range loops and boxing" [
        test "for _ in 1 .. n counts without naming the counter" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let repeat (n : int) (s : string) ="
                    "    let mutable acc = \"\""
                    "    for _ in 1 .. n do"
                    "        acc <- acc + s"
                    "    acc"
                    "let r1 = print (repeat 3 \"ab\")"
                    "let r2 = print (repeat 0 \"ab\" + \"|\")"
                    "" ])
            Expect.equal out "ababab\n|\n" "the wildcard binder still drives the loop"
        }
        test "box and unbox are the identity at runtime" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let store : obj = box 41"
                    "let back = unbox<int> store"
                    "let r1 = print (string (back + 1))"
                    "let s : obj = box \"hi\""
                    "let r2 = print (unbox<string> s)"
                    "" ])
            Expect.equal out "42\nhi\n" "a value survives a round trip through obj"
        }
        test "the Option module" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let a = Option.map (fun x -> x + 1) (Some 1)"
                    "let b = Option.bind (fun x -> if x > 0 then Some (x * 2) else None) (Some 3)"
                    "let c = Option.filter (fun x -> x > 10) (Some 3)"
                    "let show (o : int option) = match o with Some v -> string v | None -> \"none\""
                    "let r = print (show a + \",\" + show b + \",\" + show c)"
                    "let d = print (string (Option.isSome (Some 1)) + \",\" + string (Option.isNone (Some 1)))"
                    "let e = print (string (Option.defaultValue 9 None) + \",\" + string (Option.defaultValue 9 (Some 4)))"
                    "" ])
            Expect.equal out "2,6,none\nTrue,False\n9,4\n" "map, bind, filter, isSome, defaultValue"
        }
    ]

[<Tests>]
let tupleSpecializationTests =
    // A tuple is a UNIFORM reference, so a generic instantiated at one shares
    // the canonical body — the same conclusion arrays reached. Before this,
    // the stamper called it "layout is not statically known": an ERROR at top
    // level, and SILENCE inside a class, where the member simply vanished
    // from the module. Both paths are pinned.
    //
    // `Slot` is layout-dependent (it holds an array of its key type), which
    // is what forces the stamper to have an opinion at all.
    let slot =
        [ "type Slot<'k, 'v> = { mutable Keys : 'k[]; mutable Vals : 'v[]; mutable N : int }"
          "let slotNew<'k, 'v> () : Slot<'k, 'v> ="
          "    { Keys = Array.zeroCreate 8; Vals = Array.zeroCreate 8; N = 0 }"
          "let slotPut (s : Slot<'k, 'v>) (k : 'k) (v : 'v) : unit ="
          "    s.Keys.[s.N] <- k"
          "    s.Vals.[s.N] <- v"
          "    s.N <- s.N + 1"
          "let slotGet (s : Slot<'k, 'v>) (k : 'k) (fallback : 'v) : 'v ="
          "    let mutable i = 0"
          "    let mutable found = fallback"
          "    while i < s.N do"
          "        if s.Keys.[i] = k then found <- s.Vals.[i]"
          "        i <- i + 1"
          "    found" ]
    testList "generics instantiated at a tuple" [
        test "top level: a tuple-keyed table round-trips" {
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ slot @
                    [ "let t : Slot<string * string, int> = slotNew ()"
                      "let a = slotPut t (\"s\", \"a\") 1"
                      "let b = slotPut t (\"s\", \"b\") 2"
                      "let r1 = print (string (slotGet t (\"s\", \"b\") -1))"
                      "let r2 = print (string (slotGet t (\"s\", \"zz\") -1))"
                      "" ]))
            Expect.equal out "2\n-1\n" "tuple keys are distinct and found"
        }
        test "class field: the members must still exist" {
            // the regression this guards is not a wrong answer but a MISSING
            // one — the class emitted nothing and every use was unbound
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ slot @
                    [ "type Db() ="
                      "    let t : Slot<string * string, int> = slotNew ()"
                      "    member _.Put (q : string) (k : string) (v : int) : unit = slotPut t (q, k) v"
                      "    member _.Get (q : string) (k : string) : int = slotGet t (q, k) -1"
                      "let db = Db()"
                      "let a = db.Put \"s\" \"a\" 7"
                      "let r1 = print (string (db.Get \"s\" \"a\"))"
                      "let r2 = print (string (db.Get \"s\" \"nope\"))"
                      "" ]))
            Expect.equal out "7\n-1\n" "the class's members are emitted and callable"
        }
        test "distinct tuple instantiations share one body without colliding" {
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ slot @
                    [ "let a : Slot<string * string, int> = slotNew ()"
                      "let b : Slot<int * bool, string> = slotNew ()"
                      "let s1 = slotPut a (\"x\", \"y\") 1"
                      "let s2 = slotPut b (2, true) \"two\""
                      "let r1 = print (string (slotGet a (\"x\", \"y\") -1))"
                      "let r2 = print (slotGet b (2, true) \"?\")"
                      "let r3 = print (slotGet b (2, false) \"absent\")"
                      "" ]))
            Expect.equal out "1\ntwo\nabsent\n" "one shared body, two independent tables"
        }
    ]

[<Tests>]
let disposalTests =
    let res =
        [ "type Res(n : int) ="
          "    member x.N = n"
          "    member x.Dispose () = printfn \"disposed %d\" n"
          "    interface IDisposable with"
          "        member x.Dispose () = x.Dispose ()" ]
    testList "try/finally and use" [
        test "the finalizer runs on both paths, and the value is the body's" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let f (bang : bool) ="
                    "    try"
                    "        if bang then failwith \"boom\""
                    "        7"
                    "    finally"
                    "        printfn \"fin\""
                    "let go ="
                    "    printfn \"got %d\" (f false)"
                    "    try f true |> ignore with Failure m -> printfn \"caught %s\" m"
                    "" ])
            Expect.equal out "fin\ngot 7\nfin\ncaught boom\n" "finalizer on the normal and the raising path"
        }
        test "use disposes at the end of the scope, and when the scope raises" {
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ res @
                    [ "let scope (bang : bool) ="
                      "    use r = Res 1"
                      "    printfn \"using %d\" r.N"
                      "    if bang then failwith \"boom\""
                      "let go ="
                      "    scope false"
                      "    try scope true with Failure m -> printfn \"caught %s\" m"
                      "" ]))
            Expect.equal out "using 1\ndisposed 1\nusing 1\ndisposed 1\ncaught boom\n"
                            "disposal on the normal and the raising path"
        }
        test "use through IDisposable dispatches on the vtable" {
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ res @
                    [ "let go ="
                      "    use d = (Res 7 :> IDisposable)"
                      "    printfn \"in scope\""
                      "" ]))
            Expect.equal out "in scope\ndisposed 7\n" "the interface's Dispose is the one called"
        }
        test "an enumerator is disposable, and a wrapper passes it on" {
            // .NET's IEnumerator<'T> inherits IDisposable and real F# leans
            // on it: `use e = xs.GetEnumerator()` is how a library walks a
            // sequence it did not build.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let walk (xs : seq<int>) ="
                    "    use e = xs.GetEnumerator ()"
                    "    let mutable s = 0"
                    "    while e.MoveNext () do s <- s + e.Current"
                    "    s"
                    "let go = printfn \"%d\" (walk (Seq.map (fun x -> x * 2) ([ 1; 2; 3 ] :> seq<int>)))"
                    "" ])
            Expect.equal out "12\n" "the built-in list iterator disposes as a no-op"
        }
        test "use on a known type with no Dispose is a diagnostic" {
            let ws = Workspace()
            ws.SetFileText "prog.fpp" (String.concat "\n" [
                "module M"
                "type Plain(n : int) ="
                "    member x.N = n"
                "let go ="
                "    use p = Plain 1"
                "    printfn \"%d\" p.N"
                "" ])
            let ds = ws.Diagnostics "prog.fpp"
            Expect.isNonEmpty ds "a type that declares no Dispose cannot be used with `use`"
        }
    ]

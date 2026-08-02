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

[<Tests>]
let computationExpressionTests =
    let optBuilder =
        // Bind/Return/ReturnFrom and NOTHING else — the shape of
        // FSharp.Data.Adaptive's AValBuilder, and the reason the rewrite
        // never emits a method the construct did not ask for
        [ "type OptionBuilder() ="
          "    member _.Bind (v : option<'a>, f : 'a -> option<'b>) : option<'b> ="
          "        match v with"
          "        | Some x -> f x"
          "        | None -> None"
          "    member _.Return (v : 'a) : option<'a> = Some v"
          "    member _.ReturnFrom (v : option<'a>) : option<'a> = v"
          "let opt = OptionBuilder()" ]
    testList "computation expressions" [
        test "yield, yield! and an implicit yield build a sequence" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let a = seq { 1; 2 }"
                    "let b ="
                    "    seq {"
                    "        yield 10"
                    "        yield! a"
                    "    }"
                    "let go = for x in b do printfn \"%d\" x"
                    "" ])
            Expect.equal out "10\n1\n2\n" "Combine and Delay compose the parts"
        }
        test "for and while are the builder's, not the language's" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let b ="
                    "    seq {"
                    "        for i in 0 .. 2 do"
                    "            yield i * 100"
                    "        let mutable k = 0"
                    "        while k < 2 do"
                    "            yield k"
                    "            k <- k + 1"
                    "    }"
                    "let go = for x in b do printfn \"%d\" x"
                    "" ])
            Expect.equal out "0\n100\n200\n0\n1\n" "For collects and While repeats a delayed body"
        }
        test "a builder with only Bind and Return needs no other method" {
            // the rewrite emits Delay, Combine and Zero only where the
            // CONSTRUCT requires them, so a bind/return chain asks for
            // nothing else
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ optBuilder @
                    [ "let add (a : option<int>) (b : option<int>) ="
                      "    opt {"
                      "        let! x = a"
                      "        let! y = b"
                      "        return x + y"
                      "    }"
                      "let out (v : option<int>) = printfn \"%d\" (match v with Some n -> n | None -> -1)"
                      "let go ="
                      "    out (add (Some 2) (Some 3))"
                      "    out (add (Some 2) None)"
                      "    out (opt { return! Some 9 })"
                      "" ]))
            Expect.equal out "5\n-1\n9\n" "Bind chains and short-circuits"
        }
        test "an if with no else is where Zero comes from" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let b (n : int) ="
                    "    seq {"
                    "        if n > 0 then yield \"pos\" else yield \"neg\""
                    "        if n = 0 then yield \"zero\""
                    "    }"
                    "let go ="
                    "    for s in b 0 do printfn \"%s\" s"
                    "    for s in b 5 do printfn \"%s\" s"
                    "" ])
            Expect.equal out "neg\nzero\npos\n" "the missing branch is Zero, not a hole"
        }
        test "the body is lazy: nothing runs until it is enumerated" {
            // Delay under Combine is what buys this. A statement AHEAD of
            // the first yield is not covered — see DIVERGENCES.md
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let noisy ="
                    "    seq {"
                    "        yield 1"
                    "        printfn \"side effect\""
                    "        yield 2"
                    "    }"
                    "let go ="
                    "    printfn \"built\""
                    "    for x in noisy do printfn \"%d\" x"
                    "" ])
            Expect.equal out "built\n1\nside effect\n2\n" "the tail runs during enumeration"
        }
        test "a brace after something that is not a name stays an argument" {
            // `test \"name\" { ... }` is a computation expression in F#, but
            // guessing that here would newly EXPOSE every construct in a
            // body the parser used to keep as token soup. The builder has
            // to be a name.
            let ws = Workspace()
            ws.SetFileText "prog.fpp" (String.concat "\n" [
                "module M"
                "type P = { X : int }"
                "let f (r : P) = r.X"
                "let go = printfn \"%d\" (f { X = 3 })"
                "" ])
            Expect.isEmpty (ws.Diagnostics "prog.fpp") "a record argument is still a record argument"
        }
    ]

[<Tests>]
let inheritedSyntaxTests =
    testList "F# syntax the library writes" [
        test "assert checks, and says so when it fails" {
            // F# elides `assert` outside DEBUG. A wasm module has no
            // debugger attached to notice the difference, so a silent
            // assertion would be worth nothing — here it is a real check.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let f (n : int) ="
                    "    assert (n > 0)"
                    "    n * 2"
                    "let g (n : int) ="
                    "    assert n > 0"
                    "    n * 3"
                    "let go ="
                    "    printfn \"%d\" (f 3)"
                    "    printfn \"%d\" (g 4)"
                    "    try printfn \"%d\" (f -1) with Failure m -> printfn \"caught %s\" m"
                    "" ])
            Expect.equal out "6\n12\ncaught assertion failed\n"
                            "the operand is a whole expression, not an application"
        }
        test "`not` with nothing to negate is the function" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let isOdd (n : int) = n % 2 = 1"
                    "let evens = List.filter (isOdd >> not) [ 1; 2; 3; 4 ]"
                    "let go = printfn \"%d\" (List.length evens)"
                    "" ])
            Expect.equal out "2\n" "`f >> not` composes with it as a value"
        }
        test "`instance` is a name as well as a declaration" {
            // F# does not reserve it, and real code binds it: `static let
            // instance = ...` is how a type holds a singleton of itself.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "class Sized<'a>"
                    "    static size : 'a -> int"
                    "instance Sized<int>"
                    "    static size _ = 4"
                    "let instance = 7"
                    "let go = printfn \"%d %d\" instance (size 1)"
                    "" ])
            Expect.equal out "7 4\n" "the keyword is contextual, the identifier is not"
        }
        test "a flexible type inside a generic argument" {
            // `aval<#seq<'T1>>` — the caret and the hash both used to glue
            // onto the angle bracket, so the argument list was never entered
            let ws = Workspace()
            ws.SetFileText "prog.fpp" (String.concat "\n" [
                "module M"
                "type Box<'a> = B of 'a"
                "let f (x : Box<#seq<int>>) = 1"
                "let inline g (a : ^T, b : ^T) : ^T = a"
                "let go = printfn \"%d\" (f (B ([ 1 ] :> seq<int>)))"
                "" ])
            Expect.isEmpty (ws.Diagnostics "prog.fpp") "flexible and statically-resolved parameters parse"
        }
        test "static let holds a value on the type" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Counter<'a>() ="
                    "    static let mutable made = 0"
                    "    member x.Bump () ="
                    "        made <- made + 1"
                    "        made"
                    "let c = Counter<int>()"
                    "let go ="
                    "    printfn \"%d\" (c.Bump ())"
                    "    printfn \"%d\" (c.Bump ())"
                    "" ])
            Expect.equal out "1\n2\n" "one cell, shared by every instance"
        }
    ]

[<Tests>]
let baseCallTests =
    testList "base member calls" [
        test "base.M() calls the base's own implementation" {
            // `base` IS the receiver — one object, not two. What the keyword
            // changes is which type the member was looked up on, so the call
            // names the base's implementation directly and never goes
            // through the vtable.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Animal(name : string) ="
                    "    member x.Name = name"
                    "    abstract member Speak : unit -> string"
                    "    default x.Speak () = \"...\""
                    "type Dog(name : string) ="
                    "    inherit Animal(name)"
                    "    override x.Speak () = \"woof\""
                    "    member x.Both () = base.Speak () + \"/\" + x.Speak ()"
                    "let go ="
                    "    let d = Dog \"rex\""
                    "    printfn \"%s\" (d.Speak ())"
                    "    printfn \"%s\" (d.Both ())"
                    "" ])
            Expect.equal out "woof\n.../woof\n" "the override is virtual, base is not"
        }
    ]

[<Tests>]
let assignmentBlockTests =
    testList "an assignment may take a block" [
        test "x <- let ... in ..." {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let f (xs : int list) ="
                    "    let mutable result = 0"
                    "    for v in xs do"
                    "        result <-"
                    "            let k = v * 2"
                    "            result + k"
                    "    result"
                    "let go = printfn \"%d\" (f [ 1; 2; 3 ])"
                    "" ])
            Expect.equal out "12\n" "the right-hand side is a whole block"
        }
    ]

[<Tests>]
let undentedClauseTests =
    testList "a clause list may undent inside brackets" [
        test "`f (x, function` puts its clauses left of the keyword" {
            // The bracket delimits the group, so the offside line is the
            // enclosing statement's and not the keyword's. This shape is
            // everywhere in real F#.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Store() ="
                    "    member x.AlterV (k : int, f : int -> int) = f k"
                    "let store = Store()"
                    "let add (value : int) ="
                    "    store.AlterV(value, function"
                    "        | 0 -> 1"
                    "        | o -> o + 1"
                    "    )"
                    "let go = printfn \"%d %d\" (add 0) (add 5)"
                    "" ])
            Expect.equal out "1 6\n" "the clauses belong to the `function`"
        }
        test "but not past a clause list that encloses it" {
            // Without a bound, the inner `match` takes the outer's last
            // clause and the outer loses it.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type T = A | C"
                    "type U = B | D"
                    "let f (x : T) (y : U) ="
                    "    (match x with"
                    "     | A -> match y with"
                    "            | B -> 1"
                    "            | D -> 2"
                    "     | C -> 3)"
                    "let go = printfn \"%d %d %d\" (f A B) (f A D) (f C B)"
                    "" ])
            Expect.equal out "1 2 3\n" "the outer clause still owns `| C`"
        }
    ]

[<Tests>]
let memberOverloadArityTests =
    let map2 =
        [ "type Map2<'K, 'V>(k : 'K, v : 'V) ="
          "    member x.Key = k"
          // the THREE-argument overload is declared FIRST, which is what
          // made the one-argument call take it
          "    member x.TryRemove (key : 'K, result : byref<Map2<'K, 'V>>, removed : byref<'V>) ="
          "        result <- x"
          "        removed <- v"
          "        true"
          "    member x.TryRemove (key : 'K) = Some v" ]
    testList "member overloads are selected by unification" [
        test "a one-argument call cannot reach a tupled member" {
            // Selection unifies each candidate against what the call asks
            // for, and undoes the attempt. What makes the answer come out
            // right here is RIGIDITY: inside `tryRemove (key : 'K) (map :
            // Map2<'K, 'V>)` the caller's own type parameters are not the
            // candidate's to choose, so a three-parameter member cannot make
            // itself fit by deciding `'K` is a tuple. The earlier structural
            // stand-in called every unresolved type a wildcard, so it fit,
            // and the overload declared first won.
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ map2 @
                    [ "module M2 ="
                      "    let tryRemove (key : 'K) (map : Map2<'K, 'V>) = map.TryRemove(key)"
                      "let go ="
                      "    let m = Map2<int, string>(1, \"one\")"
                      "    printfn \"%s\" (match M2.tryRemove 1 m with Some v -> v | None -> \"?\")"
                      "" ]))
            Expect.equal out "one\n" "the generic receiver picks the one-argument overload"
        }
        test "and the tupled call still reaches the tupled member" {
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ map2 @
                    [ "let go ="
                      "    let m = Map2<int, string>(1, \"one\")"
                      "    let mutable r = m"
                      "    let mutable s = \"\""
                      "    printfn \"%b %s\" (m.TryRemove(1, &r, &s)) s"
                      "" ]))
            Expect.equal out "true one\n" "three written arguments select the three-parameter member"
        }
    ]

[<Tests>]
let constructorSpecificityTests =
    let map3 =
        [ "type Cmp<'a>() ="
          "    member x.Tag = \"cmp\""
          "type Node<'k, 'v>(tag : string) ="
          "    member x.Tag = tag"
          // two constructors of the SAME arity: arity cannot separate them
          "type Map3<'K, 'V>(comparer : Cmp<'K>, root : Node<'K, 'V>) ="
          "    member x.Which = root.Tag"
          "    new(key : 'K, value : 'V) ="
          "        Map3<'K, 'V>(Cmp<'K>(), Node<'K, 'V>(\"from-kv\"))" ]
    testList "constructor overloads are selected by unification" [
        test "an argument whose type is still a variable does not fit a concrete parameter" {
            // Two constructors of the SAME arity, so counting settles
            // nothing. What settles it is that inside `let singleton (key :
            // 'K) (value : 'V)` the caller's type parameters are RIGID: the
            // body has to work for every instantiation, so `Cmp<'K>` cannot
            // accept `'K` however much the candidate would like it to. F#
            // rejects it for exactly this reason, which is why the two
            // compilers agree.
            let out =
                runProgram (String.concat "\n" (
                    [ "module M" ] @ map3 @
                    [ "module Map3 ="
                      "    let singleton (key : 'K) (value : 'V) = Map3<'K, 'V>(key, value)"
                      "    let raw (c : Cmp<'K>) (r : Node<'K, 'V>) = Map3<'K, 'V>(c, r)"
                      "let go ="
                      "    printfn \"%s\" (Map3.singleton 1 \"one\").Which"
                      "    printfn \"%s\" (Map3.raw (Cmp<int>()) (Node<int, string>(\"from-raw\"))).Which"
                      "    printfn \"%s\" (Map3<int, string>(3, \"three\")).Which"
                      "" ]))
            Expect.equal out "from-kv\nfrom-raw\nfrom-kv\n"
                            "generic actuals take the generic constructor, concrete ones the concrete"
        }
    ]

[<Tests>]
let overloadTrialTests =
    testList "overload trials leave no trace" [
        test "a candidate that fails does not bind what it touched" {
            // A trial unifies for REAL, so it must be undone completely —
            // including the levels it adjusted. If the losing candidate left
            // anything bound, the winner would be chosen against a type that
            // had already been narrowed by a hypothesis nobody accepted.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Box<'a>(v : 'a) ="
                    "    member x.Value = v"
                    // the first candidate is the one that must NOT stick
                    "    member x.Pick (a : Box<'a>, b : Box<'a>) = a.Value"
                    "    member x.Pick (a : 'a) = a"
                    "let outer (z : 'z) (bx : Box<'z>) ="
                    "    let one = bx.Pick z"
                    "    let two = bx.Pick (Box<'z>(z), Box<'z>(z))"
                    "    (one, two)"
                    "let go ="
                    "    let p = outer 7 (Box<int>(7))"
                    "    printfn \"%d %d\" (fst p) (snd p)"
                    "" ])
            Expect.equal out "7 7\n" "both overloads reachable from one body"
        }
    ]

[<Tests>]
let derivedOrderingTests =
    testList "a type that declares CompareTo is ordered" [
        test "comparison, sorting and the operators all reach it" {
            // F#'s `'a : comparison` is satisfied by IComparable, and
            // `Ordered<'a>` is how that constraint is spelled here — so a
            // library implementing comparison the .NET way must not also
            // have to declare an instance it never wrote. The member lifts
            // to a function of the receiver and the argument, which is
            // exactly `compare`'s shape, so nothing is synthesized.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Version(major : int, minor : int) ="
                    "    member x.Major = major"
                    "    member x.Minor = minor"
                    "    member x.CompareTo (o : Version) ="
                    "        if major <> o.Major then compare major o.Major"
                    "        else compare minor o.Minor"
                    "    interface IComparable<Version> with"
                    "        member x.CompareTo (o : Version) = x.CompareTo o"
                    "let go ="
                    "    let a = Version(1, 2)"
                    "    let b = Version(1, 9)"
                    "    printfn \"%b %b\" (a < b) (b < a)"
                    "    printfn \"%d\" (compare a b)"
                    "    printfn \"%d\" (List.head (List.sort [ b; a ])).Minor"
                    "" ])
            // `a < b` is `compare a b < 0`, which only happens for a member
            // the instance calls `compare` — naming it after the TYPE's
            // member left the raw int standing in for the boolean, and both
            // comparisons came out true
            Expect.equal out "true false\n-1\n2\n" "the operators wrap the comparison"
        }
        test "an explicit instance still wins over the derived one" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type V(n : int) ="
                    "    member x.N = n"
                    "    member x.CompareTo (o : V) = compare n o.N"
                    // reversed on purpose: if this is ignored, the sort flips
                    "instance Ordered<V>"
                    "    static compare (a : V) (b : V) = compare b.N a.N"
                    "let go = printfn \"%d\" (List.head (List.sort [ V 1; V 9 ])).N"
                    "" ])
            Expect.equal out "9\n" "what the program declares beats what it implies"
        }
    ]

[<Tests>]
let structTuplePayloadTests =
    testList "a comma pattern over a struct-tuple payload" [
        test "a union case destructures a struct tuple" {
            // A comma pattern says nothing about WHICH kind of tuple it takes
            // apart. F# reads that from what it is matched against, and this
            // was measured against it: `ValueSome (a, b)` over a struct-tuple
            // payload is allowed, and the same pattern in a `let` is not.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let pick (v : voption<struct(int * string)>) ="
                    "    match v with"
                    "    | ValueSome (a, b) -> b + string a"
                    "    | ValueNone -> \"none\""
                    "let go ="
                    "    printfn \"%s\" (pick (ValueSome (struct(7, \"x\"))))"
                    "    printfn \"%s\" (pick ValueNone)"
                    "" ])
            Expect.equal out "x7\nnone\n" "the payload is bound whole and read out"
        }
        test "but a let still refuses it, as F# does" {
            // "One tuple type is a struct tuple, the other is a reference
            // tuple". The mismatch used to be computed and DISCARDED, so the
            // binding compiled and trapped — the worst of the three outcomes.
            let ws = Workspace()
            ws.SetFileText "prog.fpp" (String.concat "\n" [
                "module M"
                "let g () = struct(2, \"y\")"
                "let go ="
                "    let (p, q) = g ()"
                "    printfn \"%d %s\" p q"
                "" ])
            Expect.isNonEmpty (ws.Diagnostics "prog.fpp") "a reference-tuple pattern does not take a struct apart"
        }
    ]

[<Tests>]
let genericValueTests =
    testList "an explicitly generic value is generic" [
        test "two instantiations of one value binding" {
            // The value restriction exists to withhold generality from a
            // binding that made no promise. `let empty<'k, 'v> : Mp<'k, 'v>`
            // makes exactly that promise, so it keeps it — F# reads it the
            // same way and calls the result a generic value.
            //
            // Without this every use shared ONE type, which is how a map
            // bound empty before a loop became tied to the map the loop read
            // from: storing a pair into it asked `'T` to become `'T * 'T`,
            // and that surfaced as an occurs check on the TUPLE, a long way
            // from the binding responsible.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Mp<'k, 'v>(n : int) ="
                    "    member x.N = n"
                    "    static member Empty : Mp<'k, 'v> = Mp<'k, 'v>(0)"
                    "module Mp ="
                    "    let empty<'k, 'v> : Mp<'k, 'v> = Mp<'k, 'v>.Empty"
                    "let a : Mp<int, string> = Mp.empty"
                    "let b : Mp<bool, int> = Mp.empty"
                    "let go = printfn \"%d %d\" a.N b.N"
                    "" ])
            Expect.equal out "0 0\n" "the two uses do not share a type"
        }
        test "a binding with no declared parameters still does not generalize" {
            // the restriction still applies where nothing was promised:
            // `let cell = ResizeArray<int>()` is one array, not one per use
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let cell = ResizeArray<int>()"
                    "let go ="
                    "    cell.Add 1"
                    "    cell.Add 2"
                    "    printfn \"%d\" cell.Count"
                    "" ])
            Expect.equal out "2\n" "one cell, shared"
        }
    ]

[<Tests>]
let structTupleExpressionTests =
    testList "a paren tuple builds the struct it is asked for" [
        test "both spellings store into one map" {
            // The mirror of the pattern rule, measured the same way: F#
            // builds a STRUCT tuple from `(a, b)` when a struct tuple is
            // what the context asks for. FSharp.Data.Adaptive relies on it —
            // `PairwiseCyclicV` writes `struct(v0, v1)` in its loop and
            // `(v0, initial)` after it, into the same map.
            //
            // The expectation has to reach the tuple from a LATER argument:
            // in `add k (a, b) m` the parameter is still a variable when the
            // tuple is typed, and only `m` says it is a struct. So the
            // application ties its RESULT to the context first — but only
            // when an argument is a tuple literal, and only if the tie
            // cannot itself fail.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Mp<'k, 'v>(n : int) ="
                    "    member x.N = n"
                    "module Mp ="
                    "    let empty<'k, 'v> : Mp<'k, 'v> = Mp<'k, 'v>(0)"
                    "    let add (k : 'k) (v : 'v) (m : Mp<'k, 'v>) : Mp<'k, 'v> = Mp<'k, 'v>(m.N + 1)"
                    "let go ="
                    "    let mutable m : Mp<int, struct(int * int)> = Mp.empty"
                    "    m <- Mp.add 1 struct(2, 3) m"
                    "    m <- Mp.add 2 (4, 5) m"
                    "    printfn \"%d\" m.N"
                    "" ])
            Expect.equal out "2\n" "the paren form reached the same map"
        }
        test "an expectation does not leak into a nested expression" {
            // it reached a constructor inside `ValueSome struct(v, C(...))`
            // and tied its result to the tuple. Consumed once, by whichever
            // node is being typed.
            let ws = Workspace()
            ws.SetFileText "prog.fpp" (String.concat "\n" [
                "module M"
                "type C<'k, 'v>(n : int) ="
                "    member x.N = n"
                "let wrap (v : 'k) (n : int) : voption<struct('k * C<'k, 'v>)> ="
                "    ValueSome struct(v, C<'k, 'v>(n))"
                "let go = printfn \"%d\" (match wrap 1 5 with ValueSome (_, c) -> c.N | ValueNone -> 0)"
                "" ])
            Expect.isEmpty (ws.Diagnostics "prog.fpp") "the constructor keeps its own result type"
        }
    ]

[<Tests>]
let dotnetNameAndOperatorTests =
    testList "the .NET name, and let-bound operators" [
        test "List<'a> is what .NET calls ResizeArray" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let swap (h : List<int>) ="
                    "    let t = h.[0]"
                    "    h.[0] <- h.[1]"
                    "    h.[1] <- t"
                    "    h.[0]"
                    "let go ="
                    "    let r = ResizeArray<int>()"
                    "    r.Add 5"
                    "    r.Add 9"
                    "    printfn \"%d\" (swap r)"
                    "" ])
            Expect.equal out "9\n" "one type under two names"
        }
        test "an extension on an abbreviation extends what it abbreviates" {
            // `type List<'T> with` adds members to ResizeArray, because that
            // is what `List` IS. Resolution is per file and cannot know —
            // the abbreviation is in another one — so the member key is
            // aligned where the project's aliases are known.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type List<'T> with"
                    "    member x.Second : 'T = x.[1]"
                    "let go ="
                    "    let r = ResizeArray<int>()"
                    "    r.Add 5"
                    "    r.Add 9"
                    "    printfn \"%d\" r.Second"
                    "" ])
            Expect.equal out "9\n" "the member is on ResizeArray"
        }
        test "a let-bound operator is a call, a class operator still dispatches" {
            // `let (+++) a b = ...` is an ordinary binding whose NAME is
            // fused, and its uses are calls. A symbol the class layer owns —
            // `/` is `Div.(/)` — keeps its dispatch, or the prelude's own
            // arithmetic starts calling declarations with no body.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let (+++) (a : int) (b : int) = a * 10 + b"
                    "let inline refequal (l : 'T) (r : 'T) ="
                    "    System.Object.ReferenceEquals(l :> obj, r :> obj)"
                    "let inline (==) (l : 'T) (r : 'T) = refequal l r"
                    "type Box(n : int) ="
                    "    member x.N = n"
                    "let go ="
                    "    printfn \"%d\" (1 +++ 2)"
                    "    printfn \"%d\" (7 / 2)"
                    "    let a = Box 1"
                    "    printfn \"%b %b\" (a == a) (a == Box 1)"
                    "" ])
            Expect.equal out "12\n3\ntrue false\n" "both kinds of operator keep working"
        }
    ]

[<Tests>]
let byrefReadTests =
    testList "reading a byref is reading what it holds" [
        test "a byref parameter reads as its value" {
            // F# dereferences a byref read silently, and the library writes
            // `let mutable initial = location`. Two positions want the CELL
            // and say so: the operand of `&`, which forwards it, and the left
            // of an assignment, which writes through it.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let bump (location : byref<int>) ="
                    "    let mutable initial = location"
                    "    initial <- initial + 1"
                    "    location <- initial"
                    "let inner (loc : byref<int>) = loc <- loc + 10"
                    "let outer (loc : byref<int>) ="
                    "    let seen = loc"
                    "    inner &loc"
                    "    seen"
                    "let go ="
                    "    let mutable n = 5"
                    "    bump &n"
                    "    printfn \"%d\" n"
                    "    let mutable m = 5"
                    "    printfn \"%d\" (outer &m)"
                    "    printfn \"%d\" m"
                    "" ])
            Expect.equal out "6\n5\n15\n" "read dereferences, & forwards, assignment writes through"
        }
        test "Interlocked.Change, as the library writes it" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let change (location : byref<int>, f : int -> int) ="
                    "    let mutable initial = location"
                    "    let mutable computed = f initial"
                    "    while Interlocked.CompareExchange(&location, computed, initial) <> initial do"
                    "        initial <- location"
                    "        computed <- f initial"
                    "    computed"
                    "let go ="
                    "    let mutable m = 3"
                    "    printfn \"%d\" (change (&m, fun v -> v * 2))"
                    "    printfn \"%d\" m"
                    "" ])
            Expect.equal out "6\n6\n" "a byref forwarded into a byref member"
        }
    ]

[<Tests>]
let nestedStructPayloadTests =
    testList "a struct payload inside a tuple pattern" [
        test "a clause matching a tuple of cases" {
            // The scrutinee is a tuple, so the expectation has to reach the
            // ELEMENTS of the clause's pattern before each case can know its
            // payload is a struct. Lowering then binds each payload whole
            // and reads its fields out, at whatever depth the case sits.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let pick (l : voption<struct(int * string)>) (r : voption<struct(int * string)>) ="
                    "    match l, r with"
                    "    | ValueNone, ValueNone -> \"none\""
                    "    | ValueSome (_, a), ValueNone -> \"left \" + a"
                    "    | ValueNone, ValueSome (_, b) -> \"right \" + b"
                    "    | ValueSome (_, a), ValueSome (_, b) -> a + b"
                    "let go ="
                    "    printfn \"%s\" (pick ValueNone ValueNone)"
                    "    printfn \"%s\" (pick (ValueSome (struct(1, \"x\"))) ValueNone)"
                    "    printfn \"%s\" (pick (ValueSome (struct(1, \"x\"))) (ValueSome (struct(2, \"y\"))))"
                    "" ])
            Expect.equal out "none\nleft x\nxy\n" "each element destructures its own payload"
        }
    ]

[<Tests>]
let lambdaParameterTests =
    testList "a lambda's parameters are tied before its body" [
        test "a pattern inside the body can tell a struct tuple apart" {
            // Otherwise the parameters are still variables while the body is
            // typed, and `match left, right with | ValueSome(_, l), ...` has
            // nothing to read the struct-ness from.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let apply (f : voption<struct(int * string)> -> voption<struct(int * string)> -> string)"
                    "          (l : voption<struct(int * string)>) (r : voption<struct(int * string)>) = f l r"
                    "let go ="
                    "    let describe ="
                    "        apply (fun left right ->"
                    "            match left, right with"
                    "            | ValueNone, ValueNone -> \"none\""
                    "            | ValueSome (_, a), ValueNone -> \"left \" + a"
                    "            | ValueNone, ValueSome (_, b) -> \"right \" + b"
                    "            | ValueSome (_, a), ValueSome (_, b) -> a + b)"
                    "    printfn \"%s\" (describe (ValueSome (struct(1, \"x\"))) ValueNone)"
                    "    printfn \"%s\" (describe ValueNone ValueNone)"
                    "" ])
            Expect.equal out "left x\nnone\n" "the expected type reaches the parameters first"
        }
    ]

[<Tests>]
let objectInitializerTests =
    testList "array elements, val storage and object initializers" [
        test "array elements are elements, not an application" {
            // Each element parses at its OWN column, so a sibling on the
            // next line is a new element. Against the enclosing context the
            // next line became an ARGUMENT of the one before — a leading
            // block comment exposed it by moving the elements right.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let sizes ="
                    "    [|"
                    "        (*  a comment  *) 7"
                    "        (*  another    *) 13"
                    "        31"
                    "    |]"
                    "let flat = [| 1; 2; 3 |]"
                    "let go = printfn \"%d %d %d\" (Array.length sizes) sizes.[1] (Array.length flat)"
                    "" ])
            Expect.equal out "3 13 3\n" "three elements, and the flat form still works"
        }
        test "a type whose storage is declared gets a primary constructor" {
            // `type E() = val mutable X : int` — F# gives it one that
            // zero-initializes; without it `E()` named a constructor nothing
            // emitted, and the type could only be built by an explicit `new`
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type E() ="
                    "    val mutable public Hash : int"
                    "let go ="
                    "    let e = E()"
                    "    e.Hash <- 5"
                    "    printfn \"%d\" e.Hash"
                    "" ])
            Expect.equal out "5\n" "built, then written"
        }
        test "new T(Prop = v, ...) sets the fields" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type E<'V>() ="
                    "    val mutable public Hash : int"
                    "    val mutable public Value : 'V"
                    "    static member New(h, v) = new E<_>(Hash = h, Value = v)"
                    "let go ="
                    "    let e = E<string>.New(3, \"x\")"
                    "    printfn \"%d %s\" e.Hash e.Value"
                    "" ])
            Expect.equal out "3 x\n" "the named pairs are field writes, not comparisons"
        }
        test "a union case applied to a comparison is still that" {
            // `LBool (b = \"1\")` looks identical to an initializer, and the
            // head is what tells them apart: a TYPE, not a case
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Lit = LBool of bool | LInt of int"
                    "let parse (b : string) = LBool (b = \"1\")"
                    "let go = printfn \"%b\" (match parse \"1\" with LBool v -> v | _ -> false)"
                    "" ])
            Expect.equal out "true\n" "the case takes the comparison's value"
        }
    ]

[<Tests>]
let outParameterOverloadTests =
    testList "an out parameter has two spellings" [
        test "TryGetTarget, both ways" {
            // .NET declares `TryGetTarget(out T)` and F# SYNTHESIZES the
            // tuple view — the prelude writes one signature, not two, and
            // both spellings come from it. FSharp.Data.Adaptive passes a
            // cell; `stdlib/dotnet.fpp` matches the tuple.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Cell(n : int) ="
                    "    member x.N = n"
                    "let go ="
                    "    let w = WeakReference<Cell>(Cell 7)"
                    "    (match w.TryGetTarget () with"
                    "     | (true, t) -> printfn \"tuple %d\" t.N"
                    "     | _ -> printfn \"none\")"
                    "    let mutable got = Cell 0"
                    "    if w.TryGetTarget(&got) then printfn \"outparam %d\" got.N"
                    "" ])
            Expect.equal out "tuple 7\noutparam 7\n" "arity picks between them"
        }
    ]

[<Tests>]
let outViewTests =
    testList "the tuple view of an out parameter is synthesized" [
        test "one declaration, both spellings" {
            // F# creates the view for every method with a trailing out
            // parameter. Declaring it twice in the prelude was doing the
            // compiler's job by hand — the library declares .NET signatures
            // and calls them either way.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "type Store() ="
                    "    let mutable v = 42"
                    "    member x.TryGet (key : int, value : byref<int>) : bool ="
                    "        if key = 0 then"
                    "            value <- v"
                    "            true"
                    "        else false"
                    "let go ="
                    "    let s = Store()"
                    "    (match s.TryGet 0 with"
                    "     | (true, n) -> printfn \"found %d\" n"
                    "     | (false, n) -> printfn \"missing %d\" n)"
                    "    (match s.TryGet 1 with"
                    "     | (true, n) -> printfn \"found %d\" n"
                    "     | (false, n) -> printfn \"missing %d\" n)"
                    "    let mutable got = 0"
                    "    printfn \"%b %d\" (s.TryGet (0, &got)) got"
                    "" ])
            Expect.equal out "found 42\nmissing 0\ntrue 42\n" "the view and the out-parameter call agree"
        }
        test "the prelude's Dictionary reads the same way" {
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let go ="
                    "    let d = Dictionary<string, int>()"
                    "    d.Add (\"a\", 1)"
                    "    (match d.TryGetValue \"a\" with"
                    "     | (true, v) -> printfn \"a=%d\" v"
                    "     | _ -> printfn \"missing\")"
                    "    let mutable v = 0"
                    "    printfn \"%b\" (d.TryGetValue (\"b\", &v))"
                    "" ])
            Expect.equal out "a=1\nfalse\n" "one declaration serves both"
        }
    ]

[<Tests>]
let refCellTests =
    testList "ref cells, and what makes a read dereference" [
        test "a ref cell reads as itself, a byref parameter as its value" {
            // F# has `byref<'T>` for a location a callee may write and
            // `Ref<'T>` for one a program passes around. wasm-GC has no
            // address of a local, so both are one cell here — and what tells
            // them apart is the DECLARATION, not the type. Keying the
            // automatic dereference on the type instead made `r.Value` read
            // through the cell twice.
            let out =
                runProgram (String.concat "\n" [
                    "module M"
                    "let fill (target : byref<int>) = target <- 42"
                    "let bump (location : byref<int>) = location <- location + 1"
                    "let go ="
                    "    let r = ref 5"
                    "    r.Value <- r.Value + 1"
                    "    printfn \"%d\" r.Value"
                    "    let cells = ref (Array.zeroCreate 3)"
                    "    cells.Value.[0] <- 7"
                    "    printfn \"%d\" cells.Value.[0]"
                    "    fill &r.Value"
                    "    printfn \"%d\" r.Value"
                    "    let mutable n = 5"
                    "    bump &n"
                    "    printfn \"%d\" n"
                    "" ])
            Expect.equal out "6\n7\n42\n6\n" "the cell keeps its identity, the parameter reads through"
        }
    ]

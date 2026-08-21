// Sequences are PULL-BASED: a combinator does no work until something
// enumerates it, and then only as much as the consumer asks for. This suite
// measures that by counting how often the SOURCE is touched — a combinator
// that materialises its input shows up as a source count of 10 where F# has 1
// or 2. Nothing here enumerates an infinite sequence, so an eager
// implementation reports a wrong COUNT rather than hanging the gate.
module Core_seqlazy

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let mutable calls = 0
let src () =
    calls <- 0
    Seq.map (fun x -> calls <- calls + 1; x) [0..9]

// ---- nothing runs until something asks -----------------------------------

let unused = src ()
test "build-runs-nothing" (calls = 0)

// ---- consumers take only what they need ----------------------------------

let s1 = src ()
let r1 = s1 |> Seq.take 2 |> Seq.toList
test "take-2" (r1 = [0;1])
test "take-2-calls" (calls = 2)

let s2 = src ()
let r2 = s2 |> Seq.head
test "head" (r2 = 0)
test "head-calls" (calls = 1)

let s3 = src ()
let r3 = s3 |> Seq.exists (fun x -> x = 2)
test "exists" r3
test "exists-calls" (calls = 3)

let s4 = src ()
let r4 = s4 |> Seq.find (fun x -> x = 1)
test "find" (r4 = 1)
test "find-calls" (calls = 2)

// ---- combinators pull, they do not materialise ---------------------------

let s5 = src ()
let r5 = s5 |> Seq.takeWhile (fun x -> x < 2) |> Seq.toList
test "takeWhile" (r5 = [0;1])
test "takeWhile-calls" (calls = 3)

let s6 = src ()
let r6 = s6 |> Seq.filter (fun x -> x % 2 = 0) |> Seq.take 2 |> Seq.toList
test "filter" (r6 = [0;2])
test "filter-calls" (calls = 3)

let s7 = src ()
let r7 = s7 |> Seq.pairwise |> Seq.take 1 |> Seq.toList
test "pairwise" (r7 = [ (0, 1) ])
test "pairwise-calls" (calls = 2)

let s8 = src ()
let r8 = s8 |> Seq.scan (+) 0 |> Seq.take 2 |> Seq.toList
test "scan" (r8 = [0; 0])
test "scan-calls" (calls = 1)

let s9 = src ()
let r9 = s9 |> Seq.distinct |> Seq.take 2 |> Seq.toList
test "distinct" (r9 = [0;1])
test "distinct-calls" (calls = 2)

let s10 = src ()
let r10 = Seq.zip s10 [ "a"; "b" ] |> Seq.toList
test "zip" (r10 = [ (0, "a"); (1, "b") ])
test "zip-calls" (calls <= 3)

let s11 = src ()
let r11 = s11 |> Seq.mapi (fun i x -> i + x) |> Seq.take 2 |> Seq.toList
test "mapi" (r11 = [0; 2])
test "mapi-calls" (calls = 2)

let s12 = src ()
let r12 = s12 |> Seq.collect (fun x -> [x; x]) |> Seq.take 3 |> Seq.toList
test "collect" (r12 = [0;0;1])
test "collect-calls" (calls = 2)

let s13 = src ()
let r13 = s13 |> Seq.skip 8 |> Seq.toList
test "skip" (r13 = [8;9])
test "skip-calls" (calls = 10)

let s14 = src ()
let r14 = s14 |> Seq.indexed |> Seq.take 2 |> Seq.toList
test "indexed" (r14 = [ (0, 0); (1, 1) ])
test "indexed-calls" (calls = 2)

let s15 = src ()
let r15 = s15 |> Seq.append [ 100 ] |> Seq.take 1 |> Seq.toList
test "append" (r15 = [100])
test "append-calls" (calls = 0)

// ---- a sequence is RE-ENUMERABLE, and re-runs its pipeline ---------------

let s16 = src ()
let a16 = s16 |> Seq.toList
let firstPass = calls
let b16 = s16 |> Seq.toList
test "re-enumerate-same" (a16 = b16)
test "re-enumerate-reruns" (calls = firstPass * 2)

// ---- unfold is lazy too --------------------------------------------------

let r17 = Seq.unfold (fun s -> if s > 100 then None else Some (s, s + 1)) 0 |> Seq.take 3 |> Seq.toList
test "unfold-take" (r17 = [0;1;2])

printfn "DONE tests=%d failures=%d" ntests failures

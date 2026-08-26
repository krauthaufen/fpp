// ARRAY BOUNDS, ported from the IndexOutOfRange cases of dotnet/fsharp's
// tests/fsharp/core/array and the Language/IndexerTests of the Conformance
// suite.
//
// An element access outside the array RAISES — it does not read whatever is
// next in memory. The cases that matter are the edges: one past the end, a
// negative index (which the check catches in the same test, because it
// compares unsigned), the empty array where EVERY index is out of range,
// and the last valid index, which must still work.
//
// This is also the suite that pins the check's VISIBILITY: it is a catchable
// exception with .NET's message, not a trap, so a program can recover from
// it — and the accesses a loop has proven in range still run unchecked, so
// the ordinary cases below have to keep answering.
//
// DROPPED: `IndexOutOfRangeException` BY TYPE (`:? IndexOutOfRangeException`
// needs the BCL hierarchy, which does not exist here — the message is what
// is checked instead), and 2D arrays.
module Core_bounds

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let oob = "Index was outside the bounds of the array."

/// what an access answers, or the message it raised
let attempt (f : unit -> int) : string =
    try string (f ()) with e -> e.Message

let a = [| 10; 20; 30 |]

// ---- in range still works ---------------------------------------------------

eq "first-element" (attempt (fun () -> a.[0])) "10"
eq "middle-element" (attempt (fun () -> a.[1])) "20"
eq "last-element" (attempt (fun () -> a.[2])) "30"
eq "computed-index" (attempt (fun () -> a.[1 + 1])) "30"

// ---- out of range raises ----------------------------------------------------

eq "one-past-the-end" (attempt (fun () -> a.[3])) oob
eq "far-past-the-end" (attempt (fun () -> a.[1000])) oob
eq "negative-index" (attempt (fun () -> a.[-1])) oob
eq "very-negative-index" (attempt (fun () -> a.[-1000])) oob

// the empty array has NO valid index
let empty : int[] = [||]
eq "empty-array-zero" (attempt (fun () -> empty.[0])) oob
eq "empty-array-negative" (attempt (fun () -> empty.[-1])) oob
eq "empty-array-length" (string empty.Length) "0"

// a one-element array: 0 works, 1 does not
let one = [| 7 |]
eq "single-valid" (attempt (fun () -> one.[0])) "7"
eq "single-past-end" (attempt (fun () -> one.[1])) oob

// ---- WRITING out of range raises too ----------------------------------------

let dst = [| 1; 2; 3 |]

let attemptWrite (i : int) (v : int) : string =
    try
        dst.[i] <- v
        "wrote"
    with e -> e.Message

eq "write-in-range" (attemptWrite 1 99) "wrote"
eq "write-took-effect" (string dst.[1]) "99"
eq "write-past-the-end" (attemptWrite 3 5) oob
eq "write-negative" (attemptWrite -1 5) oob
// a rejected write leaves the array alone
eq "rejected-write-changed-nothing" (String.concat "," (List.map string (Array.toList dst))) "1,99,3"

// ---- the exception is CATCHABLE and the program continues -------------------

let mutable recovered = 0
for i in 0 .. 4 do
    try
        recovered <- recovered + a.[i]
    with _ -> recovered <- recovered + 100

// 10 + 20 + 30, then two failures at 100 each
eq "recovers-and-continues" (string recovered) "260"

// a handler may return a default instead
let safeGet (arr : int[]) (i : int) : int =
    try arr.[i] with _ -> 0

eq "safe-get-valid" (string (safeGet a 1)) "20"
eq "safe-get-invalid" (string (safeGet a 9)) "0"
eq "safe-get-negative" (string (safeGet a -3)) "0"

// ---- loops over the whole array still answer --------------------------------
// These are the accesses the compiler PROVES in range; they must produce the
// same values a checked access would.

let mutable sum1 = 0
for i in 0 .. a.Length - 1 do sum1 <- sum1 + a.[i]
eq "counted-loop-over-length" (string sum1) "60"

let mutable sum2 = 0
for v in a do sum2 <- sum2 + v
eq "for-in-loop" (string sum2) "60"

let mutable sum3 = 0
let mutable k = 0
while k < a.Length do
    sum3 <- sum3 + a.[k]
    k <- k + 1
eq "while-over-length" (string sum3) "60"

// the empty array's loop runs zero times rather than raising
let mutable sum4 = 0
for i in 0 .. empty.Length - 1 do sum4 <- sum4 + empty.[i]
eq "counted-loop-over-empty" (string sum4) "0"

// a loop that writes every element
let filled : int[] = Array.zeroCreate 4
for i in 0 .. filled.Length - 1 do filled.[i] <- i * i
eq "counted-write-loop" (String.concat "," (List.map string (Array.toList filled))) "0,1,4,9"

// nested loops over two arrays
let rows = [| 1; 2 |]
let cols = [| 10; 20; 30 |]
let mutable pairs = 0
for i in 0 .. rows.Length - 1 do
    for j in 0 .. cols.Length - 1 do
        pairs <- pairs + rows.[i] * cols.[j]
eq "nested-counted-loops" (string pairs) "180"

// ---- a DERIVED index inside a proven loop ----------------------------------
// `a.[i - 1]` is in range wherever `a.[i]` is, as long as the counter starts
// at 1 or above: i is in [start, len), so i - k is in [start - k, len - k).
// The other direction does not hold — `a.[i + 1]` needs a tighter upper
// bound than the loop gives — so it stays checked, and still answers.

let seq5 = [| 1; 2; 3; 4; 5 |]

let mutable diffs = 0
for i in 1 .. seq5.Length - 1 do
    diffs <- diffs + (seq5.[i] - seq5.[i - 1])
eq "sliding-window" (string diffs) "4"

let mutable three = 0
for i in 2 .. seq5.Length - 1 do
    three <- three + seq5.[i] + seq5.[i - 1] + seq5.[i - 2]
eq "window-of-three" (string three) "27"

// writing through a derived index
let shifted = Array.copy seq5
for i in 1 .. shifted.Length - 1 do
    shifted.[i - 1] <- shifted.[i]
eq "shift-left" (String.concat "," (List.map string (Array.toList shifted))) "2,3,4,5,5"

// `i + 1` is still checked, and the loop that uses it stops in time
let mutable ahead = 0
for i in 0 .. seq5.Length - 2 do
    ahead <- ahead + seq5.[i + 1]
eq "look-ahead" (string ahead) "14"

// a derived index that would leave the array still raises
eq "derived-past-the-end" (attempt (fun () -> seq5.[seq5.Length - 1 + 1])) oob

// the guard that makes the rule sound: a loop starting at ZERO does NOT
// prove `a.[i - 1]`, and the first iteration raises
let mutable hits = 0
let mutable caught = 0
for i in 0 .. seq5.Length - 1 do
    try hits <- hits + seq5.[i - 1] with _ -> caught <- caught + 1
eq "zero-start-does-not-prove-minus-one" (string caught) "1"
eq "zero-start-rest-still-runs" (string hits) "10"

// ---- a PRECONDITION on a parameter ------------------------------------------
// An index that arrives as a parameter is in range only if every CALLER
// passes one — which the compiler works out across the whole program. Where
// that holds the access is free; where a caller breaks it, the access still
// raises, so both directions are pinned here.

let trio = [| 10; 20; 30 |]

let getAt (i : int) : int = trio.[i]

eq "parameter-index-valid" (string (getAt 1)) "20"
eq "parameter-index-past-end" (try string (getAt 9) with e -> e.Message) oob
eq "parameter-index-negative" (try string (getAt -1) with e -> e.Message) oob

// the midpoint of two in-range parameters is in range: the shape a binary
// search or a partition uses
let rec midSum (lo : int) (hi : int) : int =
    if lo >= hi then trio.[lo]
    else
        let m = lo + (hi - lo) / 2
        trio.[m] + midSum lo m

eq "midpoint-of-parameters" (string (midSum 0 2)) "40"

// a recursion that walks off the end still raises
let rec walkOff (i : int) (acc : int) : int =
    if i > 100 then acc else walkOff (i + 1) (acc + trio.[i])

eq "recursion-past-the-end" (try string (walkOff 0 0) with e -> e.Message) oob

// a function passed as a VALUE has no precondition: nothing constrains what
// reaches it, so the access inside is checked
let applyTo (f : int -> int) (v : int) : int = f v
eq "indirect-call-valid" (string (applyTo getAt 2)) "30"
eq "indirect-call-past-end" (try string (applyTo getAt 7) with e -> e.Message) oob

// ---- the same for STRINGS ---------------------------------------------------

let s = "abc"

let attemptChar (i : int) : string =
    try string s.[i] with e -> e.Message

eq "string-first" (attemptChar 0) "a"
eq "string-last" (attemptChar 2) "c"
eq "string-past-end" (attemptChar 3) oob
eq "string-negative" (attemptChar -1) oob
eq "empty-string" (try string ("").[0] with e -> e.Message) oob

// walking a string stays in range
let mutable chars = ""
for c in s do chars <- chars + string c
eq "for-in-string" chars "abc"

let mutable chars2 = ""
for i in 0 .. s.Length - 1 do chars2 <- chars2 + string s.[i]
eq "counted-loop-over-string" chars2 "abc"

// ---- arrays of other element kinds ------------------------------------------

let floats = [| 1.5; 2.5 |]
eq "float-array-valid" (try string floats.[1] with e -> e.Message) "2.5"
eq "float-array-past-end" (try string floats.[2] with e -> e.Message) oob

let strs = [| "x"; "y" |]
eq "string-array-valid" (try strs.[0] with e -> e.Message) "x"
eq "string-array-past-end" (try strs.[5] with e -> e.Message) oob

type Pt = { X : int; Y : int }
let pts = [| { X = 1; Y = 2 } |]
eq "record-array-valid" (try string pts.[0].X with e -> e.Message) "1"
eq "record-array-past-end" (try string pts.[1].X with e -> e.Message) oob

// an array grown by Array.append is checked at its NEW length
let grown = Array.append a [| 40 |]
eq "grown-last-valid" (try string grown.[3] with e -> e.Message) "40"
eq "grown-past-end" (try string grown.[4] with e -> e.Message) oob

printfn "DONE tests=%d failures=%d" ntests failures

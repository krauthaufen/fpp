// REFERENCE CELLS, ported from dotnet/fsharp's tests/fsharp/core/libtest
// (the `ref`/`!`/`:=` cases) and core/ref-ops-deprecation.
//
// A ref cell is a one-field mutable record with four spellings for the same
// thing: `!r` and `r.Value` and `r.contents` read it, `r := v` and the two
// assignments write it. What matters is that they are the SAME location — a
// write through any spelling is visible through all of them — and that a
// cell is a VALUE: passing it around aliases the location, copying the
// binding does not copy the cell.
//
// DROPPED: `Ref.value` (modern FSharp.Core no longer has it), byref
// parameters (their own aliasing rules, and `&x` has its own gate), and the
// deprecation WARNINGS the original suite asserts — warning text is not
// behaviour.
module Core_refcells

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

// ---- the four spellings are one location -----------------------------------

let r = ref 0

eq "initial-deref" (string !r) "0"
eq "initial-value" (string r.Value) "0"
eq "initial-contents" (string r.contents) "0"

r := 5
eq "after-assign-deref" (string !r) "5"
eq "after-assign-value" (string r.Value) "5"
eq "after-assign-contents" (string r.contents) "5"

r.Value <- 6
eq "after-value-write" (string !r) "6"

r.contents <- 7
eq "after-contents-write" (string !r) "7"
eq "after-contents-write-value" (string r.Value) "7"

// ---- incr and decr ----------------------------------------------------------

let counter = ref 10
incr counter
eq "incr-once" (string !counter) "11"
incr counter
incr counter
eq "incr-thrice" (string !counter) "13"
decr counter
eq "decr-once" (string !counter) "12"
decr counter
decr counter
decr counter
eq "decr-past-start" (string !counter) "9"

// incr from zero and below
let z = ref 0
decr z
eq "decr-below-zero" (string !z) "-1"
incr z
incr z
eq "incr-back-up" (string !z) "1"

// ---- a cell is a VALUE that aliases its location ----------------------------

// passing the cell into a function reaches the SAME location
let bumpBy (n : int) (c : int ref) : unit = c := !c + n

let shared = ref 100
bumpBy 5 shared
eq "written-through-a-function" (string !shared) "105"

// binding the cell to another name does not copy it
let alias = shared
alias := 1
eq "alias-writes-through" (string !shared) "1"
eq "alias-reads-through" (string !alias) "1"

// but `ref !r` makes a NEW cell
let copied = ref !shared
copied := 42
eq "copy-is-independent" (string !shared) "1"
eq "copy-has-its-own" (string !copied) "42"

// a cell in a LIST is still one location per element
let cells = [ ref 1; ref 2; ref 3 ]
for c in cells do c := !c * 10
eq "cells-in-a-list" (String.concat "," (List.map (fun (c : int ref) -> string !c) cells)) "10,20,30"

// the same cell twice in a list is ONE location
let one = ref 0
let twice = [ one; one ]
for c in twice do incr c
eq "same-cell-twice" (string !one) "2"

// ---- cells of other types ---------------------------------------------------

let sr = ref "a"
sr := !sr + "b"
eq "string-cell" !sr "ab"

let lr = ref ([] : int list)
lr := 1 :: !lr
lr := 2 :: !lr
eq "list-cell" (String.concat "," (List.map (fun (v : int) -> string v) !lr)) "2,1"

let br = ref false
br := not !br
test "bool-cell" !br

let fr = ref 1.5
fr := !fr * 2.0
eq "float-cell" (string !fr) "3"

type Pt = { X : int; Y : int }
let pr = ref { X = 1; Y = 2 }
pr := { X = 3; Y = 4 }
eq "record-cell" (string (!pr).X + "," + string (!pr).Y) "3,4"

// a cell holding an OPTION, read through the option's own members
let orr = ref (Some 5)
test "option-cell-is-some" (!orr).IsSome
orr := None
test "option-cell-is-none" (!orr).IsNone

// a cell of a CELL
let nested = ref (ref 7)
eq "nested-cell" (string !(!nested)) "7"
(!nested) := 8
eq "nested-cell-write" (string !(!nested)) "8"

// ---- cells as accumulators --------------------------------------------------

// the shape the original suite leans on: a cell threaded through a fold
let total = ref 0
for v in [ 1; 2; 3; 4 ] do total := !total + v
eq "accumulated-in-a-loop" (string !total) "10"

let collected = ref ([] : string list)
List.iter (fun (v : int) -> collected := string v :: !collected) [ 1; 2 ]
eq "collected-in-iter" (String.concat "," !collected) "2,1"

// a cell captured by a CLOSURE outlives the call that made it
let makeCounter () : (unit -> int) =
    let n = ref 0
    fun () ->
        incr n
        !n

let next = makeCounter ()
eq "closure-cell-first" (string (next ())) "1"
eq "closure-cell-second" (string (next ())) "2"
eq "closure-cell-third" (string (next ())) "3"

// two counters have two cells
let other = makeCounter ()
eq "second-counter-is-fresh" (string (other ())) "1"
eq "first-counter-continues" (string (next ())) "4"

// ---- a cell inside a data structure -----------------------------------------

type Node = { Name : string; Hits : int ref }

let nodes = [ { Name = "a"; Hits = ref 0 }; { Name = "b"; Hits = ref 0 } ]
for nd in nodes do incr nd.Hits
incr (List.head nodes).Hits

eq "cell-in-a-record" (String.concat "," (List.map (fun (nd : Node) -> string !nd.Hits) nodes)) "2,1"

// ---- equality and printing --------------------------------------------------

// a ref cell compares by CONTENTS in F#
test "cells-with-equal-contents" (ref 1 = ref 1)
test "cells-with-different-contents" (ref 1 <> ref 2)

let printed = ref 3
eq "printed-value" (string !printed) "3"

printfn "DONE tests=%d failures=%d" ntests failures

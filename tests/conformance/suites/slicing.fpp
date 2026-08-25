// SLICING, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Language/SlicingTests and the
// GetSlice cases of Conformance/Expressions.
//
// `a.[lo..hi]` is INCLUSIVE at both ends and yields a fresh value, so the
// cases that matter are the edges: an open end takes the rest, a reversed
// range is empty rather than an error, a full slice is a COPY (writing the
// slice must not reach the source), and a one-element range is not empty.
//
// DROPPED: list slicing (`l.[1..2]`), which is not supported — see
// tests/known-issues/list-slicing.fpp — and 2D array slices.
module Core_slicing

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

let a = [| 1; 2; 3; 4; 5 |]

// ---- array slices ----------------------------------------------------------

test "closed-range" (Array.toList a.[1..3] = [ 2; 3; 4 ])
test "open-upper" (Array.toList a.[3..] = [ 4; 5 ])
test "open-lower" (Array.toList a.[..1] = [ 1; 2 ])
test "whole-by-star" (Array.toList a.[*] = [ 1; 2; 3; 4; 5 ])
test "whole-by-range" (Array.toList a.[0..4] = [ 1; 2; 3; 4; 5 ])
test "single-element" (Array.toList a.[2..2] = [ 3 ])
test "reversed-is-empty" (Array.length a.[3..1] = 0)
test "empty-at-start" (Array.length a.[0 .. 0 - 1] = 0)
test "length-of-slice" (Array.length a.[1..3] = 3)
test "sum-of-slice" (Array.sum a.[1..3] = 9)

// a slice is a COPY: writing it leaves the source alone
let copy = a.[1..3]
copy.[0] <- 99
test "slice-is-a-copy" (a.[1] = 2 && copy.[0] = 99)

// slicing a slice
test "slice-of-slice" (Array.toList (a.[1..4].[1..2]) = [ 3; 4 ])

// the source can be any array expression
test "slice-of-expression" (Array.toList ((Array.map (fun v -> v * 2) a).[0..1]) = [ 2; 4 ])
test "slice-of-literal" (Array.toList ([| 9; 8; 7 |].[1..]) = [ 8; 7 ])

// ---- slice ASSIGNMENT -------------------------------------------------------

let dst = [| 0; 0; 0; 0; 0 |]
dst.[1..3] <- [| 7; 8; 9 |]
test "slice-write" (Array.toList dst = [ 0; 7; 8; 9; 0 ])

let dst2 = [| 1; 2; 3 |]
dst2.[0..0] <- [| 5 |]
test "slice-write-single" (Array.toList dst2 = [ 5; 2; 3 ])

// ---- string slices ----------------------------------------------------------

let s = "hello"

eq "string-closed" s.[1..3] "ell"
eq "string-open-upper" s.[3..] "lo"
eq "string-open-lower" s.[..1] "he"
eq "string-whole" s.[0..4] "hello"
eq "string-single" s.[0..0] "h"
eq "string-reversed-is-empty" s.[3..1] ""
eq "string-of-expression" ("ab" + "cd").[1..2] "bc"
test "string-slice-length" (s.[1..3].Length = 3)

// a slice of a slice, and a slice used as a value
eq "string-slice-of-slice" (s.[1..4].[0..1]) "el"
eq "string-slice-concat" (s.[0..1] + s.[3..4]) "helo"

// ---- slices in expressions --------------------------------------------------

test "slice-in-fold" (Array.fold (fun acc v -> acc + v) 0 a.[0..2] = 6)
test "slice-in-map" (Array.toList (Array.map (fun v -> v + 1) a.[3..]) = [ 5; 6 ])
// arrays compare by REFERENCE here (a chosen divergence, see DIVERGENCES.md),
// so a slice is compared through its elements
test "slice-compared" (Array.toList a.[1..2] = [ 2; 3 ])

let takeFirst (n : int) (xs : int[]) : int[] = if n <= 0 then [||] else xs.[0 .. n - 1]
test "slice-in-function" (Array.toList (takeFirst 2 a) = [ 1; 2 ])
test "slice-in-function-zero" (Array.length (takeFirst 0 a) = 0)

// bounds computed at run time
let lo = 1
let hi = 3
test "computed-bounds" (Array.toList a.[lo..hi] = [ 2; 3; 4 ])
test "computed-bounds-expression" (Array.toList a.[lo + 1 .. hi] = [ 3; 4 ])

printfn "DONE tests=%d failures=%d" ntests failures

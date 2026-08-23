// FLOAT32 as its OWN value set, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Expressions/
// ConstantExpressions (float32.fs, single.fs) and the Single cases of the
// FSharp.Core primitive tests.
//
// A float32 is NOT a double: every operation answers the single-precision
// result, and the printed form carries the digits a single round-trips
// through — nine at most. Both show up here as ordinary value checks:
// `0.1f + 0.2f = 0.3f` is TRUE for singles and false for doubles, and
// `string (1.0f/3.0f)` is "0.33333334" rather than the double's digits.
//
// DROPPED: Single.MaxValue/Epsilon (no System.Single here — the extremes are
// spelled as literals) and float32 formatting with an explicit precision,
// which follows the double path.
module Core_float32

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

// ---- arithmetic rounds to SINGLE at every step ---------------------------

test "add-rounds" (0.1f + 0.2f = 0.3f)
test "double-does-not" (0.1 + 0.2 <> 0.3)
test "sub" (1.0f - 0.9f <> 0.1f)
test "mul" (1.1f * 1.1f = 1.21f)
test "div" (1.0f / 3.0f * 3.0f = 1.0f)
test "sqrt" (sqrt 2.0f * sqrt 2.0f = 1.9999999f)

// the value a float32 carries is exactly what a single can hold
test "third-widened" (float (1.0f / 3.0f) = 0.3333333432674408)
test "tenth-widened" (float 0.1f = 0.10000000149011612)

// ---- comparisons ----------------------------------------------------------

test "lt" (1.0f < 1.0000001f)
test "eq" (2.5f = 2.5f)
test "ne" (2.5f <> 2.5000002f)
test "compare" (compare 1.0f 2.0f < 0)
test "sort" (List.sort [ 2.0f; 1.0f ] = [ 1.0f; 2.0f ])
test "min-max" (min 1.0f 2.0f = 1.0f && max 1.0f 2.0f = 2.0f)

// ---- printing is SINGLE round-trip ---------------------------------------

eq "string-third" (string (1.0f / 3.0f)) "0.33333334"
eq "string-tenth" (string 0.1f) "0.1"
eq "string-one" (string 1.0f) "1"
eq "string-negative" (string -2.5f) "-2.5"
eq "string-big" (string 1e20f) "1E+20"
eq "string-small" (string 1e-7f) "1E-07"
eq "string-boundary-fixed" (string 1e8f) "100000000"
eq "string-boundary-exponent" (string 1e9f) "1E+09"
eq "string-div" (string (1.0f / 7.0f)) "0.14285715"
eq "string-sqrt" (string (sqrt 2.0f)) "1.4142135"

// the non-finite values
eq "string-nan" (string (0.0f / 0.0f)) "NaN"
eq "string-infinity" (string (1.0f / 0.0f)) "Infinity"
eq "string-neg-infinity" (string (-1.0f / 0.0f)) "-Infinity"

// `%A` spells ten digits and the `f` suffix
eq "showa" (sprintf "%A" (1.0f / 3.0f)) "0.3333333433f"
eq "showa-whole" (sprintf "%A" 1.0f) "1.0f"

// `%f` and `%g` take a float32 as readily as a float
eq "printf-f" (sprintf "%f" (1.0f / 3.0f)) "0.333333"
eq "printf-g" (sprintf "%g" (1.0f / 3.0f)) "0.333333"

// ---- conversions both ways ------------------------------------------------

test "of-int" (float32 7 = 7.0f)
test "of-int64" (float32 3L = 3.0f)
test "of-float" (float32 1.5 = 1.5f)
test "of-float-rounds" (float32 0.1 = 0.1f)
test "to-int" (int 2.9f = 2)
test "to-int64" (int64 2.9f = 2L)
test "to-float" (float 1.5f = 1.5)
eq "parse" (string (float32 "0.1")) "0.1"
eq "parse-exponent" (string (float32 "1e-7")) "1E-07"

// a double that is NOT representable as a single rounds when narrowed
test "narrowing-loses" (float (float32 0.1) <> 0.1)
test "narrowing-is-idempotent" (float32 (float (float32 0.1)) = 0.1f)

// ---- float32 in containers ------------------------------------------------

let arr = [| 1.5f; 2.5f; 3.5f |]
test "array-read" (arr.[1] = 2.5f)
test "array-sum" (Array.sum arr = 7.5f)
test "array-map" (Array.toList (Array.map (fun (v : float32) -> v * 2.0f) arr) = [ 3.0f; 5.0f; 7.0f ])

// an array element keeps SINGLE precision through a store and a read
let acc = [| 0.0f |]
acc.[0] <- 0.1f
acc.[0] <- acc.[0] + 0.2f
test "array-element-rounds" (acc.[0] = 0.3f)

let lst = [ 1.5f; 2.5f ]
test "list" (List.sum lst = 4.0f)

type Vertex = { X : float32; Y : float32 }
let v = { X = 0.1f; Y = 0.2f }
test "record-field" (v.X = 0.1f)
test "record-field-arithmetic" (v.X + v.Y = 0.3f)
test "record-equality" (v = { X = 0.1f; Y = 0.2f })

test "tuple" (fst (1.5f, 2) = 1.5f)
test "option" ((Some 1.5f) = Some 1.5f)

// ---- a float32 through a function boundary --------------------------------

let scale (k : float32) (v : float32) : float32 = k * v
test "through-call" (scale 0.1f 3.0f = 0.3f * 1.0f)
test "through-call-rounds" (scale 1.0f (0.1f + 0.2f) = 0.3f)

let mutable total = 0.0f
for i in 1 .. 10 do
    total <- total + 0.1f
test "loop-accumulates-in-single" (total = 1.0000001f)

printfn "DONE tests=%d failures=%d" ntests failures

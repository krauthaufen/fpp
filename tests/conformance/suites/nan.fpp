// Ported from dotnet/fsharp tests/fsharp/core/libtest/test.fsx — the DoubleNaN
// and SingleNaN modules — into the common F#/F++ subset. Test NAMES are the
// originals.
//
// The point: IEEE says every relational operator on NaN is FALSE, but F#'s
// structural `compare` is a total order — it calls NaN equal to itself and
// less than every other value, so sorting and Map keys stay well defined.
// The two rules disagree on purpose, and both have to hold at once.
//
// DROPPED: the DoubleNaNNonStructuralComparison modules (they re-run the same
// checks under `open NonStructuralComparison`, which is not in the subset);
// (the two generic relations — equality, IEEE on floats, and comparison, a
// total order with NaN lowest — are separate here as they are in F#, so both
// sets of checks below hold at once).
module Core_nan

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// not literals: a value the optimizer cannot fold away, as upstream does
// with a ref cell
let nan1 = (let r = ref nan in (if sprintf "Hello" = "Hello" then r.Value else 0.0))
let nan2 = (let r = ref nan in (if sprintf "Hello" = "Hello" then r.Value else 0.0))
let posInf = infinity
let negInf = 0.0 - infinity

// ---- relational operators: every one is FALSE on NaN --------------------

test "d3wiojd30a" ((nan > nan) = false)
test "d3wiojd30a2" ((if (nan > nan) then "a" else "b") = "b")
test "d3wiojd30b" ((nan >= nan) = false)
test "d3wiojd30b2" ((if (nan >= nan) then "a" else "b") = "b")
test "d3wiojd30c" ((nan < nan) = false)
test "d3wiojd30c2" ((if (nan < nan) then "a" else "b") = "b")
test "d3wiojd30d" ((nan <= nan) = false)
test "d3wiojd30d2" ((if (nan <= nan) then "a" else "b") = "b")
test "d3wiojd30e" ((nan = nan) = false)
test "d3wiojd30e2" ((if (nan = nan) then "a" else "b") = "b")
test "d3wiojd30q" ((nan <> nan) = true)
test "d3wiojd30w" ((nan > 1.0) = false)
test "d3wiojd30e3" ((nan >= 1.0) = false)
test "d3wiojd30r" ((nan < 1.0) = false)
test "d3wiojd30t" ((nan <= 1.0) = false)
test "d3wiojd30y" ((nan = 1.0) = false)
test "d3wiojd30u" ((nan <> 1.0) = true)
test "d3wiojd30i" ((1.0 > nan) = false)
test "d3wiojd30o" ((1.0 >= nan) = false)
test "d3wiojd30p" ((1.0 < nan) = false)
test "d3wiojd30a3" ((1.0 <= nan) = false)
test "d3wiojd30s" ((1.0 = nan) = false)
test "d3wiojd30d3" ((1.0 <> nan) = true)

// the same through VALUES rather than the literal
test "d3wiojd30a4" ((nan1 > nan) = false)
test "d3wiojd30b3" ((nan1 >= nan2) = false)
test "d3wiojd30c3" ((nan1 < nan2) = false)
test "d3wiojd30d4" ((nan1 <= nan2) = false)
test "d3wiojd30e4" ((nan1 = nan2) = false)
test "d3wiojd30q2" ((nan1 <> nan2) = true)
test "d3wiojd30w2" ((nan1 > 1.0) = false)
test "d3wiojd30e5" ((nan1 >= 1.0) = false)
test "d3wiojd30r2" ((nan1 < 1.0) = false)
test "d3wiojd30t2" ((nan1 <= 1.0) = false)
test "d3wiojd30y2" ((nan1 = 1.0) = false)
test "d3wiojd30u2" ((nan1 <> 1.0) = true)
test "d3wiojd30i2" ((1.0 > nan2) = false)
test "d3wiojd30o2" ((1.0 >= nan2) = false)
test "d3wiojd30p2" ((1.0 < nan2) = false)
test "d3wiojd30a5" ((1.0 <= nan2) = false)
test "d3wiojd30s2" ((1.0 = nan2) = false)
test "d3wiojd30d5" ((1.0 <> nan2) = true)

// ---- infinities are ordinary ordered values -----------------------------

test "d3wiojd30f" ((negInf = negInf) = true)
test "d3wiojd30g" ((negInf < posInf) = true)
test "d3wiojd30h" ((negInf > posInf) = false)
test "d3wiojd30j" ((negInf <= negInf) = true)

// ---- structural compare: a TOTAL order, NaN lowest ----------------------

test "D1nancompare01" (0 = compare nan nan)
test "D1nancompare02" (0 = compare nan nan1)
test "D1nancompare03" (0 = compare nan1 nan)
test "D1nancompare04" (0 = compare nan1 nan1)
test "D1nancompare05" (1 = compare 1. nan)
test "D1nancompare06" (1 = compare 0. nan)
test "D1nancompare07" (1 = compare (0.0 - 1.) nan)
test "D1nancompare08" (1 = compare negInf nan)
test "D1nancompare09" (1 = compare posInf nan)
test "D1nancompare10" (1 = compare System.Double.MaxValue nan)
test "D1nancompare11" (1 = compare System.Double.MinValue nan)
test "D1nancompare12" (-1 = compare nan 1.)
test "D1nancompare13" (-1 = compare nan 0.)
test "D1nancompare14" (-1 = compare nan (0.0 - 1.))
test "D1nancompare15" (-1 = compare nan negInf)
test "D1nancompare16" (-1 = compare nan posInf)
test "D1nancompare17" (-1 = compare nan System.Double.MaxValue)
test "D1nancompare18" (-1 = compare nan System.Double.MinValue)

// ---- what the total order is FOR ----------------------------------------

// the sorted list is compared with COMPARE, not `=`: structural EQUALITY on
// a float is IEEE, so `[nan] = [nan]` is false however well sorted it is
test "nan-sort" (compare (List.sort [ 1.0; nan; 0.0 ]) [ nan; 0.0; 1.0 ] = 0)
// float `min`/`max` PROPAGATE NaN, in either argument order (F# lowers them
// to Math.Min/Math.Max) — neither the IEEE `<` rule nor the structural order
// would give this on its own
test "nan-min" (System.Double.IsNaN (min nan 1.0))
test "nan-min-rev" (System.Double.IsNaN (min 1.0 nan))
test "nan-max" (System.Double.IsNaN (max nan 1.0))
test "nan-max-rev" (System.Double.IsNaN (max 1.0 nan))
test "nan-contains" (List.exists (fun x -> System.Double.IsNaN x) [ 1.0; nan ])
// equality and comparison DISAGREE here, and that is the point: `=` is IEEE
// all the way down, `compare` is the total order all the way down
test "nan-structural-eq" (([ nan ] = [ nan ]) = false)
test "nan-in-tuple" (((1.0, nan) = (1.0, nan)) = false)
test "nan-in-option" ((Some nan = Some nan) = false)
test "nan-compare-list" (compare [ nan ] [ nan ] = 0)
test "nan-compare-tuple" (compare (1.0, nan) (1.0, nan) = 0)

// ---- float32 ------------------------------------------------------------

let nanF : float32 = nanf
test "S1nan-gt" ((nanF > nanF) = false)
test "S1nan-eq" ((nanF = nanF) = false)
test "S1nan-neq" ((nanF <> nanF) = true)
test "S1nancompare01" (0 = compare nanF nanF)
test "S1nancompare05" (1 = compare 1.0f nanF)
test "S1nancompare12" (-1 = compare nanF 1.0f)

printfn "DONE tests=%d failures=%d" ntests failures

// THE MATH OPERATORS AND FUNCTIONS, ported from dotnet/fsharp's
// tests/FSharp.Core.UnitTests/FSharp.Core/OperatorsModule (Operators.Math,
// OperatorsModule1/2) and the arithmetic cases of Conformance/Expressions.
//
// The cases that matter are the ones where a rounding rule or a sign
// convention decides the answer: `round` goes to EVEN on a tie, `truncate`
// goes toward zero (so it is not `floor` for negatives), integer division
// truncates rather than floors, and `%` takes the sign of the DIVIDEND.
// Each is checked as a value, so a wrong convention is a wrong number.
//
// DROPPED: `Math.Round(x, digits)` and the decimal overloads, and the
// hyperbolic functions (no bit-exact reference here for them).
module Core_mathfns

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// a comparison that tolerates the last bits, for the transcendental cases
let near (name : string) (got : float) (want : float) : unit =
    ntests <- ntests + 1
    let d = if got > want then got - want else want - got
    if not (d < 1e-9) then
        failures <- failures + 1
        printfn "NO: %s" name

// ---- abs / sign -----------------------------------------------------------

test "abs-int" (abs 5 = 5 && abs (0 - 5) = 5)
test "abs-zero" (abs 0 = 0)
test "abs-float" (abs 2.5 = 2.5 && abs (0.0 - 2.5) = 2.5)
test "abs-int64" (abs (0L - 7L) = 7L)
test "sign-int" (sign 5 = 1 && sign (0 - 5) = 0 - 1 && sign 0 = 0)
test "sign-float" (sign 2.5 = 1 && sign (0.0 - 2.5) = 0 - 1 && sign 0.0 = 0)

// ---- rounding: four rules that disagree -----------------------------------

test "floor" (floor 2.7 = 2.0 && floor 2.0 = 2.0)
test "floor-negative" (floor (0.0 - 2.1) = 0.0 - 3.0)
test "ceil" (ceil 2.1 = 3.0 && ceil 2.0 = 2.0)
test "ceil-negative" (ceil (0.0 - 2.7) = 0.0 - 2.0)
test "truncate" (truncate 2.7 = 2.0)
test "truncate-negative-is-toward-zero" (truncate (0.0 - 2.7) = 0.0 - 2.0)
test "round" (round 2.4 = 2.0 && round 2.6 = 3.0)

// a TIE rounds to the even neighbour, not away from zero
test "round-half-to-even-up" (round 2.5 = 2.0)
test "round-half-to-even-down" (round 3.5 = 4.0)
test "round-half-negative" (round (0.0 - 2.5) = 0.0 - 2.0)

// ---- integer division and remainder ---------------------------------------

test "div-truncates" (7 / 2 = 3)
test "div-negative-truncates-toward-zero" ((0 - 7) / 2 = 0 - 3)
test "mod-sign-follows-dividend" ((0 - 7) % 2 = 0 - 1)
test "mod-positive" (7 % 2 = 1)
test "mod-divides-evenly" (8 % 4 = 0)
test "divmod-identity" (let a = 0 - 7 in let b = 2 in (a / b) * b + (a % b) = a)
test "float-div" (7.0 / 2.0 = 3.5)
test "float-mod" (7.5 % 2.0 = 1.5)

// ---- powers and roots ------------------------------------------------------

test "pown" (pown 2 10 = 1024)
test "pown-zero" (pown 2 0 = 1)
test "pown-negative-base" (pown (0 - 2) 3 = 0 - 8)
test "pown-float" (pown 2.0 3 = 8.0)
test "power-operator" (2.0 ** 10.0 = 1024.0)
test "power-fractional" (4.0 ** 0.5 = 2.0)
test "sqrt" (sqrt 9.0 = 3.0 && sqrt 0.0 = 0.0)
near "sqrt-two-squared" (sqrt 2.0 * sqrt 2.0) 2.0

// ---- exp / log -------------------------------------------------------------

test "log-one" (log 1.0 = 0.0)
near "exp-log" (log (exp 1.0)) 1.0
near "log-e" (log 2.718281828459045) 1.0
near "log10" (log10 1000.0) 3.0
near "exp-zero" (exp 0.0) 1.0

// ---- trigonometry ----------------------------------------------------------

test "sin-zero" (sin 0.0 = 0.0)
test "cos-zero" (cos 0.0 = 1.0)
test "tan-zero" (tan 0.0 = 0.0)
near "sin-squared-plus-cos-squared" (sin 1.0 * sin 1.0 + cos 1.0 * cos 1.0) 1.0
near "atan-one-times-four" (atan 1.0 * 4.0) 3.141592653589793
near "asin-one" (asin 1.0 * 2.0) 3.141592653589793
near "acos-one" (acos 1.0) 0.0
near "atan2" (atan2 1.0 1.0 * 4.0) 3.141592653589793

// ---- min / max / clamping --------------------------------------------------

test "min-int" (min 3 5 = 3)
test "max-int" (max 3 5 = 5)
test "min-equal" (min 3 3 = 3)
test "min-float" (min 2.5 2.6 = 2.5)
test "min-negative" (min (0 - 3) 3 = 0 - 3)
test "max-of-list" (List.max [ 3; 9; 2 ] = 9)
test "min-of-list" (List.min [ 3; 9; 2 ] = 2)

// ---- conversions round the same way ----------------------------------------

test "int-of-float-truncates" (int 2.9 = 2)
test "int-of-negative-float-truncates" (int (0.0 - 2.9) = 0 - 2)
test "int64-of-float" (int64 2.9 = 2L)
test "float-of-int" (float 3 = 3.0)
test "float-of-int64" (float 3L = 3.0)
test "int-of-int64" (int 3L = 3)
test "int64-of-int" (int64 3 = 3L)

// ---- integer widths --------------------------------------------------------

test "int-max-wraps" (2147483647 + 1 = 0 - 2147483647 - 1)
test "int-min-abs-is-itself" (0 - 2147483647 - 1 < 0)
test "int64-range" (9000000000L > 2147483647L)
test "int64-mul" (3000000L * 3000L = 9000000000L)

// ---- sums and products over collections ------------------------------------

test "sum-int" (List.sum [ 1; 2; 3 ] = 6)
test "sum-float" (List.sum [ 1.5; 2.5 ] = 4.0)
test "sum-empty" (List.sum ([] : int list) = 0)
test "sumBy" (List.sumBy (fun v -> v * 2) [ 1; 2; 3 ] = 12)
test "fold-product" (List.fold (fun a b -> a * b) 1 [ 1; 2; 3; 4 ] = 24)
test "average" (List.average [ 1.0; 2.0; 3.0 ] = 2.0)

printfn "DONE tests=%d failures=%d" ntests failures

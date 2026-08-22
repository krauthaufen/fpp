// How a double PRINTS. .NET (and so F#) prints the SHORTEST decimal that
// reads back as the same double, in fixed-point when the exponent is in
// [-4, 17) and in the `E+xx` form otherwise — 1e300 is "1E+300", not
// "1.000000000000000E+300", and 1/3 keeps 16 digits rather than 15.
//
// Every line here is a round-trip too: the same machinery parses, so a value
// that prints as F# prints it also reads back bit for bit.
module Core_floatprint

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let str (x : float) : string = string x
let bits (x : float) : int64 = System.BitConverter.DoubleToInt64Bits x

// ---- the shapes -----------------------------------------------------------

test "one" (str 1.0 = "1")
test "half" (str 1.5 = "1.5")
test "tenth" (str 0.1 = "0.1")
test "third" (str (1.0 / 3.0) = "0.3333333333333333")
test "hundred" (str 100.0 = "100")
test "negative" (str (0.0 - 2.5) = "-2.5")
test "zero" (str 0.0 = "0")
test "sum-artefact" (str (0.1 + 0.2) = "0.30000000000000004")
test "next-after-two" (str 2.0000000000000004 = "2.0000000000000004")

// ---- where the exponent form takes over -----------------------------------

test "e14" (str 1e14 = "100000000000000")
test "e15" (str 1e15 = "1000000000000000")
test "e16" (str 1e16 = "10000000000000000")
test "e17" (str 1e17 = "1E+17")
test "e21" (str 1e21 = "1E+21")
test "digits15" (str 123456789012345.0 = "123456789012345")
test "digits16" (str 1234567890123456.0 = "1234567890123456")

test "small4" (str 1e-4 = "0.0001")
test "small5" (str 1e-5 = "1E-05")
test "small6" (str 1e-6 = "1E-06")
test "small7" (str 1e-7 = "1E-07")
test "small-mixed" (str 0.00012345 = "0.00012345")

// ---- the extremes ---------------------------------------------------------

test "big" (str 1e300 = "1E+300")
test "tiny" (str 1e-300 = "1E-300")
test "denormal" (str 5e-324 = "5E-324")
test "max" (str 1.7976931348623157e308 = "1.7976931348623157E+308")

// ---- the named values -----------------------------------------------------

test "nan" (str nan = "NaN")
test "inf" (str infinity = "Infinity")
test "neg-inf" (str (0.0 - infinity) = "-Infinity")

// ---- printing and parsing are inverse -------------------------------------

let roundTrips (x : float) : bool = bits (float (str x)) = bits x

test "rt-third" (roundTrips (1.0 / 3.0))
test "rt-tenth" (roundTrips 0.1)
test "rt-big" (roundTrips 1e300)
test "rt-tiny" (roundTrips 1e-300)
test "rt-denormal" (roundTrips 5e-324)
test "rt-max" (roundTrips 1.7976931348623157e308)
test "rt-artefact" (roundTrips (0.1 + 0.2))
test "rt-e17" (roundTrips 1e17)
test "rt-negative" (roundTrips (0.0 - 2.5))

printfn "DONE tests=%d failures=%d" ntests failures

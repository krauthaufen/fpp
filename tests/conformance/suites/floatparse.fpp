// Ported from dotnet/fsharp tests/fsharp/core/libtest/test.fsx — the
// FloatParseTests module — into the common F#/F++ subset. Test NAMES are the
// originals; the expected values are upstream's, spelled in decimal.
//
// ADAPTED: upstream splits the sign off before calling Double.Parse (a
// .NET Framework quirk with -0.0 that modern .NET does not have), so `float s`
// is called directly here.
//
// These pin the DENORMAL boundary: 1E-323 is two ticks above zero, 1E-324
// rounds to zero, and the sign has to survive that rounding.
//
// The extreme exponents are here too: parsing is a DECIMAL SHIFT (the
// prelude's FloatFmt, one bit at a time), which is exact, so the answer is
// the correctly-rounded double whatever the exponent — the old digit-at-a-
// time scaling landed 3-4 ulps out.
module Core_floatparse

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let ofString (s : string) : float = float s
let toBits (x : float) : int64 = System.BitConverter.DoubleToInt64Bits x

test "FloatParse.1" (toBits (ofString "0.0") = 0L)
// the cases the digit-at-a-time scaling could not round: a large NEGATIVE
// exponent, the largest finite double, and a 17-significant-digit mantissa
test "FloatParse.2" (toBits (ofString "-1E-127") = toBits (0.0 - 1E-127))
test "FloatParse.C" (toBits (ofString "1E308") = toBits 1E308)
test "FloatParse.D" (toBits (ofString "1.2345678901234567E17") = toBits 1.2345678901234567E17)
test "FloatParse.E" (toBits (ofString "2.2250738585072011E-308") = toBits 2.2250738585072011E-308)
test "FloatParse.F" (toBits (ofString "1E22") = toBits 1E22)
test "FloatParse.G" (toBits (ofString "1E23") = toBits 1E23)
test "FloatParse.0" (toBits (ofString "-0.0") = -9223372036854775808L)
test "FloatParse.3" (toBits (ofString "-1E-323") = -9223372036854775806L)
test "FloatParse.4" (toBits (ofString "-1E-324") = -9223372036854775808L)
test "FloatParse.5" (toBits (ofString "-1E-325") = -9223372036854775808L)
test "FloatParse.6" (toBits (ofString "1E-325") = 0L)
test "FloatParse.7" (toBits (ofString "1E-322") = 20L)
test "FloatParse.8" (toBits (ofString "1E-323") = 2L)
test "FloatParse.9" (toBits (ofString "1E-324") = 0L)
test "FloatParse.A" (toBits (ofString "Infinity") = 9218868437227405312L)
test "FloatParse.B" (toBits (ofString "-Infinity") = -4503599627370496L)
test "FloatParse.C" (System.Double.IsNaN (ofString "NaN") = true)

// ---- ordinary values, and the shapes a parser gets wrong -----------------

test "FloatParse.plain" (ofString "1.5" = 1.5)
test "FloatParse.neg" (ofString "-2.25" = -2.25)
test "FloatParse.int-shaped" (ofString "3" = 3.0)
test "FloatParse.lead-dot" (ofString "0.125" = 0.125)
test "FloatParse.exp-plus" (ofString "1E+2" = 100.0)
test "FloatParse.exp-minus" (ofString "1E-2" = 0.01)
test "FloatParse.exp-lower" (ofString "1e3" = 1000.0)
test "FloatParse.round" (toBits (ofString "0.1") = toBits 0.1)
test "FloatParse.round2" (toBits (ofString "1234567890.123") = toBits 1234567890.123)

printfn "DONE tests=%d failures=%d" ntests failures

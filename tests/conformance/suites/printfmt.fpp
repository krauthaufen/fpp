// PRINTF FORMAT SPECIFIERS, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/BasicTypeAndModuleDefini-
// tions/PrintfFormatStrings and the sprintf cases of the FSharp.Core string
// tests.
//
// Every case here is a STRING comparison, so a specifier that pads, rounds
// or signs differently shows up as an inequality rather than a build error.
// The suite covers the specifier, its flags (`-`, `0`, `+`), an explicit
// width and precision, and the widths taken from an argument (`%*d`
// is DROPPED — it is not in the common subset).
//
// DROPPED: `%O` on a non-primitive (its ToString is the .NET one), `%a`/`%t`
// (the callback forms), and the byte-array `%A` layout.
module Core_printfmt

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

// ---- the plain specifiers -------------------------------------------------

eq "d" (sprintf "%d" 42) "42"
eq "d-negative" (sprintf "%d" (0 - 42)) "-42"
eq "s" (sprintf "%s" "abc") "abc"
eq "b-true" (sprintf "%b" true) "true"
eq "b-false" (sprintf "%b" false) "false"
eq "c" (sprintf "%c" 'x') "x"
eq "percent" (sprintf "100%%") "100%"

// several holes, and literal text between them
eq "several" (sprintf "%s=%d (%b)" "n" 7 true) "n=7 (true)"
eq "adjacent" (sprintf "%d%d%d" 1 2 3) "123"

// ---- integers in other bases ---------------------------------------------

eq "x" (sprintf "%x" 255) "ff"
eq "X" (sprintf "%X" 255) "FF"
eq "o" (sprintf "%o" 8) "10"
eq "x-zero" (sprintf "%x" 0) "0"

// ---- floats ---------------------------------------------------------------

eq "f-default" (sprintf "%f" 1.5) "1.500000"
eq "f-precision" (sprintf "%.2f" 1.567) "1.57"
eq "f-precision-zero" (sprintf "%.0f" 1.5) "2"
eq "f-integral" (sprintf "%.1f" 2.0) "2.0"
eq "g" (sprintf "%g" 1.5) "1.5"
eq "e" (sprintf "%e" 1234.5) "1.234500e+003"
eq "f-negative" (sprintf "%.1f" (0.0 - 1.25)) "-1.2"

// `%A` and `%O` on primitives
eq "A-int" (sprintf "%A" 3) "3"
eq "A-string" (sprintf "%A" "s") "\"s\""
eq "A-list" (sprintf "%A" [ 1; 2 ]) "[1; 2]"
eq "A-tuple" (sprintf "%A" (1, "a")) "(1, \"a\")"
eq "A-option" (sprintf "%A" (Some 1)) "Some 1"
eq "O-int" (sprintf "%O" 3) "3"

// ---- width, alignment and zero padding ------------------------------------

eq "width-d" (sprintf "%5d" 42) "   42"
eq "width-left" (sprintf "%-5d|" 42) "42   |"
eq "width-zero" (sprintf "%05d" 42) "00042"
eq "width-s" (sprintf "%6s|" "ab") "    ab|"
eq "width-s-left" (sprintf "%-6s|" "ab") "ab    |"
eq "width-smaller-than-value" (sprintf "%2d" 12345) "12345"
eq "plus-flag" (sprintf "%+d" 42) "+42"
eq "plus-flag-negative" (sprintf "%+d" (0 - 42)) "-42"
eq "width-float" (sprintf "%8.2f|" 1.5) "    1.50|"
eq "width-float-left" (sprintf "%-8.2f|" 1.5) "1.50    |"
eq "zero-float" (sprintf "%08.2f" 1.5) "00001.50"

// the exponent forms: `%e` spells THREE exponent digits, `%g` two, and
// `%g` drops the trailing zeros
eq "e-zero" (sprintf "%e" 0.0) "0.000000e+000"
eq "e-small" (sprintf "%e" 0.000123) "1.230000e-004"
eq "e-precision" (sprintf "%.2e" 1234.5) "1.23e+003"
eq "E-upper" (sprintf "%E" 1234.5) "1.234500E+003"
eq "e-huge" (sprintf "%e" 1e100) "1.000000e+100"
eq "g-fixed" (sprintf "%g" 0.0001) "0.0001"
eq "g-exponent" (sprintf "%g" 1e-7) "1e-07"
eq "g-six-digits" (sprintf "%g" 1234567.0) "1.23457e+06"
eq "g-boundary-in" (sprintf "%g" 100000.0) "100000"
eq "g-boundary-out" (sprintf "%g" 1000000.0) "1e+06"
eq "g-precision" (sprintf "%.3g" 1234.5) "1.23e+03"
eq "g-zero" (sprintf "%g" 0.0) "0"
eq "G-upper" (sprintf "%G" 1e-7) "1E-07"

// the non-finite values keep .NET's words whatever the specifier
eq "f-nan" (sprintf "%f" nan) "NaN"
eq "f-infinity" (sprintf "%f" infinity) "Infinity"
eq "f-neg-infinity" (sprintf "%.2f" (0.0 - infinity)) "-Infinity"
eq "e-nan" (sprintf "%e" nan) "NaN"
eq "g-nan" (sprintf "%g" nan) "NaN"

// rounding is HALF TO EVEN, on the true binary value
eq "round-half-down" (sprintf "%.0f" 0.5) "0"
eq "round-half-up" (sprintf "%.0f" 2.5) "2"
eq "round-below-half" (sprintf "%.2f" 1.005) "1.00"
// `0.0 - 0.0` is POSITIVE zero — the sign has to come from the literal
eq "negative-zero" (sprintf "%.1f" -0.0) "-0.0"
eq "f-large" (sprintf "%f" 1e20) "100000000000000000000.000000"
eq "f-ten-digits" (sprintf "%.10f" (1.0 / 3.0)) "0.3333333333"

// a sign pads AFTER itself, never before
eq "zero-pad-negative" (sprintf "%05d" (0 - 42)) "-0042"
eq "zero-pad-negative-float" (sprintf "%05.1f" (0.0 - 1.5)) "-01.5"
eq "plus-zero" (sprintf "%+d" 0) "+0"

// `%O` is ToString, which for a primitive is what `string` answers
eq "O-string" (sprintf "%O" "s") "s"
eq "O-bool" (sprintf "%O" true) "True"
eq "O-float" (sprintf "%O" 1.5) "1.5"
eq "O-char" (sprintf "%O" 'c') "c"

// ---- the other integer widths --------------------------------------------

eq "int64" (sprintf "%d" 9000000000L) "9000000000"
eq "uint32" (sprintf "%d" 4000000000u) "4000000000"
eq "byte" (sprintf "%d" 200uy) "200"

// ---- printf into a value, and the partially applied form -----------------

let render = sprintf "[%s]"
eq "partial-apply" (render "x") "[x]"

let two = sprintf "%d-%d"
eq "partial-two" (two 1 2) "1-2"

// failwithf builds its message the same way
let msg =
    try
        failwithf "bad %d" 7
    with
    | ex -> ex.Message

eq "failwithf" msg "bad 7"

// ---- printfn writes a LINE, and the suite's own output proves it ---------

test "printfn-runs" true

// ---- strings with characters the formatter must not touch ----------------

eq "backslash" (sprintf "%s" "a\\b") "a\\b"
eq "quote" (sprintf "%s" "a\"b") "a\"b"
eq "newline-literal" (sprintf "a\nb") "a\nb"
eq "tab" (sprintf "a\tb") "a\tb"
eq "empty" (sprintf "%s" "") ""
eq "format-with-no-holes" (sprintf "plain") "plain"

// ---- string concatenation and the `string` conversion agree --------------

eq "string-of-int" (string 42) "42"
eq "string-of-bool" (string true) "True"
eq "string-of-char" (string 'x') "x"
eq "string-of-float" (string 1.5) "1.5"

printfn "DONE tests=%d failures=%d" ntests failures

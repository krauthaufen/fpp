// INTERPOLATED STRINGS, ported from dotnet/fsharp's tests/fsharp/core/
// printf-interpolated.
//
// `$"a{e}b"` is not sugar for concatenation: it is a printf FORMAT, and the
// two consequences are what this suite is about. A `%d` before a hole binds
// to that hole — it formats it AND type-checks it — and `%%` is one literal
// percent, because the whole literal is a format string.
//
// Both were wrong here and neither said so. A specifier printed itself
// (`$"%d{x}"` gave `%d42`), and an escaped percent stayed a pair
// (`$"100%%{x}"` gave `100%%42`). Nothing rejected either one; they simply
// rendered the wrong text.
//
// DROPPED: `$"{x:N2}"`, the .NET format specifier — the `:` reads as a type
// annotation here (see the lexer). Also `$$"""…"""`, and a string literal
// INSIDE a hole of a single-quoted interpolation, which F# itself rejects
// (FS3373).
module Core_interpolated

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let x = 42
let s = "ab"
let f = 1.5
let b = true

// ---- the plain hole ---------------------------------------------------------

eq "no-holes" $"plain" "plain"
eq "one-hole" $"v={x}" "v=42"
eq "two-holes" $"{x} and {s}" "42 and ab"
eq "hole-at-the-start" $"{x} trails" "42 trails"
eq "hole-at-the-end" $"leads {x}" "leads 42"
eq "adjacent-holes" $"{x}{s}" "42ab"
eq "empty-interpolation" $"" ""

// the hole is an EXPRESSION, not just a name
eq "arithmetic" $"expr={x + 1}" "expr=43"
eq "a-call" $"call={string (x * 2)}" "call=84"
eq "a-comparison" $"cmp={x > 0}" "cmp=True"

// every scalar renders as `string` renders it
eq "float-hole" $"f={f}" "f=1.5"
eq "bool-hole" $"b={b}" "b=True"
eq "string-hole" $"s={s}" "s=ab"

// and so do the structured shapes
eq "tuple-hole" $"t={(1, 2)}" "t=(1, 2)"
eq "list-hole" $"l={[ 1; 2 ]}" "l=[1; 2]"

// ---- a FORMAT SPECIFIER binds to the hole after it --------------------------

eq "percent-d" $"n=%d{x}" "n=42"
eq "percent-s" $"s=%s{s}" "s=ab"
eq "percent-b" $"b=%b{b}" "b=true"
eq "percent-x" $"h=%x{255}" "h=ff"
eq "percent-O" $"o=%O{x}" "o=42"
eq "percent-A" $"a=%A{[ 1; 2 ]}" "a=[1; 2]"

// width and precision, which is the whole reason to write one
eq "width" $"|%5d{x}|" "|   42|"
eq "precision" $"%.3f{f}" "1.500"
eq "plus-flag" $"%+d{x}" "+42"

// several in one string, and one right after another
eq "two-specifiers" $"%d{x} and %s{s}" "42 and ab"
eq "adjacent-specifiers" $"%d{x}%s{s}" "42ab"

// a specified hole beside an unspecified one
eq "mixed" $"{x} then %d{x}" "42 then 42"

// `%b` is F#'s lowercase bool, which is NOT what `string` gives — proof the
// hole really went through printf rather than the plain conversion
eq "specifier-not-string" ($"%b{b}" + "/" + $"{b}") "true/True"

// ---- `%%` is ONE literal percent --------------------------------------------

eq "escaped-percent" $"100%%" "100%"
eq "escaped-then-hole" $"100%%{x}" "100%42"

// `%%d` is a literal `%d`, so the hole after it has NO specifier and takes
// the plain conversion. The pair has to be recognised BEFORE the specifier
// scan, or this reads as a `%d` and swallows the hole.
eq "escaped-looks-like-a-specifier" $"%%d{x}" "%d42"

// and three percents are an escaped one FOLLOWED by a real specifier
eq "escape-then-specifier" $"%%%d{x}" "%42"

// ---- literal BRACES ----------------------------------------------------------

eq "escaped-braces" $"{{literal}}" "{literal}"
eq "brace-beside-a-hole" $"{{{x}}}" "{42}"

// ---- nesting and composition -------------------------------------------------

let inner = $"in={x}"
eq "interpolation-of-an-interpolation" $"out={inner}" "out=in=42"

eq "concatenated" ($"a" + $"b={x}") "ab=42"

let g (v : int) : string = $"g{v}"
eq "interpolation-in-a-function" (g 7) "g7"

let each = List.map (fun (v : int) -> $"<%d{v}>") [ 1; 2 ]
eq "interpolation-in-a-lambda" (String.concat "," each) "<1>,<2>"

// a hole reading a MUTABLE sees its current value, since the string is built
// where it is written
let mutable counter = 0
counter <- 5
eq "hole-reads-a-mutable" $"c={counter}" "c=5"

// ---- it is an ordinary string afterwards --------------------------------------

let built = $"k={x}"
eq "length" (string built.Length) "4"
eq "concat-after" (built + "!") "k=42!"
eq "compares-equal-to-its-literal" (string (built = "k=42")) "True"

printfn "DONE tests=%d failures=%d" ntests failures

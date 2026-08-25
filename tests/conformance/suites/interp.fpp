// STRING INTERPOLATION, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Language/StringInterpolation.
//
// `$"a{e}b"` is the literal text with each hole's value rendered by `string`
// and concatenated. The cases that matter are the ones where the SPLIT is
// non-obvious: adjacent holes with no text between them, a hole at either
// end, `{{`/`}}` for a literal brace, and an expression in the hole rather
// than a name — the hole is parsed as ordinary code, so a call, an operator
// or a member access all belong there.
//
// DROPPED: .NET format specifiers (`{x:N2}`), `%d`-style typed holes, and
// `$$"""…"""`. A string literal inside a hole is an ERROR in F# too (FS3373).
module Core_interp

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let n = 42
let s = "ab"
let xs = [ 1; 2; 3 ]

// ---- the shape of the split ------------------------------------------------

eq "hole-at-end" $"v={n}" "v=42"
eq "hole-at-start" $"{n} left" "42 left"
eq "hole-only" $"{n}" "42"
eq "no-hole" $"plain" "plain"
eq "empty" $"" ""
eq "adjacent-holes" $"{n}{n}" "4242"
eq "text-between-holes" $"{n}-{s}-{n}" "42-ab-42"
eq "two-holes-with-words" $"len={xs.Length} first={List.head xs}" "len=3 first=1"

// ---- a brace is doubled to be literal --------------------------------------

eq "literal-braces" $"{{literal}}" "{literal}"
eq "brace-around-hole" $"{{{n}}}" "{42}"
eq "open-brace-only" $"{{" "{"
eq "close-brace-only" $"}}" "}"

// ---- the hole is ordinary code ---------------------------------------------

eq "arithmetic" $"{n + 1}" "43"
eq "precedence-inside-hole" $"{1 + 2 * 3}" "7"
eq "call" $"{List.sum xs}" "6"
eq "member-access" $"{s.Length}" "2"
eq "method-call" $"{s.ToUpper ()}" "AB"
eq "nested-parens" $"{(n + 1) * 2}" "86"
eq "comparison" $"{n > 3}" "True"

// a STRUCTURED value (record, union, tuple, list) renders through `string`,
// which answers "?" here — see tests/known-issues/string-of-structured.fpp

// ---- the rendering is `string` ---------------------------------------------

eq "int" $"{7}" "7"
eq "float" $"{2.5}" "2.5"
eq "bool" $"{true}" "True"
eq "char" $"{'x'}" "x"
eq "string-value" $"{s}" "ab"
eq "negative" $"{0 - 5}" "-5"

// ---- interpolation in every position ---------------------------------------

let f (v : int) : string = $"v={v * 2}"
eq "inside-function" (f 5) "v=10"

let bound = $"b={n}"
eq "let-bound" bound "b=42"

let listOf = [ $"a{1}"; $"b{2}" ]
eq "inside-list" (String.concat "," listOf) "a1,b2"

let viaMap = List.map (fun v -> $"<{v}>") xs
eq "inside-lambda" (String.concat "" viaMap) "<1><2><3>"

eq "as-argument" (String.concat "|" [ $"{n}"; "x" ]) "42|x"
eq "concatenated" ($"{n}" + "!") "42!"
eq "length-of-result" (string ($"v={n}").Length) "4"

// a loop building interpolated pieces
let built =
    let mutable acc = ""
    for i in 1 .. 3 do
        acc <- acc + $"[{i}]"
    acc

eq "built-in-loop" built "[1][2][3]"

printfn "DONE tests=%d failures=%d" ntests failures

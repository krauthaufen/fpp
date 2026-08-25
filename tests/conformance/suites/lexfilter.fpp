// LEXICAL FILTERING, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/LexicalFiltering
// (Basic, HighPrecedenceApplication, LexicalAnalysisOfTypeApplications,
// OffsideExceptions) — those are compile-only checks, so what is kept here
// is the RESULT each form produces, which is what a differential gate can
// actually see.
//
// The theme is that WHITESPACE decides the parse. `f -1` applies `f` to
// minus one while `f - 1` subtracts; `a.[i]` indexes while `f x.[i]` applies
// `f` to the element; `f<int>` is a type application while `a < b > c` is
// two comparisons. Every case here is a pair whose two spellings mean
// DIFFERENT things.
//
// DROPPED: `#light "off"` (verbose syntax), `{ -128y .. 1y }` seq-brace
// ranges (deprecated in F# itself), and the `.err.bsl` cases, which check
// error text rather than behaviour.
module Core_lexfilter

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- high-precedence application -------------------------------------------

let f (v : int) : int = v * 10
let arr = [| 1; 2; 3 |]

// `f -1` is an APPLICATION; `f - 1` is a subtraction of the function's…
// no: `f - 1` does not type check, so the pair that shows the split is a
// VALUE minus one against a function applied to minus one
let n = 7
eq "apply-to-negative" (string (f -1)) "-10"
eq "subtract-one" (string (n - 1)) "6"
eq "unary-minus-on-name" (string (-n)) "-7"
eq "minus-with-spaces" (string (n - -1)) "8"

// `f x.[0]` applies f to the ELEMENT: indexing binds tighter than application
eq "index-binds-tighter" (string (f arr.[0])) "10"
eq "index-of-applied" (string ((f arr.[1]) + 1)) "21"

// adjacent parenthesised argument vs a spaced one — the same call
eq "adjacent-paren" (string (f(2))) "20"
eq "spaced-paren" (string (f (2))) "20"

// two adjacent applications chain left
let add2 (a : int) (b : int) : int = a + b
eq "chained-application" (string (add2 1 2)) "3"
eq "chained-with-parens" (string (add2 (1) (2))) "3"
eq "application-then-index" (string ((Array.map f arr).[2])) "30"

// a method call's argument list is high-precedence too
let s = "hello"
eq "method-adjacent" (s.Substring(1, 2)) "el"
eq "method-spaced" (s.Substring (1, 2)) "el"

// ---- type applications versus comparison -----------------------------------

let idT<'a> (v : 'a) : 'a = v
let a2 = 1
let b2 = 2
let c2 = 3

eq "type-application" (string (idT<int> 5)) "5"
eq "type-application-string" (idT<string> "x") "x"
// `a < b > c` is TWO comparisons, not a type application
eq "less-then-greater" (string ((a2 < b2) > (b2 < c2))) "False"
eq "comparison-chain" (string (a2 < b2 && b2 < c2)) "True"
// a generic call whose argument is itself parenthesised
eq "type-application-nested" (string (idT<int> (a2 + b2))) "3"

// ---- the offside line ------------------------------------------------------

// a `then` body indented under the `if`, and an `else` that lines up
let branch (v : int) : int =
    if v > 0 then
        v * 2
    else
        0 - v

eq "if-then-else-offside" (string (branch 3)) "6"
eq "if-then-else-offside-neg" (string (branch -4)) "4"

// a pipeline broken across lines, the operator LEADING each continuation
let piped =
    [ 1; 2; 3; 4 ]
    |> List.filter (fun v -> v % 2 = 0)
    |> List.map (fun v -> v * 10)
    |> List.sum

eq "leading-pipeline" (string piped) "60"

// an infix operator at the END of a line continues the expression
let trailing =
    1 +
    2 +
    3

eq "trailing-infix" (string trailing) "6"

// "infix token plus one": a continuation may start ONE column left of the
// offside line when it begins with an infix operator
let plusOne =
    let v = 10
    v
     + 1
     + 2

eq "infix-token-plus-one" (string plusOne) "13"

// match arms under a `match` that is itself an argument
let described (v : int) : string =
    match v with
    | 0 -> "zero"
    | 1 -> "one"
    | _ -> "many"

eq "match-arms-offside" (described 0) "zero"
eq "match-arms-offside-wild" (described 9) "many"

// a match INSIDE a lambda inside an application
eq "match-in-lambda"
    (String.concat ","
        (List.map (fun v ->
            match v with
            | 1 -> "a"
            | _ -> "b") [ 1; 2 ]))
    "a,b"

// a `let` body may sit on the same line as its binding
let sameLine = let v = 4 in v * v
eq "let-in-on-one-line" (string sameLine) "16"

// nested lets, each on its own line, sharing the block
let nestedLets =
    let a = 1
    let b = a + 1
    let c = b + 1
    a + b + c

eq "nested-lets" (string nestedLets) "6"

// ---- multi-line brackets ---------------------------------------------------

// a list literal broken over lines, elements separated by NEWLINE
let listOverLines =
    [ 1
      2
      3 ]

eq "list-over-lines" (string (List.sum listOverLines)) "6"

// a record broken over lines, and one written on a single line
type R = { A : int; B : string }

let recOverLines =
    { A = 1
      B = "x" }

let recOneLine = { A = 2; B = "y" }

eq "record-over-lines" (recOverLines.B + string recOverLines.A) "x1"
eq "record-one-line" (recOneLine.B + string recOneLine.A) "y2"

// an argument list broken over lines
let three (x : int) (y : int) (z : int) : int = x + y + z

let brokenArgs =
    three
        1
        2
        3

eq "arguments-over-lines" (string brokenArgs) "6"

// nested type arguments over more than one line
let nestedGeneric : int list list =
    [ [ 1; 2 ]
      [ 3 ] ]

eq "nested-generic-over-lines" (string (List.sum (List.map List.sum nestedGeneric))) "6"

// ---- ranges ----------------------------------------------------------------

// the range operator against a NEGATIVE bound: the dots must not be eaten by
// the literal, whichever way the spaces fall
eq "range-negative-tight" (string (List.sum [ -3..1 ])) "-5"
eq "range-negative-left" (string (List.sum [ -3.. 1 ])) "-5"
eq "range-negative-right" (string (List.sum [ -3 ..1 ])) "-5"
eq "range-negative-spaced" (string (List.sum [ -3 .. 1 ])) "-5"
eq "range-step" (string (List.sum [ 0 .. 2 .. 6 ])) "12"
eq "range-empty" (string (List.length [ 3 .. 1 ])) "0"

// a float range, whose dots sit next to a decimal point
eq "float-range" (string (List.length [ 1.0 .. 3.0 ])) "3"

// ---- application spanning a line break -------------------------------------

// the argument indented under the function continues the application
let spanning =
    f
        3

eq "application-over-lines" (string spanning) "30"

// a lambda whose body is the block below it
let lam = fun (v : int) ->
            let d = v * 2
            d + 1

eq "lambda-body-block" (string (lam 5)) "11"

// ---- semicolons and blocks --------------------------------------------------

// statements separated by `;` on one line
let mutable acc = 0
let bumpTwice () : unit = acc <- acc + 1; acc <- acc + 1
bumpTwice ()
eq "semicolon-statements" (string acc) "2"

// a `do` block indented under a `for`
let mutable total = 0
for i in 1 .. 3 do
    total <- total + i
eq "for-body-offside" (string total) "6"

// a `while` whose body is on the SAME line
let mutable k = 0
while k < 3 do k <- k + 1
eq "while-body-same-line" (string k) "3"

// ---- operators that look like other tokens ----------------------------------

// `|>` at the start of a line, `||` and `|` in a pattern, `<|` backwards pipe
eq "backward-pipe" (string (f <| 4)) "40"
eq "or-else" (string (true || false)) "True"

let pat (v : int) : string =
    match v with
    | 1 | 2 -> "small"
    | _ -> "big"

eq "or-pattern" (pat 2) "small"
test "or-pattern-other" (pat 5 = "big")

// `..` inside an index, and `.` on a literal
eq "index-range" (string (Array.length arr.[0..1])) "2"
eq "float-literal-member" ((2.5).ToString()) "2.5"

printfn "DONE tests=%d failures=%d" ntests failures

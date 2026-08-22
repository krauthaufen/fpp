// LEXICAL FILTERING — the offside rule and the places F# relaxes it —
// ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/LexicalFiltering
// (OffsideExceptions/InfixTokenPlusOne, HighPrecedenceApplication,
// LexicalAnalysisOfTypeApplications) and the adjacency rules of
// BasicGrammarElements/PrecedenceAndOperators.
//
// These are all about WHERE a token may sit: a continuation line that starts
// with an infix operator may hang left of its expression, `f -x` passes a
// negative argument while `f - x` subtracts, and `a.[i]` indexes where `a .[
// i ]` does not parse. Every case here answers a VALUE, so a layout read the
// wrong way shows up as a wrong answer rather than only a parse error.
module Core_layout

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- a continuation line may start with an infix operator ----------------

let x = 3

let y = x
      + x

test "infix-continuation" (y = 6)

let longer =
    1
    + 2
    + 3

test "infix-chain" (longer = 6)

// NOTE: a BUILTIN operator hanging left of its operand (`x` then `-  1` one
// column in) is rejected by F# itself — the relaxation below is for
// user-defined operators, which is how upstream spells it.

// a pipeline across lines
let piped =
    [ 1; 2; 3 ]
    |> List.map (fun v -> v * 2)
    |> List.sum

test "pipeline-lines" (piped = 12)

// and one whose continuation hangs left
let piped2 = [ 1; 2; 3 ]
                |> List.length

test "pipeline-hanging" (piped2 = 3)

// ---- a user-defined operator continues a line the same way ---------------

let (--) (a : int) (b : int) = a - b

let z =    x
        -- 1

test "custom-op-continuation" (z = 2)

let ( *** ) (a : int) (b : int) = a * b

let a2 =
                 x
             *** x

test "custom-op-hanging" (a2 = 9)

// ---- adjacency decides `f -x` from `f - x` -------------------------------

let neg (v : int) = v * 10

test "adjacent-minus-is-argument" (neg -2 = 0 - 20)
test "spaced-minus-is-subtraction" (neg 2 - 1 = 19)
test "parenthesised-negative" (neg (0 - 2) = 0 - 20)

// the same for a literal argument
let twoArgs (p : int) (q : int) = p * 100 + q

test "adjacent-negative-second" (twoArgs 1 -2 = 98)

// ---- indexing and slicing are adjacency too ------------------------------

let arr = [| 10; 20; 30 |]

test "index-adjacent" (arr.[1] = 20)
test "slice-adjacent" (Array.toList arr.[1..2] = [ 20; 30 ])

// a nested index
let grid = [| [| 1; 2 |]; [| 3; 4 |] |]
test "index-nested" (grid.[1].[0] = 3)

// ---- a `match` arm's body may run on to the next line --------------------

let classify (v : int) =
    match v with
    | 0 ->
        "zero"
    | n when n < 0 ->
        "neg"
    | _ ->
        "pos"

test "match-body-next-line" (classify 0 = "zero" && classify (0 - 1) = "neg" && classify 1 = "pos")

// an arm body that is a multi-line block
let blocky (v : int) =
    match v with
    | 0 ->
        let a = 1
        let b = 2
        a + b
    | _ -> 0

test "match-body-block" (blocky 0 = 3)

// ---- `if` and its branches across lines ----------------------------------

let branched (v : int) =
    if v > 0 then
        "pos"
    elif v = 0 then
        "zero"
    else
        "neg"

test "if-lines" (branched 1 = "pos" && branched 0 = "zero" && branched (0 - 1) = "neg")

// a condition that itself spans lines
let wideCond (v : int) =
    if v > 0
       && v < 10 then "in"
    else "out"

test "condition-continuation" (wideCond 5 = "in" && wideCond 50 = "out")

// ---- a function's arguments may spread over lines ------------------------

let three (p : int) (q : int) (r : int) = p + q + r

let spread =
    three
        1
        2
        3

test "args-on-lines" (spread = 6)

// a tuple argument split across lines
let tupled (p : int, q : int) = p * q

let tupleSpread =
    tupled (
        3,
        4)

test "tuple-args-lines" (tupleSpread = 12)

// ---- a `let` body indented under its binding -----------------------------

let outer =
    let inner =
        let deepest = 1
        deepest + 1
    inner + 1

test "nested-let-blocks" (outer = 3)

// a `let ... in` on one line
let inline1 = let t = 5 in t * 2
test "let-in-one-line" (inline1 = 10)

// ---- list and record layout ----------------------------------------------

let listLines =
    [ 1
      2
      3 ]

test "list-newline-separated" (listLines = [ 1; 2; 3 ])

type R = { A : int; B : int }

let recLines =
    { A = 1
      B = 2 }

test "record-newline-separated" (recLines.A = 1 && recLines.B = 2)

let arrLines =
    [| 1
       2 |]

test "array-newline-separated" (Array.toList arrLines = [ 1; 2 ])

// nested inside a list
let listOfRecs =
    [ { A = 1; B = 2 }
      { A = 3; B = 4 } ]

test "list-of-records" (List.length listOfRecs = 2 && (List.item 1 listOfRecs).A = 3)

// ---- generic type applications lex as one thing --------------------------

let boxed : int option = Some 1
test "type-application" (boxed = Some 1)

let mapped : Map<string, int> = Map.ofList [ ("a", 1) ]
test "type-application-two-args" (Map.find "a" mapped = 1)

// a comparison that is NOT a type application
let lessThan = 1 < 2
test "less-than-not-generic" lessThan

printfn "DONE tests=%d failures=%d" ntests failures

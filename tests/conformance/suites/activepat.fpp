// ACTIVE PATTERNS, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/PatternMatching/Named
// (activePatterns01-10, MultiActivePatterns01, ParameterizedPartialActive-
// Pattern01, RecursiveActivePats, AsHighOrderFunc01) and the And directory,
// whose `&` patterns exist mainly to combine partial patterns.
//
// Every shape F# has is here: TOTAL multi-case, TOTAL single-case, PARTIAL,
// PARAMETERIZED (total and partial), a pattern used inside another pattern,
// one used in a `let` binding, one used through `function`, and `&`.
//
// DROPPED: the upstream cases that reach into the BCL (`#Exception` message
// lengths, System.Collections.Generic.List membership) and `null` as a
// parameterized pattern's argument.
module Core_activepat

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- total, several cases ------------------------------------------------

let (|Even|Odd|) (x : int) = if x % 2 = 0 then Even else Odd

let isEven (x : int) : bool =
    match x with
    | Even -> true
    | Odd -> false

test "total-two-even" (isEven 2)
test "total-two-odd" (not (isEven 1))

// a case may carry a value, and the cases need not carry the same one
let (|Zero|Positive|Negative|) (x : int) =
    if x = 0 then Zero
    elif x > 0 then Positive x
    else Negative (0 - x)

let describe (x : int) : string =
    match x with
    | Zero -> "zero"
    | Positive v -> "pos:" + string v
    | Negative v -> "neg:" + string v

test "total-three-zero" (describe 0 = "zero")
test "total-three-pos" (describe 7 = "pos:7")
test "total-three-neg" (describe (0 - 7) = "neg:7")

// a wildcard clause is allowed beside the cases
let onlyEven (x : int) : string =
    match x with
    | Even -> "even"
    | _ -> "other"

test "total-with-wildcard-hit" (onlyEven 2 = "even")
test "total-with-wildcard-miss" (onlyEven 3 = "other")

// ---- total, ONE case: the payload is bare --------------------------------

let (|Double|) (x : int) = (x, x)

let doubled (x : int) : int * int =
    match x with
    | Double y -> y

test "single-case" (doubled 1 = (1, 1))

let (|Split|) (s : string) = (s.Length, s)

let lengthOf (s : string) : int =
    match s with
    | Split (n, _) -> n

test "single-case-destructure" (lengthOf "abcd" = 4)

// ---- partial: a `None` falls through to the next clause ------------------

let (|Pos|_|) (x : int) : unit option = if x > 0 then Some () else None

let sign (x : int) : string =
    match x with
    | Pos -> "pos"
    | _ -> "nonpos"

test "partial-hit" (sign 3 = "pos")
test "partial-miss" (sign 0 = "nonpos")

let (|Big|_|) (x : int) : int option = if x > 100 then Some (x * 2) else None

let big (x : int) : int =
    match x with
    | Big v -> v
    | _ -> 0

test "partial-payload-hit" (big 200 = 400)
test "partial-payload-miss" (big 5 = 0)

// several DIFFERENT patterns in one match, beside ordinary clauses
let mixed (x : int) : string =
    match x with
    | Big v -> "big:" + string v
    | Pos -> "pos"
    | 0 -> "zero"
    | _ -> "neg"

test "mixed-big" (mixed 500 = "big:1000")
test "mixed-pos" (mixed 5 = "pos")
test "mixed-zero" (mixed 0 = "zero")
test "mixed-neg" (mixed (0 - 3) = "neg")

// a guard runs AFTER the pattern binds, and a failed guard falls through
let guarded (x : int) : string =
    match x with
    | Big v when v > 1000 -> "huge:" + string v
    | Big v -> "big:" + string v
    | _ -> "small"

test "partial-guard-first" (guarded 600 = "huge:1200")
test "partial-guard-second" (guarded 200 = "big:400")
test "partial-guard-none" (guarded 1 = "small")

// ---- parameterized -------------------------------------------------------

let (|Mul|) (k : int) (x : int) = x * k

let scaled (x : int) : int =
    match x with
    | Mul 3 v -> v

test "parameterized-total" (scaled 7 = 21)

let (|DivBy|_|) (k : int) (x : int) : int option =
    if x % k = 0 then Some (x / k) else None

let divide (x : int) : string =
    match x with
    | DivBy 7 q -> "seven:" + string q
    | DivBy 2 q -> "two:" + string q
    | _ -> "none"

test "parameterized-partial-first" (divide 14 = "seven:2")
test "parameterized-partial-second" (divide 8 = "two:4")
test "parameterized-partial-none" (divide 9 = "none")

// the argument may be a bound name rather than a literal
let three = 3

let byThree (x : int) : bool =
    match x with
    | DivBy three _ -> true
    | _ -> false

test "parameterized-ident-arg" (byThree 9)
test "parameterized-ident-arg-miss" (not (byThree 8))

// ---- `&`: both sides must match ------------------------------------------

let (|DivisibleByTwo|_|) (x : int) : unit option = if x % 2 = 0 then Some () else None
let (|DivisibleByX|_|) (k : int) (y : int) : unit option = if y % k = 0 then Some () else None

let divisibleBy (x : int) : int list =
    match x with
    | DivisibleByTwo & DivisibleByX 3 & DivisibleByX 4 -> [ 2; 3; 4 ]
    | DivisibleByTwo & DivisibleByX 4 -> [ 2; 4 ]
    | DivisibleByTwo & DivisibleByX 3 -> [ 2; 3 ]
    | DivisibleByX 3 & DivisibleByX 4 -> [ 3; 4 ]
    | DivisibleByX 4 -> [ 4 ]
    | DivisibleByX 3 -> [ 3 ]
    | _ -> []

test "and-three" (divisibleBy 12 = [ 2; 3; 4 ])
test "and-two-four" (divisibleBy 16 = [ 2; 4 ])
test "and-two-three" (divisibleBy 6 = [ 2; 3 ])
test "and-three-only" (divisibleBy 9 = [ 3 ])
test "and-none" (divisibleBy 5 = [])

// `&` over ORDINARY patterns binds both sides
let andPlain (p : int * int) : int =
    match p with
    | (0, _) & (_, 0) -> 0
    | (x, _) & (_, y) -> x + y

test "and-plain-both-zero" (andPlain (0, 0) = 0)
test "and-plain-binds" (andPlain (3, 4) = 7)

// ---- nested inside another pattern ---------------------------------------

let insideOption (o : int option) : string =
    match o with
    | Some Pos -> "some-pos"
    | Some _ -> "some-other"
    | None -> "none"

test "nested-some-pos" (insideOption (Some 3) = "some-pos")
test "nested-some-other" (insideOption (Some 0) = "some-other")
test "nested-none" (insideOption None = "none")

let insideTuple (p : int * int) : string =
    match p with
    | (Pos, Pos) -> "both"
    | (Pos, _) -> "first"
    | _ -> "neither"

test "nested-tuple-both" (insideTuple (1, 2) = "both")
test "nested-tuple-first" (insideTuple (1, 0) = "first")
test "nested-tuple-neither" (insideTuple (0, 0) = "neither")

let insideList (xs : int list) : string =
    match xs with
    | [ Big v ] -> "one-big:" + string v
    | [ _ ] -> "one"
    | _ -> "other"

test "nested-list-big" (insideList [ 500 ] = "one-big:1000")
test "nested-list-plain" (insideList [ 5 ] = "one")
test "nested-list-other" (insideList [ 1; 2 ] = "other")

// ---- in a `let` binding and through `function` ---------------------------

let (Split (letLen, letStr)) = "abcde"

test "let-binding-length" (letLen = 5)
test "let-binding-value" (letStr = "abcde")

let viaFunction =
    function
    | Even -> "even"
    | Odd -> "odd"

test "function-total" (viaFunction 4 = "even" && viaFunction 5 = "odd")

let viaFunctionPartial =
    function
    | Big v -> v
    | _ -> 0

test "function-partial" (viaFunctionPartial 200 = 400 && viaFunctionPartial 2 = 0)

// ---- a pattern that RECURSES through itself ------------------------------

let rec (|Halved|) (x : int) : int =
    if x < 2 then x
    else
        match x / 2 with
        | Halved h -> h

test "recursive-pattern" (match 32 with Halved h -> h = 1)

// ---- the same value matched by two patterns of different kinds -----------

let classify (x : int) : string =
    match x with
    | Even & Pos -> "even-pos"
    | Even -> "even-nonpos"
    | Pos -> "odd-pos"
    | _ -> "odd-nonpos"

test "combined-even-pos" (classify 4 = "even-pos")
test "combined-even-nonpos" (classify 0 = "even-nonpos")
test "combined-odd-pos" (classify 3 = "odd-pos")
test "combined-odd-nonpos" (classify (0 - 3) = "odd-nonpos")

printfn "DONE tests=%d failures=%d" ntests failures

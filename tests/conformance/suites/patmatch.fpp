// Pattern matching, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/PatternMatching: the
// And, Array, As, ConsList, Record, Simple, SimpleConstant, Tuple, Union and
// Wildcard directories, plus the DynamicTypeTest cases that stay inside the
// subset.
//
// Upstream each file answers through `exit 1`; here every case is a named
// assert, so a failure says which pattern form broke.
//
// DROPPED: everything built on ACTIVE PATTERNS ((|MulTwo|_|), parameterized
// and recursive active patterns, (|Id|) in as-patterns). F++ parses a TOTAL
// active pattern and has the ActiveChoice machinery behind it, but a match on
// one traps at run time, and the PARTIAL form (`(|Pos|_|)` returning an
// option) does not typecheck at all — the single largest gap this directory
// shows. The `&` (and) pattern is dropped with them.
// `:? int` on a boxed scalar is a documented divergence (typed boxes), so the
// dynamic tests here use user types.
module Core_patmatch

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- constants: one arm per literal type --------------------------------

let intConst (x : int) : int =
    match x with
    | 0 -> 100
    | 1 -> 101
    | -1 -> 102
    | _ -> 0 - 1

test "const-int-zero" (intConst 0 = 100)
test "const-int-one" (intConst 1 = 101)
test "const-int-neg" (intConst (0 - 1) = 102)
test "const-int-other" (intConst 7 = 0 - 1)

let charConst (c : char) : bool =
    match c with
    | 'a' -> true
    | '\\' -> false
    | _ -> false

test "const-char" (charConst 'a')
test "const-char-escape" (not (charConst '\\'))
test "const-char-other" (not (charConst 'z'))

let strConst (s : string) : int =
    match s with
    | "" -> 0
    | "one" -> 1
    | "two" -> 2
    | _ -> 0 - 1

test "const-string-empty" (strConst "" = 0)
test "const-string" (strConst "two" = 2)
test "const-string-other" (strConst "three" = 0 - 1)

let boolConst (b : bool) : int =
    match b with
    | true -> 1
    | false -> 0

test "const-bool" (boolConst true = 1 && boolConst false = 0)

let wideConst (x : int64) : int =
    match x with
    | 0L -> 0
    | 9223372036854775807L -> 1
    | _ -> 2

test "const-int64" (wideConst 0L = 0)
test "const-int64-max" (wideConst 9223372036854775807L = 1)

let floatConst (x : float) : int =
    match x with
    | 0.0 -> 0
    | 1.5 -> 1
    | _ -> 2

test "const-float" (floatConst 1.5 = 1)
// IEEE: a NaN scrutinee equals no literal, not even a NaN one
test "const-float-nan-falls-through" (floatConst nan = 2)
// and -0.0 IS 0.0
test "const-float-negzero" (floatConst (0.0 - 0.0) = 0)

let unitConst (u : unit) : int =
    match u with
    | () -> 7

test "const-unit" (unitConst () = 7)

// ---- guards decide between arms that match alike -------------------------

let sign3 (x : int) : int =
    match x with
    | 0 -> 0
    | x when x < 0 -> 0 - 1
    | _ -> 1

test "guard-zero" (sign3 0 = 0)
test "guard-neg" (sign3 (0 - 5) = 0 - 1)
test "guard-pos" (sign3 5 = 1)

// a guard that fails falls through to the NEXT arm, not out of the match
let guardFallthrough (x : int) : string =
    match x with
    | n when n > 100 -> "big"
    | n when n > 10 -> "medium"
    | n when n > 0 -> "small"
    | _ -> "none"

test "guard-fallthrough-big" (guardFallthrough 200 = "big")
test "guard-fallthrough-medium" (guardFallthrough 50 = "medium")
test "guard-fallthrough-small" (guardFallthrough 5 = "small")
test "guard-fallthrough-none" (guardFallthrough 0 = "none")

// ---- tuples --------------------------------------------------------------

let tupleShape (p : int * int) : string =
    match p with
    | (0, 0) -> "origin"
    | (0, _) -> "x-axis"
    | (_, 0) -> "y-axis"
    | _ -> "other"

test "tuple-origin" (tupleShape (0, 0) = "origin")
test "tuple-x" (tupleShape (0, 5) = "x-axis")
test "tuple-y" (tupleShape (5, 0) = "y-axis")
test "tuple-other" (tupleShape (1, 1) = "other")

let nestedTuple (p : (int * int) * (int * int)) : int =
    match p with
    | ((1, 2), (3, 4)) -> 1
    | ((1, _), (_, 4)) -> 2
    | _ -> 3

test "tuple-nested-exact" (nestedTuple ((1, 2), (3, 4)) = 1)
test "tuple-nested-partial" (nestedTuple ((1, 9), (9, 4)) = 2)
test "tuple-nested-none" (nestedTuple ((9, 9), (9, 9)) = 3)

// a tuple pattern in a LET binds every component at once
let (tx, ty) = (11, 22)
test "tuple-let" (tx = 11 && ty = 22)

// ---- as-patterns ---------------------------------------------------------

let t1 = (1, 2)
let (ax, ay) as asPatResult = t1
test "as-let-components" (ax = 1 && ay = 2)
test "as-let-whole" (asPatResult = (1, 2))

let asInMatch (xs : int list) : int =
    match xs with
    | (h :: _) as whole -> h + List.length whole
    | [] -> 0

test "as-match" (asInMatch [ 10; 1; 1 ] = 13)
test "as-match-empty" (asInMatch [] = 0)

// NOTE: the `&` (and) pattern of the upstream And/ directory is NOT in the
// subset — F++ has no AndPat. Upstream's own comment says it is "pretty much
// only useful with active patterns", which are the larger gap here.

// ---- lists and cons ------------------------------------------------------

let rec lengthOf (xs : int list) : int =
    match xs with
    | [] -> 0
    | _ :: [] -> 1
    | _ :: _ :: [] -> 2
    | _ :: tail -> 1 + lengthOf tail

test "cons-empty" (lengthOf [] = 0)
test "cons-one" (lengthOf [ 1 ] = 1)
test "cons-two" (lengthOf [ 1; 2 ] = 2)
test "cons-ten" (lengthOf [ 1 .. 10 ] = 10)

let listLiteralPat (xs : int list) : int =
    match xs with
    | [ 1 ] -> 1
    | [ 1; 2 ] -> 2
    | [ 1; 2; 3 ] -> 3
    | _ -> 0 - 1

test "list-literal-1" (listLiteralPat [ 1 ] = 1)
test "list-literal-2" (listLiteralPat [ 1; 2 ] = 2)
test "list-literal-3" (listLiteralPat [ 1; 2; 3 ] = 3)
test "list-literal-none" (listLiteralPat [ 9 ] = 0 - 1)

// a head/tail split binds both halves
let headTail (xs : int list) : int * int =
    match xs with
    | h :: t -> h, List.length t
    | [] -> 0 - 1, 0 - 1

test "cons-binds" (headTail [ 5; 6; 7 ] = (5, 2))

// ---- arrays --------------------------------------------------------------

let arrayPat (xs : int[]) : int =
    match xs with
    | [| 1 |] -> 1
    | [| 1; 2 |] -> 2
    | [| 1; 2; 3 |] -> 3
    | _ -> 0 - 1

test "array-1" (arrayPat [| 1 |] = 1)
test "array-2" (arrayPat [| 1; 2 |] = 2)
test "array-3" (arrayPat [| 1; 2; 3 |] = 3)
test "array-none" (arrayPat [| 4; 5 |] = 0 - 1)
test "array-empty" (arrayPat [||] = 0 - 1)

let arrayBinds (xs : int[]) : int =
    match xs with
    | [| a; b |] -> a * b
    | _ -> 0

test "array-binds" (arrayBinds [| 6; 7 |] = 42)

// ---- records: a SUBSET of the fields may be named ------------------------

type Kind =
    | Plant
    | Animal
    | Mineral

type Thing = { Name : string; Age : int; Kind : Kind }

let isAnimal (t : Thing) : bool =
    match t with
    | { Kind = Animal } -> true
    | _ -> false

let isSteve (t : Thing) : bool =
    match t with
    | { Name = "Steve"; Age = 2 } -> true
    | _ -> false

let animal = { Name = "Steve"; Age = 2; Kind = Animal }
let plant = { Name = "Sunflower"; Age = 5; Kind = Plant }
let rock = { Name = "Gold"; Age = 500000; Kind = Mineral }

test "record-one-field" (isAnimal animal)
test "record-one-field-no" (not (isAnimal rock))
test "record-two-fields" (isSteve animal)
test "record-two-fields-no" (not (isSteve plant))

type Person = { PName : string; PAge : int }

type Band =
    | Child
    | Adult
    | Senior

let getBand (p : Person) : Band =
    match p with
    | { PName = _; PAge = age } when age < 12 -> Child
    | { PName = _; PAge = age } when age > 55 -> Senior
    | { PName = _; PAge = _ } -> Adult

test "record-guard-senior" (getBand { PName = "Abe"; PAge = 70 } = Senior)
test "record-guard-adult" (getBand { PName = "Homer"; PAge = 40 } = Adult)
test "record-guard-child" (getBand { PName = "Lisa"; PAge = 11 } = Child)

// nested record patterns
type Wrapper = { Tag : string; Inner : Person }

let innerAge (w : Wrapper) : int =
    match w with
    | { Inner = { PAge = a } } -> a

test "record-nested" (innerAge { Tag = "t"; Inner = { PName = "Bart"; PAge = 10 } } = 10)

// ---- unions --------------------------------------------------------------

type Shape =
    | Circle of float
    | Rect of float * float
    | Empty

let area (s : Shape) : float =
    match s with
    | Circle r -> 3.0 * r * r
    | Rect (w, h) -> w * h
    | Empty -> 0.0

test "union-circle" (area (Circle 2.0) = 12.0)
test "union-rect" (area (Rect (3.0, 4.0)) = 12.0)
test "union-empty" (area Empty = 0.0)

// a union pattern nested inside another
type Outcome =
    | Got of Shape
    | Nothing

let nestedUnion (o : Outcome) : string =
    match o with
    | Got (Circle _) -> "circle"
    | Got (Rect (w, h)) when w = h -> "square"
    | Got (Rect _) -> "rect"
    | Got Empty -> "empty"
    | Nothing -> "nothing"

test "union-nested-circle" (nestedUnion (Got (Circle 1.0)) = "circle")
test "union-nested-square" (nestedUnion (Got (Rect (2.0, 2.0))) = "square")
test "union-nested-rect" (nestedUnion (Got (Rect (2.0, 3.0))) = "rect")
test "union-nested-empty" (nestedUnion (Got Empty) = "empty")
test "union-nested-nothing" (nestedUnion Nothing = "nothing")

// or-patterns: several shapes, one arm, provided they bind the same names
let orPattern (s : Shape) : float =
    match s with
    | Circle x | Rect (x, _) -> x
    | Empty -> 0.0

test "or-pattern-circle" (orPattern (Circle 5.0) = 5.0)
test "or-pattern-rect" (orPattern (Rect (6.0, 7.0)) = 6.0)
test "or-pattern-empty" (orPattern Empty = 0.0)

// or-patterns over constants bind nothing and just widen an arm
let vowel (c : char) : bool =
    match c with
    | 'a' | 'e' | 'i' | 'o' | 'u' -> true
    | _ -> false

test "or-const-yes" (vowel 'e')
test "or-const-no" (not (vowel 'z'))

// ---- options and results -------------------------------------------------

let optPat (o : int option) : int =
    match o with
    | Some 0 -> 0
    | Some x when x < 0 -> 0 - 1
    | Some _ -> 1
    | None -> 0 - 2

test "option-some-zero" (optPat (Some 0) = 0)
test "option-some-neg" (optPat (Some (0 - 3)) = 0 - 1)
test "option-some-pos" (optPat (Some 3) = 1)
test "option-none" (optPat None = 0 - 2)

let resPat (r : Result<int, string>) : string =
    match r with
    | Ok 0 -> "zero"
    | Ok _ -> "ok"
    | Error "" -> "blank"
    | Error _ -> "err"

test "result-ok-zero" (resPat (Ok 0) = "zero")
test "result-ok" (resPat (Ok 5) = "ok")
test "result-error-blank" (resPat (Error "") = "blank")
test "result-error" (resPat (Error "x") = "err")

// ---- wildcards and ordering ----------------------------------------------

// the FIRST matching arm wins, even when a later one also matches
let firstWins (x : int) : int =
    match x with
    | _ when x > 0 -> 1
    | 5 -> 2
    | _ -> 3

test "first-arm-wins" (firstWins 5 = 1)

// a wildcard inside a tuple ignores that component entirely
let ignoreSecond (p : int * string) : int =
    match p with
    | (n, _) -> n

test "wildcard-component" (ignoreSecond (9, "anything") = 9)

// ---- dynamic type tests over user types ----------------------------------

type Animal2 =
    abstract member Legs : int

type Dog () =
    interface Animal2 with
        member _.Legs = 4

type Bird () =
    interface Animal2 with
        member _.Legs = 2

let describe (a : Animal2) : string =
    match a with
    | :? Dog -> "dog"
    | :? Bird -> "bird"
    | _ -> "other"

test "typetest-dog" (describe (Dog () :> Animal2) = "dog")
test "typetest-bird" (describe (Bird () :> Animal2) = "bird")
test "typetest-legs" ((Dog () :> Animal2).Legs = 4)

// ---- `function` is a match on the argument -------------------------------

let classify =
    function
    | 0 -> "zero"
    | 1 -> "one"
    | _ -> "many"

test "function-zero" (classify 0 = "zero")
test "function-one" (classify 1 = "one")
test "function-many" (classify 42 = "many")

// ---- patterns in a `for` and in a lambda ---------------------------------

let mutable pairSum = 0
for (a, b) in [ (1, 2); (3, 4) ] do
    pairSum <- pairSum + a * b

test "for-tuple-pattern" (pairSum = 14)

let addPair = fun (a, b) -> a + b
test "lambda-tuple-pattern" (addPair (20, 22) = 42)

// a function parameter destructures a record
let ageOf { PName = _; PAge = a } = a
test "param-record-pattern" (ageOf { PName = "Maggie"; PAge = 1 } = 1)

printfn "DONE tests=%d failures=%d" ntests failures

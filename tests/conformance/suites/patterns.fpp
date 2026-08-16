// Ported from dotnet/fsharp tests/fsharp/core/patterns/test.fsx into the
// common F#/F++ subset. Dropped: every active-pattern module ((|Rect|),
// (|Even|Odd|), JoinList/UnZip/LazyList/XmlPattern/RegExp/Combinator —
// active patterns are not in F++), custom exception declarations
// (`exception XInt of int`), quotation examples, System.Type examples.
// The top-level pattern battery and the plain match-shape semantics are
// kept faithfully.
module Core_patterns

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- what kinds of top-level let patterns are possible? ------------------

type R2 = { F1 : int; F2 : int }
type Either<'a, 'b> = | This of 'a | That of 'b

// those with no variables (assert-or-trap, as F#'s MatchFailureException)
let () = ()
let 1 = 1
let (1) = (1)
let 1, 2, 3 = (1, 2, 3)
let (None) = None
let (1, 2, 3) = (1, 2, 3)
let [ 1 ] = [ 1 ]
let [ 1; 2 ] = [ 1; 2 ]
let (Some 1) = Some 1
let { F1 = f1v; F2 = f2v } = { F1 = 1; F2 = 2 }
test "toplevel-record" (f1v = 1 && f2v = 2)

// those with some variables
let (v1) = (1)
let (v2, v3) = (2, 3)
let v4, v5, v6 = (4, 5, 6)
let [ v8 ] = [ 8 ]
let [ v9; v10 ] = [ 9; 10 ]
let (Some v11) = Some 11
let v12, v13 = (let { F1 = a; F2 = b } = { F1 = 12; F2 = 13 } in (a, b))
let w1, [ w2, Some (w3, w4) ] = 1, [ 2, Some (3, 4) ]

test "toplevel-vars" (v1 = 1 && v2 = 2 && v3 = 3 && v4 = 4 && v5 = 5 && v6 = 6)
test "toplevel-lists" (v8 = 8 && v9 = 9 && v10 = 10)
test "toplevel-some" (v11 = 11 && v12 = 12 && v13 = 13)
test "toplevel-nested" (w1 = 1 && w2 = 2 && w3 = 3 && w4 = 4)

// those with alternatives
let this_10 = This 10
let that_20 = That 20
let (This eiA | That eiA) = this_10
let (This eiB | That eiB) = that_20
test "toplevel-or1" (eiA = 10)
test "toplevel-or2" (eiB = 20)

// relics
let aaa : int list = []
let bb = match aaa with x :: xs -> x | [] -> 0
let [ p, q, r, (sA, sB) ] = [ 1, 2, 3, (4, 5) ]
let [ 1 ], ra, rb, rc = List.map (fun x -> x) [ 1 ], 11, 12, 13
let tryRes = try failwith "a" with e -> 12
let [ x2 ] = [ 1 ]

test "relic-bb" (bb = 0)
test "relic-list-tuple" (p = 1 && q = 2 && r = 3 && sA = 4 && sB = 5)
test "relic-map" (ra = 11 && rb = 12 && rc = 13)
test "relic-try" (tryRes = 12)
test "relic-x2" (x2 = 1)

// ---- string and null patterns (bug 438) ----------------------------------

let bug438repro (tok : string) =
    match tok with
    | null -> 11
    | "" -> 22
    | "aa" -> 33
    | str -> 99

test "bug438-empty" (bug438repro "" = 22)
test "bug438-aa" (bug438repro "aa" = 33)
test "bug438-other" (bug438repro "bb" = 99)

// ---- match shapes over unions -------------------------------------------

type IList =
    | Nil
    | Single of int
    | Join of IList * IList

let rec firstOf (l : IList) : int option =
    match l with
    | Single x -> Some x
    | Join (a, b) ->
        (match firstOf a with
         | Some x -> Some x
         | None -> firstOf b)
    | Nil -> None

let deep = Join (Join (Nil, Join (Nil, Single 7)), Single 9)
test "union-first" (firstOf deep = Some 7)
test "union-first-empty" (firstOf (Join (Nil, Nil)) = None)

// nested ctor patterns in one match
let classify (l : IList) =
    match l with
    | Join (Single a, Single b) -> a + b
    | Join (Nil, Single b) -> b
    | Join (Single a, Nil) -> a
    | Single a -> a
    | _ -> -1

test "nested-1" (classify (Join (Single 3, Single 4)) = 7)
test "nested-2" (classify (Join (Nil, Single 5)) = 5)
test "nested-3" (classify (Join (Single 6, Nil)) = 6)
test "nested-4" (classify (Single 8) = 8)
test "nested-5" (classify (Join (Join (Nil, Nil), Nil)) = -1)

// guards and as-patterns
let guarded (x : int list) =
    match x with
    | h :: _ when h > 10 -> "big"
    | (h :: _) as whole when List.length whole > 2 -> "long"
    | [ _ ] -> "one"
    | _ -> "other"

test "guard-big" (guarded [ 11 ] = "big")
test "guard-long" (guarded [ 1; 2; 3 ] = "long")
test "guard-one" (guarded [ 1 ] = "one")
test "guard-other" (guarded [] = "other")

// or-patterns in match with shared binders
let orb (e : Either<int, int>) =
    match e with
    | This n | That n -> n * 2

test "orb-this" (orb (This 21) = 42)
test "orb-that" (orb (That 10) = 20)

// literal char and bool patterns
let charCase (c : char) =
    match c with
    | 'a' -> 1
    | 'b' -> 2
    | _ -> 0

test "char-a" (charCase 'a' = 1)
test "char-b" (charCase 'b' = 2)
test "char-z" (charCase 'z' = 0)

let boolCase (b : bool) = match b with true -> "t" | false -> "f"
test "bool-t" (boolCase true = "t")
test "bool-f" (boolCase false = "f")

// cons chains
let thirdOr (d : int) (xs : int list) =
    match xs with
    | _ :: _ :: x :: _ -> x
    | _ -> d

test "cons3-hit" (thirdOr 0 [ 1; 2; 3; 4 ] = 3)
test "cons3-miss" (thirdOr 0 [ 1; 2 ] = 0)

// polymorphic or-pattern binder over closures
let this_f1 : Either<int -> int, int -> int> = This (fun x -> x + 1)
let that_f2 : Either<int -> int, int -> int> = That (fun x -> x * 2)
let (This fA | That fA) = this_f1
let (This fB | That fB) = that_f2
test "poly-or-f1" (fA 4 = 5)
test "poly-or-f2" (fB 4 = 8)

// ---- record patterns in matches -----------------------------------------

type RML = { A : int; B : string }
let rpick (r : RML) =
    match r with
    | { A = 1 } -> "one"
    | { A = n; B = "hi" } -> "hi" + string n
    | { B = s } when s = "guarded" -> "g"
    | { B = s } -> s

test "recpat-1" (rpick { A = 1; B = "z" } = "one")
test "recpat-2" (rpick { A = 5; B = "hi" } = "hi5")
test "recpat-3" (rpick { A = 9; B = "guarded" } = "g")
test "recpat-4" (rpick { A = 9; B = "tail" } = "tail")
let rg (r : RML) = match r with { A = n } when n > 3 -> "big" | _ -> "small"
test "recpat-guard" (rg { A = 4; B = "" } = "big" && rg { A = 1; B = "" } = "small")

printfn "DONE tests=%d failures=%d" ntests failures

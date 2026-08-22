// TYPE INFERENCE, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/InferenceProcedures
// (Generalization/*, TypeInference/*, ResolvingApplicationExpressions) into
// the common F#/F++ subset.
//
// The interesting thing about these is that they check the SHAPE inference
// arrives at, not a value: a binding that must generalize is USED at two
// different types, so a compiler that generalized too little fails to build
// and one that generalized too much answers wrongly.
//
// DROPPED: the value-restriction diagnostics (the negative gate's job),
// `inline` member constraints resolved by SRTP, and the .fsi signature
// cases.
module Core_inference

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- generalization of a RECURSIVE GROUP ---------------------------------

// upstream GenGroup01: `g` is used twice inside `f`, so the group generalizes
// only after both are solved
let rec f1 x = (g1 x, g1 x)
and g1 x = [ x ]

test "recgroup-int" (f1 5 = ([ 5 ], [ 5 ]))
test "recgroup-string" (f1 "a" = ([ "a" ], [ "a" ]))

// mutual recursion where one side is used at a DIFFERENT type than the other
let rec evens n = if n = 0 then true else odds (n - 1)
and odds n = if n = 0 then false else evens (n - 1)

test "mutual-even" (evens 10)
test "mutual-odd" (not (evens 7))

// ---- a binding generalizes, and both uses are independent ----------------

let idf x = x

test "generalized-int" (idf 3 = 3)
test "generalized-string" (idf "s" = "s")
test "generalized-list" (idf [ 1 ] = [ 1 ])

let pairUp a b = (a, b)

test "two-vars-int-string" (pairUp 1 "x" = (1, "x"))
test "two-vars-bool-float" (pairUp true 2.5 = (true, 2.5))

// a function taking a FUNCTION generalizes over both
let twice fn x = fn (fn x)

test "hof-int" (twice (fun n -> n + 1) 0 = 2)
test "hof-string" (twice (fun s -> s + "!") "a" = "a!!")

// ---- annotations pin what inference would otherwise leave open -----------

let annotated (x : int) : int = x + 1
test "annotated" (annotated 1 = 2)

// the annotation on ONE side settles the other
let addTo (x : int) y = x + y
test "annotation-propagates" (addTo 1 2 = 3)

// ---- inference through a record ------------------------------------------

type Holder<'a> = { Held : 'a; Count : int }

let hold v = { Held = v; Count = 1 }

test "record-generic-int" ((hold 5).Held = 5)
test "record-generic-string" ((hold "s").Held = "s")
test "record-field-known" ((hold 5).Count = 1)

// a function over the generic record stays generic
let heldOf (h : Holder<'a>) : 'a = h.Held

test "record-fn-int" (heldOf (hold 7) = 7)
test "record-fn-list" (heldOf (hold [ 1; 2 ]) = [ 1; 2 ])

// ---- inference through a union -------------------------------------------

type Tree<'a> =
    | Leaf of 'a
    | Node of Tree<'a> * Tree<'a>

let rec sizeOf (t : Tree<'a>) : int =
    match t with
    | Leaf _ -> 1
    | Node (l, r) -> sizeOf l + sizeOf r

test "union-generic-int" (sizeOf (Node (Leaf 1, Leaf 2)) = 2)
test "union-generic-string" (sizeOf (Node (Leaf "a", Node (Leaf "b", Leaf "c"))) = 3)

let rec mapTree (fn : 'a -> 'b) (t : Tree<'a>) : Tree<'b> =
    match t with
    | Leaf v -> Leaf (fn v)
    | Node (l, r) -> Node (mapTree fn l, mapTree fn r)

test "map-tree" (sizeOf (mapTree (fun n -> string n) (Node (Leaf 1, Leaf 2))) = 2)
test "map-tree-value" (match mapTree (fun n -> n + 1) (Leaf 1) with Leaf v -> v = 2 | _ -> false)

// ---- a generic CLASS whose method introduces its own variable ------------

// upstream LessRestrictive01, without the tuple-of-tuples result
type Vec<'a> (x : 'a, y : 'a) =
    member _.X = x
    member _.Y = y
    // the method's OWN parameter, declared: an inferred one would be
    // pinned by the first use
    member _.PairWith<'b> (w : 'b) : 'a * 'b = (x, w)

let vi = Vec<int> (1, 2)
let vs = Vec<string> ("a", "b")

test "class-generic-int" (vi.X = 1 && vi.Y = 2)
test "class-generic-string" (vs.X = "a")
test "method-own-var-int" (vi.PairWith "z" = (1, "z"))
test "method-own-var-float" (vi.PairWith 2.5 = (1, 2.5))

// ---- inference decides an operator's type from its operands --------------

// arithmetic does NOT generalize on its own in F# (that needs `inline` and
// a member constraint): one annotated operand settles the operator
let addInt (a : int) b = a + b
let addFloat (a : float) b = a + b
let addStr (a : string) b = a + b

test "op-int" (addInt 1 2 = 3)
test "op-float" (addFloat 1.5 2.5 = 4.0)
test "op-string" (addStr "a" "b" = "ab")

// ---- unit parameters are ignored, not inferred away ----------------------

let unitTaker () = 42
test "unit-param" (unitTaker () = 42)

let curriedUnit () x = x + 1
test "unit-then-arg" (curriedUnit () 1 = 2)

// ---- the result type flows BACKWARDS through a branch --------------------

let branchInfers b = if b then [] else [ 1 ]

test "branch-empty" (List.isEmpty (branchInfers true))
test "branch-full" (branchInfers false = [ 1 ])

// a match whose arms decide one type together
let matchInfers (o : int option) =
    match o with
    | Some v -> [ v ]
    | None -> []

test "match-arms-agree" (matchInfers (Some 3) = [ 3 ] && List.isEmpty (matchInfers None))

// ---- a LATER use settles an earlier binding ------------------------------

// `acc` starts as an empty list and only the fold says what it holds
let sumInto (xs : int list) =
    let mutable acc = []
    for x in xs do
        acc <- x :: acc
    List.rev acc

test "mutable-inferred" (sumInto [ 1; 2; 3 ] = [ 1; 2; 3 ])

// ---- application resolution: a function VALUE applied later --------------

let applyTo (fn : int -> int) (x : int) = fn x
let addOne = fun n -> n + 1

test "apply-value" (applyTo addOne 4 = 5)
test "apply-lambda" (applyTo (fun n -> n * 2) 4 = 8)

// a partial application under a parameter stays generic (bare, it would meet
// the value restriction)
let const3 x = pairUp 3 x
test "partial-int" (const3 "s" = (3, "s"))
test "partial-bool" (const3 true = (3, true))

printfn "DONE tests=%d failures=%d" ntests failures

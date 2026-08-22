// Generated ORDERING, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/GeneratedEqualityHashing-
// Comparison (Basic/Comparison01.fs, Basic/Unions.fsx, Basic/Options.fsx,
// Basic/Sample_Records.fsx, Basic/Sample_Tuples.fsx, Basic/Lists.fsx,
// Basic/Structs.fsx and the IComparison record/DU/struct cases).
//
// The upstream files answer through `exit 1`; here every line is an assert,
// which keeps the failure NAMED. Comparison is checked through all four
// ordering operators AND through `compare` — an operator lowers per shape
// while `compare` passed as a value lands in the runtime walker, and the two
// have disagreed before.
//
// DROPPED: `[|DU.B|] > [|DU.A|]` and the other ARRAY comparisons — an array
// compares by REFERENCE here (DIVERGENCES.md), so the upstream lines are
// carried over the equivalent lists. Custom equality/comparison attributes
// ([<CustomEquality>], [<CustomComparison>]) are not in the subset, and
// exceptions have no comparison in F# either.
module Core_comparison

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// every ordering answer at once: the four operators AND `compare`, which is
// the runtime walker rather than the shaped lowering
let lt (a : 'a) (b : 'a) : bool =
    a < b && a <= b && not (a > b) && not (a >= b) && compare a b < 0 && compare b a > 0

let eqv (a : 'a) (b : 'a) : bool =
    not (a < b) && a <= b && not (a > b) && a >= b && compare a b = 0

// ---- tuples: lexicographic, left to right ---------------------------------

let baseline = (1, 2, 3, 4, 5)

test "tuple5-self-eq" (eqv (1, 2, 3, 4, 5) baseline)
test "tuple5-first" (lt (0, 2, 3, 4, 5) baseline)
test "tuple5-second" (lt (1, 1, 3, 4, 5) baseline)
test "tuple5-third" (lt (1, 2, 2, 4, 5) baseline)
test "tuple5-fourth" (lt (1, 2, 3, 3, 5) baseline)
test "tuple5-fifth" (lt (1, 2, 3, 4, 4) baseline)
test "tuple5-first-wins" (lt baseline (2, 0, 0, 0, 0))
test "tuple5-gt-first" (lt baseline (2, 2, 3, 4, 5))
test "tuple5-gt-last" (lt baseline (1, 2, 3, 4, 6))

test "tuple2-str-eq" (eqv ("B", "B") ("B", "B"))
test "tuple2-str-both" (lt ("A", "A") ("B", "B"))
test "tuple2-str-second" (lt ("B", "A") ("B", "B"))
test "tuple2-str-first" (lt ("A", "B") ("B", "B"))

let baseline2 = (("A", "A"), ("B", "B"), ("C", "C"))
test "nested-tuple-eq" (eqv (("A", "A"), ("B", "B"), ("C", "C")) baseline2)
// all equal but the last element of the last, nested tuple
test "nested-tuple-deep-last" (lt (("A", "A"), ("B", "B"), ("C", "B")) baseline2)
// lower everywhere later, but higher at the very beginning
test "nested-tuple-first-wins" (lt baseline2 (("A", "B"), ("A", "A"), ("A", "A")))

// ---- NaN: no operator answers true, in any shape --------------------------

// upstream's helper: OR together every operator's answer, which must stay
// false when a NaN is anywhere inside
let anyOp (x : 'a) (y : 'a) : bool = x < y || x > y || x <= y || x >= y || x = y

test "nan-scalar" (not (anyOp nan 0.0) && not (anyOp 0.0 nan))
test "nan-scalar32" (not (anyOp nanf 0.0f) && not (anyOp 0.0f nanf))
test "nan-tuple" (not (anyOp (1, nan, 3) (1, 0.0, 3)) && not (anyOp (1, 0.0, 3) (1, nan, 3)))
test "nan-tuple32" (not (anyOp (1, nanf, 3) (1, 0.0f, 3)) && not (anyOp (1, 0.0f, 3) (1, nanf, 3)))

type R1 = { a : float; b : float }

test "nan-record" (not (anyOp { a = 0.0; b = nan } { a = 0.0; b = 0.0 }))
test "nan-record-rev" (not (anyOp { a = 0.0; b = 0.0 } { a = 0.0; b = nan }))
test "nan-list" (not (anyOp [ 1.0; nan ] [ 1.0; 0.0 ]))
test "nan-option" (not (anyOp (Some nan) (Some 0.0)))

// `compare` is a TOTAL order even where the operators all answer false: NaN
// is equal to itself and below every number (DIVERGENCES has neither — this
// is F#'s own split between IEEE equality and ordering)
test "nan-compare-self" (compare nan nan = 0)
test "nan-compare-below" (compare nan 0.0 < 0 && compare 0.0 nan > 0)
test "nan-compare-in-tuple" (compare (1, nan) (1, nan) = 0)
test "nan-equality-false" (not ([ nan ] = [ nan ]) && not ({ a = nan; b = 1.0 } = { a = nan; b = 1.0 }))

// ---- unions order by CASE ORDER, then by payload --------------------------

type DU =
    | A
    | B

type DU2 =
    | B2
    | A2

test "du-eq" (eqv (DU.A, DU.B) (DU.A, DU.B))
test "du-hash" (hash (DU.A, DU.B) = hash (DU.A, DU.B))
test "du-tag-order" (lt (DU.A, DU.B) (DU.B, DU.A))
test "du-list-order" (lt [ DU.A ] [ DU.B ])
// the same case NAMES declared the other way round order the other way round
test "du2-tag-order" (lt (DU2.B2, DU2.A2) (DU2.A2, DU2.B2))
test "du2-list-order" (lt [ DU2.B2 ] [ DU2.A2 ])

type Payload =
    | Zero
    | One of int
    | Two of int * string

test "du-payload-tag-first" (lt Zero (One 0))
test "du-payload-tag-first2" (lt (One 999) (Two (0, "")))
test "du-payload-value" (lt (One 1) (One 2))
test "du-payload-tuple-second" (lt (Two (1, "a")) (Two (1, "b")))
test "du-payload-tuple-first" (lt (Two (1, "z")) (Two (2, "a")))
test "du-payload-eq" (eqv (Two (1, "a")) (Two (1, "a")))

type Tree =
    | Leaf of int
    | Node of Tree * Tree

test "tree-order-leafs" (lt (Leaf 1) (Leaf 2))
test "tree-order-tag" (lt (Leaf 999) (Node (Leaf 0, Leaf 0)))
test "tree-order-deep" (lt (Node (Leaf 1, Leaf 1)) (Node (Leaf 1, Leaf 2)))
test "tree-eq" (eqv (Node (Leaf 1, Leaf 2)) (Node (Leaf 1, Leaf 2)))

// ---- options: None below every Some --------------------------------------

test "opt-none-eq" (eqv (None : int option) None)
test "opt-none-lowest" (lt (None : int option) (Some 0))
test "opt-none-lowest-neg" (lt (None : int option) (Some (0 - 999)))
test "opt-some-order" (lt (Some 1) (Some 2))
test "opt-nested" (lt (Some (Some 1)) (Some (Some 2)))
test "opt-nested-none" (lt (Some (None : int option)) (Some (Some 0)))
test "opt-in-tuple" (lt (1, (None : int option)) (1, Some 0))

// ---- results --------------------------------------------------------------

let okA : Result<int, string> = Ok 1
let okB : Result<int, string> = Ok 2
let errA : Result<int, string> = Error "a"

test "result-ok-order" (lt okA okB)
test "result-ok-below-error" (lt okA errA)
test "result-eq" (eqv okA (Ok 1))

// ---- records compare in DECLARATION order ---------------------------------

// the field order the SOURCE declares is the comparison order, whatever the
// runtime layout does with the fields (a scalar-first layout compared `n`
// before `name` here, which disagreed with a hand-written instance)
type Person = { name : string; n : int }

test "rec-decl-order-first" (lt { name = "a"; n = 999 } { name = "b"; n = 0 })
test "rec-decl-order-second" (lt { name = "a"; n = 1 } { name = "a"; n = 2 })
test "rec-eq" (eqv { name = "a"; n = 1 } { name = "a"; n = 1 })

// the same fields the other way round order the other way round
type Person2 = { n2 : int; name2 : string }

test "rec-decl-order-rev" (lt { n2 = 0; name2 = "z" } { n2 = 1; name2 = "a" })

// a record mixing widths: byte/char/bool ride packed slots, the refs do not
type Mixed = { s1 : string; i1 : int; c1 : char; s2 : string; b1 : bool; f1 : float }

let mixedBase = { s1 = "m"; i1 = 5; c1 = 'c'; s2 = "s"; b1 = true; f1 = 1.5 }

test "mixed-eq" (eqv mixedBase { s1 = "m"; i1 = 5; c1 = 'c'; s2 = "s"; b1 = true; f1 = 1.5 })
test "mixed-first" (lt { mixedBase with s1 = "l" } mixedBase)
test "mixed-second" (lt { mixedBase with i1 = 4 } mixedBase)
test "mixed-third" (lt { mixedBase with c1 = 'b' } mixedBase)
test "mixed-fourth" (lt { mixedBase with s2 = "r" } mixedBase)
test "mixed-fifth" (lt { mixedBase with b1 = false } mixedBase)
test "mixed-sixth" (lt { mixedBase with f1 = 1.25 } mixedBase)
// an earlier field outranks every later one
test "mixed-first-outranks"
    (lt { s1 = "l"; i1 = 99; c1 = 'z'; s2 = "z"; b1 = true; f1 = 9.0 } mixedBase)

// nested records
type Outer = { tag : string; inner : Person }

test "rec-nested-outer" (lt { tag = "a"; inner = { name = "z"; n = 9 } } { tag = "b"; inner = { name = "a"; n = 0 } })
test "rec-nested-inner" (lt { tag = "a"; inner = { name = "a"; n = 0 } } { tag = "a"; inner = { name = "a"; n = 1 } })

// ---- lists: element by element, then length -------------------------------

test "list-empty-lowest" (lt ([] : int list) [ 0 ])
test "list-prefix" (lt [ 1; 2 ] [ 1; 2; 3 ])
test "list-element" (lt [ 1; 2; 3 ] [ 1; 2; 4 ])
test "list-first-wins" (lt [ 1; 9; 9 ] [ 2; 0 ])
test "list-eq" (eqv [ 1; 2; 3 ] [ 1; 2; 3 ])
test "list-of-records" (lt [ { name = "a"; n = 1 } ] [ { name = "a"; n = 2 } ])
test "list-of-tuples" (lt [ (1, "a"); (2, "b") ] [ (1, "a"); (2, "c") ])
test "list-of-lists" (lt [ [ 1 ]; [ 2 ] ] [ [ 1 ]; [ 3 ] ])

// ---- struct tuples --------------------------------------------------------

test "struct-tuple-eq" (eqv (struct (1, "a")) (struct (1, "a")))
test "struct-tuple-first" (lt (struct (1, "z")) (struct (2, "a")))
test "struct-tuple-second" (lt (struct (1, "a")) (struct (1, "b")))

// ---- strings and chars ----------------------------------------------------

test "string-order" (lt "abc" "abd")
test "string-prefix" (lt "ab" "abc")
test "string-empty" (lt "" "a")
test "char-order" (lt 'a' 'b')
test "bool-order" (lt false true)

// ---- the operators, `compare` and SORTING all agree -----------------------

// List.sort passes `compare` as a VALUE, so a sorted answer pins the runtime
// walker against the same expectations the operators above pin
let sortedPeople = List.sort [ { name = "b"; n = 1 }; { name = "a"; n = 2 }; { name = "a"; n = 1 } ]

test "sort-records" (sortedPeople = [ { name = "a"; n = 1 }; { name = "a"; n = 2 }; { name = "b"; n = 1 } ])
test "sort-unions" (List.sort [ Two (1, "b"); Zero; One 5; Two (1, "a") ] = [ Zero; One 5; Two (1, "a"); Two (1, "b") ])
test "sort-tuples" (List.sort [ (2, "a"); (1, "z"); (1, "a") ] = [ (1, "a"); (1, "z"); (2, "a") ])
test "sort-options" (List.sort [ Some 2; None; Some 1 ] = [ None; Some 1; Some 2 ])
test "sort-lists" (List.sort [ [ 2 ]; []; [ 1; 2 ]; [ 1 ] ] = [ []; [ 1 ]; [ 1; 2 ]; [ 2 ] ])
// bound first: fsi rejects a continuation line that starts with `=`
let sortedMixed = List.sort [ { mixedBase with i1 = 6 }; mixedBase; { mixedBase with s1 = "a" } ]
let wantMixed = [ { mixedBase with s1 = "a" }; mixedBase; { mixedBase with i1 = 6 } ]
test "sort-mixed-records" (sortedMixed = wantMixed)

// max/min go through the same order
test "max-record" (max { name = "a"; n = 1 } { name = "a"; n = 2 } = { name = "a"; n = 2 })
test "min-union" (min (One 5) Zero = Zero)

// ---- equal implies compare 0 implies equal hashes -------------------------

let agrees (x : 'a) (y : 'a) : bool =
    let e = x = y
    let c = compare x y = 0
    e = c && (not e || hash x = hash y)

test "agree-record" (agrees { name = "a"; n = 1 } { name = "a"; n = 1 })
test "agree-record-ne" (agrees { name = "a"; n = 1 } { name = "a"; n = 2 })
test "agree-union" (agrees (Two (1, "a")) (Two (1, "a")))
test "agree-union-ne" (agrees (Two (1, "a")) (One 1))
test "agree-tuple" (agrees (1, "a", 2.0) (1, "a", 2.0))
test "agree-list" (agrees [ Some 1; None ] [ Some 1; None ])
test "agree-nested" (agrees (Some { name = "a"; n = 1 }) (Some { name = "a"; n = 1 }))
test "agree-mixed" (agrees mixedBase { s1 = "m"; i1 = 5; c1 = 'c'; s2 = "s"; b1 = true; f1 = 1.5 })

printfn "DONE tests=%d failures=%d" ntests failures

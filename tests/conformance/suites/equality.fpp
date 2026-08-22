// Structural equality, comparison and hashing over records, unions, tuples,
// options and lists — the shapes dotnet/fsharp's GenericComparisonAndEquality
// module covers (its own body drives them through SortedList/List<T>, which
// are out of subset, so the same types are driven through Map/Set/Dictionary
// here instead).
//
// The three relations have to agree with each other: values that are EQUAL
// must hash EQUAL and compare 0, and a structurally equal key must find its
// entry however it was built.
//
// ADAPTED: `Dictionary` is reached through `open System.Collections.Generic`
// rather than its fully-qualified name — F++ knows the type but not the
// namespace path, and an unresolved path becomes a field access that traps.
module Core_equality

open System.Collections.Generic

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

type RecA = { f1 : string; f2 : int }
type UnionA =
    | Foo of float
    | Int of int
    | Recursive of UnionA
type Tree =
    | Leaf
    | Node of Tree * int * Tree

// ---- records ------------------------------------------------------------

let ra1 = { f1 = "joj"; f2 = 69 }
let ra2 = { f1 = "joj"; f2 = 69 }
let ra3 = { f1 = "bri"; f2 = 68 }

test "rec-eq" (ra1 = ra2)
test "rec-neq" (not (ra1 = ra3))
test "rec-compare-0" (compare ra1 ra2 = 0)
test "rec-compare-order" (compare ra3 ra1 < 0)
// DECLARATION order decides: f1 first, f2 only as a tie-break
test "rec-compare-fields" (compare { f1 = "b"; f2 = 1 } { f1 = "a"; f2 = 2 } > 0)
let sortedRecs = List.sort [ { f1 = "b"; f2 = 9 }; { f1 = "b"; f2 = 2 }; { f1 = "a"; f2 = 5 } ]
test "rec-sort" (sortedRecs = [ { f1 = "a"; f2 = 5 }; { f1 = "b"; f2 = 2 }; { f1 = "b"; f2 = 9 } ])
test "rec-hash" (hash ra1 = hash ra2)
test "rec-in-list" (List.contains ra2 [ ra3; ra1 ])

// ---- unions -------------------------------------------------------------

test "union-eq" (Int 1 = Int 1)
test "union-neq-payload" (not (Int 1 = Int 2))
test "union-neq-case" (not (Int 1 = Foo 1.0))
test "union-compare-0" (compare (Int 1) (Int 1) = 0)
// cases order by DECLARATION order, then by payload
test "union-compare-case" (compare (Foo 9.0) (Int 0) < 0)
test "union-compare-payload" (compare (Int 1) (Int 2) < 0)
test "union-hash" (hash (Int 1) = hash (Int 1))
test "union-recursive-eq" (Recursive (Foo 3.0) = Recursive (Foo 3.0))
test "union-recursive-neq" (not (Recursive (Foo 3.0) = Recursive (Foo 4.0)))
test "union-recursive-hash" (hash (Recursive (Foo 3.0)) = hash (Recursive (Foo 3.0)))
test "union-nullary-eq" (Leaf = Leaf)

let t1 = Node (Node (Leaf, 1, Leaf), 2, Node (Leaf, 3, Leaf))
let t2 = Node (Node (Leaf, 1, Leaf), 2, Node (Leaf, 3, Leaf))
let t3 = Node (Node (Leaf, 1, Leaf), 2, Node (Leaf, 4, Leaf))

test "tree-eq" (t1 = t2)
test "tree-neq" (not (t1 = t3))
test "tree-compare-0" (compare t1 t2 = 0)
test "tree-compare-lt" (compare t1 t3 < 0)
test "union-nullary-compare" (compare Leaf (Node (Leaf, 1, Leaf)) < 0)
test "tree-hash" (hash t1 = hash t2)

// ---- tuples, options, lists --------------------------------------------

test "tuple-eq" ((1, "a", 2.0) = (1, "a", 2.0))
test "tuple-neq" (not ((1, "a") = (1, "b")))
test "tuple-compare" (compare (1, 2) (1, 3) < 0)
test "tuple-compare-first" (compare (2, 0) (1, 9) > 0)
test "tuple-hash" (hash (1, "a") = hash (1, "a"))
test "opt-eq" (Some 3 = Some 3)
test "opt-none" ((None : int option) = None)
test "opt-neq" (not (Some 3 = Some 4))
test "opt-compare-none-first" (compare (None : int option) (Some 0) < 0)
test "opt-hash" (hash (Some 3) = hash (Some 3))
test "list-eq" ([1;2;3] = [1;2;3])
test "list-neq-len" (not ([1;2] = [1;2;3]))
test "list-compare-prefix" (compare [1;2] [1;2;3] < 0)
test "list-hash" (hash [1;2;3] = hash [1;2;3])
test "nested-eq" ([ (1, { f1 = "a"; f2 = 2 }) ] = [ (1, { f1 = "a"; f2 = 2 }) ])
test "nested-hash" (hash [ Some (1, "x") ] = hash [ Some (1, "x") ])
test "string-eq" ("abc" = "abc")
test "string-hash" (hash "abc" = hash "abc")

// ---- the relations agree ------------------------------------------------

let sameShape = [ box ra1; box (Int 1); box t1; box (1, "a"); box (Some 3); box [1;2] ]
let sameShape2 = [ box ra2; box (Int 1); box t2; box (1, "a"); box (Some 3); box [1;2] ]

test "equal-implies-hash-equal"
     (List.forall2 (fun (a : obj) (b : obj) -> not (Unchecked.equals a b) || Unchecked.hash a = Unchecked.hash b) sameShape sameShape2)
test "equal-implies-compare-0"
     (List.forall2 (fun (a : obj) (b : obj) -> not (Unchecked.equals a b) || Unchecked.compare a b = 0) sameShape sameShape2)

// ---- as KEYS ------------------------------------------------------------

let mapByRec = Map.ofList [ (ra1, "one"); (ra3, "two") ]
test "map-record-key" (Map.tryFind ra2 mapByRec = Some "one")
test "map-record-missing" (Map.tryFind { f1 = "zz"; f2 = 0 } mapByRec = None)

let mapByUnion = Map.ofList [ (Int 1, "i"); (Foo 2.0, "f") ]
test "map-union-key" (Map.tryFind (Int 1) mapByUnion = Some "i")
test "map-union-key2" (Map.tryFind (Foo 2.0) mapByUnion = Some "f")

let mapByTuple = Map.ofList [ ((1, "a"), 10); ((2, "b"), 20) ]
test "map-tuple-key" (Map.tryFind (1, "a") mapByTuple = Some 10)

let setOfRecs = Set.ofList [ ra1; ra3 ]
test "set-record-contains" (Set.contains ra2 setOfRecs)
test "set-record-dedup" (Set.count (Set.ofList [ ra1; ra2; ra3 ]) = 2)
test "set-tree-contains" (Set.contains t2 (Set.ofList [ t1; t3 ]))

let d = Dictionary<RecA, int>()
d.[ra1] <- 1
test "dict-record-key" (d.ContainsKey ra2)
test "dict-record-get" (d.[ra2] = 1)
d.[ra2] <- 2
test "dict-record-overwrite" (d.Count = 1 && d.[ra1] = 2)

printfn "DONE tests=%d failures=%d" ntests failures

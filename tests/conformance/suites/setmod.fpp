// The Set module, including the deterministic `test_fold` block from the
// SetTests module of dotnet/fsharp tests/fsharp/core/libtest/test.fsx (its
// unionTest driver is Random- and Stopwatch-based, so only the fold checks
// port). Test NAMES are the originals where there are any.
//
// A Set is an ORDERED structure: `toList` is sorted, `fold` walks ascending
// and `foldBack` descending, and the set operations answer the same whatever
// order elements went in.
module Core_setmod

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let raises (f : unit -> 'a) : bool =
    try
        f () |> ignore
        false
    with _ -> true

// ---- the fold block (upstream) ------------------------------------------

let m = Set.ofList [ for i in 1..20 -> i ]

test "fold 1" (Set.fold (fun acc _ -> acc + 1) 0 m = 20)
test "fold 2" (Set.foldBack (fun _ acc -> acc + 1) m 0 = 20)
test "fold 3"
     (Set.fold (fun acc n -> acc + " " + string n) "0" m = String.concat " " [ for i in 0..20 -> string i ])
test "fold 4"
     (Set.foldBack (fun n acc -> acc + " " + string n) m "21" = String.concat " " (List.rev [ for i in 1..21 -> string i ]))
let mmax x y = if x > y then x else y
test "fold 5" (Set.foldBack mmax m 0 = 20)
test "fold 6" (m |> Set.fold mmax 0 = 20)

// ---- shape --------------------------------------------------------------

let empty : Set<int> = Set.empty

test "empty-count" (Set.count empty = 0)
test "empty-isEmpty" (Set.isEmpty empty)
test "singleton" (Set.toList (Set.singleton 3) = [3])
test "add" (Set.toList (Set.add 1 (Set.add 2 empty)) = [1;2])
test "add-dup" (Set.count (Set.add 1 (Set.add 1 empty)) = 1)
test "add-order-irrelevant" (Set.toList (Set.ofList [3;1;2]) = Set.toList (Set.ofList [2;3;1]))
test "sorted" (Set.toList (Set.ofList [5;3;9;1]) = [1;3;5;9])
test "contains" (Set.contains 3 (Set.ofList [1;3]))
test "contains-not" (not (Set.contains 9 (Set.ofList [1;3])))
test "remove" (Set.toList (Set.remove 3 (Set.ofList [1;3;5])) = [1;5])
test "remove-absent" (Set.toList (Set.remove 9 (Set.ofList [1;3])) = [1;3])
test "ofList-dups" (Set.count (Set.ofList [1;1;2;2;2]) = 2)

// ---- set algebra --------------------------------------------------------

let a = Set.ofList [1;2;3]
let b = Set.ofList [3;4;5]

test "union" (Set.toList (Set.union a b) = [1;2;3;4;5])
test "union-empty" (Set.toList (Set.union a empty) = [1;2;3])
test "intersect" (Set.toList (Set.intersect a b) = [3])
test "intersect-none" (Set.toList (Set.intersect a (Set.ofList [9])) = ([] : int list))
test "difference" (Set.toList (Set.difference a b) = [1;2])
test "difference-self" (Set.toList (Set.difference a a) = ([] : int list))
test "unionMany" (Set.toList (Set.unionMany [ a; b; Set.ofList [0] ]) = [0;1;2;3;4;5])
test "intersectMany" (Set.toList (Set.intersectMany [ a; b ]) = [3])

test "isSubset" (Set.isSubset (Set.ofList [1;2]) a)
test "isSubset-self" (Set.isSubset a a)
test "isSubset-not" (not (Set.isSubset b a))
test "isProperSubset" (Set.isProperSubset (Set.ofList [1;2]) a)
test "isProperSubset-self" (not (Set.isProperSubset a a))
test "isSuperset" (Set.isSuperset a (Set.ofList [1;2]))
test "isProperSuperset" (Set.isProperSuperset a (Set.ofList [1;2]))

// ---- traversal ----------------------------------------------------------

test "filter" (Set.toList (Set.filter (fun x -> x % 2 = 1) (Set.ofList [1;2;3;4])) = [1;3])
test "map" (Set.toList (Set.map (fun x -> x * 2) a) = [2;4;6])
test "map-collides" (Set.count (Set.map (fun x -> x % 2) a) = 2)
test "exists" (Set.exists (fun x -> x = 2) a)
test "exists-not" (not (Set.exists (fun x -> x = 9) a))
test "forall" (Set.forall (fun x -> x < 9) a)
let partYes, partNo = Set.partition (fun x -> x % 2 = 1) a
test "partition" ((Set.toList partYes, Set.toList partNo) = ([1;3], [2]))
test "minElement" (Set.minElement a = 1)
test "maxElement" (Set.maxElement a = 3)
test "minElement-raises" (raises (fun () -> Set.minElement empty))
test "maxElement-raises" (raises (fun () -> Set.maxElement empty))
test "toArray-len" (Array.length (Set.toArray a) = 3)
test "ofArray" (Set.toList (Set.ofArray [| 2; 1 |]) = [1;2])
test "ofSeq" (Set.toList (Set.ofSeq (Seq.init 3 (fun i -> 2 - i))) = [0;1;2])

// ---- sets of other things ----------------------------------------------

test "string-set" (Set.toList (Set.ofList [ "b"; "a"; "c" ]) = [ "a"; "b"; "c" ])
test "tuple-set" (Set.toList (Set.ofList [ (2, "b"); (1, "a") ]) = [ (1, "a"); (2, "b") ])
test "set-of-lists" (Set.toList (Set.ofList [ [2]; [1]; [1;2] ]) = [ [1]; [1;2]; [2] ])
test "big-set" (Set.count (Set.ofList [ for i in 1..500 -> i % 100 ]) = 100)
test "big-set-sorted" (Set.toList (Set.ofList [ for i in 1..200 -> 201 - i ]) = [ for i in 1..200 -> i ])

printfn "DONE tests=%d failures=%d" ntests failures

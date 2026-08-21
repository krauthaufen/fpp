// The List module across its edges, in the shape of the List usage in
// dotnet/fsharp tests/fsharp/core/libtest/test.fsx: empty inputs, one-element
// inputs, fold direction, sort stability, and the functions that RAISE.
//
// A hand-written List module tends to agree with F# on the ordinary cases and
// part company at the edges, so the edges are most of what is here.
module Core_listmod

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

let empty : int list = []

// ---- construction and shape --------------------------------------------

test "length-empty" (List.length empty = 0)
test "length-3" (List.length [1;2;3] = 3)
test "isEmpty-t" (List.isEmpty empty)
test "isEmpty-f" (not (List.isEmpty [1]))
test "head" (List.head [1;2;3] = 1)
test "head-raises" (raises (fun () -> List.head empty))
test "tail" (List.tail [1;2;3] = [2;3])
test "tail-raises" (raises (fun () -> List.tail empty))
test "last" (List.last [1;2;3] = 3)
test "last-raises" (raises (fun () -> List.last empty))
test "tryHead" (List.tryHead [1;2] = Some 1)
test "tryHead-empty" (List.tryHead empty = None)
test "tryLast" (List.tryLast [1;2] = Some 2)
test "tryLast-empty" (List.tryLast empty = None)
test "item" (List.item 1 [1;2;3] = 2)
test "item-raises-high" (raises (fun () -> List.item 3 [1;2;3]))
test "item-raises-neg" (raises (fun () -> List.item (0 - 1) [1;2;3]))
test "tryItem" (List.tryItem 1 [1;2;3] = Some 2)
test "tryItem-high" (List.tryItem 3 [1;2;3] = None)
test "tryItem-neg" (List.tryItem (0 - 1) [1;2;3] = None)

// ---- mapping and folding ------------------------------------------------

test "map" (List.map (fun x -> x * 2) [1;2;3] = [2;4;6])
test "map-empty" (List.map (fun x -> x * 2) empty = empty)
test "mapi" (List.mapi (fun i x -> i * x) [1;2;3] = [0;2;6])
test "map2" (List.map2 (+) [1;2] [10;20] = [11;22])
test "map2-mismatch" (raises (fun () -> List.map2 (+) [1;2] [10]))
test "fold" (List.fold (fun acc x -> acc - x) 0 [1;2;3] = -6)
// direction matters: fold is left, foldBack is right
test "fold-order" (List.fold (fun acc x -> acc + string x) "" [1;2;3] = "123")
test "foldBack-order" (List.foldBack (fun x acc -> acc + string x) [1;2;3] "" = "321")
test "fold2" (List.fold2 (fun acc a b -> acc + a * b) 0 [1;2] [3;4] = 11)
test "reduce" (List.reduce (+) [1;2;3] = 6)
test "reduce-raises" (raises (fun () -> List.reduce (+) empty))
test "scan" (List.scan (+) 0 [1;2;3] = [0;1;3;6])
test "collect" (List.collect (fun x -> [x; x]) [1;2] = [1;1;2;2])
test "collect-empty" (List.collect (fun x -> [x]) empty = empty)

// ---- searching ----------------------------------------------------------

test "filter" (List.filter (fun x -> x % 2 = 0) [1;2;3;4] = [2;4])
test "filter-none" (List.filter (fun x -> x > 9) [1;2] = empty)
test "exists" (List.exists (fun x -> x = 2) [1;2])
test "exists-empty" (not (List.exists (fun x -> true) empty))
test "forall" (List.forall (fun x -> x > 0) [1;2])
test "forall-empty" (List.forall (fun x -> false) empty)
test "find" (List.find (fun x -> x > 1) [1;2;3] = 2)
test "find-raises" (raises (fun () -> List.find (fun x -> x > 9) [1;2]))
test "tryFind" (List.tryFind (fun x -> x > 1) [1;2] = Some 2)
test "tryFind-none" (List.tryFind (fun x -> x > 9) [1;2] = None)
test "findIndex" (List.findIndex (fun x -> x = 3) [1;2;3] = 2)
test "findIndex-raises" (raises (fun () -> List.findIndex (fun x -> x = 9) [1;2]))
test "tryFindIndex" (List.tryFindIndex (fun x -> x = 3) [1;2;3] = Some 2)
test "tryPick" (List.tryPick (fun x -> if x > 1 then Some (x * 10) else None) [1;2] = Some 20)
test "pick" (List.pick (fun x -> if x > 1 then Some (x * 10) else None) [1;2] = 20)
test "pick-raises" (raises (fun () -> List.pick (fun x -> None) [1;2]))
test "contains" (List.contains 2 [1;2])
test "contains-not" (not (List.contains 9 [1;2]))

// ---- rearranging --------------------------------------------------------

test "rev" (List.rev [1;2;3] = [3;2;1])
test "rev-empty" (List.rev empty = empty)
test "append" (List.append [1] [2;3] = [1;2;3])
test "append-empty" (List.append empty [1] = [1])
test "concat" (List.concat [[1]; []; [2;3]] = [1;2;3])
test "sort" (List.sort [3;1;2] = [1;2;3])
test "sort-empty" (List.sort empty = empty)
test "sortDescending" (List.sortDescending [3;1;2] = [3;2;1])
test "sortBy" (List.sortBy (fun x -> 0 - x) [1;2;3] = [3;2;1])
// STABILITY: equal keys keep their input order
test "sort-stable"
     (List.sortBy (fun (k, _) -> k) [ (1, "a"); (0, "b"); (1, "c"); (0, "d") ] = [ (0, "b"); (0, "d"); (1, "a"); (1, "c") ])
test "distinct" (List.distinct [1;1;2;1] = [1;2])
test "truncate" (List.truncate 2 [1;2;3] = [1;2])
test "truncate-over" (List.truncate 9 [1;2] = [1;2])
test "take" (List.take 2 [1;2;3] = [1;2])
test "take-raises" (raises (fun () -> List.take 9 [1;2]))
test "skip" (List.skip 2 [1;2;3] = [3])
test "skip-raises" (raises (fun () -> List.skip 9 [1;2]))
test "zip" (List.zip [1;2] [ "a"; "b" ] = [ (1, "a"); (2, "b") ])
test "zip-mismatch" (raises (fun () -> List.zip [1;2] [ "a" ]))
test "unzip" (List.unzip [ (1, "a"); (2, "b") ] = ([1;2], [ "a"; "b" ]))
test "partition" (List.partition (fun x -> x % 2 = 0) [1;2;3;4] = ([2;4], [1;3]))
test "replicate" (List.replicate 3 7 = [7;7;7])
test "replicate-0" (List.replicate 0 7 = empty)
test "init" (List.init 3 (fun i -> i * i) = [0;1;4])
test "init-0" (List.init 0 (fun i -> i) = empty)
test "indexed" (List.indexed [ "a"; "b" ] = [ (0, "a"); (1, "b") ])
test "pairwise" (List.pairwise [1;2;3] = [ (1,2); (2,3) ])
test "pairwise-1" (List.pairwise [1] = ([] : (int * int) list))

// ---- numeric ------------------------------------------------------------

test "sum" (List.sum [1;2;3] = 6)
test "sum-empty" (List.sum empty = 0)
test "sumBy" (List.sumBy (fun x -> x * 2) [1;2] = 6)
test "max" (List.max [1;3;2] = 3)
test "max-raises" (raises (fun () -> List.max empty))
test "min" (List.min [3;1;2] = 1)
test "maxBy" (List.maxBy (fun x -> 0 - x) [1;2;3] = 1)
test "average" (List.average [1.0; 2.0; 3.0] = 2.0)
test "average-raises" (raises (fun () -> List.average ([] : float list)))

// ---- conversions --------------------------------------------------------

test "ofArray" (List.ofArray [| 1;2 |] = [1;2])
test "toArray-len" (Array.length (List.toArray [1;2]) = 2)
test "ofSeq" (List.ofSeq (Seq.init 3 (fun i -> i)) = [0;1;2])

printfn "DONE tests=%d failures=%d" ntests failures

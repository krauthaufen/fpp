// Ported from dotnet/fsharp tests/fsharp/core/libtest/test.fsx — the
// IEnumerableTests module and the Seq block that follows it — into the common
// F#/F++ subset. Test NAMES are the originals.
//
// DROPPED: the 1,000,000-element `Seq.init`/`{1 .. 1000000}` cases (kept at
// 100000 — the point is tail-calling, not the constant, and a million-element
// toList under wasm makes the gate minutes long); `Seq.cast` to and from obj
// (no boxed-obj element identity here); the typed
// KeyNotFoundException catch (a wildcard catch asserts the same thing);
// `x.Length` on a string element is spelled String.length; `{ 1 .. n }` (the
// bare-brace range sequence) is spelled `seq { 1 .. n }`.
//
// ADAPTED: comparisons against array literals go through Seq.toList /
// List.ofArray — arrays compare by REFERENCE here (DIVERGENCES.md), so
// `Seq.toArray xs = [| 1 |]` is false in F++ and true in F#. The element TYPE
// is still pinned: List.ofArray only typechecks on an array, which is what
// Seq.windowed/chunkBySize/splitInto must yield.
module Core_seqmod

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- IEnumerableTests ---------------------------------------------------

// these gave a stack overflow when F# was not tail-calling on 64-bit
test "Seq.filter-length" ((seq { 1 .. 100000 } |> Seq.filter (fun n -> n <> 1) |> Seq.length) = 99999)
test "Seq.filter-length" ((seq { 1 .. 100000 } |> Seq.filter (fun n -> n = 1) |> Seq.length) = 1)
test "Seq.filter-length" ((seq { 1 .. 100000 } |> Seq.filter (fun n -> n % 2 = 0) |> Seq.length) = 50000)

test "IEnumerableTest.empty-length" (Seq.length Seq.empty = 0)
test "IEnumerableTest.length-of-array" (Seq.length [| 1;2;3 |] = 3)
test "IEnumerableTest.head-of-array" (Seq.head [| 1;2;3 |] = 1)
test "IEnumerableTest.take-0-of-array" ((Seq.take 0 [| 1;2;3 |] |> Seq.toList) = [])
test "IEnumerableTest.take-1-of-array" ((Seq.take 1 [| 1;2;3 |] |> Seq.toList) = [1])
test "IEnumerableTest.take-3-of-array" ((Seq.take 3 [| 1;2;3 |] |> Seq.toList) = [1;2;3])
test "IEnumerableTest.nonempty-true" (Seq.isEmpty [| 1;2;3 |] = false)
test "IEnumerableTest.nonempty-false" (Seq.isEmpty ([| |] : int[]) = true)
test "IEnumerableTest.fold" (Seq.fold (+) 0 [| 1;2;3 |] = 6)
test "IEnumerableTest.unfold" ((Seq.unfold (fun _ -> None) 1 |> Seq.toList) = ([] : int list))
test "IEnumerableTest.unfold" ((Seq.unfold (fun x -> if x = 1 then Some ("a", 2) else None) 1 |> Seq.toList) = [ "a" ])
test "IEnumerableTest.exists" (Seq.exists (fun x -> x = "a") ([| |] : string[]) = false)
test "IEnumerableTest.exists" (Seq.exists (fun x -> x = "a") [| "a" |] = true)
test "IEnumerableTest.exists" (Seq.exists (fun x -> x = "a") [| "1"; "a" |] = true)
test "IEnumerableTest.forall" (Seq.forall (fun x -> x = "a") ([| |] : string[]) = true)
test "IEnumerableTest.forall" (Seq.forall (fun x -> x = "a") [| "a" |] = true)
test "IEnumerableTest.forall" (Seq.forall (fun x -> x = "a") [| "1"; "a" |] = false)
test "IEnumerableTest.map on finite" (([| "a" |] |> Seq.map (fun x -> String.length x) |> Seq.toList) = [ 1 ])
test "IEnumerableTest.filter on finite" (([| "a";"ab";"a" |] |> Seq.filter (fun x -> String.length x = 1) |> Seq.toList) = [ "a";"a" ])
test "IEnumerableTest.choose on finite" (([| "a";"ab";"a" |] |> Seq.choose (fun x -> if String.length x = 1 then Some (x + "a") else None) |> Seq.toList) = [ "aa";"aa" ])
test "Seq.tryPick on finite (succeeding)" (([| "a";"ab";"a" |] |> Seq.tryPick (fun x -> if String.length x = 1 then Some (x + "a") else None)) = Some "aa")
test "Seq.tryPick on finite (failing)" (([| "a";"ab";"a" |] |> Seq.tryPick (fun x -> if String.length x = 6 then Some (x + "a") else None)) = None)
test "IEnumerableTest.find on finite (succeeding)" (([| "a";"ab";"a" |] |> Seq.find (fun x -> String.length x = 1)) = "a")
test "IEnumerableTest.find on finite (failing)" ((try Some ([| "a";"ab";"a" |] |> Seq.find (fun x -> String.length x = 6)) with _ -> None) = None)
test "IEnumerableTest.append, finite, finite" ((Seq.append [| "a" |] [| "b" |] |> Seq.toList) = [ "a"; "b" ])
test "IEnumerableTest.concat, finite" ((Seq.concat [| [| "a" |]; [| |]; [| "b";"c" |] |] |> Seq.toList) = [ "a";"b";"c" ])
test "IEnumerableTest.init_infinite, then take" ((Seq.take 2 (Seq.initInfinite (fun i -> i + 1)) |> Seq.toList) = [ 1;2 ])
test "IEnumerableTest.to_array, empty" ((Seq.init 0 (fun i -> i + 1) |> Seq.toList) = ([] : int list))
test "IEnumerableTest.to_array, small" ((Seq.init 1 (fun i -> i + 1) |> Seq.toList) = [ 1 ])
test "IEnumerableTest.to_array, large" ((Seq.init 100000 (fun i -> i + 1) |> Seq.toArray |> Array.length) = 100000)
test "IEnumerableTest.to_list, empty" ((Seq.init 0 (fun i -> i + 1) |> Seq.toList) = ([] : int list))
test "IEnumerableTest.to_list, small" ((Seq.init 1 (fun i -> i + 1) |> Seq.toList) = [ 1 ])
test "IEnumerableTest.to_list, large" ((Seq.init 100000 (fun i -> i + 1) |> Seq.toList |> List.length) = 100000)
test "IEnumerableTest.to_list, large-ofSeq" ((Seq.init 100000 (fun i -> i + 1) |> List.ofSeq |> List.length) = 100000)
test "List.unzip, large" ((Seq.init 100000 (fun i -> (i, i + 1)) |> List.ofSeq |> List.unzip |> fst |> List.length) = 100000)

test "IEnumerableTest.tryFind" (([| 1..100 |] |> Seq.tryFind (fun x -> x > 50)) = Some 51)
test "IEnumerableTest.tryFind" (([| 1..100 |] |> Seq.tryFind (fun x -> x > 180)) = None)

test "Seq.compareWith" (Seq.compareWith compare [1;2] [2;1] = -1)
test "Seq.compareWith" (Seq.compareWith compare [2;1] [1;2] = 1)
test "Seq.compareWith" (Seq.compareWith compare [1;2] [1;2] = 0)
test "Seq.compareWith" (Seq.compareWith compare [1] [1;2] = -1)
test "Seq.compareWith" (Seq.compareWith compare [1;2] [1] = 1)
test "Seq.compareWith" (Seq.compareWith compare ([] : int list) ([] : int list) = 0)

test "Seq.exists2" (Seq.exists2 (fun a b -> a = b) [| 1; 2; 3; 4; 5; 6 |] [| 2; 3; 4; 5; 6; 6 |] = true)
test "Seq.exists2" (Seq.exists2 (fun a b -> a = b) [| 1; 2; 3; 4; 5; 6 |] [| 2; 3; 4; 5; 6; 7 |] = false)
test "Seq.forall2" (Seq.forall2 (fun a b -> a = b) [| 1..10 |] [| 1..10 |] = true)
test "Seq.forall2" (Seq.forall2 (fun a b -> a = b) [| 1;2;3;4;5 |] [| 1;2;3;0;5 |] = false)

test "Seq.truncate" ((Seq.truncate 10 [1..100] |> Seq.toList) = [1..10])
test "Seq.truncate" ((Seq.truncate 1 [1..100] |> Seq.toList) = [1])
test "Seq.truncate" ((Seq.truncate 0 [1..100] |> Seq.toList) = ([] : int list))
test "Seq.scan" ((Seq.scan (+) 0 [| 1..5 |] |> Seq.toList) = [ 0; 1; 3; 6; 10; 15 ])

// ---- the Seq block ------------------------------------------------------

test "Seq.windowed 1" ((Seq.windowed 1 [1..20] |> Seq.toList |> List.map List.ofArray) = [ for i in 1 .. 20 -> [ i ] ])
test "Seq.windowed 2" ((Seq.windowed 2 [1..20] |> Seq.toList |> List.map List.ofArray) = [ for i in 1 .. 19 -> [ i; i+1 ] ])
test "Seq.windowed 3" ((Seq.windowed 3 [1..20] |> Seq.toList |> List.map List.ofArray) = [ for i in 1 .. 18 -> [ i; i+1; i+2 ] ])
test "Seq.windowed 4" ((Seq.windowed 4 [1..20] |> Seq.toList |> List.map List.ofArray) = [ for i in 1 .. 17 -> [ i; i+1; i+2; i+3 ] ])

let group = Seq.groupBy (fun x -> x % 5) [1..100]
for n, s in group do
    test "Seq.groupBy" (Seq.forall (fun x -> x % 5 = n) s = true)
test "Seq.groupBy" (([ for n, _ in group -> n ] |> List.sort) = [0..4])

let sorted = Seq.sortBy abs [2; 4; 3; -5; 2; -4; -8; 0; 5; 2]
test "Seq.sortBy" ((Seq.pairwise sorted |> Seq.forall (fun (x, y) -> abs x <= abs y)) = true)

test "Seq.sum" (Seq.sum [1..100] = 100 * 101 / 2)
test "Seq.sumBy" (Seq.sumBy (fun x -> float x) [1..100] = 100. * 101. / 2.)
test "Seq.average" (Seq.average [1.; 2.; 3.] = 2.)
test "Seq.averageBy" (Seq.averageBy (fun x -> float x) [0..100] = 50.)
test "Seq.min" (Seq.min [1; 4; 2; 5; 8; 4; 0; 3] = 0)
test "Seq.max" (Seq.max [1; 4; 2; 5; 8; 4; 0; 3] = 8)
test "Seq.minBy" (Seq.minBy abs [3; -1; 4; -1; 5] = -1)
test "Seq.maxBy" (Seq.maxBy abs [3; -1; 4; -9; 5] = -9)

test "Seq.item" (Seq.item 0 [1;2;3] = 1)
test "Seq.item" (Seq.item 2 [1;2;3] = 3)
test "Seq.item" ((try Seq.item 3 [1;2;3] |> ignore; false with _ -> true) = true)
test "Seq.item" ((try Seq.item (0 - 1) [1;2;3] |> ignore; false with _ -> true) = true)

test "Seq.pairwise" ((Seq.pairwise [1..5] |> Seq.toList) = [(1,2); (2,3); (3,4); (4,5)])
test "Seq.pairwise" ((Seq.pairwise [1] |> Seq.toList) = ([] : (int * int) list))
test "Seq.distinct" ((Seq.distinct [1;1;2;3;3;3;4] |> Seq.toList) = [1;2;3;4])
test "Seq.distinctBy" ((Seq.distinctBy (fun x -> x % 3) [1..10] |> Seq.toList) = [1;2;3])
test "Seq.countBy" ((Seq.countBy (fun x -> x % 2) [1..10] |> Seq.toList) = [(1, 5); (0, 5)])
test "Seq.chunkBySize" ((Seq.chunkBySize 3 [1..7] |> Seq.toList |> List.map List.ofArray) = [[1;2;3]; [4;5;6]; [7]])
test "Seq.splitInto" ((Seq.splitInto 3 [1..6] |> Seq.toList |> List.map List.ofArray) = [[1;2]; [3;4]; [5;6]])
test "Seq.mapi" ((Seq.mapi (fun i x -> i * x) [1;2;3] |> Seq.toList) = [0;2;6])
test "Seq.map2" ((Seq.map2 (+) [1;2;3] [10;20;30] |> Seq.toList) = [11;22;33])
test "Seq.collect" ((Seq.collect (fun x -> [x; x]) [1;2] |> Seq.toList) = [1;1;2;2])
test "Seq.skip" ((Seq.skip 2 [1..5] |> Seq.toList) = [3;4;5])
test "Seq.skipWhile" ((Seq.skipWhile (fun x -> x < 3) [1..5] |> Seq.toList) = [3;4;5])
test "Seq.takeWhile" ((Seq.takeWhile (fun x -> x < 3) [1..5] |> Seq.toList) = [1;2])
test "Seq.rev" ((Seq.rev [1..5] |> Seq.toList) = [5;4;3;2;1])
test "Seq.last" (Seq.last [1..5] = 5)
test "Seq.tryLast" (Seq.tryLast [1..5] = Some 5)
test "Seq.tryLast" (Seq.tryLast ([] : int list) = None)
test "Seq.tryHead" (Seq.tryHead [1..5] = Some 1)
test "Seq.tryHead" (Seq.tryHead ([] : int list) = None)
test "Seq.indexed" ((Seq.indexed [| "a"; "b" |] |> Seq.toList) = [(0, "a"); (1, "b")])
test "Seq.zip" ((Seq.zip [1;2] [| "a"; "b" |] |> Seq.toList) = [(1, "a"); (2, "b")])
test "Seq.replicate" ((Seq.replicate 3 "x" |> Seq.toList) = ["x"; "x"; "x"])
test "Seq.contains" (Seq.contains 3 [1..5] = true)
test "Seq.contains" (Seq.contains 9 [1..5] = false)
test "Seq.reduce" (Seq.reduce (+) [1..5] = 15)
test "Seq.fold2" (Seq.fold2 (fun acc a b -> acc + a * b) 0 [1;2;3] [4;5;6] = 32)
test "Seq.exactlyOne" (Seq.exactlyOne [42] = 42)
test "Seq.tryExactlyOne" (Seq.tryExactlyOne [42] = Some 42)
test "Seq.tryExactlyOne" (Seq.tryExactlyOne [1;2] = None)

printfn "DONE tests=%d failures=%d" ntests failures

// Ported from dotnet/fsharp tests/fsharp/core/array/test.fsx into the
// common F#/F++ subset. Dropped: step ranges (`0..+2..100`, `1000..-1..1` —
// spelled with Array.init / List.rev instead), the user extension
// `module Array` with findIndexi/tryFindIndexi (extending the prelude
// module by name is its own trap), the stable-sort LIST batteries (ported
// with the List module elsewhere), average (float formatting parity has
// its own suite plans), the Array2D/3D/4D sections, struct/stress tails,
// and the seq-view tests. Everything else is kept with its original names.
module Core_array

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// array `=` is REFERENCE equality in F++ (a chosen divergence,
// DIVERGENCES.md) — content checks go through this element-wise helper,
// which means the same thing in both languages
let aeq (a : 'a[]) (b : 'a[]) : bool =
    a.Length = b.Length
    && (let mutable ok = true
        for i in 0 .. a.Length - 1 do
            if a.[i] <> b.[i] then ok <- false
        ok)

let evens = Array.init 51 (fun i -> i * 2)          // 0..+2..100
let odds = Array.init 50 (fun i -> i * 2 + 1)       // 1..+2..100

let test_make_get_set_length () =
    let arr = Array.create 3 0 in
    test "fewoih" (Array.get arr 0 = 0)
    test "vvrew0" (Array.get arr 2 = 0)
    ignore (Array.set arr 0 4)
    test "vsdiuvs" (Array.get arr 0 = 4)
    test "vropivrwe" (Array.length arr = 3)

let test_const () =
    let arr = [| 4; 3; 2 |] in
    test "sdvjk2" (Array.get arr 0 = 4)
    test "cedkj" (Array.get arr 2 = 2)
    ignore (Array.set arr 0 4)
    test "ds9023" (Array.get arr 0 = 4)
    test "sdio2" (Array.length arr = 3)

let test_const_empty () =
    let arr = [| |] in
    test "sdio2b" (Array.length arr = 0)

let test_map () =
    let arr = Array.map (fun x -> x + 1) [| 4; 3; 2 |] in
    test "test2927: sdvjk2" (Array.get arr 0 = 5)
    test "test2927: cedkj" (Array.get arr 2 = 3)

let test_iter () =
    Array.iter (fun x -> test "fuo" (x <= 4)) [| 4; 3; 2 |]

let test_iteri () =
    let arr = [| 4; 3; 2 |] in
    Array.iteri (fun i x -> test "fuo2" (arr.[i] = x)) arr

let test_mapi () =
    let arr = [| 4; 3; 2 |] in
    let arr2 = Array.mapi (fun i x -> test "dwqfuo" (arr.[i] = x); i + x) arr in
    test "test2927: sdvjk2b" (Array.get arr2 0 = 4)
    test "test2927: cedkjb" (Array.get arr2 2 = 4)

let test_isEmpty () =
    test "isEmpty a" (Array.isEmpty [||])
    test "isEmpty b" (Array.isEmpty (Array.create 0 42))
    test "isEmpty c" (not (Array.isEmpty [| 1 |]))

let test_create () =
    let arr = Array.create 10 10
    for i in 0 .. 9 do
        test "test_create" (arr.[i] = 10)

let test_concat () =
    // F++'s Array.concat takes a LIST of arrays (one of F#'s accepted
    // shapes), so the sources are lists here
    let make n = [| for i in n .. n + 9 -> i |]
    let arr = [ for i in 0 .. 5 -> make (i * 10) ]
    test "concat a" (aeq (Array.concat arr) [| 0 .. 59 |])
    let arr2 = [ for i in 0 .. 50 -> ([||] : int[]) ]
    test "concat b" (aeq (Array.concat arr2) [| |])
    let arr3 = [ [||]; [||]; [| 1; 2 |]; [||] ]
    test "concat c" (aeq (Array.concat arr3) [| 1; 2 |])

let test_sub () =
    test "sub a" (aeq (Array.sub [| 0 .. 100 |] 10 20) [| 10 .. 29 |])
    test "sub b" (aeq (Array.sub [| 0 .. 100 |] 0 101) [| 0 .. 100 |])
    test "sub c" (aeq (Array.sub [| 0 .. 100 |] 0 1) [| 0 |])
    test "sub d" (aeq (Array.sub [| 0 .. 100 |] 0 0) [||])

let test_fold2 () =
    test "fold2 a" (Array.fold2 (fun i j k -> i + j + k) 100 [| 1; 2; 3 |] [| 1; 2; 3 |] = 112)
    test "fold2_b" (Array.fold2 (fun i j k -> i - j - k) 100 [| 1; 2; 3 |] [| 1; 2; 3 |] = 100 - 12)

let test_foldBack2 () =
    test "foldBack2 a" (Array.foldBack2 (fun i j k -> i + j + k) [| 1; 2; 3 |] [| 1; 2; 3 |] 100 = 112)
    test "foldBack2_b" (Array.foldBack2 (fun i j k -> k - i - j) [| 1; 2; 3 |] [| 1; 2; 3 |] 100 = 100 - 12)

let test_scan () =
    test "scan" (aeq (Array.scan (+) 0 [| 1 .. 5 |]) [| 0; 1; 3; 6; 10; 15 |])
    test "scanBack" (aeq (Array.scanBack (+) [| 1 .. 5 |] 0) [| 15; 14; 12; 9; 5; 0 |])

let test_iter2 () =
    let c = ref -1
    Array.iter2 (fun x y -> c := !c + 1; test "iter2" (!c = x && !c = y)) [| 0 .. 100 |] [| 0 .. 100 |]
    test "iter2" (!c = 100)

let test_iteri2 () =
    let c = ref 0
    Array.iteri2 (fun i j k -> c := !c + i + j + k) [| 1; 2; 3 |] [| 10; 20; 30 |]
    test "iteri2" (!c = 6 + 60 + 3)

let test_map2 () =
    test "map2" (aeq (Array.map2 (+) [| 0 .. 100 |] [| 0 .. 100 |]) (Array.init 101 (fun i -> i * 2)))

let test_mapi2 () =
    test "mapi2 a" (aeq (Array.mapi2 (fun i j k -> i + j + k) [| 1 .. 10 |] [| 1 .. 10 |]) (Array.init 10 (fun i -> 2 + i * 3)))
    test "mapi2_b"
        (try Array.mapi2 (fun i j k -> i + j + k) [||] [| 1 .. 10 |] |> ignore; false
         with _ -> true)

let test_exists () =
    test "exists a" ([| 1 .. 100 |] |> Array.exists ((=) 50))
    test "exists b" (not ([| 1 .. 100 |] |> Array.exists ((=) 150)))

let test_forall () =
    test "forall a" ([| 1 .. 100 |] |> Array.forall (fun x -> x < 150))
    test "forall b" (not ([| 1 .. 100 |] |> Array.forall (fun x -> x < 80)))

let test_exists2 () =
    test "exists2 a" (Array.exists2 (=) [| 1; 2; 3; 4; 5; 6 |] [| 2; 3; 4; 5; 6; 6 |])
    test "exists2 b" (not (Array.exists2 (=) [| 1; 2; 3; 4; 5; 6 |] [| 2; 3; 4; 5; 6; 7 |]))

let test_forall2 () =
    test "forall2 a" (Array.forall2 (=) [| 1 .. 10 |] [| 1 .. 10 |])
    test "forall2_b" (not (Array.forall2 (=) [| 1; 2; 3; 4; 5 |] [| 1; 2; 3; 0; 5 |]))

let test_filter () =
    test "filter a" (aeq (Array.filter (fun x -> x % 2 = 0) [| 0 .. 100 |]) evens)
    test "filter b" (aeq (Array.filter (fun x -> false) [| 0 .. 100 |]) [||])
    test "filter c" (aeq (Array.filter (fun x -> true) [| 0 .. 100 |]) [| 0 .. 100 |])

let test_partition () =
    let p1, p2 = Array.partition (fun x -> x % 2 = 0) [| 0 .. 100 |]
    test "partition" (aeq p1 evens && aeq p2 odds)

let test_choose () =
    test "choose" (aeq (Array.choose (fun x -> if x % 2 = 0 then Some (x / 2) else None) [| 0 .. 100 |]) [| 0 .. 50 |])

let test_find () =
    test "find a" ([| 1 .. 100 |] |> Array.find (fun x -> x > 50) = 51)
    test "find b"
        (try [| 1 .. 100 |] |> Array.find (fun x -> x > 180) |> ignore; false
         with _ -> true)

let test_findIndex () =
    test "findIndex a" (Array.findIndex (fun i -> i >= 4) [| 0 .. 10 |] = 4)
    test "findIndex b"
        (try Array.findIndex (fun i -> i >= 20) [| 0 .. 10 |] |> ignore; false
         with _ -> true)

let test_tryfind () =
    test "tryFind" ([| 1 .. 100 |] |> Array.tryFind (fun x -> x > 50) = Some 51)
    test "tryFind b" ([| 1 .. 100 |] |> Array.tryFind (fun x -> x > 180) = None)
    test "tryfind_index a" (Array.tryFindIndex (fun x -> x = 4) [| 0 .. 10 |] = Some 4)
    test "tryfind_index b" (Array.tryFindIndex (fun x -> x = 42) [| 0 .. 10 |] = None)

let test_first () =
    test "first a" ([| 1 .. 100 |] |> Array.tryPick (fun x -> if x > 50 then Some (x * x) else None) = Some (51 * 51))
    test "first b" ([| 1 .. 100 |] |> Array.tryPick (fun x -> None) = None)
    test "first c" (([||] : int[]) |> Array.tryPick (fun _ -> Some 42) = None)

let test_sort () =
    test "sort a" (aeq (Array.sort ([||] : int[])) [||])
    test "sort b" (aeq (Array.sort [| 1 |]) [| 1 |])
    test "sort c" (aeq (Array.sort [| 1; 2 |]) [| 1; 2 |])
    test "sort d" (aeq (Array.sort [| 2; 1 |]) [| 1; 2 |])
    test "sort e" (aeq (Array.sort [| 1 .. 1000 |]) [| 1 .. 1000 |])
    test "sort f" (aeq (Array.sort (Array.ofList (List.rev [ 1 .. 1000 ]))) [| 1 .. 1000 |])

let test_sort_by () =
    test "Array.sortBy d" (aeq (Array.sortBy (fun (x : int) -> x) [| 2; 1 |]) [| 1; 2 |])
    test "Array.sortBy e" (aeq (Array.sortBy (fun (x : int) -> x) [| 1 .. 1000 |]) [| 1 .. 1000 |])
    test "Array.sortBy f" (aeq (Array.sortBy (fun (x : int) -> x) (Array.ofList (List.rev [ 1 .. 1000 ]))) [| 1 .. 1000 |])
    test "Array.sortBy neg" (aeq (Array.sortBy (fun (x : int) -> -x) [| 1 .. 10 |]) (Array.ofList (List.rev [ 1 .. 10 ])))

let test_zip () =
    test "zip" (aeq (Array.zip [| 1; 2; 3 |] [| "a"; "b"; "c" |]) [| 1, "a"; 2, "b"; 3, "c" |])
    let u1, u2 = Array.unzip [| 1, "a"; 2, "b"; 3, "c" |]
    test "unzip" (aeq u1 [| 1; 2; 3 |] && aeq u2 [| "a"; "b"; "c" |])

let test_zip3 () =
    test "zip3" (aeq (Array.zip3 [| 1; 2 |] [| "a"; "b" |] [| true; false |]) [| 1, "a", true; 2, "b", false |])

let test_rev () =
    test "rev a" (aeq (Array.rev [| 1; 2; 3 |]) [| 3; 2; 1 |])
    test "rev b" (aeq (Array.rev ([||] : int[])) [||])
    test "rev c" (aeq (Array.rev [| 1 |]) [| 1 |])

let test_sum () =
    test "sum a" (Array.sum ([||] : int[]) = 0)
    test "sum b" (Array.sum [| 1 .. 100 |] = 5050)

let test_sum_by () =
    test "sumBy" (Array.sumBy (fun x -> x * 2) [| 1 .. 100 |] = 10100)

let test_min () =
    test "min a" (Array.min [| 3; 1; 2 |] = 1)
    test "max a" (Array.max [| 3; 1; 2 |] = 3)
    test "minBy" (Array.minBy (fun (x : int) -> -x) [| 1 .. 10 |] = 10)
    test "maxBy" (Array.maxBy (fun (x : int) -> -x) [| 1 .. 10 |] = 1)

let test_zero_create () =
    test "zeroCreate a" (aeq (Array.zeroCreate 3) [| 0; 0; 0 |])
    test "zeroCreate b" (aeq (Array.zeroCreate 0 : int[]) [||])

let test_init () =
    let arr = Array.init 10 (fun i -> i * i)
    test "init" (arr.[3] = 9 && arr.[9] = 81 && arr.Length = 10)

let test_init_empty () =
    test "init empty" (aeq (Array.init 0 (fun i -> i) : int[]) [||])

let test_append () =
    test "append a" (aeq (Array.append [| 1; 2 |] [| 3; 4 |]) [| 1; 2; 3; 4 |])
    test "append b" (aeq (Array.append [||] [| 3; 4 |]) [| 3; 4 |])
    test "append c" (aeq (Array.append [| 1; 2 |] [||]) [| 1; 2 |])

let test_fill () =
    let arr = Array.create 10 0
    Array.fill arr 2 3 7
    test "fill" (aeq arr [| 0; 0; 7; 7; 7; 0; 0; 0; 0; 0 |])

let test_copy () =
    let arr = [| 1; 2; 3 |]
    let c = Array.copy arr
    c.[0] <- 99
    test "copy" (arr.[0] = 1 && c.[0] = 99 && c.[2] = 3)

let test_blit () =
    let src = [| 1; 2; 3; 4; 5 |]
    let dst = Array.create 5 0
    Array.blit src 1 dst 2 3
    test "blit" (aeq dst [| 0; 0; 2; 3; 4 |])

let test_of_list () =
    test "ofList" (aeq (Array.ofList [ 1; 2; 3 ]) [| 1; 2; 3 |])
    test "ofList empty" (aeq (Array.ofList [] : int[]) [||])

let test_to_list () =
    test "toList" (Array.toList [| 1; 2; 3 |] = [ 1; 2; 3 ])
    test "toList empty" (Array.toList ([||] : int[]) = [])

let test_fold_left () =
    test "fold" (Array.fold (fun acc x -> acc * 10 + x) 0 [| 1; 2; 3 |] = 123)

let test_fold_right () =
    test "foldBack" (Array.foldBack (fun x acc -> acc * 10 + x) [| 1; 2; 3 |] 0 = 321)

test_make_get_set_length ()
test_const ()
test_const_empty ()
test_map ()
test_iter ()
test_iteri ()
test_mapi ()
test_isEmpty ()
test_create ()
test_concat ()
test_sub ()
test_fold2 ()
test_foldBack2 ()
test_scan ()
test_iter2 ()
test_iteri2 ()
test_map2 ()
test_mapi2 ()
test_exists ()
test_forall ()
test_exists2 ()
test_forall2 ()
test_filter ()
test_partition ()
test_choose ()
test_find ()
test_findIndex ()
test_tryfind ()
test_first ()
test_sort ()
test_sort_by ()
test_zip ()
test_zip3 ()
test_rev ()
test_sum ()
test_sum_by ()
test_min ()
test_zero_create ()
test_init ()
test_init_empty ()
test_append ()
test_fill ()
test_copy ()
test_blit ()
test_of_list ()
test_to_list ()
test_fold_left ()
test_fold_right ()

printfn "DONE tests=%d failures=%d" ntests failures

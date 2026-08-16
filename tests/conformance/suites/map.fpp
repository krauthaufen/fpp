// Ported from dotnet/fsharp tests/fsharp/core/map/test.fsx into the common
// F#/F++ subset. Dropped: the .NET member surface on Map (`x.TryGetValue`,
// byref overloads), the typed KeyNotFoundException catch (a wildcard catch
// asserts the same behaviour), testEqNoComparison (`obj()` sentinel values),
// Bug6307 (`global.System.Int32`, typeof), and the Set.GetHashCode probe
// (kept as a Set smoke instead). `21..-1..1` step ranges are spelled with
// List.rev — F++ has no step-range syntax.
module Core_map

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let test_eq_range (n : int) (m : int) (x : Map<int, int>) =
    for i = n to m do
        test "ew9wef-find" (Map.find i x = i * 100)
    for i = n to m do
        test "ew9wef-try" (Map.tryFind i x = Some (i * 100))
    for i = m + 1 to m + 100 do
        test "ew9wef-none" (Map.tryFind i x = None)
    for i = m + 1 to m + 5 do
        test "ew9cwef" ((try Some (Map.find i x) with _ -> None) = None)

let test39342 () =
    let x = Map.empty in
    let x = Map.add 1 100 x in
    let x = Map.add 2 200 x in
    let x = Map.add 3 300 x in
    let x = Map.add 4 400 x in
    let x = Map.add 5 500 x in
    let x = Map.add 6 600 x in
    let x = Map.add 7 700 x in
    let x = Map.add 8 800 x in
    let x = Map.add 9 900 x in
    let x = Map.add 10 1000 x in
    let x = Map.add 11 1100 x in
    let x = Map.add 12 1200 x in
    let x = Map.add 13 1300 x in
    let x = Map.add 14 1400 x in
    let x = Map.add 15 1500 x in
    test_eq_range 1 15 x

test39342 ()

let test39343 () =
    let x = Map.empty in
    let x = Map.add 15 1500 x in
    let x = Map.add 14 1400 x in
    let x = Map.add 13 1300 x in
    let x = Map.add 12 1200 x in
    let x = Map.add 11 1100 x in
    let x = Map.add 10 1000 x in
    let x = Map.add 9 900 x in
    let x = Map.add 8 800 x in
    let x = Map.add 7 700 x in
    let x = Map.add 6 600 x in
    let x = Map.add 5 500 x in
    let x = Map.add 4 400 x in
    let x = Map.add 3 300 x in
    let x = Map.add 2 200 x in
    let x = Map.add 1 100 x in
    test_eq_range 1 15 x

test39343 ()

let test39344 () =
    let x = Map.empty in
    let x = Map.add 4 400 x in
    test_eq_range 4 4 x

test39344 ()

let test39345 () =
    let x = Map.empty in
    let x = Map.add 4 400 x in
    let x = Map.add 4 400 x in
    test_eq_range 4 4 x

test39345 ()

let test39346 () =
    let x = Map.empty in
    let x = Map.add 4 400 x in
    let x = Map.remove 4 x in
    test_eq_range 4 3 x

test39346 ()

let test39347 () =
    let x = Map.empty in
    let x = Map.add 1 100 x in
    let x = Map.add 2 200 x in
    let x = Map.add 3 300 x in
    let x = Map.add 4 400 x in
    let x = Map.add 5 500 x in
    let x = Map.add 6 600 x in
    let x = Map.add 7 700 x in
    let x = Map.add 8 800 x in
    let x = Map.add 9 900 x in
    let x = Map.add 10 1000 x in
    let x = Map.add 11 1100 x in
    let x = Map.add 12 1200 x in
    let x = Map.add 13 1300 x in
    let x = Map.add 14 1400 x in
    let x = Map.add 15 1500 x in
    let x = Map.remove 3 x in
    let x = Map.remove 2 x in
    let x = Map.remove 1 x in
    let x = Map.remove 15 x in
    test_eq_range 4 14 x

test39347 ()

let test_fold () =
    let m = Map.ofList [ for i in 1 .. 20 -> i, i ] in
    test "fold 1" (Map.fold (fun acc _ _ -> acc + 1) 0 m = 20)
    test "fold 2" (Map.foldBack (fun _ _ acc -> acc + 1) m 0 = 20)
    let fold3 = Map.fold (fun acc n _ -> acc + " " + string n) "0" m
    test "fold 3" (fold3 = String.concat " " [ for i in 0 .. 20 -> string i ])
    let fold4 = Map.foldBack (fun n _ acc -> acc + " " + string n) m "21"
    test "fold 4" (fold4 = String.concat " " (List.rev [ for i in 1 .. 21 -> string i ]))
    test "fold 5" (Map.foldBack (fun _ -> max) m 0 = 20)
    test "fold 6" (Map.fold (fun acc n _ -> max acc n) 0 m = 20)

test_fold ()

// Set smoke, in place of the GetHashCode regression probe
let setSmoke () =
    let s = Set.singleton 2147483017
    test "set-count" (Set.count s = 1)
    test "set-mem" (Set.contains 2147483017 s)
    let s2 = Set.add 5 (Set.add 3 s)
    test "set-add" (Set.count s2 = 3 && Set.contains 3 s2 && Set.contains 5 s2)
    test "set-rm" (Set.count (Set.remove 3 s2) = 2)

setSmoke ()

printfn "DONE tests=%d failures=%d" ntests failures

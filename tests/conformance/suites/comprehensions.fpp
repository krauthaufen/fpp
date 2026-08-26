// The portable core of fsc's comprehensions test: list and array
// comprehension BODIES — nested for, if filters, if/else with a yield in
// both arms, match-with-yield, tuple binders, the while form, and stepped
// ranges. The `seq { }` forms, IEnumerator plumbing and Regex parts are
// dropped (no seq builder in the subset).
module Core_comprehensions

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// stepped and reversed ranges as list comprehension sources
test "colc-r1" ([ 1 .. 0 ] = [])
test "colc-r2" ([ 3 .. -1 .. -3 ] = [ 3; 2; 1; 0; -1; -2; -3 ])
test "colc-r3" ([ 3 .. -2 .. -3 ] = [ 3; 1; -1; -3 ])
test "colc-r4" ([ 1.0 .. 1.0 .. 3.0 ] = [ 1.0; 2.0; 3.0 ])
test "colc-r5" ([ 1.0 .. 1.0 .. 2.01 ] = [ 1.0; 2.0 ])
test "colc-r6" ([ 3.0 .. -1.0 .. 0.0 ] = [ 3.0; 2.0; 1.0; 0.0 ])
test "colc-r7" ([ 4.0 .. -2.0 .. 0.0 ] = [ 4.0; 2.0; 0.0 ])

let ie1 = [ 1 .. 1 .. 3 ]

// arrow form with a tuple element
test "colc1" ([ for i in ie1 -> i, i * i ] = [ (1, 1); (2, 4); (3, 9) ])

// if filter
test "colc2" ([ for i in [ 1 .. 5 ] do
                  if i % 2 = 0 then yield i + 100 ] = [ 102; 104 ])

// nested for, yield a tuple
let colc3 = [ for i in ie1 do
                for j in [ 1 .. 4 ] do yield i, j ]
test "colc3" (colc3 = [ (1, 1); (1, 2); (1, 3); (1, 4)
                        (2, 1); (2, 2); (2, 3); (2, 4)
                        (3, 1); (3, 2); (3, 3); (3, 4) ])

// filter above a nested for
let colc4 = [ for i in ie1 do
                if i % 2 = 1 then
                    for j in [ 1 .. 4 ] do yield i, j ]
test "colc4" (colc4 = [ (1, 1); (1, 2); (1, 3); (1, 4)
                        (3, 1); (3, 2); (3, 3); (3, 4) ])

// inner range depends on the outer binder
let colc5 = [ for i in ie1 do
                for j in [ i .. 3 ] do yield i, j ]
test "colc5" (colc5 = [ (1, 1); (1, 2); (1, 3); (2, 2); (2, 3); (3, 3) ])

// if/else with a yield in BOTH arms
let colc6 = [ for i in ie1 do
                for j in [ i .. 3 ] do
                    if i = j then yield i + i, j + j
                    else yield i, j ]
test "colc6" (colc6 = [ (2, 2); (1, 2); (1, 3); (4, 4); (2, 3); (6, 6) ])

// tuple binder over a list of pairs
test "colc7" ([ for (i, j) in [ (1, 2); (3, 4) ] -> i + j ] = [ 3; 7 ])
test "colc8" ([ for (i, j) in [ (1, 2); (3, 4) ] do
                  if i % 3 = 0 then yield i + j ] = [ 7 ])

// match with a yield in one arm and unit in the other
test "colc9" ([ for opt in [ Some "a"; None; Some "b" ] do
                  match opt with
                  | Some r -> yield r
                  | None -> () ] = [ "a"; "b" ])

// while form that never runs
test "colc10" ([ while false do yield 1 ] = [])

// while form driven by a mutable counter
let whileUp () =
    let mutable i = 0
    [ while i < 3 do
        i <- i + 1
        yield i * 10 ]
test "colc11" (whileUp () = [ 10; 20; 30 ])

// ARRAY comprehensions: same shapes. Arrays compare by REFERENCE in F++
// (a chosen divergence, DIVERGENCES.md) — compare through Array.toList.
test "coac1" (Array.toList [| for i in ie1 -> i, i * i |] = [ (1, 1); (2, 4); (3, 9) ])
test "coac2" (Array.toList [| for i in [ 1 .. 5 ] do
                                if i % 2 = 0 then yield i + 100 |] = [ 102; 104 ])
let coac3 = [| for i in ie1 do
                 for j in [ i .. 3 ] do yield i, j |]
test "coac3" (Array.toList coac3 = [ (1, 1); (1, 2); (1, 3); (2, 2); (2, 3); (3, 3) ])
let coac4 = [| for i in ie1 do
                 for j in [ i .. 3 ] do
                     if i = j then yield i + i, j + j
                     else yield i, j |]
test "coac4" (Array.toList coac4 = [ (2, 2); (1, 2); (1, 3); (4, 4); (2, 3); (6, 6) ])
test "coac5" (Array.toList [| for (i, j) in [| (1, 2); (3, 4) |] -> i + j |] = [ 3; 7 ])
// a stepped range in ARRAY brackets splices, as in a list
test "coar1" (Array.toList [| 3 .. -1 .. 0 |] = [ 3; 2; 1; 0 ])

// a for over a comprehension result, counting
let count1 =
    let mutable count = 0
    for _i in [ 1 .. 3 ] do
        for _j in [ 1 .. 3 ] do
            count <- count + 1
    count
test "conest1" (count1 = 9)

// ---- the ELEMENT type of a comprehension -----------------------------------
// A `for` types as unit, so the collection's element type has to come from
// what the body YIELDS. Left free it looked fine — until something needed a
// CLASS instance for the element (`List.sum` wants Num), which then had
// nothing to dispatch on and trapped at run time.

test "sum-of-an-arrow-comprehension" (List.sum [ for i in [ 1; 2; 3 ] -> i * 10 ] = 60)
test "sum-of-a-yield-comprehension" (List.sum [ for i in [ 1; 2; 3 ] do yield i * 10 ] = 60)
test "sum-of-a-conditional-comprehension" (List.sum [ for i in [ 1; 2; 3 ] do if i > 1 then yield i ] = 5)
test "sum-of-a-yield-bang-comprehension" (List.sum [ for i in [ 1; 2; 3 ] do yield! [ i; i ] ] = 12)
test "sum-of-an-array-comprehension" (Array.sum [| for i in [ 1; 2; 3 ] -> i * 10 |] = 60)
test "sum-over-a-range" (List.sum [ for i in 1 .. 4 -> i ] = 10)
test "sum-of-a-nested-loop" (List.sum [ for i in 1 .. 2 do for j in 1 .. 2 do yield i * j ] = 9)
test "sum-through-a-let" (List.sum [ for i in [ 1; 2 ] do let d = i * 3 in yield d ] = 9)
test "sum-with-a-tuple-binder" (List.sum [ for (a, b) in [ (1, 2); (3, 4) ] -> a + b ] = 10)

// the same for FLOAT elements, where the instance differs
test "float-sum" (List.sum [ for i in [ 1.5; 2.5 ] -> i ] = 4.0)
test "float-average" (List.average [ for i in [ 1.0; 3.0 ] -> i ] = 2.0)

// other class-constrained functions over a comprehension
test "max-of-a-comprehension" (List.max [ for i in [ 1; 5; 3 ] -> i ] = 5)
test "min-of-a-comprehension" (List.min [ for i in [ 4; 2 ] -> i ] = 2)
test "sort-of-a-comprehension" (List.sort [ for i in [ 3; 1 ] -> i ] = [ 1; 3 ])
test "sumBy-over-a-comprehension" (List.sumBy (fun v -> v * 2) [ for i in 1 .. 3 -> i ] = 12)

// a NESTED comprehension: the outer element is the inner COLLECTION, not its
// element — taking the inner yield for the outer froze it to int
let grid = [| for i in 0 .. 2 -> [| for j in 0 .. i -> j |] |]
test "nested-array-comprehension" (Array.sum (Array.map Array.sum grid) = 4)
test "nested-list-comprehension" (List.sum [ for i in 1 .. 2 -> List.sum [ for j in 1 .. i -> j ] ] = 4)

printfn "DONE tests=%d failures=%d" ntests failures

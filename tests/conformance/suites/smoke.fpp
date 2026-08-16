// Harness smoke: the common-subset test protocol itself.
module Core_smoke

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

test "arith1" (1 + 2 * 3 = 7)
test "cmp1" (compare 3 2 > 0)
test "sort1" (List.sort [ 3; 1; 2 ] = [ 1; 2; 3 ])
test "str1" ("ab" + "c" = "abc")
test "opt1" (Some 5 |> Option.map (fun x -> x + 1) = Some 6)

printfn "DONE tests=%d failures=%d" ntests failures

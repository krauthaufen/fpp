// Ported from dotnet/fsharp tests/fsharp/core/nested/test.fsx into the
// common F#/F++ subset. `module X = begin ... end` becomes the indented
// form, and the stderr trace prints are folded into the `wher` list the
// original asserts on. The point of the test is module INITIALIZATION
// ORDER: module bodies run in declaration order, interleaved with the
// top-level statements around them.
module Core_nested

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let wher : string list ref = ref []
let spot (x : string) = wher := !wher @ [ x ]

spot "Initialized before X1 OK"

module X1 =
    type x = X | Y
    let y = 3
    let _ = spot "Initialized X1 OK"

module X2 =
    type x = X | Y
    let x = 3
    let y () = X
    let z = x + (match y () with X -> 4 | Y -> 5)
    let _ = spot "Initialized X2 OK"

module X3 =
    let y = X2.X
    let _ = spot "Initialized X3 OK"

spot "Initialized after X3 OK"

test "uyf78-order"
    (!wher = [ "Initialized before X1 OK"
               "Initialized X1 OK"
               "Initialized X2 OK"
               "Initialized X3 OK"
               "Initialized after X3 OK" ])
test "uyf78-vals" (X2.z + X2.x + X1.y = 13)

printfn "DONE tests=%d failures=%d" ntests failures

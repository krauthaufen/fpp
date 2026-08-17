// Ported from dotnet/fsharp tests/fsharp/core/recordResolution/test.fsx
// into the common F#/F++ subset. The original is a COMPILE test: a record
// literal picks the LAST-declared record whose fields cover the written
// labels. Value asserts are added so the chosen layouts are observable.
// Dropped: Ex3 (`open` re-exporting the types — F++ modules here nest in
// one file, the open shadows differently) and Ex4's `a2 :> A2` coercion
// (an upcast on a record type, warning-laden even in F#).
module Core_recordres

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

module Ex1 =
    type A = { FA : int }
    type B = { FB : int }
    type AB = { FA : int; FB : int }

    let a = { FA = 1 }
    let b = { FB = 2 }
    let a2 = { a with FA = 2 }

test "ex1" (Ex1.a.FA = 1 && Ex1.b.FB = 2 && Ex1.a2.FA = 2)

module Ex2 =
    type A = { FA : int }
    type B = { FB : int }
    type C = { FC : int }
    type AB = { FA : int; FB : int }
    type AC = { FA : int; FC : int }
    type CB = { FC : int; FB : int }
    type ABC = { FA : int; FB : int; FC : int }

    let a = { FA = 1 }
    let b = { FB = 1 }
    let c = { FC = 1 }
    let ab = { FA = 1; FB = 2 }
    let ac = { FA = 1; FC = 2 }
    let cb = { FC = 1; FB = 2 }
    let abc = { FA = 1; FB = 2; FC = 3 }

    let a2 = { a with FA = 2 }

test "ex2-singles" (Ex2.a.FA = 1 && Ex2.b.FB = 1 && Ex2.c.FC = 1)
test "ex2-pairs" (Ex2.ab.FB = 2 && Ex2.ac.FC = 2 && Ex2.cb.FC = 1 && Ex2.cb.FB = 2)
test "ex2-abc" (Ex2.abc.FA = 1 && Ex2.abc.FB = 2 && Ex2.abc.FC = 3)
test "ex2-with" (Ex2.a2.FA = 2)

printfn "DONE tests=%d failures=%d" ntests failures

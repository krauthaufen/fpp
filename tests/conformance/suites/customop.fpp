// `[<CustomOperation>]` computation-expression operations — FShade's sampler
// CE shape: each op threads the accumulator, seeded by Yield, closed by Run.
module CustomOp

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "WRONG %s: %s exp..got %s" name want got

type State = { A : int; B : int }
type Result = { Sum : int }
type Builder() =
    member _.Yield(_ : unit) : State = { A = 0; B = 0 }
    [<CustomOperation("setA")>]
    member _.SetA(s : State, v : int) : State = { s with A = v }
    [<CustomOperation("setB")>]
    member _.SetB(s : State, v : int) : State = { s with B = v }
    member _.Run(s : State) : Result = { Sum = s.A + s.B }

let build = Builder()

let r1 = build { setA 3; setB 4 }
eq "two-ops" (string r1.Sum) "7"
let r2 = build { setB 10; setA 5 }
eq "order-independent-here" (string r2.Sum) "15"
let r3 = build { setA 100 }
eq "one-op" (string r3.Sum) "100"

printfn "DONE tests=%d failures=%d" ntests failures

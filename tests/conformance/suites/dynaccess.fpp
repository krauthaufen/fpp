// `a?Name` is `(?) a "Name"` — FShade's custom-uniform spelling — and an
// enum member may be negative. Both from the fpp.shader request list.
module DynAccess

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "WRONG %s: %s exp..got %s" name want got

type Scope = { Vals : (string * int) list }
let (?) (s : Scope) (name : string) : int =
    s.Vals |> List.pick (fun (k, v) -> if k = name then Some v else None)

let scope = { Vals = [ "Alpha", 10; "Beta", 20 ] }
eq "dyn-simple" (string scope?Alpha) "10"
eq "dyn-second" (string scope?Beta) "20"
eq "dyn-in-expr" (string (scope?Alpha + scope?Beta)) "30"

type Level =
    | Debug = -1
    | Info = 0
    | Compute = 5
eq "enum-negative" (string (int Level.Debug)) "-1"
eq "enum-positive" (string (int Level.Compute)) "5"

printfn "DONE tests=%d failures=%d" ntests failures

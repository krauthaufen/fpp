// `use x = new T(...)` INSIDE A MATCH ARM fails to parse ("unexpected token
// at top level" from the arm onward). The same binding parses fine at
// function top, and a plain `let` + explicit Dispose in the arm works —
// which is the workaround Fpp.Cli's publish path uses.
module UseNewInArm

type D() =
    member x.Get () : int = 7
    member x.Dispose () : unit = ()

let f (o : option<int>) : int =
    match o with
    | None -> 0
    | Some v ->
        use d = new D()
        d.Get () + v

let a = printfn "%d" (f (Some 1))

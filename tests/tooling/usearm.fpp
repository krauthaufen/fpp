// REGRESSION: `use x = new T(...)` inside a MATCH ARM once fell out of the
// clause entirely (the arm-body gate was missing the `use` keyword) and
// surfaced as "unexpected token at top level". Both backends, both `use`
// positions.
module UseArm

type D(tag : int) =
    member x.Get () : int = tag
    member x.Dispose () : unit = printfn "%d" (tag * 10)

let top () : int =
    use d = new D(1)
    d.Get ()

let inArm (o : option<int>) : int =
    match o with
    | None -> 0
    | Some v ->
        use d = new D(2)
        d.Get () + v

let a = printfn "%d" (top ())
let b = printfn "%d" (inArm (Some 5))
let c = printfn "%d" (inArm None)

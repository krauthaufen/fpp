// The uniqueness query, NATIVE semantics: heap+static edges only, stack
// excluded. A top-level binding is a static (counts), a function local is
// not (reuses). The oracle answers conservatively (never unique) — this
// program is native-only, asserted by exact output.
module GcUniq
type Holder = { mutable Slot : int[] }
let held = [| 4; 5; 6 |]
let cell = { Slot = held }
let localCase () : string =
    let a = [| 7; 8; 9 |]
    match GC.ReuseIfUnique a (fun x ->
            x.[0] <- 70
            x.[0]) with
    | Some v -> "reused " + string v
    | None -> "copied"
let topCase () : string =
    match GC.ReuseIfUnique held (fun x -> x.[0]) with
    | Some _ -> "WRONG"
    | None -> "shared stays"
let r1 = printfn "%s" (localCase ())
let r2 = printfn "%s" (topCase ())
let r3 = printfn "%d" (GC.HeapRefs held)
let r4 = printfn "%d" cell.Slot.[0]

// A COMPUTATION EXPRESSION NESTED UNDER CONTROL FLOW INSIDE ANOTHER ONE.
//
// The rewrite needs each CE's BUILDER TYPE — `Run` and `Delay` wrap the body
// if and only if the builder declares them — and that comes from a probe pass
// that types every CE's builder before the rewrite runs. The probe walked a
// CE's body items, but deliberately skipped the ones still written in forms
// the rewrite has not produced yet: `for`, `if`, `match`, `yield`, `let!`. A
// CE nested INSIDE one of those was therefore never typed, came back as the
// UNKNOWN builder — no Run, no Delay — and its statements desugared onto the
// OUTER builder instead.
//
// In fpp.dom that was silent: `div { for i in 1 .. 3 do span { … } }` put the
// spans' attributes on the div and produced no span children at all
// (~/claude/fpp-base-snags.md #50). In the smaller shape below it was a type
// error at a synthetic offset, which is no better a diagnosis.
//
// The builder here is the donor shape reduced to what the bug needs: Yield,
// Combine, Delay, Zero, For and Run, with Run changing the type (a list of
// children becomes a node), which is what makes a missing Run observable.
module Core_nestedce

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

type Node = { Tag : string; Kids : Node list }

let rec render (n : Node) : string =
    n.Tag + "[" + String.concat "," (List.map render n.Kids) + "]"

type ElemBuilder(tag : string) =
    member _.Yield (s : string) : Node list = [ { Tag = s; Kids = [] } ]
    member _.Yield (n : Node) : Node list = [ n ]
    member _.Combine (a : Node list, b : Node list) : Node list = a @ b
    member _.Delay (f : unit -> Node list) : Node list = f ()
    member _.Zero () : Node list = []
    member _.For (xs : int seq, f : int -> Node list) : Node list = List.collect f (List.ofSeq xs)
    member _.Run (kids : Node list) : Node = { Tag = tag; Kids = kids }

let div = ElemBuilder "div"
let span = ElemBuilder "span"

// the control: a nested CE as a direct statement always worked
let a = div { span { "x" } }
eq "nested-ce-as-a-statement" (render a) "div[span[x[]]]"

// under a `for`
let b = div { for i in 1 .. 3 do span { "k" } }
eq "nested-ce-in-a-for-body" (render b) "div[span[k[]],span[k[]],span[k[]]]"

// under a `for`, with an explicit yield
let c = div { for i in 1 .. 2 do yield span { "y" } }
eq "nested-ce-in-a-for-body-yielded" (render c) "div[span[y[]],span[y[]]]"

// under both branches of an `if`
let d = div { if true then span { "t" } else span { "f" } }
eq "nested-ce-in-a-then-branch" (render d) "div[span[t[]]]"
let e = div { if false then span { "t" } else span { "f" } }
eq "nested-ce-in-an-else-branch" (render e) "div[span[f[]]]"

// two levels down: a CE inside a CE inside a for-body
let f = div { for i in 1 .. 2 do span { div { "deep" } } }
eq "two-levels-under-a-for" (render f) "div[span[div[deep[]]],span[div[deep[]]]]"

// beside plain items, so the Combine path carries both
let g =
    div {
        "head"
        for i in 1 .. 2 do span { "mid" }
        "tail"
    }
eq "nested-ce-beside-plain-items" (render g) "div[head[],span[mid[]],span[mid[]],tail[]]"

// under a `match`
let h (n : int) : Node =
    div {
        match n with
        | 0 -> span { "zero" }
        | _ -> span { "other" }
    }
eq "nested-ce-in-a-match-arm" (render (h 0)) "div[span[zero[]]]"
eq "and-the-other-arm" (render (h 5)) "div[span[other[]]]"

printfn "DONE tests=%d failures=%d" ntests failures

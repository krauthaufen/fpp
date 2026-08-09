// REGRESSION: same-name SAME-arity types in two modules are two TYPES.
// They used to merge layouts (B's record got A's fields and every use
// stubbed "missing field"); the pre-sweep now decorates the second
// declaration and written uses resolve through the token's binding.
// Different-arity variants and the deliberate prelude merge still work.
module SameArity
module A =
    type T<'a> = { X : 'a; Tag : int }
    let mk (v : int) : T<int> = { X = v; Tag = 1 }
module B =
    type T<'a> = { Y : 'a; Kind : string }
    let mk (v : string) : T<string> = { Y = v; Kind = "b" }
type Pair<'a, 'b> = { A : 'a; B : 'b }
module Inner =
    type Pair<'x> = { Only : 'x }
    let mk (v : int) : Pair<int> = { Only = v }
let a = A.mk 7
let b = B.mk "hi"
let p : Pair<int, string> = { A = 1; B = "x" }
let q = Inner.mk 9
let r1 = printfn "%d" a.X
let r2 = printfn "%s" b.Y
let r3 = printfn "%d" p.A
let r4 = printfn "%d" q.Only

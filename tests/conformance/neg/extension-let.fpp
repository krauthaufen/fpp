// a `let` in a type extension was silently discarded, side effects included
module Neg_extension_let
//! 7 not allowed in a type extension
type Foo() =
    member _.A = 1
type Foo with
    let helper = printfn "SIDE EFFECT"
printfn "%d" (Foo().A)

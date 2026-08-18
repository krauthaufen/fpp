// a constructor called with arguments it does not take
module Neg_ctor_arg_count
//! 6 type mismatch: unit vs int * int
type C() =
    member x.M () = 1
let c = C(1, 2)
printfn "%d" (c.M ())

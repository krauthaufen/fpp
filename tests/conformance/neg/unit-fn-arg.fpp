// a unit-taking function applied to a value
module Neg_unit_fn_arg
//! 5 type mismatch: unit vs int
let f () = 1
let y = f 3
printfn "%d" y

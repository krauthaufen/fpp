// applying a non-function value
module Neg_apply_non_function
//! 5 type mismatch: int vs int -> 'a
let x = 1
let y = x 3
printfn "%d" y

// more arguments than the function takes
module Neg_too_many_args
//! 5 type mismatch: int vs int -> 'a
let f (x : int) = x + 1
let y = f 1 2
printfn "%d" y

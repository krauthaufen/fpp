// an if condition that is not a bool
module Neg_if_not_bool
//! 4 type mismatch: int vs bool
let x = if 1 then 2 else 3
printfn "%d" x

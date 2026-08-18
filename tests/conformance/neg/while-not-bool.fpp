// a while condition that is not a bool
module Neg_while_not_bool
//! 5 type mismatch: int vs bool
let mutable n = 0
while 1 do
    n <- n + 1
printfn "%d" n

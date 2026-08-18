// assignment to an immutable binding
module Neg_assign_immutable
//! 5 'x' is not mutable
let x = 1
x <- 2
printfn "%d" x

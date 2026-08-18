// assignment to an immutable record field
module Neg_assign_immutable_field
//! 6 the field 'a' of R is not mutable
type R = { a : int }
let r = { a = 1 }
r.a <- 2
printfn "%d" r.a

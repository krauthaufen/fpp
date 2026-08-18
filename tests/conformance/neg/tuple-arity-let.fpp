// a let pattern with the wrong tuple size
module Neg_tuple_arity_let
//! 4 type mismatch: 'a * 'b vs int * int * int
let (a, b) = (1, 2, 3)
printfn "%d" a

// a union case applied at the wrong arity
module Neg_union_wrong_arity
//! 5 type mismatch: int vs int * int
type U = A of int | B
let v = A (1, 2)
printfn "ok"

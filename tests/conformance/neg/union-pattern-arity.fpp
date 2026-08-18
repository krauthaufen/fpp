// a union pattern taking the payload apart at the wrong arity
module Neg_union_pattern_arity
//! 7 type mismatch: int * int vs 'a * 'b * 'c
type U = A of int * int | B
let f (u : U) =
    match u with
    | A (x, y, z) -> x
    | _ -> 0
printfn "%d" (f B)

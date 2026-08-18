// a literal pattern of the wrong type
module Neg_literal_pattern_type
//! 6 type mismatch: int vs string
let f (x : int) =
    match x with
    | "one" -> 1
    | _ -> 0
printfn "%d" (f 1)

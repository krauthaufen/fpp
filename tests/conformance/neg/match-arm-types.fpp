// match arms answering different types
module Neg_match_arm_types
//! 7 type mismatch: string vs int
let f (x : int) =
    match x with
    | 0 -> 1
    | _ -> "many"
printfn "%A" (f 0)

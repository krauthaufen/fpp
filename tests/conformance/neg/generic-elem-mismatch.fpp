// an annotated element type the literal contradicts
module Neg_generic_elem_mismatch
//! 4 type mismatch: string vs int
let xs : int list = [ "a"; "b" ]
printfn "%d" (List.length xs)

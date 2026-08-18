// an annotation naming a type nothing declares
module Neg_unknown_type
//! 5 type mismatch: NoSuchType vs int
let f (x : NoSuchType) = 1
printfn "%d" (f 1)

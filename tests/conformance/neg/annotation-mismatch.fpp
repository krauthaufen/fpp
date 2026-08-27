// a value annotation the initializer contradicts
module Neg_annotation_mismatch
//! 4 type mismatch: string vs int
let x : string = 1
printfn "%s" x

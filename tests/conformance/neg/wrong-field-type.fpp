// a record field given a value of the wrong type
module Neg_wrong_field_type
//! 5 type mismatch: string vs int
type R = { a : int }
let r = { a = "nope" }
printfn "%d" r.a

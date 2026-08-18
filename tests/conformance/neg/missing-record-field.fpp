// a record literal that leaves a declared field out
module Neg_missing_record_field
//! 5 the record literal for R leaves field 'b' out
type R = { a : int; b : string }
let r = { a = 1 }
printfn "%d" r.a

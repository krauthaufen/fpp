// a record literal naming a field the type does not declare
module Neg_unknown_record_field
//! 5 the record R has no field 'zz'
type R = { a : int; b : string }
let r = { a = 1; zz = "x" }
printfn "%d" r.a

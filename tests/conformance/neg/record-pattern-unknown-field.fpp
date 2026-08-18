// a record pattern naming a field the type does not declare
module Neg_record_pattern_unknown_field
//! 7 the record R has no field 'zz'
type R = { a : int; b : string }
let f (r : R) =
    match r with
    | { zz = x } -> x
printfn "%d" (f { a = 1; b = "s" })

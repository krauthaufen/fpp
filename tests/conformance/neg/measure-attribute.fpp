// the declaration half: [<Measure>] promises checking that never happens.
module Neg_measure_attribute
//! 4 units of measure are not supported
[<Measure>] type m
printfn "%s" "unreachable"

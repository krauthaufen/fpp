// a unit on a numeric literal. Nothing here implements measures, so the
// suffix was parsed and discarded and `1.0<m> + 2.0<s>` answered 3.
module Neg_measure_literal
//! 7 units of measure are not supported
[<Measure>] type m
[<Measure>] type s
printfn "%s" (string (1.0<m> + 2.0<s>))

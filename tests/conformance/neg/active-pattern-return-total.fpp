// a total multi-case active pattern must return a choice — rejected at the
// DEFINITION now; unused, it was accepted outright
module Neg_active_pattern_return_total
//! 5 must return a 2-way choice
let (|Foo|Bar|) x = "BAD"
printfn "ok"

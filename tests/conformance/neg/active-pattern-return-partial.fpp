// a partial active pattern must return an option
module Neg_active_pattern_return_partial
//! 4 must return an option
let (|Foo|_|) x = "BAD"
printfn "ok"

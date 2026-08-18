// a lambda argument used at two incompatible types
module Neg_fun_arg_type
//! 4 no instance Add<int, string>
let f = fun x -> (x + 1, x + "s")
printfn "%A" (f 1)

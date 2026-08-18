// an or-pattern whose sides bind different names
module Neg_or_pattern_binding
//! 6 'v' is not bound in every alternative of this pattern
let f (x : int option) =
    match x with
    | Some v | None -> v
printfn "%d" (f (Some 1))

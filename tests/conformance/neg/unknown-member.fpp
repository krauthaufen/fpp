// a member access the receiver's type does not declare
module Neg_unknown_member
//! 6 R has no member zz
type R = { a : int }
let r = { a = 1 }
printfn "%d" r.zz

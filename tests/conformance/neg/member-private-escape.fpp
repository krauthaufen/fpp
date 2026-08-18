// a private member used from outside its type
module Neg_member_private_escape
//! 8 member Secret of C is private
type C() =
    member private x.Secret () = 42
    member x.Ok () = 1
let c = C()
printfn "%d" (c.Secret ())

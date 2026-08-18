// an instance member called through the type
module Neg_instance_as_static
//! 6 'M' is an instance member of C — call it on an instance
type C() =
    member x.M () = 1
printfn "%d" (C.M ())

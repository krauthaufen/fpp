// the value would contain itself by value: no finite size
module Neg_struct_self_field
//! 6 no finite size
[<Struct>]
type S =
    val X : S
printfn "ok"

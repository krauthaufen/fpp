// a value has no vtable to dispatch through
module Neg_struct_abstract_member
//! 7 cannot declare an abstract member
[<Struct>]
type S =
    val X : int
    abstract M : int -> int
printfn "ok"

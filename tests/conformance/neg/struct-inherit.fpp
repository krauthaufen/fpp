// a value embeds no base object
module Neg_struct_inherit
//! 8 cannot inherit
type Base() =
    member _.B = 1
[<Struct>]
type S =
    inherit Base
    val X : int
printfn "ok"

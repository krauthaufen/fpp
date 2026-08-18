// inherit used with an interface
module Neg_inherit_interface
//! 7 'IThing' is an interface — implement it with `interface IThing with`, not `inherit`
type IThing =
    abstract member Go : unit -> int
type T() =
    inherit IThing
printfn "ok"

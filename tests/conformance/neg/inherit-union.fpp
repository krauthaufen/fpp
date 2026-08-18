// Types/UnionTypes/E_InheritUnion: a class inheriting a union
module Neg_inherit_union
//! 6 cannot inherit from 'DiscUnion': it is not a class
type DiscUnion = A of int | B of string
type Foo() =
    inherit DiscUnion
    member this.Stuff = 1
printfn "ok"

// two abstract members of one name on an interface. A vtable row is keyed by
// (interface, member), so the second takes the first's slot and one of them
// is unreachable — F# rejects the declaration.
module Neg_iface_duplicate_abstract
//! 8 duplicate abstract member
type IFoo =
    abstract Do : int -> int
    abstract Do : int -> int -> int
type C() =
    interface IFoo with
        member _.Do (a : int) : int = a + 1
        member _.Do (a : int) (b : int) : int = a + b
printfn "%d" ((C() :> IFoo).Do 1)

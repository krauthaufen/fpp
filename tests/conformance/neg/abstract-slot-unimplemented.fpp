// a concrete class that leaves an inherited abstract slot empty. The slot
// stays 0 ($novt) and the call TRAPS when reached — accepted at compile time
// and dead at run time.
module Neg_abstract_slot_unimplemented
//! 9 does not implement inherited abstract member
[<AbstractClass>]
type Base() =
    abstract Speak : unit -> string
type Derived() =
    inherit Base()
printfn "%s" ((Derived() :> Base).Speak ())

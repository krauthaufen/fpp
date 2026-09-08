// AN UPCAST'S TYPE ARGUMENTS COME FROM THE CLASS.
//
// `C<'T>(v) :> IBox<_>` is an `IBox<'T>` and nothing else — the class
// declares which instantiation of the interface it implements. Left to the
// wildcard, the two were INDEPENDENT variables here, so a function written
// exactly like the adaptive port's `AVal.constant`
//
//     let constant (v : 'T) : aval<_> = ConstantVal<'T>(v) :> aval<_>
//
// inferred `'a -> aval<'b>`. A value of it then FITTED a parameter declared
// `aval<seq<_>>`, an overload was chosen on that lie, and the option inside
// was ENUMERATED at run time — a trap in a vtable row that does not exist,
// half a day away from the cast that caused it (~/claude/fpp-base-snags.md
// #48, and the six cases it kept blocked in fpp.dom's CE gate).
//
// fsc rejects the same program at the same place (FS0001).
module Neg_upcast_wildcard_argument
//! 28 IEnumerable<int> vs Option<int>
type IBox<'a> =
    abstract member Get : unit -> 'a

type C<'T>(v : 'T) =
    member x.V = v
    interface IBox<'T> with
        member x.Get () = v

let mk (v : 'T) : IBox<_> = C<'T> v :> IBox<_>
let b : IBox<seq<int>> = mk (Some 3)
printfn "%d" (Seq.length (b.Get ()))

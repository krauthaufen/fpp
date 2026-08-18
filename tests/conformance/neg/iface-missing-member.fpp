// an interface implementation leaving a member out
module Neg_iface_missing_member
//! 8 this IThing implementation leaves 'Stop' out
type IThing =
    abstract member Go : unit -> int
    abstract member Stop : unit -> int
type T() =
    interface IThing with
        member x.Go () = 1
let t = T()
printfn "%d" ((t :> IThing).Go ())

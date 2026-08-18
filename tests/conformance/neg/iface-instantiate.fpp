// instantiating an interface
module Neg_iface_instantiate
//! 6 cannot instantiate the interface 'IThing'
type IThing =
    abstract member Go : unit -> int
let t = IThing()
printfn "%d" (t.Go ())

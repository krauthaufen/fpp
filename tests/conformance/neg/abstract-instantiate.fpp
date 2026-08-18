// instantiating an abstract class directly
module Neg_abstract_instantiate
//! 7 cannot instantiate 'Shape': it is abstract
[<AbstractClass>]
type Shape() =
    abstract member Area : unit -> int
let s = Shape()
printfn "%d" (s.Area ())

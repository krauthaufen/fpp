// an override with no abstract member to override
module Neg_override_no_abstract
//! 8 'Nope' overrides nothing: no base member of that name
type Base3() =
    member x.Hi () = 1
type Der3() =
    inherit Base3()
    override x.Nope () = 2
printfn "ok"

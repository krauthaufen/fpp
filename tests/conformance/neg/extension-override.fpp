// an override in an extension registers nowhere dispatch looks — the
// original method kept answering, silently
module Neg_extension_override
//! 8 not allowed in a type extension
type C() =
    override this.ToString () = "real"
type C with
    override this.ToString () = "extension"
printfn "%s" (C().ToString ())

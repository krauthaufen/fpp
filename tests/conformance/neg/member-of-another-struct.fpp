// A MEMBER THAT EXISTS ONLY ON ANOTHER STRUCT TYPE, from the fpp.base port
// (KNOWN-ISSUES #28). `b.ToRot3d` where ToRot3d is declared on A compiled
// clean and left a bare `.ToRot3d` in the tree — which the backend answers
// with a trap. F# rejects it ("The field, constructor or member 'ToRot3d' is
// not defined"), and so does this now.
//
// The missing-member diagnostic is deliberately SUPPRESSED when the name
// exists somewhere, because a by-name guess can be legitimate — the
// arity-split sibling shape in the adaptive port depends on it. A STRUCT
// receiver is the exception: structs do not inherit, so a member declared on
// another type can never be reached on one, and the name existing as some
// other type's member is exactly the evidence that this use is wrong.
//
// fpp.base hit it with `(q.ToM44d).ToRot3d` — ToRot3d is an M33d extension —
// which built fine and trapped in its coverage tests.
module Neg_member_of_another_struct
//! 25 B has no member ToRot3d
[<Struct>]
type A = { X : float; Y : float }
[<Struct>]
type B = { P : float; Q : float; R : float }
type A with
    member a.ToRot3d : float = a.X + a.Y
let b = { P = 1.0; Q = 2.0; R = 3.0 }
let t = printfn "%g" b.ToRot3d

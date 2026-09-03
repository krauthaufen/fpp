// A VALUE SHADOWS A MODULE OF ITS OWN NAME, from the fpp.base port
// (KNOWN-ISSUES #6). F# keeps modules and values in different namespaces and
// a value-position use finds the VALUE — so with `let V3d` in scope,
// `V3d.length` is a member access on a FUNCTION, and F# rejects it (FS0039)
// at exactly the position this file expects.
//
// The idiom is standard F#: a constructor function beside a module of the
// same name, which is how `V3d (3.0, 4.0, 0.0)` and `V3d.length v` are meant
// to read. The module used to overwrite the value binding, so the CALL
// resolved to the type instead — `V3d (3.0, 4.0, 0.0)` built a zero record
// and every length came out 0, with no diagnostic anywhere. The generator in
// fpp.base writes exactly this shape.
//
// Two errors, because the access appears twice. Rejecting is F#'s answer,
// not a limitation: the module is still reachable, just not under a name a
// value has taken.
module Neg_value_shadows_module
//! 27 a function has no member 'length'
//! 28 a function has no member 'length'
[<Struct>]
type V3<'a> = { X : 'a; Y : 'a; Z : 'a }
type V3d = V3<float>
let V3d (x : float, y : float, z : float) : V3d = { X = x; Y = y; Z = z }
module V3d =
    let length (v : V3d) = sqrt (v.X * v.X + v.Y * v.Y + v.Z * v.Z)
let v = V3d (3.0, 4.0, 0.0)
let f (w : V3d) = V3d.length w
let t = printfn "%g %g" (f v) (V3d.length v)

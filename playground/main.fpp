module Main

// fpp.base FIRST: the playground's own `Vec` defines a V2d too, and the later
// open wins, so opening the library first leaves the local demos untouched
// while everything the library adds (V3d, M44d, Box3d, ...) is in scope.
open Fpp.Base
open Vec
open Classes
open Classes.Display
open Classes.Norm

// ---- generic math at three types from ONE definition -------------------
// Hover `double`: its scheme shows the inferred Add constraint.
let double x = x + x

let ints    = printfn "double 21      = %d" (double 21)
let floats  = printfn "double 1.5     = %f" (double 1.5)
let strings = printfn "double \"ab\"    = %s" (double "ab")

// ---- vectors through the same operators --------------------------------
let p = { X = 3.0; Y = 4.0 }
let q = { X = 1.0; Y = 2.0 }

// go-to-definition on `dot`, `lengthOf`, `clamp` jumps into vec.fpp
let v1 = printfn "p + q          = (%f, %f)" (p + q).X (p + q).Y
let v2 = printfn "2 * p          = (%f, %f)" (2.0 * p).X (2.0 * p).Y
let v3 = printfn "dot p q        = %f" (dot p q)
let v4 = printfn "length p       = %f" (lengthOf p)
let v5 = printfn "clamp          = (%f, %f)" (clamp Zero One p).X (clamp Zero One p).Y

// one generic body, stamped per type — ints, vectors, halves
let s1 = printfn "sum ints       = %d" (sumOf [| 1; 2; 3; 4 |] 0)
let s2 = printfn "sum vecs (X)   = %f" (sumOf [| p; q |] Zero).X

// ---- float16: 2 bytes per element, arithmetic bit-exact ----------------
let halves = [| 1.5h; 2.25h; 0.25h |]
let h1 = printfn "sum halves     = %f" (float (sumOf halves Zero))

// ---- lazy sequences over the enumerator protocol ------------------------
let seqDemo =
    [ 1; 2; 3; 4; 5; 6 ]
    |> Seq.filter (fun v -> v % 2 = 0)
    |> Seq.map (sprintf "%A")
    |> String.concat "; "
    |> printfn "evens          = [%s]"

// ---- hover `compare`, `min`, `sqrt`: constraints in the signature ------
let ordDemo = printfn "compare 2 9    = %d" (compare 2 9)

// ---- the playground's own typeclasses (classes.fpp) --------------------
let c1 = printfn "%s" (describe "answer" 42)
let c2 = printfn "%s" (describe "pi-ish" 3.14)
let c3 = printfn "%s" (describe "ready" true)
let c4 = printfn "%s" (describe "p" p)

let m1 = printfn "mconcat ints   = %d" (mconcat [ 1; 2; 3; 4 ])
let m2 = printfn "mconcat strs   = %s" (mconcat [ "a"; "b"; "c" ])
let m3 = printfn "mconcat vecs   = (%f, %f)" (mconcat [ p; q ]).X (mconcat [ p; q ]).Y

let n1 = printfn "norm p         = %f" (norm p)
let n2 = printfn "norm -2.5      = %f" (norm (0.0 - 2.5))

// ---- fpp.base, referenced as a compiled library (see playground.fppproj) ---
// The Aardvark.Base port: V3d/M44d/Box3d/Trafo3d and the geometry on them.
// Hover any of these — the types come from the .fppir, not from source in this
// folder, and go-to-definition still resolves into fpp.base.
//
// fpp.base is referenced by SOURCE (see playground.fppproj): a `lib`/package
// reference builds but does not carry type MEMBERS, so `.Dot` on a V3d from a
// library traps. By source, the whole API works — statics included.
let b1 = v3d (1.0, 2.0, 3.0)
let b2 = v3d (4.0, 5.0, 6.0)
let g1 = printfn "v3d dot        = %f" (b1.Dot b2)
let g2 = printfn "v3d cross      = (%f, %f, %f)" (b1.Cross b2).X (b1.Cross b2).Y (b1.Cross b2).Z
let g3 = printfn "v3d length     = %f" b2.Length
let g4 = printfn "v3d normalized = %f" b2.Normalized.Length

let bx = box3d (v3d (0.0, 0.0, 0.0), v3d (2.0, 4.0, 6.0))
let g5 = printfn "box3d size     = (%f, %f, %f)" bx.Size.X bx.Size.Y bx.Size.Z

// STATIC members and the geometry types
let rot = M44d.RotationZ 0.5
let rp = rot.TransformPos b1
let g6 = printfn "m44 rotate     = (%f, %f, %f)" rp.X rp.Y rp.Z
let hull = Box3d.FromPoints (b1, b2, v3d (0.0, 9.0, 0.0))
let g7 = printfn "box from pts   = (%f, %f, %f)" hull.Max.X hull.Max.Y hull.Max.Z
// NOTE: a `Ray3d.IntersectPlane` line here traps at runtime, but ONLY when all
// three of the playground's own classes (Display, Monoid, Norm) are compiled
// alongside fpp.base. Any one or two of them is fine; the three together are
// not. Reduced repro in KNOWN-ISSUES — it is a compiler bug, not this file.

// Uncomment to watch diagnostics appear as you type:
//let bad1 : int = "not an int"
//let bad2 = 1 + "x"
//let bad3 = 1.5 % 2.0y

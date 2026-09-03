// THE BY-VALUE STRUCT ABI, from the two shapes the fpp.base port broke on
// (KNOWN-ISSUES #16 and #17 in that library's report).
//
// A plain function's struct parameter is passed as its FIELDS, in registers,
// rather than as a pointer — the same choice .NET makes. Two kinds of field
// had no support in the paths that read those registers back, and each
// failed in a way that named nothing useful:
//
//   * a float32 field. The register is an f32 LOCAL, and the read had arms
//     for f64 and i64 only, so it fell through to "read it as a word". The
//     consumer then took that word for a boxed-float pointer and emitted an
//     `f64.load` — a module that failed VALIDATION, with the error pointing
//     at a load instruction rather than at the parameter. Every `*f` type in
//     fpp.base (V3f, M44f, Box3f) was excluded from its build for this.
//   * a field that is itself a STRUCT. Rebuilding the whole value walked the
//     top-level fields and demanded a scalar storage type for each, which a
//     nested struct does not have — the COMPILER died with "optGet: None"
//     rather than compiling the program. A Box is `{ Min : V; Max : V }`, so
//     every lambda inside one of their members crashed the build.
//
// DROPPED: the performance side (a struct crossing a call still allocates —
// PLAN-STACK step 3), which is a number, not an answer.
module Core_structabi

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// ---- float32 FIELDS ------------------------------------------------------

[<Struct>]
type V2f = { X : float32; Y : float32 }

// reading a float32 field out into a float32 result: the shape that failed
// validation on its own
let sx (v : V2f) : float32 = v.X
let sy (v : V2f) : float32 = v.Y

eq "float32-field-out" (string (float (sx { X = 1.0f; Y = 2.0f }))) "1"
eq "the-other-float32-field" (string (float (sy { X = 1.0f; Y = 2.0f }))) "2"

// a float32 PARAMETER beside the struct, which failed the same way
let scale (s : float32) (v : V2f) : V2f = ({ X = s * v.X; Y = s * v.Y } : V2f)

eq "float32-param-and-struct" (string (float (scale 2.0f { X = 1.0f; Y = 2.0f }).Y)) "4"
eq "and-its-other-field" (string (float (scale 3.0f { X = 1.0f; Y = 2.0f }).X)) "3"

// struct in and struct out, and float32 in with struct out — both already
// worked, and are here so a fix cannot trade one for the other
let idv (v : V2f) : V2f = v
let mk (x : float32) : V2f = ({ X = x; Y = x } : V2f)

eq "struct-through" (string (float (idv { X = 5.0f; Y = 6.0f }).Y)) "6"
eq "float32-in-struct-out" (string (float (mk 7.0f).X)) "7"
eq "composed" (string (float (idv (mk 2.0f)).Y)) "2"

// arithmetic ON the fields, so the value is really an f32 and not a word
let dot (a : V2f) (b : V2f) : float32 = a.X * b.X + a.Y * b.Y
eq "float32-dot" (string (float (dot { X = 1.0f; Y = 2.0f } { X = 3.0f; Y = 4.0f }))) "11"

// a float32 struct in a collection, which crosses the uniform boundary
let vs = [ { X = 1.0f; Y = 1.0f }; { X = 2.0f; Y = 2.0f } ]
eq "float32-structs-in-a-list" (string (float (sx (List.item 1 vs)))) "2"

// the SAME shape at float, which always worked
[<Struct>]
type V2d = { A : float; B : float }
let sa (v : V2d) : float = v.A
eq "float-field-out" (string (sa { A = 1.5; B = 2.5 })) "1.5"

// ---- a field that is itself a STRUCT --------------------------------------

[<Struct>]
type V = { X : float; Y : float }

[<Struct>]
type B =
    { Min : V; Max : V }
    member b.Corner (i : int) : V = if i = 0 then b.Min else b.Max
    member b.Width = b.Max.X - b.Min.X

let box1 = { Min = { X = 1.0; Y = 2.0 }; Max = { X = 3.0; Y = 4.0 } }

eq "nested-field-read" (string box1.Min.X) "1"
eq "the-far-corner" (string box1.Max.Y) "4"
eq "computed-over-nested-fields" (string box1.Width) "2"

eq "member-over-a-nested-struct" (string (box1.Corner 0).Y) "2"
eq "the-other-branch" (string (box1.Corner 1).X) "3"

// a plain function taking the nested struct by value
let width (b : B) : float = b.Max.X - b.Min.X
eq "nested-struct-parameter" (string (width box1)) "2"

let shift (b : B) (d : float) : B =
    ({ Min = { X = b.Min.X + d; Y = b.Min.Y }; Max = { X = b.Max.X + d; Y = b.Max.Y } } : B)
eq "nested-struct-in-and-out" (string (shift box1 10.0).Min.X) "11"
eq "and-the-far-side-moved-too" (string (shift box1 10.0).Max.X) "13"

// THE CRASH: a lambda capturing a by-value struct whose fields are structs.
// Capturing it inside a MEMBER is what fpp.base wrote and what crashed the
// compiler, but F# rejects that outright — a struct receiver is a byref, and
// byrefs cannot be captured (FS0406). A struct PARAMETER is an ordinary value
// in both languages, and reaches the same rebuild.
let corners (b : B) : float[] = Array.init 2 (fun i -> (b.Corner i).X)
eq "lambda-over-a-nested-struct-parameter" (String.concat "," (List.map string (List.ofArray (corners box1)))) "1,3"

// ---- a GENERIC CLASS instantiated at a struct ------------------------------
// The constructor and the members must be stamped at the SAME instantiation,
// or the object's storage and its accessors disagree about the layout. A
// prelude class did not record the demand — `explicitCtorTypes` only ever
// held classes declared in the file being inferred — so `ResizeArray<V>`
// built its backing as a REF array while the stamped Add/Item/ToArray read
// it packed. The first read came back as a pointer made of a double's bits
// and faulted; a class element or a float worked, which is what made it look
// like a ResizeArray bug rather than a stamping one.

let ra = ResizeArray<V> ()
let ra0 = ra.Add { X = 1.0; Y = 2.0 }
let ra1 = ra.Add { X = 3.0; Y = 4.0 }

eq "resizearray-of-struct-count" (string ra.Count) "2"
eq "resizearray-of-struct-index" (string ra.[1].Y) "4"
eq "resizearray-of-struct-first" (string ra.[0].X) "1"
eq "resizearray-of-struct-toarray" (string (ra.ToArray ()).[1].X) "3"

let ra2 = ra.RemoveAt 1
eq "resizearray-of-struct-after-remove" (string ra.Count) "1"
eq "and-what-is-left" (string ra.[0].Y) "2"

// the nested struct too, since its layout is the deeper one
let rb = ResizeArray<B> ()
let rb0 = rb.Add box1
eq "resizearray-of-nested-struct" (string rb.[0].Max.X) "3"

// ---- a struct RESULT, across real collections ------------------------------
// The destination a by-value struct result is written through lives on a raw
// region the collector never scans — and that region used to be a
// compile-time address in the mutator's own space, which once the reactor is
// merged in lands INSIDE the runtime's root table. So every struct return
// wrote its fields over shadow-stack root slots, and the next collection
// traced a double's bit pattern as a pointer and faulted deep inside the
// collector, naming nothing. Struct-in/scalar-out was unaffected, which is
// what made it look like a rooting bug in the caller.
//
// It takes a COLLECTION to show, so this loop has to allocate through
// several: the shape is one struct-returning call per iteration.

[<Struct>]
type P3 = { A : float; B : float; C : float }

let negOf (p : P3) : P3 = ({ A = -p.A; B = -p.B; C = -p.C } : P3)
let sum3 (p : P3) : float = p.A + p.B + p.C

let mutable gcacc = 0.0
let mutable gi = 0
let gcloop =
    while gi < 400000 do
        gcacc <- gcacc + sum3 (negOf ({ A = float gi; B = -1.0; C = 2.0 } : P3))
        gi <- gi + 1

eq "struct-result-across-collections" (string gcacc) (string (-80000200000.0))

// the same with a NESTED struct result, whose destination is larger than one
// slot and so overran further
let shiftB (b : B) (d : float) : B =
    ({ Min = { X = b.Min.X + d; Y = b.Min.Y }; Max = { X = b.Max.X + d; Y = b.Max.Y } } : B)

let mutable nacc = 0.0
let mutable ni = 0
let nloop =
    while ni < 200000 do
        nacc <- nacc + (shiftB box1 (float ni)).Max.X
        ni <- ni + 1

eq "nested-struct-result-across-collections" (string nacc) (string 20000500000.0)

// ---- a struct crosses a call without an object ----------------------------
// Three shapes that each built a heap object and read it straight back. They
// are pinned for their ANSWERS here; the reason they matter is that a struct
// is not supposed to touch the heap at all.
//
// The third one was silently WRONG for a while, and is the reason a scratch
// destination is recorded by the call rather than recovered by scanning: a
// struct argument that is itself a struct-returning call reserves a
// destination of its own, ahead of the call's, so "the first reservation in
// these statements" named the ARGUMENT's result. `(mk3 1 2 3).Scaled` then
// answered (1,2,3) — the input, unscaled.

[<Struct>]
type Q =
    { A : float; B : float }
    member q.Scaled : Q = ({ A = q.A * 10.0; B = q.B * 10.0 } : Q)
    member q.Plus (o : Q) : Q = ({ A = q.A + o.A; B = q.B + o.B } : Q)

let mkq (a : float) (b : float) : Q = ({ A = a; B = b } : Q)

// a module-level struct GLOBAL, whose fields live in per-field globals
let qglobal = (mkq 1.0 2.0).Scaled
eq "struct-global-from-a-struct-returning-call" (string qglobal.A) "10"
eq "and-its-other-field" (string qglobal.B) "20"

// passing that global BY VALUE
let qsum (x : Q) (y : Q) : float = x.A + x.B + y.A + y.B
eq "struct-global-passed-by-value" (string (qsum qglobal (mkq 3.0 4.0))) "37"

// a struct-returning call as an ARGUMENT to another one — the shape that
// answered with the argument's own input
eq "call-result-as-a-struct-argument" (string ((mkq 1.0 2.0).Plus (mkq 3.0 4.0).Scaled).A) "31"
eq "and-the-other-field" (string ((mkq 1.0 2.0).Plus (mkq 3.0 4.0).Scaled).B) "42"

// nested, so the scratch destinations nest too
eq "nested-struct-returning-arguments" (string (((mkq 1.0 1.0).Plus (mkq 2.0 2.0).Scaled).Plus (mkq 5.0 5.0).Scaled).A) "71"

// an argument literal whose FIELDS are computed: Core lifts those into lets,
// so the literal arrived wrapped and every such argument built an object
let qi (i : int) : float = (qsum (mkq (float (i * 2)) (float (i + 1))) qglobal)
eq "computed-literal-as-an-argument" (string (qi 3)) "40"

// ---- a module-level mutable STRUCT, and a NESTED field of a struct global --
// Two shapes from the fpp.base port that never reached run time at all.
//
// A module-level `let mutable` struct keeps its fields in per-field globals,
// and there is no global under the binding's own name — so assigning to one
// emitted `global.set` for a name that was never declared and the COMPILER
// died with a NullReferenceException (#25).
//
// Reading a NESTED struct field of a struct global (`s.Center`, whose leaves
// are `Center.X` and `Center.Y`) matched the leaf-read arm, found no leaf
// called `Center`, and left an `i32.const 0` where a struct was expected.
// That module could not be PARSED — "popping from empty stack" — and the
// same read inside a function trapped instead (#27).

[<Struct>]
type Pt = { PX : float; PY : float }
[<Struct>]
type Circle = { Center : Pt; Radius : float }

let mutable macc = ({ PX = 0.0; PY = 0.0 } : Pt)
let addPt (a : Pt) (b : Pt) : Pt = ({ PX = a.PX + b.PX; PY = a.PY + b.PY } : Pt)
let accLoop =
    let mutable i = 0
    while i < 10 do
        macc <- addPt macc ({ PX = 1.0; PY = 2.0 } : Pt)
        i <- i + 1

eq "module-level-mutable-struct" (string (macc.PX + macc.PY)) "30"

let circ = { Center = { PX = 5.0; PY = 6.0 }; Radius = 1.0 }
let ctr = circ.Center
let showPt (p : Pt) : string = string p.PX + "," + string p.PY

eq "nested-field-of-a-struct-global" (showPt ctr) "5,6"
eq "and-inside-a-function" (showPt circ.Center) "5,6"
eq "the-scalar-leaf-still-reads" (string circ.Radius) "1"

printfn "DONE tests=%d failures=%d" ntests failures

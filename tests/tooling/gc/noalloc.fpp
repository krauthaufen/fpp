// The struct shapes that must never touch the heap. Every loop here runs
// millions of iterations: if any of them allocates even one small object per
// iteration, a 16 MB heap collects and the gate sees it.
//
// A struct is a struct — the only boxing anyone accepts is a struct passed as
// `obj`. These four shapes each used to build an object and read it straight
// back, which cost a collection every few hundred thousand iterations and
// showed up in every profile of the fpp.base benchmarks.
module NoAlloc

[<Struct>]
type V2 =
    { X : float; Y : float }
    member a.Plus (b : V2) : V2 = ({ X = a.X + b.X; Y = a.Y + b.Y } : V2)
    member v.Scaled : V2 = ({ X = v.X * 2.0; Y = v.Y * 0.5 } : V2)

[<Struct>]
type B2 =
    { Min : V2; Max : V2 }
    member b.ExtendedBy (p : V2) : B2 =
        ({ Min = ({ X = (if p.X < b.Min.X then p.X else b.Min.X)
                    Y = (if p.Y < b.Min.Y then p.Y else b.Min.Y) } : V2)
           Max = ({ X = (if p.X > b.Max.X then p.X else b.Max.X)
                    Y = (if p.Y > b.Max.Y then p.Y else b.Max.Y) } : V2) } : B2)

let mk (x : float) (y : float) : V2 = ({ X = x; Y = y } : V2)

// a module-level struct GLOBAL, initialised by a struct-returning call
let dir = (mk 3.0 4.0).Scaled

let dot (a : V2) (b : V2) : float = a.X * b.X + a.Y * b.Y

// (5) the CLASS spelling of a struct. `[<Struct>] type P(x, y)` is the other
// way F# writes a value type, and its storage is the constructor's
// parameters — but the inline layout was computed for records only ("not a
// class"), so every construction allocated: 64 bytes an iteration where the
// record spelling allocates none (KNOWN-ISSUES #11). It joins on stricter
// terms than a record — no type parameters, no base, no interfaces, every
// field a scalar — because a ref-carrying or dispatched one reaches the
// runtime as an interned shape and an interface call then finds no vtable row.
[<Struct>]
type SP(px : float, py : float) =
    member _.PX = px
    member _.PY = py
    static member Add (a : SP, b : SP) = SP (a.PX + b.PX, a.PY + b.PY)

let spLoop () : float =
    let mutable acc = 0.0
    let mutable k = 0
    while k < 1000000 do
        let s = SP.Add (SP (float k, 1.0), SP (2.0, 3.0))
        acc <- acc + s.PX + s.PY
        k <- k + 1
    acc

// (5) byref-as-stack-offset: `&local` to a non-escaping callee is an $ssp
// slot and a TAGGED offset — no cell, no view, no GC object anywhere
let brBump (r : byref<int>) : unit = r <- r + 1
let brAdd (r : byref<int>) (k : int) : unit = r <- r + k

// (6) byref of a BLITTABLE STRUCT: field reads are typed loads, the write
// scatters leaf by leaf — and the INLINED form beta-reduces to direct
// register mutation with the view dropped entirely
[<Struct>]
type BV = { BX : float; BY : float }

let brExtend (b : byref<BV>) (p : BV) : unit =
    b <- { BX = b.BX + p.BX; BY = b.BY + p.BY }

let brStructLoop () : float =
    let mutable acc = { BX = 0.0; BY = 0.0 }
    let step = { BX = 1.0; BY = 2.0 }
    let mutable k = 0
    while k < 1000000 do
        brExtend &acc step
        k <- k + 1
    acc.BX + acc.BY

let brLoop () : int =
    let mutable acc = 0
    let mutable k = 0
    while k < 1000000 do
        brBump &acc
        brAdd &acc 2
        k <- k + 1
    acc

let go =
    let base0 = GC.AllocatedBytes ()
    let mutable acc = 0.0
    let mutable i = 0
    // (1) a struct RESULT, (2) a computed literal as an ARGUMENT, and
    // (3) a struct GLOBAL passed by value
    while i < 2000000 do
        acc <- acc + dot ((mk (float (i % 97)) 1.0).Plus (mk 1.0 2.0)) dir
        i <- i + 1
    // (4) a NESTED struct result, whose destination is larger than one slot
    let mutable b = ({ Min = { X = 1e30; Y = 1e30 }; Max = { X = -1e30; Y = -1e30 } } : B2)
    let mutable j = 0
    while j < 2000000 do
        b <- b.ExtendedBy (mk (float (j % 1000)) (float (j % 7)))
        j <- j + 1
    let sp = spLoop ()
    let br = brLoop ()
    let brs = brStructLoop ()
    let used = GC.AllocatedBytes () - base0
    printfn "%g %g %g %g %d %g" acc b.Max.X b.Max.Y sp br brs
    printfn "allocated %d" used

module Shapes
[<Struct>]
type V3f = { X : float32; Y : float32; Z : float32 }
[<Struct>]
type V2d = { PX : float; PY : float }
[<Struct>]
type C4b = { R : byte; G : byte; B : byte; A : byte }
[<Struct>]
type Mix = { M : float; T : byte }
[<Struct>]
type Box = { Lo : V2d; Hi : V2d }
let n = 1000000
let reps = 20
let a : V3f[] = Array.zeroCreate n
let b : V2d[] = Array.zeroCreate n
let c : C4b[] = Array.zeroCreate n
let d : Mix[] = Array.zeroCreate n
let e : Box[] = Array.zeroCreate n
let fill =
    let mutable i = 0
    while i < n do
        a.[i] <- { X = 1.0f; Y = 2.0f; Z = 3.0f }
        b.[i] <- { PX = 1.0; PY = 2.0 }
        c.[i] <- { R = 1uy; G = 2uy; B = 3uy; A = 4uy }
        d.[i] <- { M = 1.0; T = 1uy }
        e.[i] <- { Lo = { PX = 1.0; PY = 1.0 }; Hi = { PX = 2.0; PY = 2.0 } }
        i <- i + 1
let go =
    let mutable s = 0.0
    let mutable r = 0
    while r < reps do
        let mutable i = 0
        while i < n do
            s <- s + float a.[i].X + float a.[i].Y + float a.[i].Z
            s <- s + b.[i].PX + b.[i].PY
            s <- s + float (int c.[i].R) + float (int c.[i].G) + float (int c.[i].B) + float (int c.[i].A)
            s <- s + d.[i].M + float (int d.[i].T)
            s <- s + e.[i].Lo.PX + e.[i].Hi.PY
            i <- i + 1
        r <- r + 1
    print s

module VertBench
[<Struct>]
type V3f = { X : float32; Y : float32; Z : float32 }
let n = 1000000
let reps = 20
let v : V3f[] = Array.zeroCreate n
let fill =
    let mutable i = 0
    while i < n do
        v.[i] <- { X = 1.0f; Y = 2.0f; Z = 3.0f }
        i <- i + 1
let go =
    let mutable acc = 0.0
    let mutable r = 0
    while r < reps do
        let mutable i = 0
        while i < n do
            acc <- acc + float v.[i].X + float v.[i].Y + float v.[i].Z
            i <- i + 1
        r <- r + 1
    print acc

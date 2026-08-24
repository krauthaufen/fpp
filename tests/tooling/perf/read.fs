// The vanilla-F# twin of read.fpp.
module Rd
[<Struct>]
type V3f = { X : float32; Y : float32; Z : float32 }
let v : V3f[] = Array.zeroCreate 1000000
let fill =
    let mutable i = 0
    while i < 1000000 do
        v.[i] <- { X = 1.0f; Y = 2.0f; Z = 3.0f }
        i <- i + 1
[<EntryPoint>]
let main _ =
    let mutable acc = 0.0
    let mutable r = 0
    while r < 20 do
        let mutable i = 0
        while i < 1000000 do
            acc <- acc + float v.[i].X
            i <- i + 1
        r <- r + 1
    printfn "%.0f" (float (acc))
    0

open System.Diagnostics
[<Struct>]
type V3f = { X : float32; Y : float32; Z : float32 }

let run (v : V3f[]) (n : int) (reps : int) =
    let mutable i = 0
    while i < n do
        v.[i] <- { X = 1.0f; Y = 2.0f; Z = 3.0f }
        i <- i + 1
    let mutable acc = 0.0
    let mutable r = 0
    while r < reps do
        let mutable j = 0
        while j < n do
            acc <- acc + float v.[j].X + float v.[j].Y + float v.[j].Z
            j <- j + 1
        r <- r + 1
    acc

[<EntryPoint>]
let main _ =
    let n = 1000000
    let reps = 20
    let v : V3f[] = Array.zeroCreate n
    let mutable best = System.Int64.MaxValue
    let mutable last = 0.0
    for round in 1 .. 10 do
        let sw = Stopwatch.StartNew()
        last <- run v n reps
        sw.Stop()
        printf "%d " sw.ElapsedMilliseconds
        if sw.ElapsedMilliseconds < best then best <- sw.ElapsedMilliseconds
    printfn "\nbest %d ms  (result %.0f)" best last
    0

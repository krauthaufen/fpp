// The vanilla-F# twin of add.fpp.
module One
[<EntryPoint>]
let main _ =
    let mutable acc = 0.0
    let mutable r = 0
    while r < 20 do
        let mutable i = 0
        while i < 1000000 do
            acc <- acc + 1.0
            i <- i + 1
        r <- r + 1
    printfn "%.0f" (float (acc))
    0

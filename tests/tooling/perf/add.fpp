module One
let go =
    let mutable acc = 0.0
    let mutable r = 0
    while r < 20 do
        let mutable i = 0
        while i < 1000000 do
            acc <- acc + 1.0
            i <- i + 1
        r <- r + 1
    print acc

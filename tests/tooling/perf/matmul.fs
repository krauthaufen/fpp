module Matmul

let n = 320

let a : float[] = Array.zeroCreate (n * n)
let b : float[] = Array.zeroCreate (n * n)
let c : float[] = Array.zeroCreate (n * n)

[<EntryPoint>]
let main _ =
    let mutable i = 0
    while i < n do
        let mutable j = 0
        while j < n do
            a.[i * n + j] <- float ((i + j) % 7)
            b.[i * n + j] <- float ((i * 2 + j) % 5)
            j <- j + 1
        i <- i + 1
    let mutable rep = 0
    while rep < 3 do
        let mutable i = 0
        while i < n do
            let mutable k = 0
            while k < n do
                let aik = a.[i * n + k]
                let mutable j = 0
                while j < n do
                    c.[i * n + j] <- c.[i * n + j] + aik * b.[k * n + j]
                    j <- j + 1
                k <- k + 1
            i <- i + 1
        rep <- rep + 1
    let mutable s = 0.0
    let mutable t = 0
    while t < n * n do
        s <- s + c.[t]
        t <- t + 1
    printfn "%.0f" s
    0

// Flat struct arrays — blittable AND ref-holding elements stay flat in
// the array payload. Reference: dotnet fsi (the oracle boxes elements).

[<Struct>]
type PV = { mutable X : int; mutable Y : int }

[<Struct>]
type SR = { mutable K : int; mutable S : string }

// blittable: create, set, read back, element copy isolation
let a1 : PV[] = Array.zeroCreate 4
a1.[1] <- { X = 7; Y = 9 }
let mutable v1 = a1.[1]
v1.X <- 100
printfn "%d" a1.[1].X
printfn "%d" v1.X
printfn "%d" a1.[0].X

// ref-holding: same semantics, elements carry a string
let a2 : SR[] = Array.zeroCreate 3
a2.[2] <- { K = 5; S = "hi" }
let mutable w = a2.[2]
w.K <- 99
w.S <- "changed"
printfn "%d" a2.[2].K
printfn "%s" a2.[2].S
printfn "%d" w.K
printfn "%s" w.S
printfn "%d" a2.[0].K

// GC churn: a large ref-holding array must keep its strings alive and
// updated while everything around it moves
let n = 500
let big : SR[] = Array.zeroCreate n
let mutable i = 0
while i < n do
    big.[i] <- { K = i; S = "s" + string i }
    i <- i + 1
let mutable junk : string = ""
let mutable j = 0
while j < 200000 do
    junk <- "x" + string (j % 10)
    j <- j + 1
let mutable ok = true
let mutable ksum = 0
i <- 0
while i < n do
    let e = big.[i]
    ksum <- ksum + e.K
    if e.S <> "s" + string e.K then ok <- false
    i <- i + 1
printfn "%d" ksum
printfn "%b" ok
printfn "%s" big.[123].S
printfn "%s" junk

[<Struct>]
type PV = { mutable X : int; mutable Y : int }

[<Struct>]
type KV<'k, 'v> = { mutable K : 'k; mutable V : 'v }

// arr.[i].F <- v : element fields mutate IN PLACE
let a1 : PV[] = Array.zeroCreate 3
a1.[1] <- { X = 1; Y = 2 }
a1.[1].X <- 42
printfn "%d %d" a1.[1].X a1.[1].Y

// same through a stamped generic struct, prim and REF fields
let a2 : KV<int, string>[] = Array.zeroCreate 3
a2.[0] <- { K = 5; V = "five" }
a2.[0].K <- 55
a2.[0].V <- "fiftyfive"
printfn "%d %s" a2.[0].K a2.[0].V
printfn "%d" a2.[1].K

// stamp array under GC churn: flat elements keep their refs alive
let n = 300
let big : KV<int, string>[] = Array.zeroCreate n
let mutable i = 0
while i < n do
    big.[i] <- { K = i; V = "v" + string i }
    i <- i + 1
let mutable junk = ""
let mutable j = 0
while j < 150000 do
    junk <- "x" + string (j % 7)
    j <- j + 1
let mutable ok = true
i <- 0
while i < n do
    if big.[i].V <> "v" + string big.[i].K then ok <- false
    i <- i + 1
printfn "%b" ok
printfn "%s %s" big.[42].V junk

// element copies stay copies
let mutable c = big.[10]
c.V <- "changed"
printfn "%s %s" big.[10].V c.V
[<Struct>]
type QV = { mutable X : int; mutable Y : int }
type Holder = { mutable P : QV; Tag : int }

let h = { P = { X = 1; Y = 2 }; Tag = 9 }
h.P.X <- 42
printfn "%d %d" h.P.X h.P.Y
let h2 = { h with Tag = 10 }
h2.P.X <- 77
printfn "%d %d" h.P.X h2.P.X
let mutable copy = h.P
copy.Y <- 99
printfn "%d %d" h.P.Y copy.Y

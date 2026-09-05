let churn () =
    for i in 0 .. 400 do
        let junk = Array.zeroCreate<int> 2000
        junk.[0] <- i
        junk.[1999] <- i

let a = Array.zeroCreate<int> 8
a.[0] <- 42
a.[7] <- 99
let addr1 = Array.pin a
churn ()
GC.Collect ()
let addr2 = Array.pin a
printfn "pinned stable: %b" (addr1 = addr2)
printfn "data intact while pinned: %b" (a.[0] = 42 && a.[7] = 99)
Array.unpin a
churn ()
GC.Collect ()
churn ()
GC.Collect ()
let addr3 = Array.pin a
printfn "moved after unpin: %b" (addr3 <> addr2)
printfn "data intact after move: %b" (a.[0] = 42 && a.[7] = 99)

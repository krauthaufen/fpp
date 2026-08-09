// The parallel combinators, CHUNKING-INDEPENDENT by construction: the
// wasm-GC leg runs the same phases sequentially (P = 1), the fpprt leg
// runs them across the pool — identical output is the gate.
module ParallelDemo
let n = 100000
let xs = Parallel.init n (fun i -> i % 97)
let doubled = Parallel.map (fun x -> x * 2) xs
let total = Parallel.fold (fun s x -> s + x) 0 (fun a b -> a + b) doubled
let sums = Parallel.scan (fun a b -> a + b) xs
let odds = Parallel.choose (fun x -> if x % 2 = 1 then Some (x * 3) else None) xs
let r1 = printfn "%d" total
let r2 = printfn "%d" sums.[n - 1]
let r3 = printfn "%d" (Array.length odds)
let r4 = printfn "%d" odds.[0]
let r5 = printfn "%d" (Parallel.fold (fun s x -> s + x) 0 (fun a b -> a + b) odds)

// phased: the ×2-then-add-left-neighbour stencil, one group = a global
// barrier; every cross-index read needs phase 0 complete first
let st = Parallel.init n (fun i -> i % 17)
let stOut : int[] = Array.zeroCreate n
let r6 =
    Parallel.dispatchPhased n 1 2 (fun phase i ->
        if phase = 0 then st.[i] <- st.[i] * 2
        else stOut.[i] <- st.[i] + (if i > 0 then st.[i - 1] else 0))
let r7 = printfn "%d" (Parallel.fold (fun s x -> s + x) 0 (fun a b -> a + b) stOut)
// sixteen groups, three phases of group-local accumulation, pipelining
let acc : int[] = Array.zeroCreate n
let r8 = Parallel.dispatchPhased n 16 3 (fun phase i -> acc.[i] <- acc.[i] + phase + 1)
let r9 = printfn "%d" (Parallel.fold (fun s x -> s + x) 0 (fun a b -> a + b) acc)

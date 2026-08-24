// In-place quicksort over an int array: branchy, swap-heavy, and allocating
// nothing at all. It isolates plain scalar codegen and array writes from the
// allocator, which avl and trees deliberately lean on.
module Sort

let n = 2000000
let reps = 6

let a : int[] = Array.zeroCreate n

let rec qsort (lo : int) (hi : int) : unit =
    if lo < hi then
        let mid = lo + (hi - lo) / 2
        let p = a.[mid]
        let mutable i = lo
        let mutable j = hi
        while i <= j do
            while a.[i] < p do
                i <- i + 1
            while a.[j] > p do
                j <- j - 1
            if i <= j then
                let t = a.[i]
                a.[i] <- a.[j]
                a.[j] <- t
                i <- i + 1
                j <- j - 1
        if lo < j then qsort lo j
        if i < hi then qsort i hi

let go =
    let mutable acc = 0L
    let mutable rep = 0
    while rep < reps do
        let mutable s = 2463534242u
        let mutable i = 0
        while i < n do
            s <- s ^^^ (s <<< 13)
            s <- s ^^^ (s >>> 17)
            s <- s ^^^ (s <<< 5)
            a.[i] <- int (s % 10000000u)
            i <- i + 1
        qsort 0 (n - 1)
        acc <- acc + int64 a.[0] + int64 a.[n / 2] + int64 a.[n - 1]
        rep <- rep + 1
    print (float acc)

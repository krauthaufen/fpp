// The vanilla-F# twin of trees.fpp.
// The binary-trees allocation stress: build a deep tree, walk it, drop it,
// repeat. Almost every allocation dies young, which is the case a generational
// collector is built for and the case a bump-and-free C arena wins outright.
//
// Where avl measures a live structure being rebuilt, this measures the
// allocator and the collector on short-lived garbage.
module Trees

type Tree =
    | Leaf
    | Node of Tree * Tree

let rec make (d : int) : Tree =
    if d = 0 then Leaf
    else Node (make (d - 1), make (d - 1))

let rec check (t : Tree) : int =
    match t with
    | Leaf -> 1
    | Node (l, r) -> 1 + check l + check r

let maxDepth = 18
let minDepth = 4

[<EntryPoint>]
let main _ =
    let mutable acc = 0L
    // one long-lived tree, so the collector always has live data to trace
    let longLived = make maxDepth
    let mutable d = minDepth
    while d <= maxDepth do
        let iters = 1 <<< (maxDepth - d + minDepth)
        let mutable i = 0
        let mutable sum = 0
        while i < iters do
            sum <- sum + check (make d)
            i <- i + 1
        acc <- acc + int64 sum
        d <- d + 2
    acc <- acc + int64 (check longLived)
    printfn "%.0f" (float acc)
    0

// A PERSISTENT AVL tree: insert, look up, traverse.
//
// The array benchmarks measure loops over flat memory. This one measures what
// they cannot: allocation rate, pointer chasing through a tree that does not
// fit in cache, recursion, and pattern matching on a union. Every insert
// rebuilds the path it walks, so the tree allocates O(log n) nodes per key —
// which is the shape idiomatic functional code actually has.
//
// The C and F# twins are line-for-line the same algorithm, including the
// xorshift that generates the keys: comparing a benchmark against a twin that
// computes something else measures nothing (see shapes' addend grouping).
module Avl

type Tree =
    | Nil
    | Node of Tree * int * int * Tree * int

let height (t : Tree) : int =
    match t with
    | Nil -> 0
    | Node (_, _, _, _, h) -> h

let mk (l : Tree) (k : int) (v : int) (r : Tree) : Tree =
    let hl = height l
    let hr = height r
    Node (l, k, v, r, 1 + (if hl > hr then hl else hr))

let bal (l : Tree) (k : int) (v : int) (r : Tree) : Tree =
    let hl = height l
    let hr = height r
    if hl > hr + 1 then
        match l with
        | Node (ll, lk, lv, lr, _) ->
            if height ll >= height lr then mk ll lk lv (mk lr k v r)
            else
                match lr with
                | Node (lrl, lrk, lrv, lrr, _) -> mk (mk ll lk lv lrl) lrk lrv (mk lrr k v r)
                | Nil -> mk l k v r
        | Nil -> mk l k v r
    elif hr > hl + 1 then
        match r with
        | Node (rl, rk, rv, rr, _) ->
            if height rr >= height rl then mk (mk l k v rl) rk rv rr
            else
                match rl with
                | Node (rll, rlk, rlv, rlr, _) -> mk (mk l k v rll) rlk rlv (mk rlr rk rv rr)
                | Nil -> mk l k v r
        | Nil -> mk l k v r
    else mk l k v r

let rec insert (k : int) (v : int) (t : Tree) : Tree =
    match t with
    | Nil -> Node (Nil, k, v, Nil, 1)
    | Node (l, k2, v2, r, _) ->
        if k < k2 then bal (insert k v l) k2 v2 r
        elif k > k2 then bal l k2 v2 (insert k v r)
        else mk l k v r

let rec find (k : int) (t : Tree) : int =
    match t with
    | Nil -> 0
    | Node (l, k2, v2, r, _) ->
        if k < k2 then find k l
        elif k > k2 then find k r
        else v2

let rec total (t : Tree) : int =
    match t with
    | Nil -> 0
    | Node (l, k, _, r, _) -> total l + k + total r

let n = 200000
let reps = 6

let go =
    let mutable acc = 0L
    let mutable rep = 0
    while rep < reps do
        // build
        let mutable s = 2463534242u
        let mutable t = Nil
        let mutable i = 0
        while i < n do
            s <- s ^^^ (s <<< 13)
            s <- s ^^^ (s >>> 17)
            s <- s ^^^ (s <<< 5)
            let k = int (s % 1000000u)
            t <- insert k (k + 1) t
            i <- i + 1
        // look every key back up
        let mutable s2 = 2463534242u
        let mutable j = 0
        while j < n do
            s2 <- s2 ^^^ (s2 <<< 13)
            s2 <- s2 ^^^ (s2 >>> 17)
            s2 <- s2 ^^^ (s2 <<< 5)
            let k = int (s2 % 1000000u)
            acc <- acc + int64 (find k t)
            j <- j + 1
        acc <- acc + int64 (total t) + int64 (height t)
        rep <- rep + 1
    print (float acc)

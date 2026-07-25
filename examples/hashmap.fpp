module HashMapPatricia

// Port of the patricia-trie core of FSharp.Data.Adaptive's HashMap
// (big-endian Okasaki-Gill over hashes, collision chains, cached counts).
// Deviations from the original: DU nodes instead of class hierarchy;
// int hashes masked to 30 bits (F++ >>> is arithmetic, as F#'s on int);
// hash/equality via structural `hash` and `=` instead of IEqualityComparer.

let maskHash (h : int) = h &&& 1073741823

let highestBitMask (x0 : int) =
    let mutable x = x0
    x <- x ||| (x >>> 1)
    x <- x ||| (x >>> 2)
    x <- x ||| (x >>> 4)
    x <- x ||| (x >>> 8)
    x <- x ||| (x >>> 16)
    x ^^^ (x >>> 1)

let getPrefix (k : int) (m : int) = k &&& ~~~((m <<< 1) - 1)
let zeroBit (k : int) (m : int) = if (k &&& m) <> 0 then 1 else 0
let matchPrefixAndGetBit (h : int) (prefix : int) (m : int) =
    if getPrefix h m = prefix then zeroBit h m else 2
let getMask (p0 : int) (p1 : int) = highestBitMask (p0 ^^^ p1)

type Linked<'k, 'v> =
    | LNil
    | LCons of 'k * 'v * Linked<'k, 'v>

type Node<'k, 'v> =
    | Empty
    | Leaf of int * 'k * 'v * Linked<'k, 'v>
    | Inner of int * int * Node<'k, 'v> * Node<'k, 'v> * int

let rec linkedCount (n : Linked<'k, 'v>) =
    match n with
    | LNil -> 0
    | LCons (k, v, t) -> 1 + linkedCount t

let rec linkedAdd (key : 'k) (value : 'v) (n : Linked<'k, 'v>) =
    match n with
    | LNil -> LCons (key, value, LNil)
    | LCons (k, v, t) ->
        if k = key then LCons (key, value, t)
        else LCons (k, v, linkedAdd key value t)

let rec linkedTryFind (key : 'k) (n : Linked<'k, 'v>) =
    match n with
    | LNil -> None
    | LCons (k, v, t) ->
        if k = key then Some v
        else linkedTryFind key t

let rec linkedRemove (key : 'k) (n : Linked<'k, 'v>) =
    match n with
    | LNil -> LNil
    | LCons (k, v, t) ->
        if k = key then t
        else LCons (k, v, linkedRemove key t)

let nodeCount (n : Node<'k, 'v>) =
    match n with
    | Empty -> 0
    | Leaf (h, k, v, rest) -> 1 + linkedCount rest
    | Inner (p, m, l, r, c) -> c

let newInner (prefix : int) (mask : int) (l : Node<'k, 'v>) (r : Node<'k, 'v>) =
    match l, r with
    | Empty, x -> x
    | x, Empty -> x
    | _ -> Inner (prefix, mask, l, r, nodeCount l + nodeCount r)

let join (p0 : int) (t0 : Node<'k, 'v>) (p1 : int) (t1 : Node<'k, 'v>) =
    let mask = getMask p0 p1
    let prefix = getPrefix p0 mask
    if zeroBit p0 mask = 0 then Inner (prefix, mask, t0, t1, nodeCount t0 + nodeCount t1)
    else Inner (prefix, mask, t1, t0, nodeCount t0 + nodeCount t1)

let rec addNode (h : int) (key : 'k) (value : 'v) (n : Node<'k, 'v>) =
    match n with
    | Empty -> Leaf (h, key, value, LNil)
    | Leaf (lh, lk, lv, rest) ->
        if lh = h then
            if lk = key then Leaf (lh, key, value, rest)
            else
                match linkedTryFind key rest with
                | Some _ -> Leaf (lh, lk, lv, linkedAdd key value rest)
                | None -> Leaf (lh, lk, lv, linkedAdd key value rest)
        else join h (Leaf (h, key, value, LNil)) lh n
    | Inner (p, m, l, r, c) ->
        let b = matchPrefixAndGetBit h p m
        if b = 0 then newInner p m (addNode h key value l) r
        elif b = 1 then newInner p m l (addNode h key value r)
        else join h (Leaf (h, key, value, LNil)) p n

let rec tryFindNode (h : int) (key : 'k) (n : Node<'k, 'v>) =
    match n with
    | Empty -> None
    | Leaf (lh, lk, lv, rest) ->
        if lh = h then
            if lk = key then Some lv
            else linkedTryFind key rest
        else None
    | Inner (p, m, l, r, c) ->
        let b = matchPrefixAndGetBit h p m
        if b = 0 then tryFindNode h key l
        elif b = 1 then tryFindNode h key r
        else None

let rec removeNode (h : int) (key : 'k) (n : Node<'k, 'v>) =
    match n with
    | Empty -> Empty
    | Leaf (lh, lk, lv, rest) ->
        if lh = h then
            if lk = key then
                match rest with
                | LNil -> Empty
                | LCons (rk, rv, rt) -> Leaf (lh, rk, rv, rt)
            else Leaf (lh, lk, lv, linkedRemove key rest)
        else n
    | Inner (p, m, l, r, c) ->
        let b = matchPrefixAndGetBit h p m
        if b = 0 then newInner p m (removeNode h key l) r
        elif b = 1 then newInner p m l (removeNode h key r)
        else n

let add (key : 'k) (value : 'v) (n : Node<'k, 'v>) = addNode (maskHash (hash key)) key value n
let tryFind (key : 'k) (n : Node<'k, 'v>) = tryFindNode (maskHash (hash key)) key n
let remove (key : 'k) (n : Node<'k, 'v>) = removeNode (maskHash (hash key)) key n

// ---- exercise it ---------------------------------------------------------

let printOpt (o : Option<int>) =
    match o with
    | Some v -> print v
    | None -> print "none"

let lcgNext (s : int) = (s * 1103515245 + 12345) &&& 536870911

let buildN (count : int) =
    let mutable m = Empty
    let mutable s = 42
    let mutable i = 0
    while i < count do
        s <- lcgNext s
        m <- add s i m
        i <- i + 1
    m

let m1 = buildN 1000
let c1 = print (nodeCount m1)

let mutable seek = 42
let step1 = seek <- lcgNext seek
let l1 = printOpt (tryFind seek m1)
let step2 = seek <- lcgNext seek
let step3 = seek <- lcgNext seek
let l2 = printOpt (tryFind seek m1)
let l3 = printOpt (tryFind 123456789 m1)

let m2 = add seek 777 m1
let c2 = print (nodeCount m2)
let l4 = printOpt (tryFind seek m2)

let m3 = remove seek m2
let c3 = print (nodeCount m3)
let l5 = printOpt (tryFind seek m3)

let sm =
    let mutable m = Empty
    m <- add "alpha" 1 m
    m <- add "beta" 2 m
    m <- add "gamma" 3 m
    m <- add "delta" 4 m
    m <- add "alpha" 10 m
    m
let s1 = print (nodeCount sm)
let s2 = printOpt (tryFind "alpha" sm)
let s3 = printOpt (tryFind "gamma" sm)
let s4 = printOpt (tryFind "epsilon" sm)
let s5 = print (nodeCount (remove "beta" sm))

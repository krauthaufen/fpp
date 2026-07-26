module Stdlib

// Port of the patricia-trie core of FSharp.Data.Adaptive's HashMap
// (big-endian Okasaki-Gill over hashes, collision chains, cached counts).
// Deviations from the original: DU nodes instead of class hierarchy;
// int hashes masked to 30 bits (F++ >>> is arithmetic, as F#'s on int);
// hash/equality via structural `hash` and `=` instead of IEqualityComparer.

module Map =
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


    let empty = Empty
    let count (n : Node<'k, 'v>) = nodeCount n
    let containsKey (key : 'k) (n : Node<'k, 'v>) =
        match tryFind key n with
        | Some v -> true
        | None -> false
    let findOr (d : 'v) (key : 'k) (n : Node<'k, 'v>) =
        match tryFind key n with
        | Some v -> v
        | None -> d
    let rec foldLinked (f : 's -> 'k -> 'v -> 's) (s : 's) (l : Linked<'k, 'v>) =
        match l with
        | LNil -> s
        | LCons (k, v, t) -> foldLinked f (f s k v) t
    let rec fold (f : 's -> 'k -> 'v -> 's) (s : 's) (n : Node<'k, 'v>) =
        match n with
        | Empty -> s
        | Leaf (h, k, v, rest) -> foldLinked f (f s k v) rest
        | Inner (p, m, l, r, c) -> fold f (fold f s l) r
    let toList (n : Node<'k, 'v>) = fold (fun acc k v -> (k, v) :: acc) [] n
    let rec ofListInto (acc : Node<'k, 'v>) (xs : ('k * 'v) list) =
        match xs with
        | (k, v) :: t -> ofListInto (add k v acc) t
        | [] -> acc
    let ofList (items : ('k * 'v) list) = ofListInto Empty items

module Set =
    let empty = Map.Empty
    let add (key : 'k) (s : Map.Node<'k, int>) = Map.add key 0 s
    let remove (key : 'k) (s : Map.Node<'k, int>) = Map.remove key s
    let contains (key : 'k) (s : Map.Node<'k, int>) = Map.containsKey key s
    let count (s : Map.Node<'k, int>) = Map.count s
    let toList (s : Map.Node<'k, int>) = Map.fold (fun acc k v -> k :: acc) [] s
    let rec ofListInto (acc : Map.Node<'k, int>) (xs : 'k list) =
        match xs with
        | h :: t -> ofListInto (add h acc) t
        | [] -> acc
    let ofList (items : 'k list) = ofListInto Map.Empty items
    let union (a : Map.Node<'k, int>) (b : Map.Node<'k, int>) =
        Map.fold (fun acc k v -> Map.add k v acc) a b

// ---- exercise ------------------------------------------------------------

let m = Map.ofList [ ("a", 1); ("b", 2); ("c", 3) ]
let r1 = print (Map.count m)
let r2 = print (Map.findOr 0 "b" m)
let r3 = print (Map.findOr 99 "zz" m)
let m2 = Map.add "b" 20 m
let r4 = print (Map.findOr 0 "b" m2)
let r5 = print (Map.count m2)
let m3 = Map.remove "a" m2
let r6 = print (Map.count m3)
let r7 = print (if Map.containsKey "a" m3 then 1 else 0)
let r8 = print (Map.fold (fun acc k v -> acc + v) 0 m2)

let s1 = Set.ofList [ 3; 1; 4; 1; 5; 9; 2; 6 ]
let r9 = print (Set.count s1)
let r10 = print (if Set.contains 4 s1 then 1 else 0)
let r11 = print (if Set.contains 7 s1 then 1 else 0)
let s2 = Set.union s1 (Set.ofList [ 7; 8; 9 ])
let r12 = print (Set.count s2)
let rec sumList (xs : int list) =
    match xs with
    | h :: t -> h + sumList t
    | [] -> 0
let r13 = print (sumList (Set.toList s2))

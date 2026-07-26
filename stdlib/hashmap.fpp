module Stdlib

// Port of the patricia-trie core of FSharp.Data.Adaptive's HashMap
// (big-endian Okasaki-Gill over hashes, collision chains, cached counts).
// Deviations from the original: DU nodes instead of class hierarchy;
// int hashes masked to 30 bits (F++ >>> is arithmetic, as F#'s on int);
// hash/equality via structural `hash` and `=` instead of IEqualityComparer.

module HashMap =
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


    let emptyH = Empty
    let isEmpty (n : Node<'k, 'v>) =
        match n with
        | Empty -> true
        | Leaf (h, k, v, rest) -> false
        | Inner (p, m, l, r, c) -> false
    let keys (n : Node<'k, 'v>) = fold (fun acc k v -> k :: acc) [] n
    let values (n : Node<'k, 'v>) = fold (fun acc k v -> v :: acc) [] n
    let alter (key : 'k) (f : Option<'v> -> Option<'v>) (n : Node<'k, 'v>) =
        match f (tryFind key n) with
        | Some nv -> add key nv n
        | None -> remove key n
    let change (key : 'k) (f : Option<'v> -> Option<'v>) (n : Node<'k, 'v>) = alter key f n
    let update (key : 'k) (f : 'v -> 'v) (dflt : 'v) (n : Node<'k, 'v>) =
        match tryFind key n with
        | Some v -> add key (f v) n
        | None -> add key dflt n
    let map (f : 'k -> 'v -> 'w) (n : Node<'k, 'v>) =
        fold (fun acc k v -> add k (f k v) acc) Empty n
    let mapValues (f : 'v -> 'w) (n : Node<'k, 'v>) = map (fun k v -> f v) n
    let filter (p : 'k -> 'v -> bool) (n : Node<'k, 'v>) =
        fold (fun acc k v -> if p k v then add k v acc else acc) Empty n
    let choose (f : 'k -> 'v -> Option<'w>) (n : Node<'k, 'v>) =
        fold (fun acc k v ->
                match f k v with
                | Some w -> add k w acc
                | None -> acc) Empty n
    let exists (p : 'k -> 'v -> bool) (n : Node<'k, 'v>) =
        fold (fun acc k v -> if acc then true else p k v) false n
    let forall (p : 'k -> 'v -> bool) (n : Node<'k, 'v>) =
        fold (fun acc k v -> if acc then p k v else false) true n
    let unionWith (resolve : 'k -> 'v -> 'v -> 'v) (a : Node<'k, 'v>) (b : Node<'k, 'v>) =
        fold (fun acc k v ->
                match tryFind k acc with
                | Some old -> add k (resolve k old v) acc
                | None -> add k v acc) a b
    let union (a : Node<'k, 'v>) (b : Node<'k, 'v>) = unionWith (fun k x y -> y) a b
    let intersectWith (resolve : 'k -> 'v -> 'v -> 'v) (a : Node<'k, 'v>) (b : Node<'k, 'v>) =
        fold (fun acc k v ->
                match tryFind k b with
                | Some other -> add k (resolve k v other) acc
                | None -> acc) Empty a
    let intersect (a : Node<'k, 'v>) (b : Node<'k, 'v>) = intersectWith (fun k x y -> x) a b
    let difference (a : Node<'k, 'v>) (b : Node<'k, 'v>) =
        fold (fun acc k v -> if containsKey k b then acc else add k v acc) Empty a
    let partition (p : 'k -> 'v -> bool) (n : Node<'k, 'v>) =
        fold (fun acc k v ->
                match acc with
                | (yes, no) -> if p k v then (add k v yes, no) else (yes, add k v no))
             (Empty, Empty) n
    let choose2 (f : 'k -> Option<'v> -> Option<'w> -> Option<'x>) (a : Node<'k, 'v>) (b : Node<'k, 'w>) =
        let withA =
            fold (fun acc k v ->
                    match f k (Some v) (tryFind k b) with
                    | Some x -> add k x acc
                    | None -> acc) Empty a
        fold (fun acc k w ->
                if containsKey k a then acc
                else
                    match f k None (Some w) with
                    | Some x -> add k x acc
                    | None -> acc) withA b
    let map2 (f : 'k -> Option<'v> -> Option<'w> -> 'x) (a : Node<'k, 'v>) (b : Node<'k, 'w>) =
        choose2 (fun k x y -> Some (f k x y)) a b

module HashSet =
    let empty = HashMap.Empty
    let isEmpty (s : HashMap.Node<'k, int>) = HashMap.isEmpty s
    let count (s : HashMap.Node<'k, int>) = HashMap.count s
    let add (key : 'k) (s : HashMap.Node<'k, int>) = HashMap.add key 0 s
    let remove (key : 'k) (s : HashMap.Node<'k, int>) = HashMap.remove key s
    let contains (key : 'k) (s : HashMap.Node<'k, int>) = HashMap.containsKey key s
    let toList (s : HashMap.Node<'k, int>) = HashMap.keys s
    let rec ofListInto (acc : HashMap.Node<'k, int>) (xs : 'k list) =
        match xs with
        | h :: t -> ofListInto (add h acc) t
        | [] -> acc
    let ofList (xs : 'k list) = ofListInto HashMap.Empty xs
    let fold (f : 's -> 'k -> 's) (s0 : 's) (s : HashMap.Node<'k, int>) =
        HashMap.fold (fun acc k v -> f acc k) s0 s
    let union (a : HashMap.Node<'k, int>) (b : HashMap.Node<'k, int>) = HashMap.union a b
    let intersect (a : HashMap.Node<'k, int>) (b : HashMap.Node<'k, int>) = HashMap.intersect a b
    let difference (a : HashMap.Node<'k, int>) (b : HashMap.Node<'k, int>) = HashMap.difference a b
    let filter (p : 'k -> bool) (s : HashMap.Node<'k, int>) = HashMap.filter (fun k v -> p k) s
    let exists (p : 'k -> bool) (s : HashMap.Node<'k, int>) = HashMap.exists (fun k v -> p k) s
    let forall (p : 'k -> bool) (s : HashMap.Node<'k, int>) = HashMap.forall (fun k v -> p k) s

// ---- tests --------------------------------------------------------------

let rec listLen (xs : 'a list) =
    match xs with
    | h :: t -> 1 + listLen t
    | [] -> 0
let rec sumList (xs : int list) =
    match xs with
    | h :: t -> h + sumList t
    | [] -> 0
let show (b : bool) = if b then 1 else 0

let e0 = HashMap.Empty
let t1 = print (HashMap.count e0)
let t2 = print (show (HashMap.isEmpty e0))
let t3 = print (show (HashMap.containsKey 1 e0))
let t4 = print (HashMap.count (HashMap.remove 1 e0))
let m1 = HashMap.add 5 50 e0
let t5 = print (HashMap.count m1)
let t6 = print (HashMap.findOr 0 5 m1)
let t7 = print (show (HashMap.isEmpty (HashMap.remove 5 m1)))
let t8 = print (HashMap.count (HashMap.add 5 999 m1))
let t9 = print (HashMap.findOr 0 5 (HashMap.add 5 999 m1))

let rec build (i : int) (n : int) (acc : HashMap.Node<int, int>) =
    if i > n then acc else build (i + 1) n (HashMap.add i (i * 10) acc)
let big = build 1 200 HashMap.Empty
let t10 = print (HashMap.count big)
let t11 = print (HashMap.findOr 0 137 big)
let t12 = print (listLen (HashMap.keys big))
let t13 = print (HashMap.fold (fun acc k v -> acc + v) 0 big)
let t14 = print (HashMap.count (HashMap.filter (fun k v -> k % 25 = 0) big))
let t15 = print (HashMap.count (HashMap.choose (fun k v -> if k % 50 = 0 then Some v else None) big))
let t16 = print (show (HashMap.exists (fun k v -> k = 200) big))
let t17 = print (show (HashMap.forall (fun k v -> v = k * 10) big))
let t18 = print (sumList (HashMap.values (HashMap.mapValues (fun v -> v / 10) big)))

let rec dropEvens (i : int) (n : int) (acc : HashMap.Node<int, int>) =
    if i > n then acc else dropEvens (i + 2) n (HashMap.remove i acc)
let odds = dropEvens 2 200 big
let t19 = print (HashMap.count odds)
let t20 = print (show (HashMap.containsKey 100 odds))
let t21 = print (show (HashMap.containsKey 101 odds))

let ua = HashMap.ofList [ (1, 1); (2, 2); (3, 3) ]
let ub = HashMap.ofList [ (3, 30); (4, 40) ]
let t22 = print (HashMap.count (HashMap.union ua ub))
let t23 = print (HashMap.findOr 0 3 (HashMap.union ua ub))
let t24 = print (HashMap.findOr 0 3 (HashMap.unionWith (fun k x y -> x + y) ua ub))
let t25 = print (HashMap.count (HashMap.intersect ua ub))
let t26 = print (HashMap.count (HashMap.difference ua ub))
let c2 = HashMap.choose2 (fun k x y ->
            match x, y with
            | Some a, Some b -> Some (a + b)
            | Some a, None -> Some a
            | None, Some b -> Some b
            | None, None -> None) ua ub
let t27 = print (HashMap.count c2)
let t28 = print (HashMap.findOr 0 3 c2)
let t29 = print (HashMap.count (HashMap.ofList (HashMap.toList big)))
let t30 = print (HashMap.findOr 0 7 (HashMap.alter 7 (fun o -> Some 70) HashMap.Empty))
let t31 = print (HashMap.count (HashMap.alter 5 (fun o -> None) m1))
let t32 = print (HashMap.findOr 0 9 (HashMap.update 9 (fun v -> v * 2) 3 HashMap.Empty))

let lcg (s : int) = (s * 1103515245 + 12345) &&& 1073741823
let rec modelAdd (k : int) (v : int) (xs : (int * int) list) =
    match xs with
    | (a, b) :: t -> if a = k then (k, v) :: t else (a, b) :: modelAdd k v t
    | [] -> [ (k, v) ]
let rec modelRemove (k : int) (xs : (int * int) list) =
    match xs with
    | (a, b) :: t -> if a = k then t else (a, b) :: modelRemove k t
    | [] -> []
let rec modelFind (k : int) (xs : (int * int) list) =
    match xs with
    | (a, b) :: t -> if a = k then Some b else modelFind k t
    | [] -> None
let rec randomOps (n : int) (seed : int) (m : HashMap.Node<int, int>) (model : (int * int) list) (bad : int) =
    if n = 0 then (HashMap.count m, listLen model, bad)
    else
        let s1 = lcg seed
        let key = s1 % 50
        let s2 = lcg s1
        let m2 = if s2 % 3 = 0 then HashMap.remove key m else HashMap.add key (key * 7) m
        let model2 = if s2 % 3 = 0 then modelRemove key model else modelAdd key (key * 7) model
        let agree =
            match HashMap.tryFind key m2, modelFind key model2 with
            | Some a, Some b -> a = b
            | None, None -> true
            | _, _ -> false
        randomOps (n - 1) s2 m2 model2 (if agree then bad else bad + 1)
let r = randomOps 500 987 HashMap.Empty [] 0
let t33 = print (match r with
                 | (c, mc, bad) -> c)
let t34 = print (match r with
                 | (c, mc, bad) -> mc)
let t35 = print (match r with
                 | (c, mc, bad) -> bad)

let sm = HashSet.ofList [ "b"; "a"; "c"; "a" ]
let t36 = print (HashSet.count sm)
let t37 = print (show (HashSet.contains "a" sm))
let t38 = print (show (HashSet.contains "z" sm))
let t39 = print (HashSet.count (HashSet.union sm (HashSet.ofList [ "c"; "d" ])))
let t40 = print (HashSet.count (HashSet.intersect sm (HashSet.ofList [ "c"; "d" ])))
let t41 = print (HashSet.count (HashSet.difference sm (HashSet.ofList [ "c"; "d" ])))
let t42 = print (HashSet.count (HashSet.filter (fun k -> k = "a") sm))
let t43 = print (show (HashSet.exists (fun k -> k = "b") sm))
let t44 = print (show (HashSet.forall (fun k -> k <> "z") sm))

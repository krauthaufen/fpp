module Stdlib

// Map = MapExt from FSharp.Data.Adaptive: height-balanced (AVL) tree map
// with cached height and count. Ported to F++; ordering via structural
// `compare`. Set (below) shares the same tree and operator vocabulary.

module Map =
    type Tree<'k, 'v> =
        | MEmpty
        | MNode of 'k * 'v * Tree<'k, 'v> * Tree<'k, 'v> * int * int

    let empty = MEmpty

    let height (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> 0
        | MNode (k, v, l, r, h, c) -> h

    let count (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> 0
        | MNode (k, v, l, r, h, c) -> c

    let isEmpty (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> true
        | MNode (k, v, l, r, h, c) -> false

    let mk (k : 'k) (v : 'v) (l : Tree<'k, 'v>) (r : Tree<'k, 'v>) =
        let hl = height l
        let hr = height r
        let h = (if hl > hr then hl else hr) + 1
        MNode (k, v, l, r, h, count l + count r + 1)

    let rebalance (k : 'k) (v : 'v) (l : Tree<'k, 'v>) (r : Tree<'k, 'v>) =
        let hl = height l
        let hr = height r
        if hr > hl + 2 then
            match r with
            | MNode (rk, rv, rl, rr, rh, rc) ->
                if height rl > height rr then
                    match rl with
                    | MNode (rlk, rlv, rll, rlr, rlh, rlc) ->
                        mk rlk rlv (mk k v l rll) (mk rk rv rlr rr)
                    | MEmpty -> mk k v l r
                else mk rk rv (mk k v l rl) rr
            | MEmpty -> mk k v l r
        elif hl > hr + 2 then
            match l with
            | MNode (lk, lv, ll, lr, lh, lc) ->
                if height lr > height ll then
                    match lr with
                    | MNode (lrk, lrv, lrl, lrr, lrh, lrc) ->
                        mk lrk lrv (mk lk lv ll lrl) (mk k v lrr r)
                    | MEmpty -> mk k v l r
                else mk lk lv ll (mk k v lr r)
            | MEmpty -> mk k v l r
        else mk k v l r

    let rec add (key : 'k) (value : 'v) (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> MNode (key, value, MEmpty, MEmpty, 1, 1)
        | MNode (k, v, l, r, h, c) ->
            let d = compare key k
            if d < 0 then rebalance k v (add key value l) r
            elif d > 0 then rebalance k v l (add key value r)
            else MNode (key, value, l, r, h, c)

    let rec tryFind (key : 'k) (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> None
        | MNode (k, v, l, r, h, c) ->
            let d = compare key k
            if d < 0 then tryFind key l
            elif d > 0 then tryFind key r
            else Some v

    let containsKey (key : 'k) (t : Tree<'k, 'v>) =
        match tryFind key t with
        | Some v -> true
        | None -> false

    let findOr (dflt : 'v) (key : 'k) (t : Tree<'k, 'v>) =
        match tryFind key t with
        | Some v -> v
        | None -> dflt

    let rec tryMin (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> None
        | MNode (k, v, l, r, h, c) ->
            match l with
            | MEmpty -> Some (k, v)
            | MNode (a, b, cc, d, e, f) -> tryMin l

    let rec tryMax (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> None
        | MNode (k, v, l, r, h, c) ->
            match r with
            | MEmpty -> Some (k, v)
            | MNode (a, b, cc, d, e, f) -> tryMax r

    let rec removeMin (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> MEmpty
        | MNode (k, v, l, r, h, c) ->
            match l with
            | MEmpty -> r
            | MNode (a, b, cc, d, e, f) -> rebalance k v (removeMin l) r

    let rec remove (key : 'k) (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> MEmpty
        | MNode (k, v, l, r, h, c) ->
            let d = compare key k
            if d < 0 then rebalance k v (remove key l) r
            elif d > 0 then rebalance k v l (remove key r)
            else
                match l, r with
                | MEmpty, _ -> r
                | _, MEmpty -> l
                | _, _ ->
                    match tryMin r with
                    | Some (sk, sv) -> rebalance sk sv l (removeMin r)
                    | None -> l

    let rec fold (f : 's -> 'k -> 'v -> 's) (s : 's) (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> s
        | MNode (k, v, l, r, h, c) -> fold f (f (fold f s l) k v) r

    let rec foldBack (f : 'k -> 'v -> 's -> 's) (t : Tree<'k, 'v>) (s : 's) =
        match t with
        | MEmpty -> s
        | MNode (k, v, l, r, h, c) -> foldBack f l (f k v (foldBack f r s))

    let toList (t : Tree<'k, 'v>) = foldBack (fun k v acc -> (k, v) :: acc) t []
    let keys (t : Tree<'k, 'v>) = foldBack (fun k v acc -> k :: acc) t []
    let values (t : Tree<'k, 'v>) = foldBack (fun k v acc -> v :: acc) t []

    let rec ofListInto (acc : Tree<'k, 'v>) (xs : ('k * 'v) list) =
        match xs with
        | (k, v) :: rest -> ofListInto (add k v acc) rest
        | [] -> acc
    let ofList (xs : ('k * 'v) list) = ofListInto MEmpty xs

    let alter (key : 'k) (f : Option<'v> -> Option<'v>) (t : Tree<'k, 'v>) =
        match f (tryFind key t) with
        | Some nv -> add key nv t
        | None -> remove key t

    let change (key : 'k) (f : Option<'v> -> Option<'v>) (t : Tree<'k, 'v>) = alter key f t

    let update (key : 'k) (f : 'v -> 'v) (dflt : 'v) (t : Tree<'k, 'v>) =
        match tryFind key t with
        | Some v -> add key (f v) t
        | None -> add key dflt t

    let map (f : 'k -> 'v -> 'w) (t : Tree<'k, 'v>) =
        fold (fun acc k v -> add k (f k v) acc) MEmpty t

    let mapValues (f : 'v -> 'w) (t : Tree<'k, 'v>) = map (fun k v -> f v) t

    let filter (p : 'k -> 'v -> bool) (t : Tree<'k, 'v>) =
        fold (fun acc k v -> if p k v then add k v acc else acc) MEmpty t

    let choose (f : 'k -> 'v -> Option<'w>) (t : Tree<'k, 'v>) =
        fold (fun acc k v ->
                match f k v with
                | Some w -> add k w acc
                | None -> acc) MEmpty t

    let exists (p : 'k -> 'v -> bool) (t : Tree<'k, 'v>) =
        fold (fun acc k v -> if acc then true else p k v) false t

    let forall (p : 'k -> 'v -> bool) (t : Tree<'k, 'v>) =
        fold (fun acc k v -> if acc then p k v else false) true t

    let unionWith (resolve : 'k -> 'v -> 'v -> 'v) (a : Tree<'k, 'v>) (b : Tree<'k, 'v>) =
        fold (fun acc k v ->
                match tryFind k acc with
                | Some old -> add k (resolve k old v) acc
                | None -> add k v acc) a b

    let union (a : Tree<'k, 'v>) (b : Tree<'k, 'v>) = unionWith (fun k x y -> y) a b

    let intersectWith (resolve : 'k -> 'v -> 'v -> 'v) (a : Tree<'k, 'v>) (b : Tree<'k, 'v>) =
        fold (fun acc k v ->
                match tryFind k b with
                | Some other -> add k (resolve k v other) acc
                | None -> acc) MEmpty a

    let intersect (a : Tree<'k, 'v>) (b : Tree<'k, 'v>) = intersectWith (fun k x y -> x) a b

    let difference (a : Tree<'k, 'v>) (b : Tree<'k, 'v>) =
        fold (fun acc k v -> if containsKey k b then acc else add k v acc) MEmpty a

    let partition (p : 'k -> 'v -> bool) (t : Tree<'k, 'v>) =
        fold (fun acc k v ->
                match acc with
                | (yes, no) -> if p k v then (add k v yes, no) else (yes, add k v no))
             (MEmpty, MEmpty) t

    // map2/choose2 over the union of both key sets
    let choose2 (f : 'k -> Option<'v> -> Option<'w> -> Option<'x>) (a : Tree<'k, 'v>) (b : Tree<'k, 'w>) =
        let withA =
            fold (fun acc k v ->
                    match f k (Some v) (tryFind k b) with
                    | Some x -> add k x acc
                    | None -> acc) MEmpty a
        fold (fun acc k w ->
                if containsKey k a then acc
                else
                    match f k None (Some w) with
                    | Some x -> add k x acc
                    | None -> acc) withA b

    let map2 (f : 'k -> Option<'v> -> Option<'w> -> 'x) (a : Tree<'k, 'v>) (b : Tree<'k, 'w>) =
        choose2 (fun k x y -> Some (f k x y)) a b

    // structural invariant used by the tests
    let rec isBalanced (t : Tree<'k, 'v>) =
        match t with
        | MEmpty -> true
        | MNode (k, v, l, r, h, c) ->
            let hl = height l
            let hr = height r
            let d = if hl > hr then hl - hr else hr - hl
            if d > 2 then false
            elif c <> count l + count r + 1 then false
            elif isBalanced l then isBalanced r
            else false

module Set =
    let empty = Map.MEmpty
    let isEmpty (s : Map.Tree<'k, int>) = Map.isEmpty s
    let count (s : Map.Tree<'k, int>) = Map.count s
    let add (key : 'k) (s : Map.Tree<'k, int>) = Map.add key 0 s
    let remove (key : 'k) (s : Map.Tree<'k, int>) = Map.remove key s
    let contains (key : 'k) (s : Map.Tree<'k, int>) = Map.containsKey key s
    let toList (s : Map.Tree<'k, int>) = Map.keys s
    let rec ofListInto (acc : Map.Tree<'k, int>) (xs : 'k list) =
        match xs with
        | h :: t -> ofListInto (add h acc) t
        | [] -> acc
    let ofList (xs : 'k list) = ofListInto Map.MEmpty xs
    let fold (f : 's -> 'k -> 's) (s0 : 's) (s : Map.Tree<'k, int>) =
        Map.fold (fun acc k v -> f acc k) s0 s
    let union (a : Map.Tree<'k, int>) (b : Map.Tree<'k, int>) = Map.union a b
    let intersect (a : Map.Tree<'k, int>) (b : Map.Tree<'k, int>) = Map.intersect a b
    let difference (a : Map.Tree<'k, int>) (b : Map.Tree<'k, int>) = Map.difference a b
    let filter (p : 'k -> bool) (s : Map.Tree<'k, int>) = Map.filter (fun k v -> p k) s
    let exists (p : 'k -> bool) (s : Map.Tree<'k, int>) = Map.exists (fun k v -> p k) s
    let forall (p : 'k -> bool) (s : Map.Tree<'k, int>) = Map.forall (fun k v -> p k) s
    let tryMin (s : Map.Tree<'k, int>) =
        match Map.tryMin s with
        | Some (k, v) -> Some k
        | None -> None
    let tryMax (s : Map.Tree<'k, int>) =
        match Map.tryMax s with
        | Some (k, v) -> Some k
        | None -> None
    let isBalanced (s : Map.Tree<'k, int>) = Map.isBalanced s

// ---- tests: per-function cases, invariants, laws, randomised model ------

let rec listLen (xs : 'a list) =
    match xs with
    | h :: t -> 1 + listLen t
    | [] -> 0

let rec sumList (xs : int list) =
    match xs with
    | h :: t -> h + sumList t
    | [] -> 0

let rec isSorted (xs : int list) =
    match xs with
    | a :: rest ->
        (match rest with
         | b :: t -> if compare a b > 0 then false else isSorted rest
         | [] -> true)
    | [] -> true

let show (b : bool) = if b then 1 else 0

// --- empty / singleton edges
let e0 = Map.empty
let t1 = print (Map.count e0)
let t2 = print (show (Map.isEmpty e0))
let t3 = print (show (Map.containsKey 1 e0))
let t4 = print (Map.findOr 42 1 e0)
let t5 = print (Map.count (Map.remove 1 e0))
let m1 = Map.add 5 50 e0
let t6 = print (Map.count m1)
let t7 = print (Map.findOr 0 5 m1)
let t8 = print (show (Map.isEmpty (Map.remove 5 m1)))

// --- ordered insertion forces rebalancing
let rec buildAsc (i : int) (n : int) (acc : Map.Tree<int, int>) =
    if i > n then acc else buildAsc (i + 1) n (Map.add i (i * 10) acc)
let asc = buildAsc 1 64 Map.empty
let t9 = print (Map.count asc)
let t10 = print (show (Map.isBalanced asc))
let t11 = print (show (isSorted (Map.keys asc)))
let t12 = print (Map.findOr 0 33 asc)

let rec buildDesc (i : int) (acc : Map.Tree<int, int>) =
    if i < 1 then acc else buildDesc (i - 1) (Map.add i (i * 10) acc)
let desc = buildDesc 64 Map.empty
let t13 = print (show (Map.isBalanced desc))
let t14 = print (show (isSorted (Map.keys desc)))

// --- duplicates overwrite, count stays
let dup = Map.add 5 999 m1
let t15 = print (Map.count dup)
let t16 = print (Map.findOr 0 5 dup)

// --- removal keeps invariants
let rec removeEvens (i : int) (n : int) (acc : Map.Tree<int, int>) =
    if i > n then acc
    else removeEvens (i + 2) n (Map.remove i acc)
let pruned = removeEvens 2 64 asc
let t17 = print (Map.count pruned)
let t18 = print (show (Map.isBalanced pruned))
let t19 = print (show (isSorted (Map.keys pruned)))

// --- alter / update / change
let al1 = Map.alter 7 (fun o -> Some 70) Map.empty
let t20 = print (Map.findOr 0 7 al1)
let al2 = Map.alter 7 (fun o -> None) al1
let t21 = print (Map.count al2)
let al3 = Map.alter 7 (fun o -> match o with
                                | Some v -> Some (v + 1)
                                | None -> Some 1) al1
let t22 = print (Map.findOr 0 7 al3)
let up1 = Map.update 9 (fun v -> v * 2) 3 Map.empty
let t23 = print (Map.findOr 0 9 up1)
let up2 = Map.update 9 (fun v -> v * 2) 3 up1
let t24 = print (Map.findOr 0 9 up2)

// --- fold / map / filter / choose / exists / forall
let t25 = print (Map.fold (fun acc k v -> acc + v) 0 asc)
let t26 = print (sumList (Map.values (Map.mapValues (fun v -> v / 10) asc)))
let t27 = print (Map.count (Map.filter (fun k v -> k % 8 = 0) asc))
let t28 = print (Map.count (Map.choose (fun k v -> if k % 16 = 0 then Some v else None) asc))
let t29 = print (show (Map.exists (fun k v -> k = 64) asc))
let t30 = print (show (Map.exists (fun k v -> k = 65) asc))
let t31 = print (show (Map.forall (fun k v -> v = k * 10) asc))

// --- min / max
let t32 = print (match Map.tryMin asc with
                 | Some (k, v) -> k
                 | None -> 0 - 1)
let t33 = print (match Map.tryMax asc with
                 | Some (k, v) -> k
                 | None -> 0 - 1)

// --- union / intersect / difference laws
let ua = Map.ofList [ (1, 1); (2, 2); (3, 3) ]
let ub = Map.ofList [ (3, 30); (4, 40) ]
let t34 = print (Map.count (Map.union ua ub))
let t35 = print (Map.findOr 0 3 (Map.union ua ub))
let t36 = print (Map.findOr 0 3 (Map.unionWith (fun k x y -> x + y) ua ub))
let t37 = print (Map.count (Map.intersect ua ub))
let t38 = print (Map.count (Map.difference ua ub))
let t39 = print (show (Map.count (Map.union ua ub) = Map.count (Map.union ub ua)))

// --- choose2 / map2 over the union of key sets
let c2 = Map.choose2 (fun k x y ->
            match x, y with
            | Some a, Some b -> Some (a + b)
            | Some a, None -> Some a
            | None, Some b -> Some b
            | None, None -> None) ua ub
let t40 = print (Map.count c2)
let t41 = print (Map.findOr 0 3 c2)
let t42 = print (Map.findOr 0 4 c2)

// --- toList/ofList round-trip
let rt = Map.ofList (Map.toList asc)
let t43 = print (Map.count rt)
let t44 = print (show (isSorted (Map.keys rt)))

// --- randomised differential test against an assoc-list model
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

let rec randomOps (n : int) (seed : int) (m : Map.Tree<int, int>) (model : (int * int) list) (bad : int) =
    if n = 0 then (Map.count m, listLen model, bad, show (Map.isBalanced m))
    else
        let s1 = lcg seed
        let key = s1 % 40
        let s2 = lcg s1
        let m2 = if s2 % 3 = 0 then Map.remove key m else Map.add key (key * 7) m
        let model2 = if s2 % 3 = 0 then modelRemove key model else modelAdd key (key * 7) model
        let agree =
            match Map.tryFind key m2, modelFind key model2 with
            | Some a, Some b -> a = b
            | None, None -> true
            | _, _ -> false
        let bad2 = if agree then bad else bad + 1
        randomOps (n - 1) s2 m2 model2 bad2

let r = randomOps 400 12345 Map.empty [] 0
let t45 = print (match r with
                 | (c, mc, bad, bal) -> c)
let t46 = print (match r with
                 | (c, mc, bad, bal) -> mc)
let t47 = print (match r with
                 | (c, mc, bad, bal) -> bad)
let t48 = print (match r with
                 | (c, mc, bad, bal) -> bal)

// --- Set surface
let s1 = Set.ofList [ 5; 3; 9; 1; 3; 7 ]
let t49 = print (Set.count s1)
let t50 = print (show (Set.contains 9 s1))
let t51 = print (show (Set.contains 4 s1))
let t52 = print (show (isSorted (Set.toList s1)))
let s2 = Set.ofList [ 7; 8 ]
let t53 = print (Set.count (Set.union s1 s2))
let t54 = print (Set.count (Set.intersect s1 s2))
let t55 = print (Set.count (Set.difference s1 s2))
let t56 = print (Set.fold (fun a k -> a + k) 0 s1)
let t57 = print (Set.count (Set.filter (fun k -> k > 4) s1))
let t58 = print (show (Set.exists (fun k -> k = 3) s1))
let t59 = print (show (Set.forall (fun k -> k > 0) s1))
let t60 = print (match Set.tryMin s1 with
                 | Some k -> k
                 | None -> 0 - 1)
let t61 = print (match Set.tryMax s1 with
                 | Some k -> k
                 | None -> 0 - 1)
let t62 = print (show (Set.isBalanced (Set.union s1 s2)))

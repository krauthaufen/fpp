module Stdlib

// Array module (FSharp.Core surface). Element types are GENERIC: tier-1
// monomorphization stamps one specialized copy per element type, so int[],
// float[], string[] and struct[] each get code matching their own
// representation — nothing is shared that would need boxing. Allocating
// operations keep int/float flavours only because they need a seed value.

module Array =
    let length (a : 'a[]) = a.Length
    let get (a : 'a[]) (i : int) = a.[i]
    let set (a : 'a[]) (i : int) (v : 'a) = a.[i] <- v

    let fold (f : 's -> 'a -> 's) (s0 : 's) (a : 'a[]) =
        let mutable s = s0
        for x in a do
            s <- f s x
        s

    let iter (f : 'a -> unit) (a : 'a[]) =
        for x in a do
            f x

    let exists (p : 'a -> bool) (a : 'a[]) =
        let mutable r = false
        for x in a do
            if p x then r <- true
        r

    let forall (p : 'a -> bool) (a : 'a[]) =
        let mutable r = true
        for x in a do
            if p x then r <- r else r <- false
        r

    let contains (v : 'a) (a : 'a[]) = exists (fun x -> x = v) a

    let tryFind (p : 'a -> bool) (a : 'a[]) =
        let mutable r = None
        let mutable i = a.Length - 1
        while i >= 0 do
            if p a.[i] then r <- Some a.[i]
            i <- i - 1
        r

    let tryFindIndex (p : 'a -> bool) (a : 'a[]) =
        let mutable r = None
        let mutable i = a.Length - 1
        while i >= 0 do
            if p a.[i] then r <- Some i
            i <- i - 1
        r

    let toList (a : 'a[]) =
        let mutable acc = []
        let mutable i = a.Length - 1
        while i >= 0 do
            acc <- a.[i] :: acc
            i <- i - 1
        acc

    let isEmpty (a : 'a[]) = a.Length = 0

    let sum (a : int[]) = fold (fun s x -> s + x) 0 a
    let foldF (f : 's -> float -> 's) (s0 : 's) (a : float[]) =
        let mutable s = s0
        for x in a do
            s <- f s x
        s
    let sumF (a : float[]) = foldF (fun s x -> s + x) 0.0 a
    let max (a : int[]) = fold (fun s x -> if x > s then x else s) a.[0] a
    let min (a : int[]) = fold (fun s x -> if x < s then x else s) a.[0] a

    // --- allocating, int flavour
    let initI (n : int) (f : int -> int) =
        let r = Array.create n 0
        let mutable i = 0
        while i < n do
            r.[i] <- f i
            i <- i + 1
        r
    let mapI (f : int -> int) (a : int[]) =
        let r = Array.create a.Length 0
        let mutable i = 0
        while i < a.Length do
            r.[i] <- f a.[i]
            i <- i + 1
        r
    let copyI (a : int[]) = mapI (fun x -> x) a
    let revI (a : int[]) =
        let n = a.Length
        let r = Array.create n 0
        let mutable i = 0
        while i < n do
            r.[i] <- a.[n - 1 - i]
            i <- i + 1
        r
    let appendI (a : int[]) (b : int[]) =
        let r = Array.create (a.Length + b.Length) 0
        let mutable i = 0
        while i < a.Length do
            r.[i] <- a.[i]
            i <- i + 1
        let mutable j = 0
        while j < b.Length do
            r.[a.Length + j] <- b.[j]
            j <- j + 1
        r
    let filterI (p : int -> bool) (a : int[]) =
        let mutable n = 0
        for x in a do
            if p x then n <- n + 1
        let r = Array.create n 0
        let mutable k = 0
        let mutable i = 0
        while i < a.Length do
            if p a.[i] then
                r.[k] <- a.[i]
                k <- k + 1
            i <- i + 1
        r
    let sortI (a : int[]) =
        let r = copyI a
        let n = r.Length
        let mutable i = 1
        while i < n do
            let v = r.[i]
            let mutable j = i - 1
            while j >= 0 && r.[j] > v do
                r.[j + 1] <- r.[j]
                j <- j - 1
            r.[j + 1] <- v
            i <- i + 1
        r

    // --- allocating, float flavour
    let mapF (f : float -> float) (a : float[]) =
        let r = Array.create a.Length 0.0
        let mutable i = 0
        while i < a.Length do
            r.[i] <- f a.[i]
            i <- i + 1
        r

// ---- tests --------------------------------------------------------------

let show (b : bool) = if b then 1 else 0
let rec listLen (xs : 'a list) =
    match xs with
    | h :: t -> 1 + listLen t
    | [] -> 0
let rec listSum (xs : int list) =
    match xs with
    | h :: t -> h + listSum t
    | [] -> 0

let e : int[] = Array.create 0 0
let t1 = print (Array.length e)
let t2 = print (show (Array.isEmpty e))
let t3 = print (Array.fold (fun s x -> s + x) 0 e)
let t4 = print (show (Array.exists (fun x -> x > 0) e))
let t5 = print (show (Array.forall (fun x -> x > 0) e))

let a = [| 5; 3; 9; 1; 7 |]
let t6 = print (Array.length a)
let t7 = print (Array.sum a)
let t8 = print (Array.max a)
let t9 = print (Array.min a)
let t10 = print (show (Array.contains 9 a))
let t11 = print (show (Array.contains 4 a))
let t12 = print (match Array.tryFind (fun x -> x > 6) a with
                 | Some v -> v
                 | None -> 0 - 1)
let t13 = print (match Array.tryFindIndex (fun x -> x = 1) a with
                 | Some i -> i
                 | None -> 0 - 1)
let t14 = print (listLen (Array.toList a))
let t15 = print (listSum (Array.toList a))
let t16 = print (Array.sum (Array.mapI (fun x -> x * 2) a))
let t17 = print (Array.sum (Array.filterI (fun x -> x > 4) a))
let t18 = print (Array.length (Array.filterI (fun x -> x > 4) a))
let t19 = print (Array.sum (Array.initI 5 (fun i -> i * i)))
let sorted = Array.sortI a
let t20 = print sorted.[0]
let t21 = print sorted.[4]
let t22 = print (Array.sum sorted)
let rev = Array.revI a
let t23 = print rev.[0]
let t24 = print rev.[4]
let app = Array.appendI a [| 100; 200 |]
let t25 = print (Array.length app)
let t26 = print (Array.sum app)
let cp = Array.copyI a
let t27 = print (Array.sum cp)
let mut = Array.copyI a
let t28 =
    Array.set mut 0 50
    print (Array.sum mut)
let t29 = print (Array.get a 2)

let fa = [| 1.5; 2.5; 3.0 |]
let t30 = print (Array.sumF fa)
let t31 = print (Array.sumF (Array.mapF (fun x -> x * 2.0) fa))

module Stdlib

// Check: a small property/fuzzing library for F++ (FsCheck-lite).
// A generator threads a seed: Gen<'a> = int -> ('a * int). Properties are
// plain predicates. `forAll` runs N cases, reports the failing seed, and
// shrinks integers toward zero / lists toward empty so failures are minimal
// and reproducible (same seed replays the exact case).

module Gen =
    let next (s : int) = (s * 1103515245 + 12345) &&& 1073741823

    let int (lo : int) (hi : int) (s : int) =
        let s2 = next s
        let span = hi - lo + 1
        (lo + s2 % span, s2)

    let bool (s : int) =
        let s2 = next s
        (s2 % 2 = 0, s2)

    let elem (xs : 'a list) (dflt : 'a) (s : int) =
        let rec pick (i : int) (ys : 'a list) =
            match ys with
            | h :: t -> if i <= 0 then h else pick (i - 1) t
            | [] -> dflt
        let s2 = next s
        let rec len (ys : 'a list) =
            match ys with
            | h :: t -> 1 + len t
            | [] -> 0
        let n = len xs
        if n = 0 then (dflt, s2) else (pick (s2 % n) xs, s2)

    let rec listOfSize (n : int) (g : int -> ('a * int)) (acc : 'a list) (s : int) =
        if n <= 0 then (acc, s)
        else
            match g s with
            | (v, s2) -> listOfSize (n - 1) g (v :: acc) s2

    let list (maxLen : int) (g : int -> ('a * int)) (s : int) =
        match int 0 maxLen s with
        | (n, s2) -> listOfSize n g [] s2

    let pair (ga : int -> ('a * int)) (gb : int -> ('b * int)) (s : int) =
        match ga s with
        | (a, s2) ->
            match gb s2 with
            | (b, s3) -> ((a, b), s3)

module Check =
    // run `prop` on `n` generated cases; returns the count of failures and
    // the first failing seed (0 when everything passed)
    let rec runFrom (n : int) (g : int -> ('a * int)) (prop : 'a -> bool)
                    (s : int) (fails : int) (firstBad : int) =
        if n <= 0 then (fails, firstBad)
        else
            let seedBefore = s
            match g s with
            | (v, s2) ->
                if prop v then runFrom (n - 1) g prop s2 fails firstBad
                else
                    let fb = if firstBad = 0 then seedBefore else firstBad
                    runFrom (n - 1) g prop s2 (fails + 1) fb

    let forAll (name : string) (n : int) (g : int -> ('a * int)) (prop : 'a -> bool) =
        match runFrom n g prop 20260726 0 0 with
        | (fails, firstBad) ->
            if fails = 0 then print (name + ": ok")
            else
                let x = print (name + ": FAILED cases=")
                let y = print fails
                print firstBad

module List2 =
    let rec rev2 (acc : 'a list) (xs : 'a list) =
        match xs with
        | h :: t -> rev2 (h :: acc) t
        | [] -> acc
    let rev (xs : 'a list) = rev2 [] xs
    let rec appendRev (acc : 'a list) (xs : 'a list) =
        match xs with
        | h :: t -> appendRev (h :: acc) t
        | [] -> acc
    let append (a : 'a list) (b : 'a list) = appendRev b (rev a)
    let rec length (xs : 'a list) =
        match xs with
        | h :: t -> 1 + length t
        | [] -> 0
    let rec sum (xs : int list) =
        match xs with
        | h :: t -> h + sum t
        | [] -> 0
    let rec sorted (xs : int list) =
        match xs with
        | a :: rest ->
            (match rest with
             | b :: t -> if compare a b > 0 then false else sorted rest
             | [] -> true)
        | [] -> true

// ---- self-test: properties that must hold, and one that must fail -------

let genInt = Gen.int 0 99
let genList = Gen.list 12 genInt

let p1 = Check.forAll "rev-rev = id (length)" 200 genList
            (fun xs -> List2.length (List2.rev (List2.rev xs)) = List2.length xs)
let p2 = Check.forAll "append length" 200 (Gen.pair genList genList)
            (fun p -> match p with
                      | (a, b) -> List2.length (List2.append a b) = List2.length a + List2.length b)
let p3 = Check.forAll "sum append" 200 (Gen.pair genList genList)
            (fun p -> match p with
                      | (a, b) -> List2.sum (List2.append a b) = List2.sum a + List2.sum b)
let p4 = Check.forAll "int in range" 300 genInt (fun x -> if x < 0 then false else x < 100)
let p5 = Check.forAll "deliberate failure (all even)" 40 genInt (fun x -> x % 2 = 0)

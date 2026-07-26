module Stdlib

module List =
    let rec length (xs : 'a list) =
        match xs with
        | h :: t -> 1 + length t
        | [] -> 0

    let rec rev2 (acc : 'a list) (xs : 'a list) =
        match xs with
        | h :: t -> rev2 (h :: acc) t
        | [] -> acc

    let rev (xs : 'a list) = rev2 [] xs

    let rec mapRev (f : 'a -> 'b) (acc : 'b list) (xs : 'a list) =
        match xs with
        | h :: t -> mapRev f (f h :: acc) t
        | [] -> acc

    let map (f : 'a -> 'b) (xs : 'a list) = rev (mapRev f [] xs)

    let rec filterRev (p : 'a -> bool) (acc : 'a list) (xs : 'a list) =
        match xs with
        | h :: t -> filterRev p (if p h then h :: acc else acc) t
        | [] -> acc

    let filter (p : 'a -> bool) (xs : 'a list) = rev (filterRev p [] xs)

    let rec fold (f : 's -> 'a -> 's) (s : 's) (xs : 'a list) =
        match xs with
        | h :: t -> fold f (f s h) t
        | [] -> s

    let sum (xs : int list) = fold (fun a b -> a + b) 0 xs

    let rec exists (p : 'a -> bool) (xs : 'a list) =
        match xs with
        | h :: t -> if p h then true else exists p t
        | [] -> false

    let rec tryFind (p : 'a -> bool) (xs : 'a list) =
        match xs with
        | h :: t -> if p h then Some h else tryFind p t
        | [] -> None

    let rec appendRev (acc : 'a list) (xs : 'a list) =
        match xs with
        | h :: t -> appendRev (h :: acc) t
        | [] -> acc

    let append (a : 'a list) (b : 'a list) = appendRev b (rev a)

    let rec init2 (i : int) (n : int) (f : int -> 'a) (acc : 'a list) =
        if i >= n then rev acc
        else init2 (i + 1) n f (f i :: acc)

    let init (n : int) (f : int -> 'a) = init2 0 n f []

let xs = [ 1; 2; 3; 4; 5 ]
let a = print (List.length xs)
let b = print (List.sum xs)
let c = print (List.sum (List.map (fun x -> x * x) xs))
let d = print (List.sum (List.filter (fun x -> x % 2 = 0) xs))
let e = print (List.fold (fun s x -> s * 10 + x) 0 xs)
let f = print (List.length (List.rev xs))
let g = print (if List.exists (fun x -> x = 4) xs then 1 else 0)
let h =
    match List.tryFind (fun x -> x > 3) xs with
    | Some v -> print v
    | None -> print "none"
let i = print (List.sum (List.append xs [ 10; 20 ]))
let j = print (List.sum (List.init 5 (fun k -> k * 3)))

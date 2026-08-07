class Mappable<'f<_>>
    static mapf : ('a -> 'b) -> 'f<'a> -> 'f<'b>

instance Mappable<list>
    static mapf f xs = List.map f xs

instance Mappable<option>
    static mapf f x =
        match x with
        | Some v -> Some (f v)
        | None -> None

instance Mappable<array>
    static mapf f xs = Array.map f xs

let double (xs : 'f<int>) : 'f<int> when Mappable<'f> =
    mapf (fun x -> x * 2) xs

let l = double [ 1; 2; 3 ]
printfn "%d" (List.sum l)

let o = double (Some 21)
printfn "%d" (match o with Some v -> v | None -> 0)

let a = double [| 5; 6 |]
printfn "%d" (a.[0] + a.[1])

// constraint CHAINS: a generic caller of a generic constrained callee
let quad (xs : 'f<int>) : 'f<int> when Mappable<'f> =
    double (double xs)

printfn "%d" (List.sum (quad [ 1; 2 ]))

// a different element type through the same constructor
let shout (xs : 'f<string>) : 'f<string> when Mappable<'f> =
    mapf (fun (s : string) -> s + "!") xs

printfn "%s" (String.concat "" (shout [ "a"; "b" ]))

// constraints are INFERRED: no annotation anywhere — the scheme comes out
// as 'f<int> -> 'f<int> when Mappable<'f>, kind included
let doubleI xs = mapf (fun x -> x * 2) xs
printfn "%d" (List.sum (doubleI [ 4; 5 ]))
printfn "%d" (match doubleI (Some 50) with Some v -> v | None -> 0)

// the QUALIFIED spelling requires (and discharges) the same constraint
let tripled xs = Mappable.mapf (fun x -> x * 3) xs
printfn "%d" (List.sum (tripled [ 1; 2 ]))
printfn "%d" (match tripled (Some 10) with Some v -> v | None -> 0)

// classes are NAMESPACES: three modes
class Mappable<'f<_>>
    static mapf : ('a -> 'b) -> 'f<'a> -> 'f<'b>

instance Mappable<list>
    static mapf f xs = List.map f xs

instance Mappable<option>
    static mapf f x =
        match x with
        | Some v -> Some (f v)
        | None -> None

// 1. QUALIFIED always works, no open needed
let t1 = Mappable.mapf (fun x -> x + 1) [ 1; 2 ]
printfn "%d" (List.sum t1)

// 2. bare `mapf` does NOT resolve before an open — this `mapf` is OURS
let mapf (x : int) = x * 100
printfn "%d" (mapf 3)

// 3. `open Mappable` injects the member, shadowing the let above
open Mappable
let t3 = mapf (fun x -> x * 2) (Some 21)
printfn "%d" (match t3 with Some v -> v | None -> 0)

[<AutoOpen>]
class Foldy<'f<_>>
    static ffold : ('s -> 'a -> 's) -> 's -> 'f<'a> -> 's

instance Foldy<list>
    static ffold f z xs = List.fold f z xs

// 4. an [<AutoOpen>] class behaves like today: bare immediately
printfn "%d" (ffold (fun a b -> a + b) 0 [ 1; 2; 3 ])

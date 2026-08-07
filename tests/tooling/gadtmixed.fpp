class ListLike<'m<_>>
    static toL : 'm<'a> -> list<'a>
instance ListLike<list>
    static toL xs = xs
instance ListLike<array>
    static toL xs = Array.toList xs
open ListLike

// DIFFERENT constraints on different cases of ONE union
type Box<'a> =
    | Many of 'm<'a> when ListLike<'m>
    | Thing of 'a when Num<'a>
    | Label of name : string * value : 'a     // named payload fields

let sum (b : Box<int>) : int =
    match b with
    | Many xs -> List.sum (toL xs)
    | Thing v -> v + v
    | Label (n, v) -> String.length n + v

let all = [ Many [| 1; 2 |]; Thing 21; Label ("ab", 5) ]
printfn "%d" (List.sum (List.map sum all))

class ListLike<'m<_>>
    static toL : 'm<'a> -> list<'a>
    static ofL : list<'a> -> 'm<'a>

instance ListLike<list>
    static toL xs = xs
    static ofL xs = xs

instance ListLike<array>
    static toL xs = Array.toList xs
    static ofL xs = List.toArray xs

open ListLike

// a union PARAMETERIZED over the constructor: the case payload is 'm<'a>
type Wrap<'m<_>, 'a> =
    | Many of 'm<'a>
    | One of 'a

let total (w : Wrap<'m, int>) : int when ListLike<'m> =
    match w with
    | Many xs -> List.sum (toL xs)
    | One x -> x

printfn "%d" (total (Many [ 1; 2; 3 ]))
printfn "%d" (total (Many [| 10; 20 |]))
let one : Wrap<list, int> = One 5
printfn "%d" (total one)

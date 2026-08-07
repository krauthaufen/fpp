class ListLike<'m<_>>
    static toL : 'm<'a> -> list<'a>

instance ListLike<list>
    static toL xs = xs

instance ListLike<array>
    static toL xs = Array.toList xs

open ListLike

// TRUE existential: 'm is bound BY THE CASE — a Wrap<'a> hides which
// container it holds, and one list can mix them
type Wrap<'a> =
    | Many of 'm<'a> when ListLike<'m>
    | One of 'a

let total (w : Wrap<int>) : int =
    match w with
    | Many xs -> List.sum (toL xs)
    | One x -> x

let mixed : Wrap<int> list = [ Many [ 1; 2; 3 ]; Many [| 10; 20 |]; One 5 ]
printfn "%d" (List.sum (List.map total mixed))
printfn "%d" (total (Many [| 7 |]))

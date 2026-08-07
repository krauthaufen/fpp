// GADT refinement: `of payload -> Result` — the constructor IS a
// function; matching a case teaches ITS BRANCH the result equation.
type E<'a> =
    | I of int -> E<int>
    | B of bool -> E<bool>
    | Pair of E<'x> * E<'y> -> E<'x * 'y>

let rec eval (e : E<'a>) : 'a =
    match e with
    | I n -> n
    | B b -> b
    | Pair (x, y) -> (eval x, eval y)

printfn "%d" (eval (I 42))
printfn "%b" (eval (B true))
let p = eval (Pair (I 7, B false))
printfn "%d %b" (fst p) (snd p)

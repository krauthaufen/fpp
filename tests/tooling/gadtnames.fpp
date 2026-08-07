// labelled payloads with arrow results
type E<'a> =
    | Lit of value : int -> E<int>
    | Add of left : E<int> * right : E<int> -> E<int>
    | IsZ of arg : E<int> -> E<bool>

let rec eval (e : E<'a>) : 'a =
    match e with
    | Lit v -> v
    | Add (l, r) -> eval l + eval r
    | IsZ x -> eval x = 0

printfn "%d" (eval (Add (Lit 20, Lit 22)))
printfn "%b" (eval (IsZ (Add (Lit 1, Lit -1))))

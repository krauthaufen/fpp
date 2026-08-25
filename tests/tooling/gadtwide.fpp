// A GADT whose payload is WIDE (float/int64): the case lays it out INLINE.
//
// The case's result type rides an arrow, and it used to be recorded as a
// second PAYLOAD type — giving the case a slot the constructor never fills.
// That kept every GADT off the inline layout, and in a loop it did not merely
// box, it trapped.
type G<'a> =
    | Num of float -> G<float>
    | Big of int64 -> G<int64>
    | Flag of bool -> G<bool>

let ev (g : G<'a>) : 'a =
    match g with
    | Num v -> v
    | Big n -> n
    | Flag b -> b

printfn "%d" (int (ev (Num 2.5) * 100.0))
printfn "%d" (ev (Big 9000000000L))
printfn "%b" (ev (Flag true))

// the shape that trapped: constructed and read in a loop, so the layout is
// exercised against a collection
let mutable s = 0.0
let mutable i = 0
while i < 200000 do
    s <- s + ev (Num (float i))
    i <- i + 1
printfn "%d" (int64 s)

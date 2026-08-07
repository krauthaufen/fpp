class Sized<'a>
    member 'a.Count : int
    static empty : unit -> 'a

instance Sized<list<'x>>
    member xs.Count = List.length xs
    static empty () = []

instance Sized<string>
    member s.Count = String.length s
    static empty () = ""

let howBig (v : 'a) : int when Sized<'a> = v.Count

printfn "%d" [ 1; 2; 3 ].Count
printfn "%d" "hello".Count
printfn "%d" (howBig [ 1.5; 2.5 ])
printfn "%d" (howBig "xyz")

class Scale<'v, 's>
    member 'v.ScaledBy : 's -> 'v

type Vec2 = { X : float; Y : float }

instance Scale<Vec2, float>
    member v.ScaledBy s = { X = v.X * s; Y = v.Y * s }

let w = { X = 1.5; Y = 2.0 }
let w2 = (w.ScaledBy 2.0).ScaledBy 10.0
printfn "%d %d" (int w2.X) (int w2.Y)

// dot-members dispatch through EXISTENTIAL slots too
type Box2 =
    | Boxed of 'c when Sized<'c>

let sizeOf (b : Box2) : int =
    match b with
    | Boxed v -> v.Count

printfn "%d" (sizeOf (Boxed [ 1; 2; 3; 4 ]))
printfn "%d" (sizeOf (Boxed "hello!"))

// `when`-constrained class members: the context is real (givens inside the
// body, carried on the scheme, demanded at the use) and it GUIDES overload
// selection — a stronger satisfiable context wins, an unsatisfiable one is
// rejected. Instance and static alike.

// a constrained body that USES its givens: the class ops resolve per stamp
type Summer(bias : int) =
    member x.Total (lo : 'a, hi : 'a) : 'a when Integral<'a> when Ordered<'a> =
        let mutable i = lo
        let mutable acc = i - i
        while i <= hi do
            acc <- acc + i
            i <- i + One
        acc
    static member Span (lo : 'a, hi : 'a) : 'a when Num<'a> = hi - lo

let s = Summer(0)
printfn "%d" (int (s.Total (1L, 4L)))
printfn "%d" (s.Total (2, 5))
printfn "%d" (int (Summer.Span (10L, 25L)))
printfn "%d" (Summer.Span (3, 11))

// selection: at float BOTH contexts hold and Fractional<'a> entails Num<'a>,
// so the stronger one wins; at int Fractional has no instance and only the
// Num overload survives
type Sel() =
    member x.Pick (v : 'a) : int when Num<'a> = 1
    member x.Pick (v : 'a) : int when Fractional<'a> = 2
    static member SPick (v : 'a) : int when Num<'a> = 10
    static member SPick (v : 'a) : int when Fractional<'a> = 20

let sel = Sel()
printfn "%d" (sel.Pick 1.5)
printfn "%d" (sel.Pick 3)
printfn "%d" (Sel.SPick 2.5)
printfn "%d" (Sel.SPick 7)

// two constraints beat one when both sets hold
type Sel2() =
    member x.Go (v : 'a) : int when Num<'a> = 1
    member x.Go (v : 'a) : int when Num<'a> when Ordered<'a> = 2

printfn "%d" (Sel2().Go 4)

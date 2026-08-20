module M
let walk (xs : seq<int>) =
    use e = xs.GetEnumerator ()
    let mutable s = 0
    while e.MoveNext () do s <- s + e.Current
    s
let go = printfn "%d" (walk ([ 1; 2; 3 ] :> seq<int>))

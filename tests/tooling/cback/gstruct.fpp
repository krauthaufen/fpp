[<Struct>]
type KV<'k, 'v> = { mutable K : 'k; mutable V : 'v }

let mutable a = { K = 1; V = 2.5 }
let mutable b = a
b.K <- 9
printfn "%d" a.K
printfn "%d" b.K

let mutable s = { K = 3; V = "three" }
printfn "%s" s.V

let dek (x : KV<int, float>) = x.K
printfn "%d" (dek a)

let choose2 (flag : bool) (x : 'a) (y : 'a) = if flag then x else y
let c = choose2 true { K = 7; V = 70 } { K = 8; V = 80 }
printfn "%d %d" c.K c.V

let d1 = { K = 1; V = 2 }
let d2 = { K = 1; V = 2 }
printfn "%b" (d1 = d2)
let lst = [ { K = 1; V = "a" }; { K = 2; V = "b" } ]
let found = lst |> List.tryFind (fun e -> e.K = 2)
let foundV =
    match found with
    | Some e -> e.V
    | None -> "?"
printfn "%s" foundV

let arr : KV<int, int>[] = Array.zeroCreate 3
arr.[1] <- { K = 5; V = 6 }
let mutable e1 = arr.[1]
e1.V <- 60
printfn "%d %d" arr.[1].V e1.V

let sum (p : KV<int, int>) = p.K + p.V
printfn "%d" (sum arr.[1])

[<Struct>]
type Wrap<'a> = { Inner : KV<int, 'a>; Tag : int }
let w = { Inner = { K = 11; V = 12 }; Tag = 99 }
printfn "%d %d %d" w.Inner.K w.Inner.V w.Tag

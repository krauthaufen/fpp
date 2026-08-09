// REGRESSION: a generic class constructed INSIDE another generic class'
// member — the .NET Enumerator shape. The enclosing member (GetEnumerator)
// is not itself layout-dependent, so its call classified CANON and reached
// the template, whose BoxEn construction canonicalized — an obj-family
// enumerator over a packed int array, and Current trapped on the cast.
// The fix: a CLASS member called at a concrete non-uniform instantiation
// stamps; the ctor family it constructs then specializes with it.
type BoxEn<'a>(items : 'a[], count : int) =
    let mutable i = 0 - 1
    interface IEnumerator<'a> with
        member _.MoveNext () =
            i <- i + 1
            i < count
        member _.Current = items.[i]

type Box<'a>(cap : int) =
    let mutable items : 'a[] = Array.zeroCreate cap
    let mutable n = 0
    member x.Add (v : 'a) : unit =
        items.[n] <- v
        n <- n + 1
    member x.GetEnumerator () : IEnumerator<'a> = BoxEn<'a>(items, n) :> IEnumerator<'a>

let b = Box<int>(8)
let go =
    b.Add 3
    b.Add 4
    for v in b do printfn "v %d" v

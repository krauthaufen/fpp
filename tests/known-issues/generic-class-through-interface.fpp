module KnownIssue

// A generic class constructed INSIDE another generic class' member — the
// .NET shape, where a collection hands out its own Enumerator<'a> — is
// stamped at the CANONICAL instantiation rather than the enclosing one.
// Expected: v 3 / v 4. Actual: a cast failure in `Current` stamped at obj.
//
// Diagnosis. A class that implements an interface is monomorphized: each
// instantiation becomes a subclass carrying its own vtable (see
// DIVERGENCES.md), and the demand comes from the constructor's stamp. Here
// the constructor call for BoxEn sits inside Box's stamped member, and the
// instantiation it carries names a variable the member's substitution does
// not know — the member's own quantified variable is not the one the class
// is generic in. An unsubstituted variable canonicalizes to `obj`, so
// BoxEn's members are stamped for reference elements while the array it
// holds is packed.
//
// The prelude's collections do not hit this: they snapshot into an array and
// hand back the built-in array iterator, which needs no class of its own.
//
// The same mismatch shows up in the member's scheme: an interface method's
// result type brings a second quantified variable for what the source calls
// one 'a. Making those one variable is probably the whole fix.

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

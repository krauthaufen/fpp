module KnownIssue

// A generic class whose FIELD LAYOUT depends on its type parameter cannot be
// reached through an interface. Expected: 5. Actual: a cast failure.
//
// Diagnosis. A member reachable through a vtable keeps the canonical
// all-anyref signature — that IS the dispatch contract — so it is never
// specialized (BinDriver, `ifaceImplKeys`). A member called DIRECTLY is
// specialized. `Arr<int>`'s constructor stores a PACKED int array in
// `items`, and the unspecialized `Current` reads it at the uniform
// representation.
//
// Constructing is fine, and calling a member directly is fine; it is the
// interface call that has no correct answer. At a reference element type
// (`Arr<string>`) even that works, which is what makes it silent.
//
// Fixing it means monomorphizing the CLASS, not just its members: a
// per-instantiation descriptor whose vtable slots name the stamped bodies.
// The prelude's own collections dodge it — see DIVERGENCES.md.

type Arr<'a>(items : 'a[]) =
    member x.First = items.[0]
    interface IEnumerator<'a> with
        member _.MoveNext () = false
        member _.Current = items.[0]

let a = Arr<int>([| 5; 6 |])
let direct = print a.First               // 5 — the specialized member
let e = a :> IEnumerator<int>            // the upcast itself is fine
let viaIface = print e.Current           // traps

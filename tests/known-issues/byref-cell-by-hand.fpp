// A `ByRefCell` built BY HAND and read back traps with a cast failure. The
// compiler's own cells work — `&x` synthesizes one, passes it and reads it
// back, and every byref test passes — but this does not:
//
//     let r : ByRefCell<int> = { Contents = 5 }
//     r.Contents <- r.Contents + 1
//     printfn "%d" r.Contents          // wasm trap: cast failure
//
// PRE-EXISTING: it fails identically before any of today's byref work, so it
// is not the automatic dereference or the out-parameter view.
//
// WHY IT MATTERS: it is what blocks `ref`. F#'s ref cell is exactly this
// shape and `let r = ref v` is ordinary F# — FSharp.Data.Adaptive writes
// `let outputs = ref (Array.zeroCreate 8)` and `let mutable valueReader =
// ref Unchecked.defaultof<_>`, then passes the cell straight to a byref
// out-parameter, which is precisely what a ByRefCell is for. Adding
//
//     let ref (value : 'a) : ByRefCell<'a> = { Contents = value }
//
// to the prelude is one line and it inherits this bug.
//
// SUSPICION, not verified: `ByRefCell<'a>` is a generic single-field record,
// so it is layout-dependent and stamped per instantiation. A literal written
// in user code has to be named at its instantiation the way the compiler's
// synthesized one is, and the cast failure looks like a stamped record
// meeting an unstamped read.

module M

let go =
    let r : ByRefCell<int> = { Contents = 5 }
    r.Contents <- r.Contents + 1
    printfn "%d" r.Contents

// A STATIC WRITTEN ABOVE ITS CONSTRUCTOR STILL HAS THE TYPE IT BUILDS.
//
// The constructor was registered only when its own declaration was reached,
// so a static above it found none and its body's type stayed a free
// VARIABLE — after which `Tok.Top` fitted EVERY annotation. This file is the
// annotation it must not fit; `suites/staticbeforector.fpp` holds the uses
// that must keep working.
//
// fsc rejects it too (FS0001: int does not match Tok).
module Neg_static_above_ctor_has_a_type
//! 18 int vs Tok
type Tok =
    val mutable n : int
    static member Top = Tok(7)
    member x.N = x.n
    new (n : int) = { n = n }

let bad : int = Tok.Top
printfn "%d" bad

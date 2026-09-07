// MIXING AN IMPLICIT YIELD WITH AN EXPLICIT ONE.
//
// A computation-expression body that names a value anywhere — `yield`,
// `yield!`, `return` — reads its OTHER bare expressions as statements, so
// `div { "bare"; yield "x" }` throws "bare" away. That is F#'s reading too:
// fsc accepts it with warning FS0020 and produces exactly what we produced,
// a body holding only the explicit yield.
//
// This compiler emits no warnings, and a value the author wrote vanishing
// with nothing said is the shape it refuses to ship. So the mix is an ERROR
// here — a DIVERGENCE, deliberately, and the same rule the historic
// wombat.dom scar and fpp.dom's scene CE both needed (that one folded an
// empty Shader, and cost its milestone the most debugging time of any bug
// in it: ~/claude/fpp-base-snags.md #51).
//
//? fsc-accepts
module Neg_ce_implicit_explicit_yield_mix
//! 25 implicit and explicit yields
type B() =
    member _.Yield (x : int) : int list = [ x ]
    member _.Combine (a : int list, b : int list) : int list = a @ b
    member _.Delay (f : unit -> int list) : int list = f ()
    member _.Zero () : int list = []
let b = B()
let r = b { 1
            yield 2 }
printfn "%d" (List.length r)

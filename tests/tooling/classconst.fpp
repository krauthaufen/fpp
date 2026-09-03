// A CLASS CONSTANT USED DIRECTLY IN AN EXPRESSION, from the fpp.base port
// (KNOWN-ISSUES #3). `t * (One - One * t)` in a `when Num<'a>` body trapped,
// while the same body with the constant bound first — `let one : 'a = One in
// t * (one - one * t)` — answered correctly. Two spellings of one thing
// disagreeing, and the working one is the longer.
//
// The stamped clone kept `$class:Num:One:#4`: the constant was typed with a
// FRESH variable that unified with 'a only afterwards, so the marker string
// was baked before the two became one and neither spelling the substitution
// knows about matched it. The backend then had a class constant at an
// unresolved type and emitted a trap.
//
// The leftover is mapped by the marker's CLASS — the scheme says which
// variable Num applies to, and that variable's position picks the
// instantiation. Not by position or by "there is only one parameter": a body
// can nest a generic lambda whose variables are its own, and mapping those
// left a vtable slot unresolved in the adaptive suite.
module Core_classconst

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// the shape that WORKED, kept so a fix cannot trade one for the other
let viaLocal (t : 'a) : 'a when Num<'a> =
    let one : 'a = One
    t * (one - one * t)

// the shape that TRAPPED
let direct (t : 'a) : 'a when Num<'a> = t * (One - One * t)

eq "constant-bound-first" (string (viaLocal 0.5)) "0.25"
eq "constant-used-directly" (string (direct 0.5)) "0.25"
eq "the-two-agree" (string (direct 0.25)) (string (viaLocal 0.25))

// Zero as well as One, and on the right of the operator
let useZero (t : 'a) : 'a when Num<'a> = t * (One + Zero) - Zero
eq "zero-and-one-together" (string (useZero 3.0)) "3"

// the same function at another instantiation, so the stamp is not a one-off
eq "at-int" (string (direct 2)) "-2"
eq "at-int-again" (string (viaLocal 2)) "-2"

// a constant inside a nested expression, several levels down
let deep (t : 'a) : 'a when Num<'a> = t * (One - (One - (One - One * t)))
eq "nested-constants" (string (deep 0.5)) "0.25"

// ---- TWO type parameters -------------------------------------------------
// `when Num<'a> when OfInt<'a>` stamped `$float$int` — two type parameters for
// a signature that has one — and its operators came out as the bare INTEGER
// defaults. The extra variable was the binding's own: the parameter and the
// return annotation were the SAME variable when the body started and two
// different ones when it ended, because `prune`'s path compression re-pointed
// a chain without recording it in the trial log, and a rollback then restored
// only what the log knew about.

let poly (t : 'a) : 'a when Num<'a> when OfInt<'a> = t * t * (OfInt 3 - OfInt 2 * t)

eq "two-parameters-at-float" (string (poly 0.5)) "0.5"
eq "two-parameters-at-int" (string (poly 2)) "-4"

// the same shape with the constant on the right, so the fix is not about
// which side the OfInt sits on
let poly2 (t : 'a) : 'a when Num<'a> when OfInt<'a> = t * (t * OfInt 2 - OfInt 1)
eq "two-parameters-other-order" (string (poly2 0.5)) "0"

// ---- a sibling member must not PIN the type's parameter -------------------
// `member v.Sign` calls a constrained generic let; `Zero - One` inside that
// let is `Sub<'z,'o>` whose RESULT is the type's 'a. The arguments are
// ordinary inner variables, so the constraint did not look
// declaration-level, numeric defaulting ground them to int — and deciding
// that constraint decided its projection, freezing 'a at int for EVERY
// member. The unrelated `member v.Length when Floating<'a>` then asked for
// `Floating:sqrt:int` and trapped on any receiver (KNOWN-ISSUES #2).

let signum (x : 'a) : 'a when Num<'a> when Ordered<'a> =
    if x < Zero then Zero - One elif x > Zero then One else Zero

[<Struct>]
type V2 =
    { PX : float; PY : float }
    member v.Len = sqrt (v.PX * v.PX + v.PY * v.PY)
    member v.Sgn = ({ PX = signum v.PX; PY = signum v.PY } : V2)

let vv = { PX = 3.0; PY = 4.0 }
eq "sibling-member-does-not-pin" (string vv.Len) "5"
eq "and-the-sibling-itself-works" (string (vv.Sgn.PX + vv.Sgn.PY)) "2"

printfn "DONE tests=%d failures=%d" ntests failures

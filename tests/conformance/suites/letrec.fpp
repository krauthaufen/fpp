// Ported from dotnet/fsharp tests/fsharp/core/letrec/test.fsx into the
// common F#/F++ subset. Dropped (outside the subset, marked in place):
// object expressions ({new System.Object() ...}), WinForms, class
// initialization-check tests (InvalidOperationException on `as this`
// pre-init calls), `module rec`, mutually-recursive class hierarchies.
module Core_letrec

let mutable ntests = 0
let mutable failures = 0
let report_failure (s : string) =
    failures <- failures + 1
    printfn "NO: %s" s
let test (t : string) (s1 : int) (s2 : int) : unit =
    ntests <- ntests + 1
    if s1 <> s2 then report_failure ("test " + t + " failed")
let check (t : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then report_failure ("test " + t + " failed")

// ---- nested letrecs ----------------------------------------------------

let f =
    let x = ref 0
    fun () ->
        x := !x + 1
        let rec g n = if n = 0 then 1 else h (n - 1)
        and h n = if n = 0 then 2 else g (n - 1)
        g (!x)

check "ewiucew" (f () = 2)
check "ewiew8w" (f () = 1)

let nestedInnerRec2 =
    let x = ref 0
    fun () ->
        x := !x + 1
        let rec g n = if n = 0 then !x + 100 else h (n - 1)
        and h n = if n = 0 then !x + 200 else g (n - 1)
        g (!x)

check "ewiucew2" (nestedInnerRec2 () = 201)
check "ewiew8w2" (nestedInnerRec2 () = 102)

// ---- recursion through constructors ------------------------------------

// DROPPED: cyclic value recursion through constructors (`let rec x =
// { F1 = 3; F2 = x }`, mutually recursive record values via delayed init) —
// F#'s FS0040 initialization-graph feature, unsupported in F++ (records in
// tests/known-issues once triaged).

// ---- non-function letrec -----------------------------------------------

let rec a1 = 1
and b = a1
check "celkewieds32w8w" (a1 = 1)
check "cel3f98u8w" (b = a1)

let rec a2 = test "grekjre" (b2 + 1) 3
and b2 = 2

let nonRecursiveImmediate () =
    let x = ref 1
    let rec aa = (x := 3; !x)
    and bb = aa
    check "dqwij" (aa = 3)
    check "dqwecqwij" (bb = 3)

nonRecursiveImmediate ()
nonRecursiveImmediate ()

// DROPPED: recObj object expression (System.Object with GetHashCode override)
// DROPPED: WouldFailAtRuntimeTest (init-graph runtime failure + exn class)
// DROPPED: WinForms MenuItem block

// ---- inner recursion where some items go TLR ---------------------------

let apply f x = f x
let dec (n : int) = n   // deliberately identity, as in the original

// compile-only in the original (dec never decrements — calling would loop)
let inner () =
    let rec odd n = if n = 1 then true else not (even (dec n))
    and even n = if n = 0 then true else not (apply odd (dec n))
    even 99

// a CALLED variant with a real decrement, same TLR shape
let inner2 () =
    let rec odd n = if n = 0 then false else even (n - 1)
    and even n = if n = 0 then true else apply odd (n - 1)
    even 99

let evenOdd100 () =
    let rec ev n = if n = 0 then true else od (n - 1)
    and od n = if n = 0 then false else ev (n - 1)
    ev 100

check "tlr-even99" (inner2 () = false)
check "tlr-even100" (evenOdd100 () = true)

// ---- partially polymorphic letrec --------------------------------------

module PartiallyPolymorphicLetRecTest =
    let rec pf x = pg (fun y -> ())
    and pg h = ()

    let rec pf2 x = pg2 (fun y -> ()); pg2 (fun z -> ())
    and pg2 h = ()

    let rec pf3 x = pg3 (fun y -> ()); pg3 (fun z -> ())
    and pg3 h = ph3 (fun z -> ())
    and ph3 h = ()

PartiallyPolymorphicLetRecTest.pf 1
PartiallyPolymorphicLetRecTest.pf2 2
PartiallyPolymorphicLetRecTest.pf3 3
check "polyletrec" true

// ---- initialization graph at top level ---------------------------------

module InitializationGraphAtTopLevel =
    let nyi2 (callback : unit -> bool) = callback
    let rec aaa = nyi2 (fun () -> ggg ())
    and ggg () = (bbb = false)
    and bbb = true

check "initgraph" (InitializationGraphAtTopLevel.aaa () = false)

// ---- basic value-letrec permutations -----------------------------------

module Perm1 =
    let rec pA1 = 1
    and pA2 = pA1
module Perm2 =
    let rec pA1 = pA2
    and pA2 = 1
module Perm3b =
    let rec pA1 = pA2
    and pA2 = pA3
    and pA3 = 1
module Perm4i =
    let rec pA1 = pA4
    and pA2 = 1
    and pA3 = pA2
    and pA4 = pA3
module PermMisc =
    let rec pA1 = pA4 + 1
    and pA2 = 1
    and pA3 = pA2 + 1
    and pA4 = pA3 + 1

check "vsdlknv01" (Perm1.pA1 = 1 && Perm1.pA2 = 1)
check "vsdlknv02" (Perm2.pA1 = 1 && Perm2.pA2 = 1)
check "vsdlknv04" (Perm3b.pA1 = 1 && Perm3b.pA2 = 1 && Perm3b.pA3 = 1)
check "vsdlknv0e" (Perm4i.pA1 = 1 && Perm4i.pA2 = 1 && Perm4i.pA3 = 1 && Perm4i.pA4 = 1)
check "vsdlknv0r" (PermMisc.pA1 = 4 && PermMisc.pA2 = 1 && PermMisc.pA3 = 2 && PermMisc.pA4 = 3)

printfn "DONE tests=%d failures=%d" ntests failures

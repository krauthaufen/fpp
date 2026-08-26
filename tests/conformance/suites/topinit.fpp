// TOP-LEVEL INITIALISATION, ported from dotnet/fsharp's
// tests/fsharp/core/topinit (the deterministic-initialisation cases).
//
// Every top-level binding in a module is an INITIALISER, and they run in
// source order, once, before anything that reads them. That order is the
// whole content of this suite: a binding computed from an earlier one sees
// the earlier VALUE, a side effect in a binding happens where the binding
// is written, and a `do` statement between two bindings runs between them.
//
// DROPPED: the `--deterministic-init` flag matrix (a compiler switch, not a
// language rule), initialisation ACROSS files, and the
// InvalidOperationException F# raises for a genuinely circular static
// initialisation — there is no such cycle in the subset here.
module Core_topinit

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- bindings run in SOURCE ORDER -------------------------------------------

let mutable trace = ""
let note (s : string) : int =
    trace <- trace + s
    0

let _a = note "a"
let _b = note "b"
let _c = note "c"

eq "bindings-run-in-order" trace "abc"

// a `do` statement runs where it is written
let mutable trace2 = ""
let step (s : string) : unit = trace2 <- trace2 + s

step "1"
let _mid = (step "2"; 0)
step "3"

eq "statements-interleave-with-bindings" trace2 "123"

// ---- a binding sees the VALUE of the ones above it --------------------------

let base1 = 10
let derived1 = base1 * 2
let derived2 = derived1 + base1

eq "derived-from-earlier" (string derived2) "30"

// a mutable read at initialisation time takes the value it had THEN
let mutable counter = 1
let snapshot = counter
counter <- 99

eq "snapshot-is-the-value-at-the-time" (string snapshot) "1"
eq "the-mutable-moved-on" (string counter) "99"

// ---- an initialiser runs ONCE ------------------------------------------------

let mutable evaluations = 0
let evaluatedOnce =
    evaluations <- evaluations + 1
    evaluations

// reading it many times does not re-run it
let readA = evaluatedOnce
let readB = evaluatedOnce
let readC = evaluatedOnce

eq "initialiser-runs-once" (string evaluations) "1"
eq "every-read-is-the-same" (string (readA + readB + readC)) "3"

// ---- initialisation inside a nested module ----------------------------------

let mutable moduleTrace = ""

module Inner =
    let first = (moduleTrace <- moduleTrace + "i1"; 1)
    let second = (moduleTrace <- moduleTrace + "i2"; first + 1)

    module Deeper =
        let third = (moduleTrace <- moduleTrace + "i3"; 3)

let afterInner = moduleTrace

eq "nested-module-in-order" afterInner "i1i2i3"
eq "nested-module-values" (string (Inner.first + Inner.second + Inner.Deeper.third)) "6"

// ---- a function defined above is callable from a binding below --------------

let double (v : int) : int = v * 2
let doubled = double 21

eq "function-then-use" (string doubled) "42"

// and a function may be defined AFTER the value it will later be applied to
let stored = 7
let useStored () : int = double stored

eq "function-defined-after-its-input" (string (useStored ())) "14"

// ---- data structures built at initialisation --------------------------------

let table = [ ("a", 1); ("b", 2) ]
let lookup = Map.ofList table
let total = List.sum (List.map snd table)

eq "list-built-at-init" (string (List.length table)) "2"
eq "map-built-from-it" (string (Map.find "b" lookup)) "2"
eq "sum-built-from-it" (string total) "3"

// an array filled by a loop at initialisation
let filled =
    let a = Array.zeroCreate 4
    for i in 0 .. 3 do a.[i] <- i * i
    a

eq "array-filled-at-init" (string (Array.sum filled)) "14"

// a value that depends on the array above
let filledMax = Array.max filled
eq "depends-on-the-filled-array" (string filledMax) "9"

// ---- order across mutually visible bindings ---------------------------------

// a `let rec ... and` group is one initialiser: both names exist before
// either body runs
let rec isEven (n : int) : bool = if n = 0 then true else isOdd (n - 1)
and isOdd (n : int) : bool = if n = 0 then false else isEven (n - 1)

let evenness = isEven 10
test "rec-group-initialised-together" evenness

// a closure captured at initialisation sees later writes to a mutable
let mutable later = 0
let readsLater () : int = later
later <- 5

eq "closure-sees-the-later-write" (string (readsLater ())) "5"

// but a VALUE captured at initialisation does not
let capturedNow = later
later <- 6
eq "value-captured-at-init" (string capturedNow) "5"
eq "mutable-moved-on-again" (string later) "6"

printfn "DONE tests=%d failures=%d" ntests failures

// NAME RESOLUTION, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/BasicGrammarElements and
// the NameResolution cases of InferenceProcedures: which declaration a name
// reaches when several are in scope.
//
// The rule that decides almost every case here is LAST ONE WINS: a later
// `let`, a later `open`, a nested module's own declaration. The suite pins
// it by making the two candidates answer DIFFERENTLY, so a resolution that
// picked the earlier one is a wrong value rather than a build error.
//
// DROPPED: the diagnostics-only cases (ambiguous record labels are an error
// in F#, not a value), `AutoOpen`, and namespace declarations.
module Core_nameres

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- a later `let` shadows an earlier one --------------------------------

// F# allows shadowing inside a scope, NOT at module level (a second
// module-level `v` is a duplicate definition), so the chains below are
// all local
let v = 2

let topLike () =
    let v = 1
    let v = 2
    v

test "scope-shadow" (topLike () = 2)

let shadowInBody () =
    let a = 1
    let a = a + 10
    let a = a * 2
    a

test "local-shadow-chain" (shadowInBody () = 22)

// a parameter shadows a top-level binding
let shadowParam (v : int) = v * 100
test "param-shadows" (shadowParam 3 = 300)

// a `for` binder shadows, and the outer one is back afterwards
let mutable seen = 0
let loopShadow () =
    for v in [ 5; 6 ] do
        seen <- seen + v
    v

test "for-binder-shadows" (loopShadow () = 2 && seen = 11)

// a match binder shadows inside its arm only
let matchShadow (o : int option) =
    match o with
    | Some v -> v * 10
    | None -> v

test "match-binder-shadows" (matchShadow (Some 3) = 30)
test "match-binder-scope-ends" (matchShadow None = 2)

// a lambda parameter shadows
test "lambda-shadows" ((fun v -> v + 1) 10 = 11)

// ---- modules qualify, and nested modules nest ----------------------------

module Inner =
    let value = 10
    let twice (x : int) = x * 2

    module Deeper =
        let value = 20
        let plus (x : int) = x + value

test "module-qualified" (Inner.value = 10)
test "module-function" (Inner.twice 4 = 8)
test "nested-module" (Inner.Deeper.value = 20)
test "nested-uses-own" (Inner.Deeper.plus 1 = 21)

// a module's own declaration wins over the enclosing scope
module Sibling =
    let v = 99
    let readsOwn () = v

test "module-own-binding" (Sibling.readsOwn () = 99)
test "outer-unaffected" (v = 2)

// a module can name a member the same as a top-level one
module Alt =
    let shadowParam (x : int) = x + 1

test "module-vs-top-level" (Alt.shadowParam 1 = 2 && shadowParam 1 = 100)

// ---- `open` brings names in, and a later open wins -----------------------

module First =
    let which = "first"
    let only1 = 1

module Second =
    let which = "second"
    let only2 = 2

open First
open Second

test "later-open-wins" (which = "second")
test "both-opens-visible" (only1 = 1 && only2 = 2)
test "qualified-beats-open" (First.which = "first")

// a local binding beats an opened one
let which = "local"
test "local-beats-open" (which = "local")

// ---- union cases and record labels ---------------------------------------

type Colour =
    | Red
    | Green

type Fruit =
    | Apple
    | Cherry

let describe (c : Colour) =
    match c with
    | Red -> "r"
    | Green -> "g"

test "union-case-unqualified" (describe Red = "r")
test "union-case-qualified" (describe Colour.Green = "g")

// two records sharing a label: the LAST declared wins for a bare literal,
// and the annotation decides otherwise
type A = { Shared : int; OnlyA : int }
type B = { Shared : int; OnlyB : int }

let bare = { Shared = 1; OnlyB = 2 }
test "record-inferred-by-labels" (bare.OnlyB = 2)

let annotated : A = { Shared = 3; OnlyA = 4 }
test "record-by-annotation" (annotated.OnlyA = 4 && annotated.Shared = 3)

// the qualified label form names the type outright
let qualified = { A.Shared = 5; A.OnlyA = 6 }
test "record-qualified-label" (qualified.OnlyA = 6)

// ---- a member name and a function name do not collide --------------------

type Box (v : int) =
    member _.Value = v
    member _.Twice = v * 2

let Value = "a function-scope name"
let b = Box 4

test "member-vs-binding" (b.Value = 4 && Value = "a function-scope name")

// a member and an extension member with different names on one type
type Box with
    member x.Thrice = x.Value * 3

test "extension-name" (b.Thrice = 12)

// ---- the value namespace and the type namespace are separate -------------

type Pair = { L : int; R : int }
let Pair = 7

test "type-and-value-same-name" (Pair = 7 && ({ L = 1; R = 2 }).L = 1)

// a union case name reused as a binding name
type Wrap = | Wrap of int
let unwrap (w : Wrap) = match w with Wrap n -> n
test "case-name-as-type-name" (unwrap (Wrap 5) = 5)

// ---- recursive scope: `let rec ... and` sees both ------------------------

let rec isEven (n : int) : bool = if n = 0 then true else isOdd (n - 1)
and isOdd (n : int) : bool = if n = 0 then false else isEven (n - 1)

test "letrec-forward-reference" (isEven 4 && isOdd 3)

// a non-recursive `let` refers to the PREVIOUS binding of its own name
let stepped () =
    let step = 1
    let step = step + 1
    let step = step + 1
    step
test "non-recursive-self-reference" (stepped () = 3)

// ---- generic parameter names are scoped to their declaration -------------

let idA<'a> (x : 'a) : 'a = x
let idB<'a> (x : 'a) : 'a = x

test "type-param-scoped" (idA 1 = 1 && idB "s" = "s")

printfn "DONE tests=%d failures=%d" ntests failures

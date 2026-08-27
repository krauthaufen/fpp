// MODULES, ported from dotnet/fsharp's tests/fsharp/core/namespaces and the
// ModuleAbbreviations / NameResolution cases of Conformance.
//
// A module is a NAMESPACE with an initialisation order. What this suite pins
// is the resolution side: what a nested name means from inside and outside,
// what `open` brings into scope and what it shadows, and — the reason this
// suite exists — that a module ABBREVIATION is a second name for the same
// module rather than a copy of it, including for the types it declares.
//
// DROPPED: `namespace` declarations (this compiler's files nest modules in
// one file, and the top-level module header stands in), `[<AutoOpen>]` on an
// assembly, and `open type` — none has a counterpart here.
module Core_modules

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

// ---- nesting, and the qualified name it produces -----------------------------

module Outer =
    let a = 1

    module Middle =
        let b = 2

        module Inner =
            let c = 3
            let sum () = a + b + c

    // a name from an enclosing module needs no qualification INSIDE
    let viaEnclosing = a + Middle.b

eq "one-level" (string Outer.a) "1"
eq "two-levels" (string Outer.Middle.b) "2"
eq "three-levels" (string Outer.Middle.Inner.c) "3"
eq "inner-sees-its-enclosing" (string (Outer.Middle.Inner.sum ())) "6"
eq "enclosing-sees-its-inner" (string Outer.viaEnclosing) "3"

// ---- a module ABBREVIATION is a second NAME ----------------------------------

module M = Outer.Middle

eq "abbreviation-reaches-the-value" (string M.b) "2"
eq "abbreviation-reaches-deeper" (string M.Inner.c) "3"
eq "abbreviation-reaches-a-function" (string (M.Inner.sum ())) "6"

// the original name still works, and both name ONE module
eq "original-still-works" (string Outer.Middle.b) "2"
test "both-names-agree" (M.b = Outer.Middle.b)

// an abbreviation OF an abbreviation
module M2 = M

eq "chained-abbreviation" (string M2.b) "2"
eq "chained-abbreviation-deeper" (string M2.Inner.c) "3"

// abbreviating a nested module directly
module Deep = Outer.Middle.Inner
eq "abbreviation-of-the-innermost" (string Deep.c) "3"

// ---- an abbreviation carries the TYPES too -----------------------------------

module Shapes =
    type Pt = { X : int; Y : int }

    type Kind =
        | Round
        | Square

    let origin = { X = 0; Y = 0 }
    let make (x : int) (y : int) : Pt = { X = x; Y = y }
    let describe (k : Kind) : string =
        match k with
        | Round -> "round"
        | Square -> "square"

module S = Shapes

// the type is reachable through the alias, as an ANNOTATION
let p : S.Pt = S.make 3 4
eq "type-through-the-alias" (string (p.X + p.Y)) "7"

// and a value of it is the SAME type as one built through the original name
let q : Shapes.Pt = S.make 1 1
eq "one-type-under-two-names" (string (q.X + q.Y)) "2"

let r : S.Pt = Shapes.make 2 2
eq "and-the-other-way-round" (string (r.X + r.Y)) "4"

// a union case through the alias
eq "union-case-through-the-alias" (S.describe S.Round) "round"
eq "union-case-mixed" (Shapes.describe S.Square) "square"

// a record literal typed by the alias
let built : S.Pt = { X = 5; Y = 6 }
eq "record-literal-under-the-alias" (string (built.X + built.Y)) "11"

// ---- abbreviating a LIBRARY module -------------------------------------------

module L = List
module A = Array

eq "library-abbreviation-length" (string (L.length [ 1; 2; 3 ])) "3"
eq "library-abbreviation-map" (String.concat "," (L.map string (L.filter (fun v -> v > 1) [ 1; 2; 3 ]))) "2,3"
eq "library-abbreviation-fold" (string (L.fold (fun a b -> a + b) 0 [ 1; 2; 3 ])) "6"
eq "array-abbreviation" (string (A.length [| 1; 2 |])) "2"
eq "array-abbreviation-sum" (string (A.sum [| 1; 2; 3 |])) "6"

// the abbreviated and original names interoperate
eq "mixed-library-names" (String.concat "," (List.map string (L.rev [ 1; 2 ]))) "2,1"

// ---- `open` brings a module's names in unqualified ---------------------------

module Colours =
    let red = "red"
    let blue = "blue"
    let mix (a : string) (b : string) = a + "+" + b

open Colours

eq "opened-value" red "red"
eq "opened-function" (mix red blue) "red+blue"

// the qualified name still works after the open
eq "qualified-after-open" Colours.red "red"

// a LATER binding shadows an opened one
let blue = "navy"
eq "later-binding-shadows" blue "navy"
eq "the-module-still-has-its-own" Colours.blue "blue"

// ---- a module and a value may share a name -----------------------------------

module Tag =
    let name = "tag"

let Tag2 = "not a module"
eq "module-member" Tag.name "tag"
eq "value-beside-it" Tag2 "not a module"

// ---- initialisation runs in source order, nested modules included ------------

let mutable trace = ""

module First =
    let x = (trace <- trace + "1"; 1)

module Second =
    let y = (trace <- trace + "2"; 2)

    module Third =
        let z = (trace <- trace + "3"; 3)

eq "nested-initialisation-order" trace "123"
eq "and-the-values-are-right" (string (First.x + Second.y + Second.Third.z)) "6"

// ---- functions defined across modules compose --------------------------------

module MathA =
    let double (v : int) = v * 2

module MathB =
    let triple (v : int) = v * 3
    // reaching into a SIBLING module by its qualified name
    let sextuple (v : int) = MathA.double (triple v)

module MB = MathB

eq "sibling-module-call" (string (MathB.sextuple 1)) "6"
eq "sibling-through-an-alias" (string (MB.sextuple 2)) "12"
eq "composed-across-modules" (string (MathA.double (MathB.triple 1))) "6"

printfn "DONE tests=%d failures=%d" ntests failures

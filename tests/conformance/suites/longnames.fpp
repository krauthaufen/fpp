// The portable core of fsc's longnames test: long-path access to values,
// constructors, fields and members through nested modules; qualified
// pattern matches; and the value-vs-type name-resolution precedence cases
// (bug 1218 / bug 4379 shapes). The reflection assertions
// (typeof<>.FullName, ModuleSuffix), Microsoft.FSharp.Core paths, measures
// and `module rec` do not fit the subset and are dropped.
module Core_longnames

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// long-path access to values and types through nested modules
module M1 =
    let v = 10
    module M2 =
        let w = 20
        type Opt = Nope | Yep of int
        module M3 =
            let deep = 30
            let mk (x : int) : Opt = Yep x

test "ln-val1" (M1.v = 10)
test "ln-val2" (M1.M2.w = 20)
test "ln-val3" (M1.M2.M3.deep = 30)

// constructor via a long path
let c1 = M1.M2.Yep 5
let c2 = M1.M2.Opt.Yep 6
let c3 : M1.M2.Opt = M1.M2.Nope
let c4 = M1.M2.M3.mk 7

// pattern match against constructors via long paths
test "ln-pat1" ((match c1 with M1.M2.Yep x -> x | M1.M2.Nope -> 0) = 5)
test "ln-pat2" ((match c2 with M1.M2.Opt.Yep x -> x | _ -> 0) = 6)
test "ln-pat3" ((match c3 with M1.M2.Nope -> 1 | _ -> 0) = 1)
test "ln-pat4" ((match c4 with M1.M2.Yep x -> x | _ -> 0) = 7)

// field access through a long path
module FM =
    type Rec = { contents : int }
    let mkRec (n : int) = { contents = n }

let r1 = FM.mkRec 1
test "ln-fld1" (r1.contents = 1)
let r2 : FM.Rec = { contents = 2 }
test "ln-fld2" (r2.contents = 2)

// bug 1218 shape: union type with a static member — S.A picks the CASE,
// S.C picks the static member, on the same head
module NameResolution1218 =
    type S =
        | A
        | B
        static member C = "ONE"

    let a = (S.A : S)
    let c = (S.C : string)

test "ln-1218a" ((match NameResolution1218.a with NameResolution1218.A -> 1 | _ -> 0) = 1)
test "ln-1218c" (NameResolution1218.c = "ONE")

// bug 1218 shape 2: a VALUE named like a type wins — S.A is the value's
// instance member, not anything on type S
module NameResolution1218b =
    type S =
        | SA
        | SB

    type s() =
        member x.A = 41

    let S : s = new s()

    let viaValue = (S.A : int)
    let viaParam = (fun (S : s) -> S.A : int) (new s())

test "ln-prec1" (NameResolution1218b.viaValue = 41)
test "ln-prec2" (NameResolution1218b.viaParam = 41)

// bug 4379 shape: a type's constructor used where a same-named function
// also exists — the later declaration wins
module Bug4379 =
    let foo (x : int) = x + 1

    type foo() =
        member x.P = 17

    // after the type declaration, `foo` is SHADOWED entirely: F# rejects
    // `foo 1` here with FS0501 (the ctor takes 0 arguments) — later wins
    let y = foo ()
    test "ln-4379a" (y.P = 17)

// values get added after types: the later value shadows the type name
module ValuesAfterTypes =
    module M =
        type name = string
        let name (x : int, y : int) = "1"
    let x = M.name (1, 1)
    test "ln-vat1" (x = "1")

// qualified static member through a nested-module type path
module SM =
    module Inner =
        type Box =
            static member Make (n : int) = n * 2

test "ln-stat1" (SM.Inner.Box.Make 21 = 42)

printfn "DONE tests=%d failures=%d" ntests failures

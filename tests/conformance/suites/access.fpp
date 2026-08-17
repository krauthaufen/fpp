// Ported from dotnet/fsharp tests/fsharp/core/access/test.fsx into the
// common F#/F++ subset. The original is a COMPILE test: every declaration
// kind carries every access modifier, and the program only has to build
// and run. Dropped: the val-field classes and explicit-constructor blocks
// (F++'s class model has no val fields), the signature-file round-trip
// (no .fsi), and the recursive-function/module tails that repeat shapes
// already covered. Small runtime asserts are added so the modifiers'
// SEMANTICS are observed, not just parsed — private stays usable inside
// its module and type, internal is assembly-wide.
module Core_access

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

type internal typInternal = | AAA1
type private typPrivate = | AAA2
type public typPublic = | AAA3
type typDefault = | AAA4
type internal rrr = | AAA

let internal ValInternal = 1212
let private ValPrivate = 1212
let public ValPublic = 1212
let ValDefault = 1212

// file-top-level private: usable anywhere in this file
test "vals" (ValInternal = 1212 && ValPrivate = 1212 && ValPublic = 1212 && ValDefault = 1212)
test "types"
    ((match AAA2 with AAA2 -> 1) = 1
     && (match AAA1 with AAA1 -> 2) = 2
     && (match AAA4 with AAA4 -> 4) = 4)

type MyClassStaticMembers() =
    static member internal SInternal = 12
    static member private SPrivate = 12
    static member public SPublic = 12
    static member SDefault = 12
    static member internal SMInternal () = 12
    static member private SMPrivate () = 12
    static member public SMPublic () = 12
    static member SMDefault () = 12
    // private members are reachable from the type's OWN members
    static member SumAll =
        MyClassStaticMembers.SInternal + MyClassStaticMembers.SPrivate
        + MyClassStaticMembers.SPublic + MyClassStaticMembers.SDefault
        + MyClassStaticMembers.SMInternal () + MyClassStaticMembers.SMPrivate ()
        + MyClassStaticMembers.SMPublic () + MyClassStaticMembers.SMDefault ()

test "statics" (MyClassStaticMembers.SumAll = 96)
test "statics-outside"
    (MyClassStaticMembers.SInternal + MyClassStaticMembers.SPublic
     + MyClassStaticMembers.SDefault + MyClassStaticMembers.SMInternal () = 48)

type MyClassPropertyGetters() =
    member internal x.InstInternal = 12
    member private x.InstPrivate = 12
    member public x.InstPublic = 12
    member x.InstDefault = 12
    member x.Sum = x.InstInternal + x.InstPrivate + x.InstPublic + x.InstDefault

let mcpg = MyClassPropertyGetters ()
test "getters" (mcpg.Sum = 48)
test "getters-outside" (mcpg.InstInternal + mcpg.InstPublic + mcpg.InstDefault = 36)

// modules: private is the enclosing module's own business
module Outer =
    let private secret = 41
    let internal sharedv = 2
    let visible = secret + 1
    type private Hidden = | HA of int
    let unwrap = match HA 5 with HA n -> n
    module Nested =
        // a nested module sees the parent's private bindings
        let peek = secret

test "module-access"
    (Outer.visible = 42 && Outer.sharedv = 2 && Outer.unwrap = 5 && Outer.Nested.peek = 41)

printfn "DONE tests=%d failures=%d" ntests failures

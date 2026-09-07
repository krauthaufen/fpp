// A MODULE AND A TYPE MAY SHARE A NAME.
//
// The companion-module pattern — `type DepthBias` beside `module DepthBias`
// holding the functions over it — is what F# code is written in, and fsi
// accepts exactly the program below. Here the module's binding shadowed the
// type FILE-WIDE: `DepthBias.None` (a static of the type) resolved through
// the module, found nothing, and the module NAME reached the backend as an
// unresolved variable — a trap at run time, and silent unless the build was
// `--strict`. Annotations written BEFORE the module's declaration went the
// same way.
//
// It killed the donor's companion-module pattern for the whole fpp.rendering
// port, which uses lowercase static members instead
// (~/claude/fpp-base-snags.md #39). A module is never a value, so an access
// through one now falls back to the type of that name.
module Core_modulenametype

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

[<Struct>]
type DepthBias =
    { Constant : float; SlopeScale : float }
    static member Zeroed : DepthBias = { Constant = 0.0; SlopeScale = 0.0 }
    member x.Scaled (k : float) : DepthBias = { Constant = x.Constant * k; SlopeScale = x.SlopeScale }

module DepthBias =
    let constant (value : float) : DepthBias = { Constant = value; SlopeScale = 0.0 }
    let sum (a : DepthBias) (b : DepthBias) : float = a.Constant + b.Constant

// the type's static, through the shared name
eq "a-static-member-of-the-type" (string DepthBias.Zeroed.Constant) "0"
// the module's let, through the same name
eq "a-let-of-the-module" (string (DepthBias.constant 2.0).Constant) "2"
// both in one expression
eq "both-at-once" (string (DepthBias.sum (DepthBias.constant 3.0) DepthBias.Zeroed)) "3"
// an instance member of the type, and the type used as an ANNOTATION
let bumped (b : DepthBias) : DepthBias = b.Scaled 3.0
eq "an-instance-member" (string (bumped (DepthBias.constant 1.5)).Constant) "4.5"
// a record literal of the type, resolved by its labels
let lit : DepthBias = { Constant = 7.0; SlopeScale = 1.0 }
eq "a-literal-annotated-with-the-type" (string lit.Constant + "," + string lit.SlopeScale) "7,1"

// the same shape one level down, so the name is reached through an `open`
module Inner =
    type Size = { W : int; H : int }
    module Size =
        let square (n : int) : Size = { W = n; H = n }

module Consumer =
    open Inner
    let s = Size.square 4
    let annotated (x : Size) : int = x.W * x.H

eq "shared-name-through-an-open" (string (Consumer.annotated Consumer.s)) "16"

printfn "DONE tests=%d failures=%d" ntests failures

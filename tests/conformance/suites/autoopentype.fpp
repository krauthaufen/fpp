// `[<AutoOpen>]` ON A TYPE OPENS ITS STATIC MEMBERS.
//
// The attribute was handled for modules and for typeclass declarations, and
// on an ordinary type it did nothing — a bare reference to a static member of
// an auto-opened type was an unresolved stub, which is a trap at run time and
// a `--strict` error at best. F# brings them into scope (checked against
// fsi), and the donor Aardvark.Dom auto-opens `type Dom` and `type Css`, so
// the port needed explicit re-export bindings for every one of them
// (~/claude/fpp-base-snags.md #49).
//
// The flag was also LEAKING: consumed only by modules and classes, an
// `[<AutoOpen>]` written on a type stayed pending and auto-opened whatever
// declaration came next.
module Core_autoopentype

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

[<AutoOpen; Sealed>]
type Dom =
    static member Cls (s : string) : string = "class=" + s
    static member Ident (s : string) : string = "id=" + s
    static member Wrap (a : string) (b : string) : string = a + "/" + b

// bare, through the attribute
eq "a-bare-static-of-an-autoopened-type" (Cls "x") "class=x"
eq "another-one" (Ident "y") "id=y"
eq "a-curried-one" (Wrap "a" "b") "a/b"

// the qualified spelling still works, and means the same thing
eq "and-still-qualified" (Dom.Cls "x") "class=x"

// a type declared AFTER it, with no attribute of its own, must NOT be opened
// (the flag was consumed by neither, so it leaked onto the next declaration)
[<Sealed>]
type Css =
    static member Rule (s : string) : string = "rule:" + s
eq "the-next-type-is-not-opened" (Css.Rule "r") "rule:r"

// a local binding still shadows the opened name
let Ident (s : string) : string = "local-" + s
eq "a-later-binding-shadows-it" (Ident "z") "local-z"

// through an `open`: an auto-opened type's statics come in with the module
// that declares it, which is how the donor's `open Aardvark.Dom` gets them
module Lib =
    [<AutoOpen; Sealed>]
    type Html =
        static member Tag (s : string) : string = "<" + s + ">"

module Use =
    open Lib
    let opened = Tag "p"

eq "opened-through-its-module" Use.opened "<p>"

printfn "DONE tests=%d failures=%d" ntests failures

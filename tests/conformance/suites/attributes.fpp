// ATTRIBUTES, ported from dotnet/fsharp's tests/fsharp/core/attributes and
// the PseudoCustomAttributes / SpecialAttributesAndTypes cases of
// Conformance.
//
// Most attributes are metadata a running program cannot see. The ones here
// are the exceptions — each CHANGES the meaning of the code it sits on, so
// each can be checked by running it:
//
//   [<Literal>]                a constant, so it may appear in a PATTERN
//   [<RequireQualifiedAccess>] the cases stop being visible unqualified
//   [<AutoOpen>]               the module's names arrive without an `open`
//   [<AbstractClass>]          the type cannot be instantiated
//   [<Struct>]                 the value is copied, not aliased
//
// DROPPED: everything read back through reflection (`GetCustomAttributes`,
// which the original file leans on heavily), assembly-level attributes,
// `[<Obsolete>]` (a warning, and warning text is not behaviour),
// `[<EntryPoint>]`, and `[<DllImport>]`.
module Core_attributes

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

// ---- [<Literal>]: a constant, usable where only a constant may go ----------

[<Literal>]
let MaxCount = 10

[<Literal>]
let Greeting = "hi"

[<Literal>]
let Enabled = true

[<Literal>]
let Ratio = 1.5

eq "literal-int" (string MaxCount) "10"
eq "literal-string" Greeting "hi"
eq "literal-bool" (string Enabled) "True"
eq "literal-float" (string Ratio) "1.5"

// the point of a literal: it may be MATCHED against, where an ordinary
// binding would be a fresh variable that captures everything
let classify (v : int) : string =
    match v with
    | MaxCount -> "max"
    | 0 -> "zero"
    | _ -> "other"

eq "literal-pattern-matches" (classify 10) "max"
eq "literal-pattern-falls-through" (classify 1) "other"
eq "literal-pattern-beside-a-constant" (classify 0) "zero"

let greet (s : string) : string =
    match s with
    | Greeting -> "known"
    | _ -> "unknown"

eq "string-literal-pattern" (greet "hi") "known"
eq "string-literal-pattern-other" (greet "bye") "unknown"

let flagOf (b : bool) : string =
    match b with
    | Enabled -> "on"
    | _ -> "off"

eq "bool-literal-pattern" (flagOf true) "on"
eq "bool-literal-pattern-other" (flagOf false) "off"

// a literal in ordinary arithmetic is just its value
eq "literal-in-arithmetic" (string (MaxCount * 2)) "20"
eq "literal-in-a-guard" (classify (MaxCount - 9)) "other"

// and as an array size
let sized : int[] = Array.zeroCreate MaxCount
eq "literal-as-a-size" (string sized.Length) "10"

// ---- [<RequireQualifiedAccess>]: the cases need their type's name ----------

[<RequireQualifiedAccess>]
type Colour =
    | Red
    | Green
    | Blue

let nameOf (c : Colour) : string =
    match c with
    | Colour.Red -> "red"
    | Colour.Green -> "green"
    | Colour.Blue -> "blue"

eq "qualified-case-red" (nameOf Colour.Red) "red"
eq "qualified-case-green" (nameOf Colour.Green) "green"
eq "qualified-case-blue" (nameOf Colour.Blue) "blue"

// DROPPED: the bare `Red`, which is the whole point of the attribute — it is
// a COMPILE ERROR, and the negative gate owns those.

// the cases still compare and print as themselves
test "qualified-cases-differ" (Colour.Red <> Colour.Green)
test "qualified-case-equals-itself" (Colour.Red = Colour.Red)
eq "qualified-case-printed" (string Colour.Red) "Red"

// an UNqualified union beside it keeps working, so the attribute is not
// changing the language globally
type Shade =
    | Light
    | Dark

let shadeOf (s : Shade) : string =
    match s with
    | Light -> "light"
    | Dark -> "dark"

eq "unqualified-still-works" (shadeOf Light) "light"
eq "unqualified-other-case" (shadeOf Dark) "dark"

// both in one expression
eq "both-kinds-together" (nameOf Colour.Blue + "/" + shadeOf Dark) "blue/dark"

// a qualified case in a list, and counted
let palette = [ Colour.Red; Colour.Blue; Colour.Red ]
eq "qualified-cases-in-a-list" (String.concat "," (List.map nameOf palette)) "red,blue,red"
eq "counted-by-equality" (string (List.length (List.filter (fun c -> c = Colour.Red) palette))) "2"

// ---- [<AutoOpen>]: names arrive without an `open` --------------------------

[<AutoOpen>]
module Helpers =
    let helper = 7
    let twice (v : int) = v * 2
    type Marker = { Tag : string }

// used UNQUALIFIED, with no `open Helpers` anywhere
eq "auto-opened-value" (string helper) "7"
eq "auto-opened-function" (string (twice 21)) "42"

// the qualified name works too
eq "auto-opened-still-qualifiable" (string Helpers.helper) "7"
eq "auto-opened-function-qualified" (string (Helpers.twice 4)) "8"

// and its TYPES arrive unqualified
let marked : Marker = { Tag = "t" }
eq "auto-opened-type" marked.Tag "t"

// a NON-auto-opened module needs the qualification
module Manual =
    let value = 3

eq "manual-module-qualified" (string Manual.value) "3"

// ---- [<AbstractClass>]: no instances of the base ---------------------------

[<AbstractClass>]
type Animal(name : string) =
    member _.Name = name
    abstract Sound : unit -> string
    member x.Speak () = name + " says " + x.Sound ()

type Dog() =
    inherit Animal("dog")
    override _.Sound () = "woof"

type Cat() =
    inherit Animal("cat")
    override _.Sound () = "meow"

let d = Dog ()
let c = Cat ()

eq "derived-of-an-abstract-base" (d.Speak ()) "dog says woof"
eq "other-derived" (c.Speak ()) "cat says meow"
eq "inherited-member" d.Name "dog"

// DROPPED: `Animal("x")` itself, which the attribute makes a compile error.

// the base type is still a usable REFERENCE type
let asAnimal (a : Animal) : string = a.Sound ()
eq "through-the-abstract-base" (asAnimal d) "woof"
eq "through-the-abstract-base-other" (asAnimal c) "meow"

let zoo : Animal list = [ d :> Animal; c :> Animal ]
eq "abstract-base-in-a-list" (String.concat "," (List.map (fun (a : Animal) -> a.Sound ()) zoo)) "woof,meow"

// ---- [<Struct>]: the value is COPIED --------------------------------------

[<Struct>]
type Point = { X : int; Y : int }

let p1 = { X = 1; Y = 2 }
let p2 = p1
let p3 = { p1 with Y = 9 }

eq "struct-fields" (string (p1.X + p1.Y)) "3"
eq "struct-copy-has-the-same-fields" (string (p2.X + p2.Y)) "3"
eq "copy-and-update" (string (p3.X + p3.Y)) "10"
eq "the-original-is-untouched" (string p1.Y) "2"

// structs compare by VALUE
test "structs-with-equal-fields" (p1 = p2)
test "structs-with-different-fields" (p1 <> p3)

// in a list, each element is its own value
let points = [ p1; p3 ]
eq "structs-in-a-list" (String.concat "," (List.map (fun (p : Point) -> string p.Y) points)) "2,9"

// a struct passed to a function is a copy: the callee cannot reach the caller's
let sumOf (p : Point) : int = p.X + p.Y
eq "struct-through-a-parameter" (string (sumOf p3)) "10"
eq "caller-unchanged" (string (p1.X + p1.Y)) "3"

// a struct union beside the struct record
[<Struct>]
type Choice2 =
    | Yes
    | No

let decide (c : Choice2) : string =
    match c with
    | Yes -> "y"
    | No -> "n"

eq "struct-union-yes" (decide Yes) "y"
eq "struct-union-no" (decide No) "n"
test "struct-union-equality" (Yes = Yes)
test "struct-union-inequality" (Yes <> No)

// ---- several attributes on one declaration --------------------------------

[<RequireQualifiedAccess>]
[<Struct>]
type Mode =
    | Fast
    | Slow

let speedOf (m : Mode) : string =
    match m with
    | Mode.Fast -> "fast"
    | Mode.Slow -> "slow"

eq "two-attributes-qualified" (speedOf Mode.Fast) "fast"
eq "two-attributes-other-case" (speedOf Mode.Slow) "slow"
test "two-attributes-equality" (Mode.Fast = Mode.Fast)
test "two-attributes-inequality" (Mode.Fast <> Mode.Slow)

printfn "DONE tests=%d failures=%d" ntests failures

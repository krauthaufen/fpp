// CLASS INITIALISATION, ported from dotnet/fsharp's
// Conformance/BasicGrammarElements/{StaticLet, FieldMembers,
// ImplicitObjectConstructors, ExplicitObjectConstructors,
// PropertyResolution}.
//
// A class body is not a list of declarations, it is a CONSTRUCTOR: its
// `let`s are private fields initialised in source order, its `do`s run
// between them, and all of it runs once per instance. `static let` inverts
// that — once per program, shared by every instance. The distinction is
// invisible until two objects exist, so every case here builds at least two.
//
// DROPPED: `[<ThreadStatic>]`, field initialisation observed through
// reflection, and the ordering of static initialisation ACROSS types (F#
// makes that lazy and observable only through side effects the subset here
// cannot portably time).
module Core_classinit

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

let mutable trace = ""
let note (s : string) : unit = trace <- trace + s

// ---- a `let` in a class body is a per-INSTANCE field ------------------------

type Counter(start : int) =
    let mutable n = start
    member _.Value = n
    member _.Bump () = n <- n + 1

let c1 = Counter 0
let c2 = Counter 100

c1.Bump ()
c1.Bump ()
c2.Bump ()

eq "instance-state-is-its-own" (string c1.Value) "2"
eq "the-other-instance-is-separate" (string c2.Value) "101"

// the constructor ARGUMENT is in scope for the whole body
type Greeter(name : string) =
    let greeting = "hello " + name
    member _.Greeting = greeting
    member _.Name = name

eq "ctor-argument-in-a-let" (Greeter "a").Greeting "hello a"
eq "ctor-argument-in-a-member" (Greeter "b").Name "b"

// a let may READ an earlier let
type Derived1() =
    let a = 2
    let b = a * 3
    let c = a + b
    member _.All = string a + "," + string b + "," + string c

eq "lets-see-earlier-lets" (Derived1 ()).All "2,6,8"

// ---- `do` runs between the `let`s, in source order --------------------------

type Ordered(tag : string) =
    do note (tag + "1")
    let v = (note (tag + "2"); 0)
    do note (tag + "3")
    member _.V = v

trace <- ""
let o1 = Ordered "a"
eq "body-runs-in-source-order" trace "a1a2a3"

// and again, per instance
trace <- ""
let o2 = Ordered "b"
let o3 = Ordered "c"
eq "body-runs-once-per-instance" trace "b1b2b3c1c2c3"

// nothing runs until an instance is built
type NeverBuilt() =
    do note "!"
    member _.V = 1

trace <- ""
eq "no-instance-no-body" trace ""

// ---- `static let` runs ONCE, shared by every instance -----------------------

type Registry() =
    static let mutable built = 0
    do built <- built + 1
    member _.Mine = built
    static member Built = built

let r1 = Registry ()
let r2 = Registry ()
let r3 = Registry ()

// DROPPED: a `static do` whose trace pins WHEN the static initialiser ran.
// F# runs it lazily at the type's first use, and which use counts is not
// portably observable — the shared COUNT below is the semantics that matters.
eq "static-state-is-shared" (string Registry.Built) "3"
eq "each-instance-saw-its-own-count" (string r1.Mine + string r2.Mine + string r3.Mine) "333"

// a static let holding a VALUE, not a counter
type Config() =
    static let name = "cfg"
    static member Name = name
    member _.Read = name

eq "static-value" Config.Name "cfg"
eq "static-value-through-an-instance" (Config ()).Read "cfg"
test "one-static-value-for-all" ((Config ()).Read = (Config ()).Read)

// static and instance state side by side
type Mixed(tag : string) =
    static let mutable total = 0
    let mine = tag
    do total <- total + 1
    member _.Mine = mine
    static member Total = total

let m1 = Mixed "x"
let m2 = Mixed "y"

eq "instance-half" (m1.Mine + m2.Mine) "xy"
eq "static-half" (string Mixed.Total) "2"

// ---- `val` fields, written after construction -------------------------------

type Slot() =
    [<DefaultValue>] val mutable Value : int
    [<DefaultValue>] val mutable Label : string
    member x.Describe () = string x.Value + ":" + (if isNull x.Label then "-" else x.Label)

let s1 = Slot ()
let s2 = Slot ()

eq "val-field-defaults" (s1.Describe ()) "0:-"
s1.Value <- 5
s1.Label <- "five"
eq "val-field-written" (s1.Describe ()) "5:five"
eq "the-other-slot-is-untouched" (s2.Describe ()) "0:-"

// a val field of a reference type defaults to null
test "val-reference-default-is-null" (isNull s2.Label)

// written through a member
type Holder() =
    [<DefaultValue>] val mutable N : int
    member x.Set (v : int) = x.N <- v
    member x.Get = x.N

let h = Holder ()
h.Set 9
eq "val-written-through-a-member" (string h.Get) "9"

// ---- SEVERAL constructors ---------------------------------------------------

type Point(x : int, y : int) =
    new (x : int) = Point (x, 0)
    new () = Point (0, 0)
    member _.X = x
    member _.Y = y
    member p.Sum = p.X + p.Y

eq "primary-ctor" (string (Point (3, 4)).Sum) "7"
eq "one-argument-ctor" (string (Point 5).Sum) "5"
eq "no-argument-ctor" (string (Point ()).Sum) "0"

// the delegating constructors run the primary's body, so its `let`s run too
type Traced(tag : string, n : int) =
    do note (tag + string n)
    new (tag : string) = Traced (tag, 0)
    member _.N = n

trace <- ""
let t1 = Traced ("a", 1)
let t2 = Traced "b"
eq "delegating-ctor-runs-the-primary-body" trace "a1b0"
eq "delegating-ctor-values" (string t1.N + string t2.N) "10"

// a secondary constructor that FILLS what it delegated to
type Bag() =
    let mutable items = ""
    member _.Items = items
    member _.Add (s : string) = items <- items + s
    new (xs : string list) as b =
        Bag()
        then for x in xs do b.Add x

eq "as-then-ctor" (Bag [ "a"; "b"; "c" ]).Items "abc"
eq "as-then-ctor-empty" (Bag ([] : string list)).Items ""
eq "primary-ctor-still-empty" (Bag ()).Items ""

// ---- PROPERTIES: get-only, get/set, and computed ----------------------------

type Temperature(celsius : float) =
    let mutable c = celsius
    member _.Celsius
        with get () = c
        and set (v : float) = c <- v
    member _.Fahrenheit = c * 9.0 / 5.0 + 32.0
    member _.IsFreezing = c <= 0.0

let t = Temperature 100.0
eq "computed-property" (string t.Fahrenheit) "212"
test "boolean-property" (not t.IsFreezing)

t.Celsius <- 0.0
eq "settable-property" (string t.Celsius) "0"
eq "computed-follows-the-setter" (string t.Fahrenheit) "32"
test "boolean-property-after-set" t.IsFreezing

// an AUTO property
type Named() =
    member val Name = "none" with get, set

let n1 = Named ()
let n2 = Named ()
eq "auto-property-default" n1.Name "none"
n1.Name <- "set"
eq "auto-property-written" n1.Name "set"
eq "auto-property-is-per-instance" n2.Name "none"

// a property that reads a `let`
type Wrapper(v : int) =
    let doubled = v * 2
    member _.Raw = v
    member _.Doubled = doubled
    member x.Sum = x.Raw + x.Doubled

eq "property-over-a-let" (string (Wrapper 5).Doubled) "10"
eq "property-over-properties" (string (Wrapper 5).Sum) "15"

// ---- a private `let` is not a member ----------------------------------------
// The only way to observe it is through the members that read it, which is
// the point: a class body's `let` is state, not surface.

type Encapsulated(seed : int) =
    let mutable hidden = seed
    member _.Peek = hidden
    member _.Advance () = hidden <- hidden * 2

let e = Encapsulated 1
e.Advance ()
e.Advance ()
eq "state-advanced" (string e.Peek) "4"

let e2 = Encapsulated 1
eq "a-fresh-instance-is-back-at-the-seed" (string e2.Peek) "1"
eq "and-the-first-is-unchanged" (string e.Peek) "4"

// ---- a class body that builds a COLLECTION ----------------------------------

type Accum(xs : int list) =
    let total = List.fold (fun a b -> a + b) 0 xs
    let count = List.length xs
    member _.Total = total
    member _.Count = count
    member _.Mean = if count = 0 then 0 else total / count

let acc = Accum [ 1; 2; 3; 4 ]
eq "let-computed-from-an-argument" (string acc.Total) "10"
eq "second-let" (string acc.Count) "4"
eq "member-over-two-lets" (string acc.Mean) "2"

let empty = Accum []
eq "empty-total" (string empty.Total) "0"
eq "empty-mean-guards" (string empty.Mean) "0"

printfn "DONE tests=%d failures=%d" ntests failures

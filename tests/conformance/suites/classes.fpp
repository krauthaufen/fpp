// CLASS TYPES, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/ObjectOrientedTypeDefini-
// tions (ClassTypes: AsDeclarations, InheritsDeclarations, MemberDeclarations,
// StaticLetDoDeclarations, AutoProperties; AbstractMembers; InterfaceTypes).
//
// The shapes here are the ones a program actually leans on: a primary
// constructor with `let` state, members that read it, an `as` self-name,
// abstract members with defaults, `base.` calls through an override chain,
// interfaces implemented by several classes, and static state.
//
// DROPPED: attributes on class-local `let`s, units of measure, delegates,
// struct types with explicit layout, and the CROSS-LANGUAGE (C#) cases.
module Core_classes

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- a primary constructor, its state and its members --------------------

type Point (x : float, y : float) =
    member _.X = x
    member _.Y = y
    member this.LengthSq = this.X * this.X + this.Y * this.Y
    member _.Shifted (dx : float) = Point (x + dx, y)

let pt = Point (3.0, 4.0)

test "ctor-fields" (pt.X = 3.0 && pt.Y = 4.0)
test "member-uses-this" (pt.LengthSq = 25.0)
test "member-returns-own-type" ((pt.Shifted 1.0).X = 4.0)

// the `as` name is the same object as `this`
type Named (n : string) as self =
    member _.Name = n
    member _.Upper = self.Name + "!"

test "as-self" (Named("a").Upper = "a!")

// class-local `let` state, and a `do` that runs at construction
type Counter (start : int) =
    let mutable n = start
    let doubled = start * 2
    member _.Value = n
    member _.Doubled = doubled
    member _.Bump () = n <- n + 1
    member _.BumpBy (k : int) = n <- n + k

let c = Counter 5
c.Bump ()
c.BumpBy 3

test "let-state" (c.Value = 9)
test "let-computed" (c.Doubled = 10)

// each instance has its own state
let c2 = Counter 0
c2.Bump ()
test "instances-separate" (c.Value = 9 && c2.Value = 1)

// ---- static members and static state -------------------------------------

type Registry () =
    static let mutable count = 0
    static member Register () = count <- count + 1
    static member Count = count
    static member Zero = 0

Registry.Register ()
Registry.Register ()

test "static-state" (Registry.Count = 2)
test "static-member" (Registry.Zero = 0)

// ---- abstract members, defaults and overrides ----------------------------

type Shape () =
    abstract Area : unit -> float
    default _.Area () = 0.0
    abstract Name : string
    default _.Name = "shape"
    member this.Describe = this.Name + ":" + string (this.Area ())

type Square (side : float) =
    inherit Shape ()
    override _.Area () = side * side
    override _.Name = "square"

type Blob () =
    inherit Shape ()
    // takes both defaults

let sq = Square 3.0
let bl = Blob ()

test "override-method" (sq.Area () = 9.0)
test "override-property" (sq.Name = "square")
test "default-method" (bl.Area () = 0.0)
test "default-property" (bl.Name = "shape")
test "base-member-uses-override" (sq.Describe = "square:9")
test "base-member-uses-default" (bl.Describe = "shape:0")

// a base class reference sees the OVERRIDE (virtual dispatch)
let asShape (s : Shape) = s.Area ()

test "virtual-dispatch" (asShape sq = 9.0 && asShape bl = 0.0)

// ---- `base.` reaches the definition one level up -------------------------

type Base () =
    abstract Speak : unit -> string
    default _.Speak () = "base"

type Derived () =
    inherit Base ()
    member this.FromBase = base.Speak ()
    member this.FromThis = this.Speak ()
    override _.Speak () = "derived"

let d = Derived ()

test "base-call" (d.FromBase = "base")
test "this-call" (d.FromThis = "derived")
test "override-direct" (d.Speak () = "derived")

// ---- interfaces ----------------------------------------------------------

type IGreeter =
    abstract Greet : string -> string
    abstract Punctuation : string

type Polite () =
    interface IGreeter with
        member _.Greet n = "Hello, " + n
        member _.Punctuation = "."

type Loud () =
    interface IGreeter with
        member _.Greet n = "HEY " + n
        member _.Punctuation = "!"

let greetWith (g : IGreeter) (n : string) = (g.Greet n) + g.Punctuation

test "iface-first" (greetWith (Polite () :> IGreeter) "a" = "Hello, a.")
test "iface-second" (greetWith (Loud () :> IGreeter) "a" = "HEY a!")

// the same object through both its class and its interface
let p = Polite ()
test "iface-upcast" (greetWith (p :> IGreeter) "b" = "Hello, b.")

// a list of implementations dispatches per element
let greeters : IGreeter list = [ Polite () :> IGreeter; Loud () :> IGreeter ]
test "iface-list" (List.map (fun (g : IGreeter) -> g.Greet "x") greeters = [ "Hello, x"; "HEY x" ])

// ---- a generic class -----------------------------------------------------

type Box<'a> (v : 'a) =
    member _.Value = v
    member _.Map (f : 'a -> 'b) = Box<'b> (f v)

let bi = Box 3
test "generic-class" (bi.Value = 3)
test "generic-map" ((bi.Map (fun n -> string n)).Value = "3")
test "generic-string" ((Box "s").Value = "s")

// a generic class holding a collection
type Stack<'a> () =
    let mutable items : 'a list = []
    member _.Push (v : 'a) = items <- v :: items
    member _.Peek = List.head items
    member _.Count = List.length items

let st = Stack<int> ()
st.Push 1
st.Push 2

test "generic-state-count" (st.Count = 2)
test "generic-state-peek" (st.Peek = 2)

// ---- members that take several arguments, and property setters -----------

type Rect (w : int, h : int) =
    let mutable width = w
    let mutable height = h
    member _.Width with get () = width and set (v : int) = width <- v
    member _.Height = height
    member _.Scale (fx : int, fy : int) = Rect (width * fx, height * fy)
    member _.Area () = width * height

let r = Rect (2, 3)
r.Width <- 4

test "property-setter" (r.Width = 4)
test "tupled-member" ((r.Scale (2, 3)).Area () = 8 * 9)
test "member-method" (r.Area () = 12)

// ---- an object expression implements an interface on the spot ------------

let anon =
    { new IGreeter with
        member _.Greet n = "anon " + n
        member _.Punctuation = "?" }

test "object-expression" (greetWith anon "z" = "anon z?")

printfn "DONE tests=%d failures=%d" ntests failures

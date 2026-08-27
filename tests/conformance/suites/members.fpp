// MEMBERS AND VIRTUAL DISPATCH, ported from dotnet/fsharp's
// tests/fsharp/core/members (basics, ops, factors) and the
// ObjectOrientedTypeDefinitions cases of Conformance.
//
// A member call picks its implementation from the value's RUN-TIME type, not
// from the type the reference is written at. That one sentence is what this
// suite checks, from every angle that can tell the two apart: a base-typed
// reference to a derived value, a three-level chain where the middle level
// overrides, `base.M ()` reaching past an override, and a virtual called
// from a base-class method that the derived type has overridden underneath
// it. Properties, statics and indexers follow, since they dispatch by the
// same rules.
//
// DROPPED: explicit interface implementations reached without an upcast (F#
// requires the upcast, and the casts suite owns it), `member val` with
// CLIMutable, events, and abstract classes with no implementation at all —
// there is nothing to call.
module Core_members

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

// ---- abstract with a default, and an override -------------------------------

type Shape() =
    abstract Name : unit -> string
    default _.Name () = "shape"
    abstract Area : unit -> int
    default _.Area () = 0
    // a CONCRETE method that calls the virtuals: whatever overrides them
    // underneath it is what runs
    member x.Describe () = x.Name () + ":" + string (x.Area ())

type Square(side : int) =
    inherit Shape()
    override _.Name () = "square"
    override _.Area () = side * side

type Circle(r : int) =
    inherit Shape()
    override _.Area () = 3 * r * r
    // Name is NOT overridden: the default answers

let sq = Square 3
let ci = Circle 2
let sh = Shape ()

eq "default-when-not-overridden" (sh.Name ()) "shape"
eq "override-replaces-the-default" (sq.Name ()) "square"
eq "partial-override-keeps-the-default" (ci.Name ()) "shape"
eq "overridden-area" (string (sq.Area ())) "9"
eq "other-override" (string (ci.Area ())) "12"

// the base-class method dispatches to the OVERRIDES, not to its own defaults
eq "base-method-calls-the-override" (sq.Describe ()) "square:9"
eq "base-method-mixed" (ci.Describe ()) "shape:12"
eq "base-method-on-the-base" (sh.Describe ()) "shape:0"

// ---- a BASE-TYPED reference still runs the derived implementation -----------

let asShape (s : Shape) : string = s.Name () + "/" + string (s.Area ())

eq "through-a-base-parameter" (asShape sq) "square/9"
eq "through-a-base-parameter-other" (asShape ci) "shape/12"

let upcast1 = sq :> Shape
eq "through-an-explicit-upcast" (upcast1.Name ()) "square"
eq "upcast-describe" (upcast1.Describe ()) "square:9"

// a LIST of the base type holds both, and each answers for itself
let shapes : Shape list = [ sq :> Shape; ci :> Shape; sh ]
eq "dispatch-per-element" (String.concat "," (List.map (fun (s : Shape) -> s.Name ()) shapes)) "square,shape,shape"
eq "dispatch-per-element-area" (String.concat "," (List.map (fun (s : Shape) -> string (s.Area ())) shapes)) "9,12,0"

// ---- THREE levels, with the middle one overriding ---------------------------

type A1() =
    abstract Tag : unit -> string
    default _.Tag () = "A"
    member x.Chain () = "<" + x.Tag () + ">"

type B1() =
    inherit A1()
    override _.Tag () = "B"

type C1() =
    inherit B1()
    override _.Tag () = "C"

type D1() =
    inherit B1()
    // no override: B's answers, not A's

eq "level-one" ((A1 ()).Tag ()) "A"
eq "level-two" ((B1 ()).Tag ()) "B"
eq "level-three" ((C1 ()).Tag ()) "C"
eq "inherits-the-middle-override" ((D1 ()).Tag ()) "B"

eq "chain-at-one" ((A1 ()).Chain ()) "<A>"
eq "chain-at-three" ((C1 ()).Chain ()) "<C>"
eq "chain-skips-a-level" ((D1 ()).Chain ()) "<B>"

// through the topmost base type
let asA (a : A1) : string = a.Tag ()
eq "three-levels-through-base" (String.concat "" (List.map asA [ A1 (); B1 () :> A1; C1 () :> A1; D1 () :> A1 ])) "ABCB"

// ---- base.M () reaches PAST the override ------------------------------------

type Loud() =
    abstract Say : unit -> string
    default _.Say () = "quiet"

type Louder() =
    inherit Loud()
    override x.Say () = "LOUD(" + base.Say () + ")"

type Loudest() =
    inherit Louder()
    override x.Say () = "!" + base.Say () + "!"

eq "base-call-from-an-override" ((Louder ()).Say ()) "LOUD(quiet)"
eq "base-call-two-levels" ((Loudest ()).Say ()) "!LOUD(quiet)!"

// ---- PROPERTIES dispatch the same way ---------------------------------------

type Counter() =
    let mutable n = 0
    abstract Step : int
    default _.Step = 1
    member _.Value = n
    member x.Bump () = n <- n + x.Step

type ByTwo() =
    inherit Counter()
    override _.Step = 2

let c1 = Counter ()
c1.Bump ()
c1.Bump ()
eq "property-default" (string c1.Value) "2"

let c2 = ByTwo ()
c2.Bump ()
c2.Bump ()
eq "overridden-property" (string c2.Value) "4"
eq "property-read-directly" (string c2.Step) "2"

// a settable property
type Holder() =
    let mutable v = 0
    member _.Item
        with get () = v
        and set (x : int) = v <- x

let h = Holder ()
eq "settable-property-initial" (string h.Item) "0"
h.Item <- 42
eq "settable-property-after-write" (string h.Item) "42"

// an AUTO property with a setter
type Auto() =
    member val Label = "none" with get, set

let au = Auto ()
eq "auto-property-initial" au.Label "none"
au.Label <- "set"
eq "auto-property-after-write" au.Label "set"

// two instances have two properties
let au2 = Auto ()
eq "auto-property-is-per-instance" (au.Label + "/" + au2.Label) "set/none"

// ---- STATIC members ---------------------------------------------------------

type MathBits =
    static member Double (v : int) = v * 2
    static member Zero = 0
    static member Combine (a : int, b : int) = a + b

eq "static-method" (string (MathBits.Double 21)) "42"
eq "static-property" (string MathBits.Zero) "0"
eq "static-two-arguments" (string (MathBits.Combine (1, 2))) "3"

// a static member on a type that also has instance members
type Mixed(n : int) =
    member _.N = n
    static member Make (v : int) = Mixed v
    static member Sum (a : Mixed, b : Mixed) = a.N + b.N

let m1 = Mixed.Make 4
let m2 = Mixed.Make 5
eq "static-factory" (string m1.N) "4"
eq "static-over-instances" (string (Mixed.Sum (m1, m2))) "9"

// ---- members on a GENERIC class ---------------------------------------------

type Box<'a>(v : 'a) =
    member _.Value = v
    member _.Map (f : 'a -> 'b) = Box<'b> (f v)
    member x.Show (f : 'a -> string) = "[" + f x.Value + "]"

let bi = Box 5
eq "generic-member" (string bi.Value) "5"
eq "generic-member-mapped" (string (bi.Map (fun v -> v + 1)).Value) "6"
eq "generic-member-across-types" ((bi.Map (fun v -> string v)).Value) "5"
eq "generic-show" (bi.Show (fun v -> string v)) "[5]"

let bs = Box "s"
eq "generic-at-another-type" bs.Value "s"
eq "generic-show-string" (bs.Show (fun v -> v + v)) "[ss]"

// a generic class with a virtual member
type Wrap<'a>(v : 'a) =
    abstract Render : unit -> string
    default x.Render () = "wrap"
    member _.Item2 = v

type WrapInt(v : int) =
    inherit Wrap<int>(v)
    override x.Render () = "int:" + string x.Item2

eq "generic-base-default" ((Wrap 1).Render ()) "wrap"
eq "generic-base-override" ((WrapInt 7).Render ()) "int:7"
eq "generic-base-through-base" ((WrapInt 7 :> Wrap<int>).Render ()) "int:7"

// ---- members that take and return the OWN type -------------------------------

type Vec(x : int, y : int) =
    member _.X = x
    member _.Y = y
    member _.Add (o : Vec) = Vec (x + o.X, y + o.Y)
    member _.Scale (k : int) = Vec (x * k, y * k)
    member v.Show () = "(" + string v.X + "," + string v.Y + ")"

let v1 = Vec (1, 2)
let v2 = Vec (3, 4)
eq "member-returning-own-type" ((v1.Add v2).Show ()) "(4,6)"
eq "chained-members" ((v1.Add(v2).Scale 2).Show ()) "(8,12)"
eq "chained-three" ((v1.Scale(2).Add(v2).Scale 1).Show ()) "(5,8)"

// ---- a member used as a FUNCTION value ---------------------------------------

let describeAll = List.map (fun (s : Shape) -> s.Describe ())
eq "member-in-a-lambda" (String.concat ";" (describeAll shapes)) "square:9;shape:12;shape:0"

// ---- a member calling ANOTHER member of the same object ----------------------

type SelfCalls(n : int) =
    member _.Base = n
    member x.Twice = x.Base * 2
    member x.Quad = x.Twice * 2
    member x.All () = string x.Base + "," + string x.Twice + "," + string x.Quad

eq "member-reads-member" ((SelfCalls 3).All ()) "3,6,12"

// and one that recurses through a virtual
type Rec1() =
    abstract Step : int -> int
    default _.Step v = v - 1
    member x.Down (v : int) : int = if v <= 0 then 0 else x.Down (x.Step v)

type ByTwoDown() =
    inherit Rec1()
    override _.Step v = v - 2

eq "virtual-in-a-recursion" (string ((Rec1 ()).Down 3)) "0"
eq "overridden-virtual-in-a-recursion" (string ((ByTwoDown ()).Down 4)) "0"

// ---- a member with a TUPLE parameter versus a curried one -------------------

type Args() =
    member _.Tupled (a : int, b : int) = a - b
    member _.Curried (a : int) (b : int) = a - b

let ar = Args ()
eq "tupled-member" (string (ar.Tupled (10, 3))) "7"
eq "curried-member" (string (ar.Curried 10 3)) "7"
eq "curried-partially-applied" (string (List.map (ar.Curried 10) [ 1; 2 ])) "[9; 8]"

printfn "DONE tests=%d failures=%d" ntests failures

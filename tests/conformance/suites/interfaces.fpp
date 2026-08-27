// INTERFACES, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/ObjectOrientedType-
// Definitions (InterfaceTypes) and the interface cases of
// tests/fsharp/core/members.
//
// An interface in F# is always implemented EXPLICITLY: the members do not
// join the type's own surface, so reaching them takes an upcast. That is the
// first thing this suite pins, because it is what separates an interface
// from a base class here. After that it is dispatch — one type implementing
// several interfaces, one interface implemented by several types, an
// interface that inherits another, and a generic interface at two
// instantiations — plus the type tests that ask at run time which of them a
// value satisfies.
//
// DROPPED: default implementations on the interface itself (a C# 8 feature
// F# consumes but does not declare), static abstract members, and explicit
// implementation of two interfaces that declare the SAME member name — F#
// resolves that by the annotation on the upcast, and it needs a C#-declared
// pair to be worth testing.
module Core_interfaces

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

// ---- one interface, one implementation --------------------------------------

type INamed =
    abstract Name : unit -> string

type Person(n : string) =
    member _.Raw = n
    interface INamed with
        member _.Name () = "person:" + n

let p = Person "ann"

// the type's OWN surface still works
eq "own-member" p.Raw "ann"

// the interface member takes an upcast — this is the whole point
eq "through-an-upcast" ((p :> INamed).Name ()) "person:ann"

let asNamed (x : INamed) : string = x.Name ()
eq "through-an-interface-parameter" (asNamed p) "person:ann"

// DROPPED: `p.Name ()` without the upcast. F# rejects it (the member is not
// on Person), so the oracle cannot compile the case.

// ---- one interface, SEVERAL implementations ---------------------------------

type Robot(id : int) =
    interface INamed with
        member _.Name () = "robot#" + string id

type Anon() =
    interface INamed with
        member _.Name () = "?"

eq "second-implementation" (asNamed (Robot 7)) "robot#7"
eq "third-implementation" (asNamed (Anon ())) "?"

// a LIST of the interface holds all three, each answering for itself
let named : INamed list = [ Person "bo" :> INamed; Robot 1 :> INamed; Anon () :> INamed ]
eq "dispatch-per-element" (String.concat "," (List.map (fun (x : INamed) -> x.Name ()) named)) "person:bo,robot#1,?"
eq "dispatch-through-a-fold"
   (List.fold (fun acc (x : INamed) -> acc + "/" + x.Name ()) "" named)
   "/person:bo/robot#1/?"

// ---- one type, SEVERAL interfaces --------------------------------------------

type ISized =
    abstract Size : unit -> int

type ITagged =
    abstract Tag : string

type Blob(n : int, t : string) =
    interface INamed with
        member _.Name () = "blob"
    interface ISized with
        member _.Size () = n
    interface ITagged with
        member _.Tag = t

let b = Blob (5, "x")

eq "first-interface" ((b :> INamed).Name ()) "blob"
eq "second-interface" (string ((b :> ISized).Size ())) "5"
eq "third-interface-property" ((b :> ITagged).Tag) "x"

// each upcast reaches the same object
let sameObject = Blob (9, "y")
eq "several-views-one-object"
   ((sameObject :> INamed).Name () + string ((sameObject :> ISized).Size ()) + (sameObject :> ITagged).Tag)
   "blob9y"

// ---- an interface that INHERITS another --------------------------------------

type IShape =
    abstract Area : unit -> int

type INamedShape =
    inherit IShape
    abstract Label : unit -> string

type Rect(w : int, h : int) =
    interface INamedShape with
        member _.Label () = "rect"
        member _.Area () = w * h

let r = Rect (3, 4)

eq "derived-interface-member" ((r :> INamedShape).Label ()) "rect"
eq "inherited-interface-member" (string ((r :> INamedShape).Area ())) "12"

// the value satisfies the BASE interface too, and can be upcast straight to it
eq "upcast-to-the-base-interface" (string ((r :> IShape).Area ())) "12"

let areaOf (s : IShape) : int = s.Area ()
eq "base-interface-parameter" (string (areaOf r)) "12"

// and through the derived one, then widened
let widened = (r :> INamedShape) :> IShape
eq "widened-in-two-steps" (string (widened.Area ())) "12"

// ---- a GENERIC interface at two instantiations -------------------------------

type IContainer<'a> =
    abstract Get : unit -> 'a
    abstract Describe : unit -> string

type IntBox(v : int) =
    interface IContainer<int> with
        member _.Get () = v
        member _.Describe () = "int:" + string v

type StrBox(v : string) =
    interface IContainer<string> with
        member _.Get () = v
        member _.Describe () = "str:" + v

eq "generic-interface-at-int" (string ((IntBox 3 :> IContainer<int>).Get ())) "3"
eq "generic-interface-at-string" ((StrBox "s" :> IContainer<string>).Get ()) "s"
eq "generic-interface-describe-int" ((IntBox 3 :> IContainer<int>).Describe ()) "int:3"
eq "generic-interface-describe-string" ((StrBox "s" :> IContainer<string>).Describe ()) "str:s"

// a function generic in the element, taking the interface
let getFrom (c : IContainer<'a>) : 'a = c.Get ()
eq "generic-function-over-the-interface-int" (string (getFrom (IntBox 4 :> IContainer<int>))) "4"
eq "generic-function-over-the-interface-string" (getFrom (StrBox "t" :> IContainer<string>)) "t"

// one type implementing the SAME generic interface is still one vtable per
// instantiation — a list at one instantiation holds only that one
let intBoxes : IContainer<int> list = [ IntBox 1 :> IContainer<int>; IntBox 2 :> IContainer<int> ]
eq "generic-interface-list" (String.concat "," (List.map (fun (c : IContainer<int>) -> string (c.Get ())) intBoxes)) "1,2"

// ---- a generic CLASS implementing a generic interface ------------------------

type Pair<'a>(a : 'a, b : 'a) =
    member _.First = a
    interface IContainer<'a> with
        member _.Get () = a
        member _.Describe () = "pair"

let pi = Pair (10, 20)
let ps = Pair ("p", "q")

eq "generic-class-generic-interface-int" (string ((pi :> IContainer<int>).Get ())) "10"
eq "generic-class-generic-interface-string" ((ps :> IContainer<string>).Get ()) "p"
eq "generic-class-own-member" (string pi.First) "10"
eq "generic-class-describe" ((pi :> IContainer<int>).Describe ()) "pair"

// ---- TYPE TESTS against an interface -----------------------------------------

let describeAny (o : obj) : string =
    match o with
    | :? INamed as n -> "named:" + n.Name ()
    | :? ISized as s -> "sized:" + string (s.Size ())
    | _ -> "other"

eq "type-test-picks-the-interface" (describeAny (Person "z")) "named:person:z"
eq "type-test-second-interface" (describeAny (Rect (1, 1))) "other"
eq "type-test-falls-through" (describeAny 5) "other"

// a value implementing BOTH takes the FIRST matching clause
eq "type-test-takes-the-first-match" (describeAny (Blob (2, "t"))) "named:blob"

// the test as a boolean
test "is-the-interface" ((Person "q") :> obj :? INamed)
test "is-not-the-interface" (not ((5 :> obj) :? INamed))

// ---- an interface implemented by an OBJECT EXPRESSION ------------------------

let literal = { new INamed with
                  member _.Name () = "literal" }

eq "object-expression-implements-it" (asNamed literal) "literal"

// and it mixes with the class implementations in the same list
let mixed : INamed list = [ literal; Person "m" :> INamed ]
eq "object-expression-in-a-list" (String.concat "," (List.map (fun (x : INamed) -> x.Name ()) mixed)) "literal,person:m"

// an object expression capturing a local
let makeNamed (s : string) : INamed =
    { new INamed with
        member _.Name () = "made:" + s }

eq "object-expression-captures" (asNamed (makeNamed "cap")) "made:cap"
eq "two-captures-are-separate" (asNamed (makeNamed "a") + asNamed (makeNamed "b")) "made:amade:b"

// one implementing the inherited pair
let bothLevels =
    { new INamedShape with
        member _.Label () = "obj"
        member _.Area () = 6 }

eq "object-expression-derived-member" ((bothLevels :> INamedShape).Label ()) "obj"
eq "object-expression-inherited-member" (string (areaOf (bothLevels :> IShape))) "6"

// ---- an interface value stored in a FIELD -------------------------------------

type Holder(inner : INamed) =
    member _.Inner = inner
    member _.Show () = "<" + inner.Name () + ">"

eq "interface-in-a-field" ((Holder (Person "h")).Show ()) "<person:h>"
eq "interface-field-read-back" ((Holder (Robot 2)).Inner.Name ()) "robot#2"

// swapped for another implementation, the holder does not care
eq "interface-field-is-polymorphic"
   (String.concat "," (List.map (fun (x : INamed) -> (Holder x).Show ()) named))
   "<person:bo>,<robot#1>,<?>"

printfn "DONE tests=%d failures=%d" ntests failures

// OVERLOAD RESOLUTION, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Tiebreakers and the
// MethodApplicationResolution cases of InferenceProcedures.
//
// A call names a member; the ARGUMENTS choose which one. The cases that
// matter are the ones where more than one candidate fits: an exact type
// against a generic one, a base class against a derived one, and an
// argument whose own type is only decided by the call it is nested in.
// Every check here is a call whose ANSWER names the member that ran, so a
// wrong choice is visible rather than merely type-correct.
//
// DROPPED: overloads that differ only by an attribute
// (`[<OverloadResolutionPriority>]`), C#-declared overloads, and `out`
// parameters — the out-parameter view has its own gate.
module Core_overloads

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// ---- by ARITY ---------------------------------------------------------------

type ByArity =
    static member M () = "none"
    static member M (a : int) = "one"
    static member M (a : int, b : int) = "two"
    static member M (a : int, b : int, c : int) = "three"

eq "arity-zero" (ByArity.M ()) "none"
eq "arity-one" (ByArity.M 1) "one"
eq "arity-two" (ByArity.M (1, 2)) "two"
eq "arity-three" (ByArity.M (1, 2, 3)) "three"

// ---- by argument TYPE -------------------------------------------------------

type ByType =
    static member M (a : int) = "int"
    static member M (a : float) = "float"
    static member M (a : float32) = "float32"
    static member M (a : string) = "string"
    static member M (a : char) = "char"
    static member M (a : bool) = "bool"
    static member M (a : int64) = "int64"

eq "type-int" (ByType.M 1) "int"
eq "type-float" (ByType.M 1.0) "float"
eq "type-float32" (ByType.M 1.0f) "float32"
eq "type-string" (ByType.M "s") "string"
eq "type-char" (ByType.M 'c') "char"
eq "type-bool" (ByType.M true) "bool"
eq "type-int64" (ByType.M 1L) "int64"

// the same by POSITION: two arguments of different types pick different members
type ByPosition =
    static member M (a : int, b : string) = "int-string"
    static member M (a : string, b : int) = "string-int"
    static member M (a : int, b : int) = "int-int"

eq "position-int-string" (ByPosition.M (1, "a")) "int-string"
eq "position-string-int" (ByPosition.M ("a", 1)) "string-int"
eq "position-int-int" (ByPosition.M (1, 2)) "int-int"

// ---- CONTAINERS as arguments -------------------------------------------------

type ByContainer =
    static member M (a : int[]) = "array"
    static member M (a : int list) = "list"
    static member M (a : int option) = "option"
    static member M (a : int * int) = "tuple"

eq "container-array" (ByContainer.M [| 1 |]) "array"
eq "container-list" (ByContainer.M [ 1 ]) "list"
eq "container-option" (ByContainer.M (Some 1)) "option"
eq "container-tuple" (ByContainer.M ((1, 2) : int * int)) "tuple"

// the ELEMENT type distinguishes two list overloads
type ByElement =
    static member M (a : int list) = "ints"
    static member M (a : string list) = "strings"

eq "element-ints" (ByElement.M [ 1 ]) "ints"
eq "element-strings" (ByElement.M [ "a" ]) "strings"
eq "element-empty-ints" (ByElement.M ([] : int list)) "ints"

// ---- the TIEBREAKERS ---------------------------------------------------------

// an EXACT type beats a generic one
type ExactBeatsGeneric =
    static member M (a : int) = "int"
    static member M (a : 'a) = "generic"

eq "exact-beats-generic" (ExactBeatsGeneric.M 1) "int"
eq "generic-takes-the-rest" (ExactBeatsGeneric.M "s") "generic"
eq "generic-takes-a-list" (ExactBeatsGeneric.M [ 1 ]) "generic"

// a DERIVED class beats its base
type Base() =
    member _.Tag = "b"

type Derived() =
    inherit Base()
    member _.Extra = 1

type BySubtype =
    static member M (a : Base) = "base"
    static member M (a : Derived) = "derived"

eq "base-argument" (BySubtype.M (Base ())) "base"
eq "derived-argument" (BySubtype.M (Derived ())) "derived"

// a derived value UPCAST explicitly takes the base member
let asBase = Derived () :> Base
eq "upcast-argument" (BySubtype.M asBase) "base"

// ---- instance members overload the same way ---------------------------------

type Instance() =
    member _.M (a : int) = "int"
    member _.M (a : string) = "string"
    member _.M (a : int, b : int) = "two"

let inst = Instance ()

eq "instance-int" (inst.M 1) "int"
eq "instance-string" (inst.M "s") "string"
eq "instance-two" (inst.M (1, 2)) "two"

// ---- CONSTRUCTORS overload too ----------------------------------------------

type Point(x : int, y : int) =
    new (x : int) = Point (x, 0)
    new () = Point (0, 0)
    member _.Sum = x + y

eq "ctor-two" (string (Point(3, 4)).Sum) "7"
eq "ctor-one" (string (Point 5).Sum) "5"
eq "ctor-none" (string (Point ()).Sum) "0"

// ---- OPTIONAL parameters -----------------------------------------------------

type WithOptional =
    static member M (a : int, ?b : int) =
        match b with
        | Some v -> a + v
        | None -> a

eq "optional-omitted" (string (WithOptional.M 1)) "1"
eq "optional-given" (string (WithOptional.M (1, b = 2))) "3"

// ---- the argument's type comes FROM the call ---------------------------------

// the inner call's result decides the outer member: `C.M 5` is an int, and
// `string` of it is a string, so the outer call takes the string member
type Nested =
    static member M (a : int) = 1
    static member M (a : string) = 2

eq "nested-choice" (string (Nested.M (string (Nested.M 5)))) "2"
eq "nested-inner-choice" (string (Nested.M 5)) "1"

// through a PIPE, where the argument is written first
eq "piped-argument" (string (5 |> Nested.M)) "1"
eq "piped-string-argument" (string ("s" |> Nested.M)) "2"

// as an argument to another function
let apply (f : int -> string) (v : int) : string = f v
eq "member-as-a-function" (apply (fun v -> string (Nested.M v)) 3) "1"

// ---- OPERATORS are overloads on the type ------------------------------------

type V(x : int) =
    member _.X = x
    static member (+) (a : V, b : V) = V (a.X + b.X)
    static member (-) (a : V, b : V) = V (a.X - b.X)
    static member (*) (a : V, k : int) = V (a.X * k)

eq "operator-plus" (string (V 1 + V 2).X) "3"
eq "operator-minus" (string (V 5 - V 2).X) "3"
eq "operator-times-scalar" (string (V 3 * 2).X) "6"

// the built-in operators are untouched by a user's
eq "builtin-plus-still-int" (string (1 + 2)) "3"
eq "builtin-plus-still-string" ("a" + "b") "ab"
eq "builtin-plus-still-float" (string (1.5 + 1.5)) "3"

// ---- an inline function resolves its operator per USE ------------------------

let inline addBoth (a : ^a) (b : ^a) = a + b

eq "inline-on-int" (string (addBoth 1 2)) "3"
eq "inline-on-float" (string (addBoth 1.5 1.5)) "3"
eq "inline-on-string" (addBoth "a" "b") "ab"

// ---- a member used at several types in ONE expression -----------------------

eq "several-types-one-expression"
   (ByType.M 1 + "," + ByType.M "s" + "," + ByType.M 1.0)
   "int,string,float"

// and inside a list, where every element is a separate resolution
let answers = [ ByType.M 1; ByType.M 'c'; ByType.M true ]
eq "resolved-per-element" (String.concat "," answers) "int,char,bool"

printfn "DONE tests=%d failures=%d" ntests failures

// THE `nameof` OPERATOR, ported from dotnet/fsharp's
// tests/fsharp/core/nameof/preview/test.fsx.
//
// `nameof x` is the SOURCE name of what `x` refers to, decided at compile
// time and never evaluated. The cases that matter are the ones where the
// name is not the whole expression: a dotted path is named by its LAST
// segment, type arguments are not part of the name, an operator names
// itself, and a user binding called `nameof` SHADOWS the operator.
//
// DROPPED: `nameof<'T>` on a type parameter, method groups with a type
// ascription (`nameof(this.M : (float * int64 -> _))`), quotations,
// attributes, units of measure, and namespace/module names — none of those
// spellings exist here.
module Core_nameofop

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// ---- local bindings --------------------------------------------------------

let ``local variable name lookup`` () : unit =
    let a = 0
    eq "local-variable" (nameof a) "a"
    let b = nameof a
    eq "local-of-local" (nameof b) "b"

``local variable name lookup`` ()

let ``local function names`` () : unit =
    let myFunction x = 0 * x
    eq "local-int-function" (nameof myFunction) "myFunction"
    let curriedFunction x y = x * y
    eq "local-curried-function" (nameof curriedFunction) "curriedFunction"
    let tupledFunction (x, y) = x * y
    eq "local-tupled-function" (nameof tupledFunction) "tupledFunction"
    let unitFunction () = 1
    eq "local-unit-function" (nameof (unitFunction)) "unitFunction"

``local function names`` ()

// a PARAMETER is named where it is bound, not where the call passes a value
let paramName parameter1 = nameof parameter1
eq "local-function-parameter" (paramName "x") "parameter1"

// from INSIDE a recursive function, naming itself
let rec myLocalFunction (x : int) : string =
    let z = 2 * x
    nameof myLocalFunction + " " + string z

eq "name-from-inside-local-function" (myLocalFunction 23) "myLocalFunction 46"

// a top-level binding, and one that is not applied
let topLevelValue = 7
let topLevelFunction (v : int) : int = v
eq "top-level-value" (nameof topLevelValue) "topLevelValue"
eq "top-level-function" (nameof topLevelFunction) "topLevelFunction"

// ---- members ---------------------------------------------------------------

type BasicNameOfTests() =
    member this.MemberMethod () = 0
    member this.MemberProperty = this.MemberMethod ()
    static member StaticMethod () = 0
    static member StaticProperty = BasicNameOfTests.StaticMethod ()
    member this.MemberMethodDefinedBelow (x : int, y : int) = x * y
    member this.get_XYZ () = 1
    static member get_SXYZ () = 1
    member this.``name from inside instance member`` () =
        nameof (this.``name from inside instance member``)
    static member ``name from inside static member`` () =
        nameof (BasicNameOfTests.``name from inside static member``)

let bn = BasicNameOfTests()

eq "instance-member-name" (nameof (bn.MemberMethod)) "MemberMethod"
eq "instance-property-name" (nameof (bn.MemberProperty)) "MemberProperty"
eq "static-member-name" (nameof (BasicNameOfTests.StaticMethod)) "StaticMethod"
eq "static-property-name" (nameof (BasicNameOfTests.StaticProperty)) "StaticProperty"
eq "member-defined-below" (nameof (bn.MemberMethodDefinedBelow)) "MemberMethodDefinedBelow"
eq "name-from-inside-instance-member" (bn.``name from inside instance member`` ()) "name from inside instance member"
eq "name-from-inside-static-member" (BasicNameOfTests.``name from inside static member`` ()) "name from inside static member"

// a member whose name STARTS WITH get_ is not a property accessor in disguise
eq "member-starting-with-get" (nameof (bn.get_XYZ)) "get_XYZ"
eq "static-starting-with-get" (nameof (BasicNameOfTests.get_SXYZ)) "get_SXYZ"

// the TYPE itself, and a generic type whose argument is not part of the name
type Box<'a>(v : 'a) =
    member _.Value = v

eq "type-name" (nameof BasicNameOfTests) "BasicNameOfTests"
eq "generic-type-name" (nameof Box<int>) "Box"

// ---- library functions and dotted paths ------------------------------------

// a dotted path is named by its LAST segment
eq "library-function" (nameof List.map) "map"
eq "library-function-two" (nameof Array.fold) "fold"
eq "library-value" (nameof List.length) "length"

// ---- unions and records ----------------------------------------------------

type CustomUnionType =
    | OptionA
    | OptionB of int * string

type CustomRecordType = { X : int; Y : int }

eq "union-case-nullary" (nameof OptionA) "OptionA"
eq "union-case-with-payload" (nameof OptionB) "OptionB"
eq "union-type" (nameof CustomUnionType) "CustomUnionType"

let sample = { X = 1; Y = 2 }
eq "record-field-1" (nameof sample.X) "X"
eq "record-field-2" (nameof sample.Y) "Y"
eq "record-type" (nameof CustomRecordType) "CustomRecordType"

// ---- operators -------------------------------------------------------------

// an operator has no identifier at all: it names ITSELF
eq "operator-plus" (nameof (+)) "+"
eq "operator-pipe-right" (nameof (|>)) "|>"
eq "operator-append" (nameof (@)) "@"
eq "operator-equals" (nameof (=)) "="

// `typeof<int>` is named for the OPERATOR, not for the type inside it
eq "typeof-operator" (nameof (typeof<int>)) "typeof"

// and `nameof` names itself
eq "nameof-operator" (nameof (nameof)) "nameof"

// ---- the name is compile time only -----------------------------------------

// the argument is never evaluated: naming a binding whose value would throw
// is still just a name
let mutable evaluated = 0
let bump () : int =
    evaluated <- evaluated + 1
    1
let named = nameof bump
eq "argument-is-not-evaluated" named "bump"
eq "argument-is-not-evaluated-count" (string evaluated) "0"

// ---- nameof in ordinary positions ------------------------------------------

// as a match guard
let asGuard (s : string) : bool =
    match s with
    | x when x = nameof topLevelValue -> true
    | _ -> false

eq "match-guard-hit" (string (asGuard "topLevelValue")) "True"
eq "match-guard-miss" (string (asGuard "other")) "False"

// in a list, concatenated, and as an argument
let names = [ nameof topLevelValue; nameof topLevelFunction ]
eq "in-a-list" (String.concat "," names) "topLevelValue,topLevelFunction"
eq "concatenated" (nameof topLevelValue + "!") "topLevelValue!"
eq "as-argument" (String.concat "|" [ nameof List.map; "x" ]) "map|x"
eq "length-of-name" (string (nameof topLevelValue).Length) "13"

// ---- a user binding SHADOWS the operator ------------------------------------

let ``user defined nameof shadows the operator`` () : string =
    let nameof (x : int) = "test" + string x
    nameof 1

eq "user-defined-nameof-shadows" (``user defined nameof shadows the operator`` ()) "test1"

// shadowed by a PARAMETER too
let shadowedByParam (nameof : string -> string) : string = nameof "z"
eq "shadowed-by-parameter" (shadowedByParam (fun s -> "got " + s)) "got z"

printfn "DONE tests=%d failures=%d" ntests failures

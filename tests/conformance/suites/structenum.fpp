// STRUCT and ENUM types, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/ObjectOrientedType-
// Definitions (StructTypes: GenericStruct01, DoStaticLetDo, ExplicitCtor,
// IndexerProperties01; EnumTypes: Simple001, BinaryOr01, NonInt32Enums01,
// EqualsTag) into the common F#/F++ subset.
//
// A struct is a VALUE: copying one copies its fields, and a mutation through
// a copy leaves the original alone. An enum is an INT with names: it converts
// both ways, combines with the bitwise operators, and compares by value.
//
// DROPPED: the reflection cases (custom attributes read back through
// GetCustomAttributes), consuming a C# enum, and explicit struct layout.
module Core_structenum

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- enums: names for integers -------------------------------------------

type Colour =
    | Red = 0
    | Green = 1
    | Blue = 2

test "enum-to-int" (int Colour.Red = 0 && int Colour.Green = 1 && int Colour.Blue = 2)
test "enum-equality" (Colour.Green = Colour.Green)
test "enum-inequality" (Colour.Green <> Colour.Blue)

// an enum value flows through a function and a match
let describe (c : Colour) : string =
    match c with
    | Colour.Red -> "r"
    | Colour.Green -> "g"
    | _ -> "b"

test "enum-match" (describe Colour.Red = "r" && describe Colour.Blue = "b")

// gaps and explicit values are kept
type Flags =
    | None = 0
    | A = 1
    | B = 2
    | C = 4
    | D = 8

test "enum-explicit-values" (int Flags.C = 4 && int Flags.D = 8)

// the bitwise operators combine them (upstream BinaryOr01, without the
// attribute reflection)
let combined = int Flags.A ||| int Flags.B ||| int Flags.C ||| int Flags.D
test "enum-or" (combined = 15)
test "enum-and" ((combined &&& int Flags.B) = 2)
test "enum-xor" ((int Flags.A ^^^ int Flags.B) = 3)

// converting an int back
test "enum-of-int" (int (enum<Colour> 2) = 2)

// enums order by their value
test "enum-compare" (compare Colour.Red Colour.Blue < 0)
test "enum-sort" (List.sort [ Colour.Blue; Colour.Red; Colour.Green ] = [ Colour.Red; Colour.Green; Colour.Blue ])

// an enum as a Map key and inside a container
let byColour = Map.ofList [ (Colour.Red, "r"); (Colour.Blue, "b") ]
test "enum-map-key" (Map.find Colour.Blue byColour = "b")
test "enum-in-list" (List.contains Colour.Green [ Colour.Red; Colour.Green ])

// ---- structs: a value, copied on assignment ------------------------------

[<Struct>]
type Pair =
    { First : int
      Second : int }

let p1 = { First = 1; Second = 2 }
let p2 = p1

test "struct-fields" (p1.First = 1 && p1.Second = 2)
test "struct-copy-equal" (p1 = p2)
test "struct-with" ({ p1 with Second = 5 }.Second = 5)
test "struct-with-leaves-original" (p1.Second = 2)

// a struct in a container keeps its value semantics
let ps = [ p1; { First = 3; Second = 4 } ]
test "struct-in-list" ((List.item 1 ps).First = 3)
test "struct-list-equality" (ps = [ { First = 1; Second = 2 }; { First = 3; Second = 4 } ])

// structs compare field by field, in declaration order
test "struct-compare-first" (compare { First = 1; Second = 9 } { First = 2; Second = 0 } < 0)
test "struct-compare-second" (compare { First = 1; Second = 1 } { First = 1; Second = 2 } < 0)
test "struct-hash" (hash p1 = hash p2)

// a struct with mixed field widths
[<Struct>]
type Mixed =
    { N : int
      F : float
      B : bool }

let m = { N = 1; F = 2.5; B = true }
test "struct-mixed-fields" (m.N = 1 && m.F = 2.5 && m.B)
test "struct-mixed-equality" (m = { N = 1; F = 2.5; B = true })
test "struct-mixed-inequality" (m <> { N = 1; F = 2.5; B = false })

// ---- struct tuples -------------------------------------------------------

let st = struct (1, "a")
let struct (sa, sb) = st

test "struct-tuple-destructure" (sa = 1 && sb = "a")
test "struct-tuple-equality" (st = struct (1, "a"))
test "struct-tuple-compare" (compare (struct (1, "a")) (struct (1, "b")) < 0)

let structTupleFn (struct (a, b) : struct (int * int)) = a + b
test "struct-tuple-param" (structTupleFn (struct (3, 4)) = 7)

// ---- a struct CLASS with a primary constructor ---------------------------

[<Struct>]
type Vec2 (x : float, y : float) =
    member _.X = x
    member _.Y = y
    member this.LengthSq = this.X * this.X + this.Y * this.Y

let v = Vec2 (3.0, 4.0)
test "struct-class-fields" (v.X = 3.0 && v.Y = 4.0)
test "struct-class-member" (v.LengthSq = 25.0)

// copying a struct class value
let v2 = v
test "struct-class-copy" (v2.X = 3.0)

// ---- a GENERIC struct ----------------------------------------------------

[<Struct>]
type Cell<'a> =
    { Held : 'a }

let ci = { Held = 5 }
let cs = { Held = "s" }

test "generic-struct-int" (ci.Held = 5)
test "generic-struct-string" (cs.Held = "s")
test "generic-struct-equality" (ci = { Held = 5 })
test "generic-struct-in-list" (List.map (fun (c : Cell<int>) -> c.Held) [ ci; { Held = 6 } ] = [ 5; 6 ])

// ---- static state on a struct type ---------------------------------------

[<Struct>]
type WithStatics =
    { V : int }
    static member Origin = { V = 0 }

test "struct-static-member" (WithStatics.Origin.V = 0)

printfn "DONE tests=%d failures=%d" ntests failures

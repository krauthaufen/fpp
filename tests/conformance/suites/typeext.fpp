// TYPE ABBREVIATIONS, TYPE EXTENSIONS and OPERATOR MEMBERS, ported from
// dotnet/fsharp's tests/FSharp.Compiler.ComponentTests/Conformance
// (TypesAndTypeConstraints/TypeAbbreviations, TypeExtensions/*,
// BasicGrammarElements/OperatorNames, ObjectOrientedTypeDefinitions/
// TypeKindInference) into the common F#/F++ subset.
//
// An abbreviation is the SAME type under another name, so a value crosses
// between the two without a conversion. An extension adds members to a type
// declared elsewhere — including one from the prelude — and they dispatch
// exactly like declared members. An operator member makes `+` mean what the
// type says it means.
//
// DROPPED: extensions on a type from another ASSEMBLY, `[<AutoOpen>]`
// module extension visibility, and the measure-annotated abbreviations.
module Core_typeext

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- abbreviations name an existing type ---------------------------------

type Count = int
type Name = string
type Pairs = (string * int) list

let cnt : Count = 3
test "abbrev-is-the-type" (cnt + 1 = 4)

let nm : Name = "a"
test "abbrev-string" (nm + "b" = "ab")

// the abbreviation and the underlying type are interchangeable
let takesInt (v : int) = v * 2
let takesCount (v : Count) = v * 3

test "abbrev-into-underlying" (takesInt cnt = 6)
test "underlying-into-abbrev" (takesCount 4 = 12)

let ps : Pairs = [ ("a", 1); ("b", 2) ]
test "abbrev-of-compound" (List.length ps = 2 && snd (List.item 1 ps) = 2)

// a GENERIC abbreviation
type Assoc<'v> = (string * 'v) list

let assoc : Assoc<int> = [ ("k", 7) ]
test "generic-abbrev" (snd (List.head assoc) = 7)

// an abbreviation of a function type
type Transform = int -> int

let inc : Transform = fun v -> v + 1
test "function-abbrev" (inc 1 = 2)
test "function-abbrev-passed" (List.map inc [ 1; 2 ] = [ 2; 3 ])

// an abbreviation of a user type
type Pt = { X : int; Y : int }
type Point2 = Pt

let pt : Point2 = { X = 1; Y = 2 }
test "abbrev-of-record" (pt.X = 1)

// ---- an intrinsic extension adds members to a type declared here ---------

type Vec =
    { A : float
      B : float }

type Vec with
    member v.LengthSq = v.A * v.A + v.B * v.B
    member v.Scaled (k : float) = { A = v.A * k; B = v.B * k }
    static member Zero = { A = 0.0; B = 0.0 }

let vv = { A = 3.0; B = 4.0 }

test "extension-property" (vv.LengthSq = 25.0)
test "extension-method" ((vv.Scaled 2.0).A = 6.0)
test "extension-static" (Vec.Zero.A = 0.0)

// an extension on a UNION
type Shape =
    | Circle of float
    | Rect of float * float

type Shape with
    member s.Area =
        match s with
        | Circle r -> 3.0 * r * r
        | Rect (w, h) -> w * h
    member s.IsRound =
        match s with
        | Circle _ -> true
        | _ -> false

test "union-extension-circle" ((Circle 2.0).Area = 12.0)
test "union-extension-rect" ((Rect (2.0, 3.0)).Area = 6.0)
test "union-extension-bool" ((Circle 1.0).IsRound && not (Rect (1.0, 1.0)).IsRound)

// an extension member calls another extension member
type Vec with
    member v.Doubled = v.Scaled 2.0
    member v.DoubledLengthSq = v.Doubled.LengthSq

test "extension-calls-extension" (vv.DoubledLengthSq = 100.0)

// ---- operator members ----------------------------------------------------

type Money =
    { Cents : int }
    static member (+) (a : Money, b : Money) = { Cents = a.Cents + b.Cents }
    static member (-) (a : Money, b : Money) = { Cents = a.Cents - b.Cents }
    static member ( * ) (a : Money, k : int) = { Cents = a.Cents * k }

let m1 = { Cents = 150 }
let m2 = { Cents = 250 }

test "operator-add" ((m1 + m2).Cents = 400)
test "operator-sub" ((m2 - m1).Cents = 100)
test "operator-mul" ((m1 * 3).Cents = 450)
test "operator-chain" ((m1 + m2 + m1).Cents = 550)

// the operator works through a fold
test "operator-in-fold" ((List.fold (fun a b -> a + b) { Cents = 0 } [ m1; m2 ]).Cents = 400)

// a unary operator member
type Temp =
    { Deg : int }
    static member (~-) (t : Temp) = { Deg = 0 - t.Deg }

test "unary-minus" ((-{ Deg = 5 }).Deg = 0 - 5)

// a comparison operator spelled as a member on a CLASS
type Version (major : int, minor : int) =
    member _.Major = major
    member _.Minor = minor
    static member (+) (a : Version, b : Version) = Version (a.Major + b.Major, a.Minor + b.Minor)

let sumv = Version (1, 2) + Version (0, 3)
test "class-operator" (sumv.Major = 1 && sumv.Minor = 5)

// ---- operator NAMES used as functions ------------------------------------

test "op-as-function" (List.fold (+) 0 [ 1; 2; 3 ] = 6)
test "op-as-function-mul" (List.fold ( * ) 1 [ 2; 3; 4 ] = 24)
test "op-partial" (List.map ((+) 10) [ 1; 2 ] = [ 11; 12 ])

// a user-defined operator on ordinary values
let (+.) (a : float) (b : float) = a + b + 1.0
test "custom-operator" (1.0 +. 2.0 = 4.0)

let (|>>) (v : int) (f : int -> int) = f (f v)
test "custom-pipe" ((3 |>> fun n -> n * 2) = 12)

// ---- a type with both members and an extension, through a function -------

let lengthOf (v : Vec) = v.LengthSq
test "extension-through-function" (lengthOf vv = 25.0)

let areas (ss : Shape list) = List.map (fun (s : Shape) -> s.Area) ss
test "extension-through-map" (areas [ Circle 1.0; Rect (2.0, 2.0) ] = [ 3.0; 4.0 ])

// ---- shadowing rules: a declared member wins over nothing else -----------

type Holder =
    { V : int }
    member h.Get = h.V

type Holder with
    member h.GetPlus = h.Get + 1

test "declared-member" ({ V = 5 }.Get = 5)
test "extension-over-declared" ({ V = 5 }.GetPlus = 6)

printfn "DONE tests=%d failures=%d" ntests failures

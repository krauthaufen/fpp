// UNION AND RECORD TYPE DEFINITIONS, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Types (UnionTypes:
// NamedFields, SingleCase, Member01, Overload_Equals, DU_Struct;
// RecordTypes: RecordCloning01-03, FieldBindingAfterWith01, MutableFields01,
// Member01, ImplicitEquals01, LongIdentifiers01).
//
// The theme is what a DECLARATION gives you for free: cases that carry named
// fields, copy-and-update that keeps the fields it does not mention,
// structural equality and ordering, and members declared on either shape.
//
// DROPPED: `[<CustomEquality>]`/`[<CustomComparison>]` (they need
// IStructuralEquatable), anonymous records (`{| x = 1 |}`), and the
// interface-implementation cases that InterfaceTypes already covers.
module Core_uniontypes

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- cases with NAMED fields ---------------------------------------------

type Shape =
    | Circle of Radius : float
    | Rectangle of Width : float * Height : float
    | Point

let area (s : Shape) =
    match s with
    | Circle r -> 3.0 * r * r
    | Rectangle (w, h) -> w * h
    | Point -> 0.0

test "named-field-single" (area (Circle 2.0) = 12.0)
test "named-field-several" (area (Rectangle (2.0, 3.0)) = 6.0)
test "nullary-case" (area Point = 0.0)

// the names can be used at CONSTRUCTION
let namedCtor = Rectangle (Width = 4.0, Height = 5.0)
test "construct-by-name" (area namedCtor = 20.0)

// a named field is NOT a property on the union (F# exposes it only for
// construction and for matching), but a PATTERN may name it
let radiusOf (s : Shape) =
    match s with
    | Circle (Radius = r) -> r
    | _ -> 0.0

test "match-by-field-name" (radiusOf (Circle 2.0) = 2.0)

// ---- a SINGLE-CASE union is a wrapper ------------------------------------

type Meters = | Meters of float

let unwrap (Meters v) = v

test "single-case-unwrap" (unwrap (Meters 2.5) = 2.5)
test "single-case-equality" (Meters 1.0 = Meters 1.0)
test "single-case-inequality" (Meters 1.0 <> Meters 2.0)

// a single-case union in a pattern position binds directly
let addMeters (Meters a) (Meters b) = Meters (a + b)
test "single-case-param-pattern" (addMeters (Meters 1.0) (Meters 2.0) = Meters 3.0)

// ---- members on a union ---------------------------------------------------

type Expr =
    | Num of int
    | Add of Expr * Expr
    | Mul of Expr * Expr

    member e.Eval =
        match e with
        | Num n -> n
        | Add (a, b) -> a.Eval + b.Eval
        | Mul (a, b) -> a.Eval * b.Eval

    member e.Depth =
        match e with
        | Num _ -> 1
        | Add (a, b) -> 1 + max a.Depth b.Depth
        | Mul (a, b) -> 1 + max a.Depth b.Depth

    static member Zero = Num 0

let tree = Add (Num 1, Mul (Num 2, Num 3))

test "union-member" (tree.Eval = 7)
test "union-member-recursive" (tree.Depth = 3)
test "union-static-member" (Expr.Zero.Eval = 0)

// ---- structural equality, ordering and hashing come for free -------------

test "union-equality" (Add (Num 1, Num 2) = Add (Num 1, Num 2))
test "union-inequality-payload" (Add (Num 1, Num 2) <> Add (Num 1, Num 3))
test "union-inequality-case" (Num 1 <> Mul (Num 1, Num 1))
test "union-hash" (hash (Num 5) = hash (Num 5))

// cases order by DECLARATION order, then by payload
test "union-order-by-case" (compare (Num 9) (Add (Num 0, Num 0)) < 0)
test "union-order-by-payload" (compare (Num 1) (Num 2) < 0)
test "union-sort" (List.sort [ Num 2; Num 1 ] = [ Num 1; Num 2 ])

// a union inside a container
test "union-in-list" (List.map (fun (e : Expr) -> e.Eval) [ Num 1; Num 2 ] = [ 1; 2 ])
test "union-as-map-key" (Map.find (Num 1) (Map.ofList [ (Num 1, "a") ]) = "a")

// ---- a generic union ------------------------------------------------------

type Result2<'a, 'e> =
    | Good of 'a
    | Bad of 'e

let describe (r : Result2<int, string>) =
    match r with
    | Good v -> string v
    | Bad m -> m

test "generic-union-good" (describe (Good 3) = "3")
test "generic-union-bad" (describe (Bad "no") = "no")
test "generic-union-equality" (Good 1 = Good 1)

let mapGood (f : 'a -> 'b) (r : Result2<'a, 'e>) : Result2<'b, 'e> =
    match r with
    | Good v -> Good (f v)
    | Bad e -> Bad e

test "generic-union-map" (describe (mapGood (fun v -> v * 2) (Good 2)) = "4")

// ---- records: copy and update --------------------------------------------

type Person =
    { Name : string
      Age : int
      City : string }

let p = { Name = "a"; Age = 30; City = "x" }

test "record-fields" (p.Name = "a" && p.Age = 30)

let older = { p with Age = 31 }
test "with-changes-one" (older.Age = 31)
test "with-keeps-rest" (older.Name = "a" && older.City = "x")
test "with-leaves-original" (p.Age = 30)

let moved = { p with Age = 40; City = "y" }
test "with-changes-several" (moved.Age = 40 && moved.City = "y" && moved.Name = "a")

// copy-and-update of a copy
let twice = { older with Name = "b" }
test "with-chained" (twice.Name = "b" && twice.Age = 31)

// a NESTED record keeps its identity through a copy
type Address = { Street : string; Number : int }
type Employee = { Who : Person; Where : Address }

let e = { Who = p; Where = { Street = "s"; Number = 1 } }
let e2 = { e with Where = { e.Where with Number = 2 } }

test "nested-with" (e2.Where.Number = 2 && e2.Where.Street = "s")
test "nested-with-keeps-other" (e2.Who.Name = "a")
test "nested-with-leaves-original" (e.Where.Number = 1)

// ---- MUTABLE record fields -----------------------------------------------

type Counter = { mutable Count : int; Label : string }

let c = { Count = 0; Label = "c" }
c.Count <- c.Count + 1
c.Count <- c.Count + 1

test "mutable-field" (c.Count = 2)
test "immutable-field-alongside" (c.Label = "c")

// a copy of a mutable record is INDEPENDENT
let c2 = { c with Count = 10 }
c2.Count <- 11
test "mutable-copy-independent" (c.Count = 2 && c2.Count = 11)

// ---- members on a record --------------------------------------------------

type Vec =
    { X : float; Y : float }

    member v.LengthSq = v.X * v.X + v.Y * v.Y
    member v.Plus (o : Vec) = { X = v.X + o.X; Y = v.Y + o.Y }
    static member Zero = { X = 0.0; Y = 0.0 }

let v = { X = 3.0; Y = 4.0 }

test "record-member" (v.LengthSq = 25.0)
test "record-method" ((v.Plus v).X = 6.0)
test "record-static" (Vec.Zero.X = 0.0)

// ---- records compare and hash structurally -------------------------------

test "record-equality" (p = { Name = "a"; Age = 30; City = "x" })
test "record-inequality" (p <> older)
test "record-hash" (hash p = hash { Name = "a"; Age = 30; City = "x" })
test "record-order-first-field" (compare { X = 1.0; Y = 9.0 } { X = 2.0; Y = 0.0 } < 0)
test "record-order-second-field" (compare { X = 1.0; Y = 1.0 } { X = 1.0; Y = 2.0 } < 0)
test "record-in-list-equality" ([ p ] = [ { Name = "a"; Age = 30; City = "x" } ])

// a record as a Map key
test "record-map-key" (Map.find { X = 1.0; Y = 2.0 } (Map.ofList [ ({ X = 1.0; Y = 2.0 }, 7) ]) = 7)

// ---- the field-name inference rule ---------------------------------------

type Left = { Shared : int; L : int }
type Right = { Shared : int; R : int }

// the LAST declared type owning the mentioned labels wins
let inferred = { Shared = 1; R = 2 }
test "inferred-by-last-label" (inferred.R = 2)

// the annotation overrides it
let pinned : Left = { Shared = 3; L = 4 }
test "pinned-by-annotation" (pinned.L = 4)

// and the qualified form names the type outright
let qualified = { Left.Shared = 5; Left.L = 6 }
test "qualified-label" (qualified.L = 6)

printfn "DONE tests=%d failures=%d" ntests failures

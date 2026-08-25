// OBJECT EXPRESSIONS AND INTERFACE DISPATCH, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/ObjectOrientedTypeDefinitions
// (ObjectExpressions) and the interface cases of TypeDefinitions.
//
// An object expression is a class written at its use site: it implements the
// interface, CAPTURES the locals in scope, and is indistinguishable from a
// named implementation at the call — a list holding both dispatches the same
// way. The cases here check that the captured value is the one at creation
// time, and that dispatch picks the object's own member rather than the
// interface's declaration.
//
// DROPPED: object expressions over a BASE CLASS with `override`, and
// `IDisposable`/`use` (deterministic cleanup has its own gate).
module Core_objexpr

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// ---- an interface, implemented two ways -----------------------------------

type IShape =
    abstract Area : unit -> float
    abstract Name : string

// … by an object expression
let mkShape (n : string) (a : float) : IShape =
    { new IShape with
        member _.Area () = a
        member _.Name = n }

// … and by a named type
type Square(side : float) =
    interface IShape with
        member _.Area () = side * side
        member _.Name = "square"

let sq = Square 3.0 :> IShape
let oe = mkShape "made" 4.0

test "objexpr-method" (oe.Area () = 4.0)
eq "objexpr-property" oe.Name "made"
test "class-method" (sq.Area () = 9.0)
eq "class-property" sq.Name "square"

// both are the same interface, so one list holds them and dispatch picks each
let shapes : IShape list = [ oe; sq; mkShape "third" 0.5 ]

test "mixed-list-sum" (List.sumBy (fun (s : IShape) -> s.Area ()) shapes = 13.5)
eq "mixed-list-names" (String.concat "," (List.map (fun (s : IShape) -> s.Name) shapes)) "made,square,third"
test "mixed-list-filter" (List.length (List.filter (fun (s : IShape) -> s.Area () > 1.0) shapes) = 2)

// ---- capture ---------------------------------------------------------------

// the object expression closes over the binding, at the value it had
let captured =
    let n = 10
    { new IShape with
        member _.Area () = float n
        member _.Name = "captured" }

test "captures-local" (captured.Area () = 10.0)

// each creation captures its OWN value
let many = List.map (fun v -> mkShape (string v) (float v)) [ 1; 2; 3 ]
test "each-captures-its-own" (List.map (fun (s : IShape) -> s.Area ()) many = [ 1.0; 2.0; 3.0 ])

// a captured MUTABLE is read when the member runs, not when it was built
let mutableCapture =
    let mutable count = 0
    let o =
        { new IShape with
            member _.Area () = float count
            member _.Name = "mut" }
    count <- 7
    o

test "captures-mutable-by-reference" (mutableCapture.Area () = 7.0)

// ---- an interface with several members and a generic one -------------------

type IFold =
    abstract Start : int
    abstract Step : int -> int -> int

let summer =
    { new IFold with
        member _.Start = 0
        member _.Step acc v = acc + v }

let producter =
    { new IFold with
        member _.Start = 1
        member _.Step acc v = acc * v }

let runFold (f : IFold) (xs : int list) : int = List.fold (fun a v -> f.Step a v) f.Start xs

test "fold-sum" (runFold summer [ 1; 2; 3; 4 ] = 10)
test "fold-product" (runFold producter [ 1; 2; 3; 4 ] = 24)
test "curried-member" (summer.Step 2 3 = 5)

type IBox<'a> =
    abstract Get : unit -> 'a
    abstract Map : ('a -> 'a) -> 'a

let boxOf (v : 'a) : IBox<'a> =
    { new IBox<'a> with
        member _.Get () = v
        member _.Map f = f v }

test "generic-interface-int" ((boxOf 5).Get () = 5)
test "generic-interface-string" ((boxOf "s").Get () = "s")
test "generic-interface-map" ((boxOf 5).Map (fun v -> v * 2) = 10)

// ---- an object expression is a value ----------------------------------------

let pick (b : bool) : IShape = if b then oe else sq

test "returned-from-branch" (pick true |> fun s -> s.Area () = 4.0)
test "returned-from-branch-other" (pick false |> fun s -> s.Area () = 9.0)

let applyTo (f : IShape -> float) (s : IShape) : float = f s
test "passed-to-function" (applyTo (fun s -> s.Area ()) oe = 4.0)

// stored in a record field and dispatched from there
type Holder = { Shape : IShape; Tag : string }
let h = { Shape = mkShape "held" 2.5; Tag = "t" }

test "in-record-field" (h.Shape.Area () = 2.5)
eq "in-record-field-name" h.Shape.Name "held"

// ---- a class implementing TWO interfaces ------------------------------------

type ILabel =
    abstract Label : string

type Both() =
    interface IShape with
        member _.Area () = 1.0
        member _.Name = "both"
    interface ILabel with
        member _.Label = "L"

let b = Both ()

test "first-interface" ((b :> IShape).Area () = 1.0)
eq "second-interface" ((b :> ILabel).Label) "L"

let bothObj =
    { new ILabel with
        member _.Label = "objL" }

eq "objexpr-second-interface" bothObj.Label "objL"

printfn "DONE tests=%d failures=%d" ntests failures

// TUPLES, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Expressions/DataExpressions
// (TupleExpressions) and Conformance/Types/TypeForwarding tuple cases.
//
// A tuple is a value with structure: it compares and hashes element by
// element, it destructures in every binding position, and a STRUCT tuple is
// the same value in a different representation — `struct (1, 2)` equals
// another struct tuple, and is a distinct type from the reference one.
//
// DROPPED: tuples past 8 elements (the .NET nesting rule is representation,
// not semantics) and `System.Tuple` interop.
module Core_tuples

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- construction and projection ------------------------------------------

let pair = (1, "a")
let triple = (1, "a", true)

test "fst" (fst pair = 1)
test "snd" (snd pair = "a")
test "destructure-pair" (let (x, y) = pair in x = 1 && y = "a")
test "destructure-triple" (let (x, y, z) = triple in x = 1 && y = "a" && z)
test "nested" (let (x, (y, z)) = (1, (2, 3)) in x + y + z = 6)
test "wildcard-in-pattern" (let (_, y) = pair in y = "a")

// a tuple of tuples is its own shape — `((1,2),3)` and `(1,(2,3))` are not
// even the same TYPE, so only the same shape can be compared
test "nested-equality" (((1, 2), 3) = ((1, 2), 3))
test "nested-inequality" (((1, 2), 3) <> ((1, 9), 3))

// ---- equality, ordering, hashing ------------------------------------------

test "eq" ((1, 2) = (1, 2))
test "ne-first" ((1, 2) <> (9, 2))
test "ne-second" ((1, 2) <> (1, 9))
test "order-by-first" (compare (1, 9) (2, 0) < 0)
test "order-by-second" (compare (1, 1) (1, 2) < 0)
test "order-equal" (compare (1, 2) (1, 2) = 0)
test "sort" (List.sort [ (2, "b"); (1, "z"); (1, "a") ] = [ (1, "a"); (1, "z"); (2, "b") ])
test "hash" (hash (1, "a") = hash (1, "a"))
test "as-map-key" (Map.find (1, "a") (Map.ofList [ ((1, "a"), 7) ]) = 7)
test "mixed-types" ((1, "a", 2.5, true) = (1, "a", 2.5, true))

// ---- tuples through functions ---------------------------------------------

let addPair (a : int, b : int) : int = a + b        // ONE tuple parameter
let addCurried (a : int) (b : int) : int = a + b    // two parameters

test "tupled-parameter" (addPair (2, 3) = 5)
test "curried-parameter" (addCurried 2 3 = 5)
test "tupled-from-value" (let p = (2, 3) in addPair p = 5)

let swap (a : int, b : string) : string * int = (b, a)
test "returns-tuple" (swap (1, "a") = ("a", 1))

let divMod (a : int) (b : int) : int * int = (a / b, a % b)
test "multiple-results" (divMod 17 5 = (3, 2))
test "multiple-results-destructured" (let (q, r) = divMod 17 5 in q * 5 + r = 17)

// a tuple flows through a generic function unchanged
let idf (v : 'a) : 'a = v
test "through-generic" (idf (1, "a") = (1, "a"))

// ---- tuples in containers and patterns ------------------------------------

let ps = [ (1, "a"); (2, "b"); (3, "c") ]

test "in-list" (List.length ps = 3)
test "map-over-tuples" (List.map fst ps = [ 1; 2; 3 ])
test "map-with-destructuring" (List.map (fun (n, s) -> s + string n) ps = [ "a1"; "b2"; "c3" ])
test "filter-on-part" (List.filter (fun (n, _) -> n > 1) ps = [ (2, "b"); (3, "c") ])
test "unzip" (List.unzip ps = ([ 1; 2; 3 ], [ "a"; "b"; "c" ]))
test "zip" (List.zip [ 1; 2 ] [ "a"; "b" ] = [ (1, "a"); (2, "b") ])
test "in-array" (Array.toList (Array.map snd [| (1, "a"); (2, "b") |]) = [ "a"; "b" ])

let classify (p : int * int) : string =
    match p with
    | (0, 0) -> "origin"
    | (0, _) -> "y-axis"
    | (_, 0) -> "x-axis"
    | _ -> "other"

test "match-literal-tuple" (classify (0, 0) = "origin")
test "match-partial" (classify (0, 5) = "y-axis" && classify (5, 0) = "x-axis")
test "match-fallthrough" (classify (1, 1) = "other")

let guarded (p : int * int) : string =
    match p with
    | (a, b) when a = b -> "diag"
    | (a, b) when a > b -> "below"
    | _ -> "above"

test "match-with-guard" (guarded (2, 2) = "diag" && guarded (3, 1) = "below" && guarded (1, 3) = "above")

// ---- STRUCT tuples ---------------------------------------------------------

let sp = struct (1, 2)

test "struct-destructure" (let struct (a, b) = sp in a + b = 3)
test "struct-equality" (sp = struct (1, 2))
test "struct-inequality" (sp <> struct (1, 9))
test "struct-order" (compare (struct (1, 1)) (struct (1, 2)) < 0)

let structAdd (struct (a, b) : struct (int * int)) : int = a + b
test "struct-parameter" (structAdd (struct (2, 3)) = 5)

let mkStruct (a : int) : struct (int * int) = struct (a, a * 2)
test "struct-returned" (let struct (x, y) = mkStruct 3 in x = 3 && y = 6)

// a struct tuple keeps VALUE semantics through a binding
let sp2 = sp
test "struct-copy" (let struct (a, _) = sp2 in a = 1)

printfn "DONE tests=%d failures=%d" ntests failures

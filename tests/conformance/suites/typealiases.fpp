// THE PRIMITIVE SCALARS HAVE TWO SPELLINGS EACH, and they are one type.
// `int`/`int32`, `float`/`double`, `float32`/`single`, `byte`/`uint8`,
// `sbyte`/`int8`, `uint32`/`uint` — F# writes both, and .NET-facing code
// writes the second of each pair constantly, so this is not a surface
// anyone can be asked to avoid.
//
// Each spelling used to become its OWN nominal type: `let (b : byte) = (a :
// uint8)` was a type error, `let n : int32 = 1` annotated a type no backend
// knows, and four of the six had no conversion FUNCTION at all. Every
// position below is a separate place a written name becomes a type — an
// annotation, a signature, a collection's element, a cast, a type test —
// and the name is canonicalized once, where it is read.
//
// DROPPED: `typeof<uint8> = typeof<byte>`, which would be the most direct
// statement of the rule. Reflection is not in the subset (`sizeof` traps
// under the canonical spelling too), so the equality is shown by USE.
module Core_typealiases

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

// ---- an ANNOTATION in either spelling names the same type -------------------

let a1 : uint8 = 3uy
let a2 : byte = a1
let b1 : int8 = 3y
let b2 : sbyte = b1
let c1 : int32 = 3
let c2 : int = c1
let d1 : uint = 3u
let d2 : uint32 = d1
let e1 : single = 1.5f
let e2 : float32 = e1
let f1 : double = 1.5
let f2 : float = f1

eq "uint8-is-byte" (string (int a2)) "3"
eq "int8-is-sbyte" (string (int b2)) "3"
eq "int32-is-int" (string c2) "3"
eq "uint-is-uint32" (string (int d2)) "3"
eq "single-is-float32" (string e2) "1.5"
eq "double-is-float" (string f2) "1.5"

// and back the other way, which is a separate unification
let g1 : byte = 4uy
let g2 : uint8 = g1
let h1 : float = 2.5
let h2 : double = h1
eq "byte-is-uint8" (string (int g2)) "4"
eq "float-is-double" (string h2) "2.5"

// ---- the CONVERSION functions -----------------------------------------------
// Four of these did not exist: `int32`, `uint`, `double`, `single` were
// unbound values, so ported code calling them did not compile at all.

eq "conv-int32" (string (int32 3.7)) "3"
eq "conv-int" (string (int 3.7)) "3"
eq "conv-uint" (string (int (uint 7))) "7"
eq "conv-uint32" (string (int (uint32 7))) "7"
eq "conv-double" (string (double 3)) "3"
eq "conv-float" (string (float 3)) "3"
eq "conv-single" (string (single 3)) "3"
eq "conv-float32" (string (float32 3)) "3"
eq "conv-uint8" (string (int (uint8 200))) "200"
eq "conv-byte" (string (int (byte 200))) "200"
eq "conv-int8" (string (int (int8 -3))) "-3"
eq "conv-sbyte" (string (int (sbyte -3))) "-3"

// the two spellings of one conversion agree on the VALUE, including where
// the conversion truncates or wraps
eq "int32-agrees-with-int" (string (int32 -3.7) + "," + string (int -3.7)) "-3,-3"
eq "double-agrees-with-float" (string (double 7 / 2.0) + "," + string (float 7 / 2.0)) "3.5,3.5"
eq "uint8-agrees-with-byte" (string (int (uint8 300)) + "," + string (int (byte 300))) "44,44"

// a conversion used as a VALUE, which is the eta-expanded path
eq "int32-as-a-value" (String.concat "," (List.map (fun (x : float) -> string (int32 x)) [ 1.5; 2.5 ])) "1,2"
eq "double-as-a-value" (String.concat "," (List.map (fun (x : int) -> string (double x)) [ 1; 2 ])) "1,2"

// ---- a SIGNATURE in either spelling ------------------------------------------

let takesDouble (x : double) : double = x * 2.0
let takesFloat (x : float) : float = x * 2.0
eq "double-signature" (string (takesDouble 1.5)) "3"
eq "float-argument-to-a-double-parameter" (string (takesDouble h1)) "5"
eq "double-argument-to-a-float-parameter" (string (takesFloat f1)) "3"

let takesUint8 (x : uint8) : int = int x
eq "uint8-signature" (string (takesUint8 5uy)) "5"
eq "byte-argument-to-a-uint8-parameter" (string (takesUint8 g1)) "4"

// the result of one feeding the parameter of the other
let widen (x : int32) : double = double x
eq "int32-in-double-out" (string (widen 3)) "3"

// ---- as a collection's ELEMENT ------------------------------------------------

let l1 : list<uint8> = [ 1uy; 2uy ]
let l2 : byte list = l1
eq "uint8-list-is-a-byte-list" (string (List.length l2)) "2"
eq "its-elements" (String.concat "," (List.map (fun (x : byte) -> string (int x)) l2)) "1,2"

let arr1 : int32[] = [| 1; 2; 3 |]
let arr2 : int[] = arr1
eq "int32-array-is-an-int-array" (string arr2.Length) "3"
eq "its-sum" (string (Array.sum arr2)) "6"

let m1 : Map<int32, double> = Map.ofList [ (1, 1.5) ]
let m2 : Map<int, float> = m1
eq "map-of-aliases" (string (Map.find 1 m2)) "1.5"

// ---- at a CAST and a TYPE TEST ------------------------------------------------
// A test names a class id. Written `uint8`, it named one that does not
// exist, so the test was silently FALSE.

let o1 : obj = box (3uy : uint8)
let o2 : obj = box (3 : int32)
let o3 : obj = box (1.5 : double)

test "boxed-uint8-is-byte" (o1 :? byte)
test "boxed-uint8-is-uint8" (o1 :? uint8)
test "boxed-int32-is-int" (o2 :? int)
test "boxed-int32-is-int32" (o2 :? int32)
test "boxed-double-is-float" (o3 :? float)
test "boxed-double-is-double" (o3 :? double)

eq "downcast-to-uint8" (string (int (o1 :?> uint8))) "3"
eq "downcast-to-byte" (string (int (o1 :?> byte))) "3"
eq "downcast-to-int32" (string (o2 :?> int32)) "3"
eq "downcast-to-double" (string (o3 :?> double)) "1.5"

// and a test still says NO to a different scalar
test "a-boxed-double-is-not-an-int32" (not (o3 :? int32))
test "a-boxed-uint8-is-not-an-int" (not (o1 :? int))

printfn "DONE tests=%d failures=%d" ntests failures

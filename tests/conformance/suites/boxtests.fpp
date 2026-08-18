// Boxed-value type tests and downcasts (the fsc subtype test's portable
// core): `:?` and `:?>` against scalars, strings and user classes on a
// boxed obj. bool/char/byte share the int representation in F++ (a chosen
// divergence, DIVERGENCES.md), so only the CONFORMING cases are asserted.
// The wasm-GC leg additionally keeps SMALL int64s in the i31 (bx15 and the
// heterogeneous dispatch would diverge there); the conformance gate runs
// the wasm-linear leg, where int64 boxes are exact.
// Also: `!x` in argument position, and int64/uint64-of-string.
module Core_boxtests

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let iobj = (3 :> obj)
test "bx1" (match iobj with :? int -> true | _ -> false)
test "bx2" ((iobj :?> int) = 3)
test "bx3" (not (match iobj with :? string -> true | _ -> false))
test "bx4" (not (match iobj with :? float -> true | _ -> false))

let sobj = box "hi"
test "bx5" (match sobj with :? string -> true | _ -> false)
test "bx6" ((sobj :?> string) = "hi")
test "bx7" (not (match sobj with :? int -> true | _ -> false))
test "bx8" (not (match sobj with :? float -> true | _ -> false))

let fobj = box 2.5
test "bx9" (match fobj with :? float -> true | _ -> false)
test "bx10" ((fobj :?> float) = 2.5)
test "bx11" (not (match fobj with :? int -> true | _ -> false))
test "bx12" (not (match fobj with :? string -> true | _ -> false))

let lobj = box 77L
test "bx13" (match lobj with :? int64 -> true | _ -> false)
test "bx14" ((lobj :?> int64) = 77L)
test "bx15" (not (match lobj with :? int -> true | _ -> false))
test "bx16" (not (match lobj with :? float -> true | _ -> false))

// dispatch over a heterogeneous list of boxes
let describe (o : obj) =
    match o with
    | :? int as i -> "int:" + string i
    | :? float as f -> (if f = 2.5 then "float:2.5" else "float:?")
    | :? string as s -> "str:" + s
    | :? int64 -> "long"
    | _ -> "other"
let described = [ box 1; box "a"; box 2.5; box 9L ] |> List.map describe
test "bx17" (described = [ "int:1"; "str:a"; "float:2.5"; "long" ])

// user classes still test exactly beside the scalar arms
type Animal() =
    member x.Kind = "animal"
type Dog() =
    inherit Animal()
    member x.Bark = "woof"
let aobj = (Dog() :> obj)
test "bx18" (match aobj with :? Dog -> true | _ -> false)
test "bx19" (match aobj with :? Animal -> true | _ -> false)
test "bx20" (not (match iobj with :? Animal -> true | _ -> false))
test "bx21" ((aobj :?> Dog).Bark = "woof")

// `!x` in argument position
let cell = ref 5
test "dr1" (max !cell 3 = 5)
test "dr2" (min !cell 3 = 3)
let addTo (a : int) (b : int) = a + b
test "dr3" (addTo !cell !cell = 10)

// numeric-of-string on every backend
test "cv1" (int64 "123" = 123L)
test "cv2" (uint64 "9007199254" = 9007199254UL)

printfn "DONE tests=%d failures=%d" ntests failures

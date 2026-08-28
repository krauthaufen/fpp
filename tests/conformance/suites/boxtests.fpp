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

// ---- EVERY int boxes, not just the odd ones --------------------------------
// A boxed 32-bit scalar used to be the RAW word, and the type test read its
// low bit as a tag the raw-i32 arc had removed: `box n :? int` answered true
// only for ODD n, and the suite above never caught it because 3, 1 and 97
// are odd. A box is a real object with a header now.

let roundTrip (n : int) : bool =
    let o : obj = box n
    (o :? int) && (o :?> int) = n

test "even-zero" (roundTrip 0)
test "odd-one" (roundTrip 1)
test "even-two" (roundTrip 2)
test "odd-three" (roundTrip 3)
test "even-four" (roundTrip 4)
test "large-even" (roundTrip 1000000)
test "large-odd" (roundTrip 1000001)
test "negative-even" (roundTrip (-2))
test "negative-odd" (roundTrip (-3))
test "int-min" (roundTrip (-2147483648))
test "int-max" (roundTrip 2147483647)

// the same through an UPCAST rather than `box`
let viaUpcast (n : int) : bool =
    let o = (n :> obj)
    (o :? int) && (o :?> int) = n

test "upcast-even" (viaUpcast 4)
test "upcast-odd" (viaUpcast 5)
test "upcast-negative" (viaUpcast (-6))

// and through `unbox`
test "unbox-even" (unbox<int> (box 8) = 8)
test "unbox-odd" (unbox<int> (box 9) = 9)

// an `as` binder gets the VALUE, not the box carrying it
let describedBox (o : obj) : string =
    match o with
    | :? int as i -> "int:" + string i
    | :? string as s -> "str:" + s
    | _ -> "?"

test "as-binds-an-even-int" (describedBox (box 10) = "int:10")
test "as-binds-an-odd-int" (describedBox (box 11) = "int:11")
test "as-binds-a-string" (describedBox (box "s") = "str:s")

// boxed ints compare and hash by VALUE
test "boxed-equal" ((box 4 : obj) = (box 4 : obj))
test "boxed-unequal" ((box 4 : obj) <> (box 5 : obj))
test "boxed-hash-agrees" (hash (box 4 : obj) = hash (box 4 : obj))

// a whole list of them, every element even
let evens : obj list = [ box 0; box 2; box 4 ]
test "every-even-tests-int" (List.forall (fun (o : obj) -> o :? int) evens)
test "every-even-downcasts" (List.sumBy (fun (o : obj) -> o :?> int) evens = 6)

// ---- each scalar type is told APART -------------------------------------
// The box carries a kind word. Sharing one representation made `box true :?
// int` true, `box true :?> int` hand back 1, and — worst — `1 :> obj` compare
// EQUAL to `true :> obj`.

test "bool-boxes" ((box false : obj) :? bool)
test "char-boxes" ((box 'a' : obj) :? char)
test "char-value" (((box 'z' : obj) :?> char) = 'z')

test "bool-is-not-an-int" (not ((box true : obj) :? int))
test "int-is-not-a-bool" (not ((box 1 : obj) :? bool))
test "char-is-not-an-int" (not ((box 'a' : obj) :? char = false))
test "char-is-not-int" (not ((box 'a' : obj) :? int))
test "byte-is-its-own-type" ((box 3uy : obj) :? byte)
test "byte-is-not-an-int" (not ((box 3uy : obj) :? int))
test "int16-is-its-own-type" ((box 3s : obj) :? int16)
test "int16-is-not-an-int" (not ((box 3s : obj) :? int))

// the values do not COMPARE equal either, which is the part that mattered
test "boxed-bool-differs-from-boxed-int" ((box true : obj) <> (box 1 : obj))
test "boxed-char-differs-from-its-code" ((box 'a' : obj) <> (box 97 : obj))
test "boxed-byte-differs-from-int" ((box 3uy : obj) <> (box 3 : obj))
test "same-type-same-value-is-equal" ((box 7 : obj) = (box 7 : obj))
test "same-type-other-value-differs" ((box 7 : obj) <> (box 8 : obj))

// a wrong downcast THROWS rather than handing back the payload
test "wrong-downcast-throws" ((try ignore ((box true : obj) :?> int); false with _ -> true))
test "right-downcast-works" (((box true : obj) :?> bool) = true)
test "unbox-checks-too" ((try ignore (unbox<int> (box true)); false with _ -> true))
test "unbox-right-type" (unbox<bool> (box true) = true)

printfn "DONE tests=%d failures=%d" ntests failures

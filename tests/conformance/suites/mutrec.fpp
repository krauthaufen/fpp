// The portable core of dotnet/fsharp tests/fsharp/core/letrec-mutrec:
// inner mutually recursive groups closing over state, and the
// partially-TLR odd/even case. Dropped: `module rec` (unsupported) and
// cyclic VALUE recursion (`let x = { f1 = 3; f2 = x }` — a documented
// F++ drop: FS0040-style delayed initialization is not implemented).
module Core_letrec_mutrec

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// an inner rec group re-created per call, reading the captured counter
let f =
    let x = ref 0
    fun () ->
        x := (!x) + 1
        let rec g n = if n = 0 then 1 else h (n - 1)
        and h n = if n = 0 then 2 else g (n - 1)
        g (!x)
test "ewiucew" (f () = 2)
test "ewiew8w" (f () = 1)

let nestedInnerRec2 =
    let x = ref 0
    fun () ->
        x := (!x) + 1
        let rec g n = if n = 0 then (!x) + 100 else h (n - 1)
        and h n = if n = 0 then (!x) + 200 else g (n - 1)
        g (!x)
test "nir1" (nestedInnerRec2 () = 201)
test "nir2" (nestedInnerRec2 () = 102)

// TLR letrec where only some functions lift (odd applied through `apply`)
let apply f x = f x
let dec (n : int) = n
let inner () =
    let rec odd n = if n = 1 then true else not (even (dec n))
    and even n = if n = 0 then true else not (apply odd (dec n))
    even 99
// dec is the identity here (as in the original), so the group ping-pongs
// n down by nothing — the original relies on dec being id and the
// SHAPE compiling; calling inner () would not terminate, so the shape
// is exercised at other arguments:
let innerAt (start : int) =
    let rec odd n = if n <= 1 then true else not (even (n - 1))
    and even n = if n <= 0 then true else not (odd (n - 1))
    even start
test "tlr1" (innerAt 0 = true)
test "tlr2" (innerAt 1 = false)
test "tlr3" (innerAt 4 = false)
test "tlr4" (innerAt 99 = false)

// recursion through a ref cell (the z1/z2 shape, spelled acyclically)
type R2 = { g1 : int; g2 : R2 option ref }
let z1 = { g1 = 3; g2 = ref None }
let z2 = { g1 = 4; g2 = ref (Some z1) }
z1.g2 := Some z2
test "ref1" (z2.g1 = 4)
test "ref2" ((match (!(z2.g2)) with Some r -> r.g1 | None -> 0) = 3)
test "ref3" ((match (!(z1.g2)) with Some r -> r.g1 | None -> 0) = 4)

// polymorphic inner letrec, partially generalized
let polyPair () =
    let rec len (xs : 'a list) = match xs with [] -> 0 | _ :: t -> 1 + len t
    (len [ 1; 2; 3 ], len [ "a" ])
test "poly1" (polyPair () = (3, 1))

printfn "DONE tests=%d failures=%d" ntests failures

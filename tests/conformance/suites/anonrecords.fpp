// ANONYMOUS RECORDS, ported from dotnet/fsharp's tests/fsharp/core/anon.
//
// `{| X = 1; Y = "s" |}` is F#'s STRUCTURAL record: no declaration, and two
// literals with the same field names and types are the same type wherever
// they are written. Everything in this compiler is nominal, so the literal
// expands to an ordinary record of a SYNTHESIZED generic type, one per
// distinct field-name set, declared once per file:
//
//     ({ X = 1; Y = "s" } : $anon$X$Y<_, _>)
//
// Generic, so the same labels at different value types stay different types;
// sorted, so field order does not make a second type. The ascription is what
// PINS it — a record literal otherwise resolves by field-name set, and a
// nominal record of the same shape in the same program would capture it,
// which is the case this suite's `Same` type exists to prove.
//
// DROPPED: struct anonymous records (`struct {| ... |}`), and equality
// against a nominal record of the same shape, which F# rejects as a type
// error and is therefore not expressible in a file both compilers read.
module Core_anonrecords

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

// ---- construction and field access -------------------------------------------

let r = {| X = 1; Y = "s" |}

eq "int-field" (string r.X) "1"
eq "string-field" r.Y "s"

let one = {| Only = 42 |}
eq "single-field" (string one.Only) "42"

let three = {| A = 1; B = 2; C = 3 |}
eq "three-fields" (string (three.A + three.B + three.C)) "6"

// a field VALUE is any expression
let computed = {| Sum = 1 + 2; Text = string 9 |}
eq "computed-field" (string computed.Sum + computed.Text) "39"

// ---- the field-name SET is the type ------------------------------------------

// same labels, different value types: a DIFFERENT type, and both exist
let asInts = {| X = 3; Y = 4 |}
eq "same-labels-other-types" (string (asInts.X + asInts.Y)) "7"
eq "and-the-first-is-untouched" (string r.X + r.Y) "1s"

// field ORDER does not make a new type: these two are the same type, and
// comparing them at all is what proves it
let ab = {| A = 1; B = 2 |}
let ba = {| B = 2; A = 1 |}
test "order-does-not-matter" (ab = ba)
eq "order-does-not-matter-fields" (string (ba.A + ba.B)) "3"

// A NOMINAL RECORD OF THE SAME SHAPE does not capture the literal. Declared
// first and covering the same labels, it is what the field-set resolution
// would otherwise pick.
type Same = { X : int; Y : string }
let nominal = { X = 8; Y = "n" }
let anon = {| X = 9; Y = "a" |}
eq "nominal-still-resolves" (string nominal.X + nominal.Y) "8n"
eq "anon-is-not-the-nominal-one" (string anon.X + anon.Y) "9a"

// ---- EQUALITY is structural ---------------------------------------------------

test "equal-to-an-equal-literal" (r = {| X = 1; Y = "s" |})
test "differs-by-a-field" (r <> {| X = 2; Y = "s" |})
test "differs-by-the-other-field" (r <> {| X = 1; Y = "t" |})
test "equal-to-itself" (r = r)

// and so is comparison
test "compares-by-field" (compare {| N = 1 |} {| N = 2 |} < 0)
test "compares-equal" (compare {| N = 1 |} {| N = 1 |} = 0)

// ---- COPY AND UPDATE ----------------------------------------------------------
// No ascription is needed here: copy-and-update takes its type from the base.

let updated = {| r with X = 7 |}
eq "updated-field" (string updated.X) "7"
eq "carried-field" updated.Y "s"
eq "the-original-is-untouched" (string r.X) "1"

let both = {| r with X = 5; Y = "z" |}
eq "updated-both" (string both.X + both.Y) "5z"

// ---- NESTING -------------------------------------------------------------------

let nested = {| A = {| B = 5 |} |}
eq "nested-field" (string nested.A.B) "5"

let deep = {| L1 = {| L2 = {| L3 = "deep" |} |} |}
eq "three-deep" deep.L1.L2.L3 "deep"

let holdsARecord = {| Inner = { X = 1; Y = "in" } |}
eq "holds-a-nominal-record" holdsARecord.Inner.Y "in"

// ---- as an ordinary VALUE -------------------------------------------------------

// annotated, which is the type form of the same shape
let f (v : {| N : int |}) : int = v.N * 2
eq "through-a-parameter" (string (f {| N = 5 |})) "10"

let g () : {| K : int; J : string |} = {| K = 3; J = "j" |}
eq "as-a-return-type" (string (g ()).K + (g ()).J) "3j"

// in a list, and through a lambda's annotated parameter
let xs = [ {| N = 1 |}; {| N = 2 |}; {| N = 3 |} ]
eq "in-a-list" (string (List.length xs)) "3"
eq "summed" (string (List.sumBy (fun (a : {| N : int |}) -> a.N) xs)) "6"
eq "mapped" (String.concat "," (List.map (fun (a : {| N : int |}) -> string a.N) xs)) "1,2,3"

// in an array, and as a tuple element
let arr = [| {| V = 1 |}; {| V = 2 |} |]
eq "in-an-array" (string arr.[1].V) "2"

let pair = ({| P = 1 |}, {| P = 2 |})
eq "in-a-tuple" (string ((fst pair).P + (snd pair).P)) "3"

// as an option's payload
let opt = Some {| Q = 4 |}
eq "in-an-option" (string (match opt with Some v -> v.Q | None -> 0)) "4"

// a MUTABLE binding holding one
let mutable current = {| C = 1 |}
current <- {| C = 2 |}
eq "reassigned" (string current.C) "2"

// ---- PRINTING -------------------------------------------------------------------
// An anonymous record prints as a record, fields one per line, the way this
// compiler prints any record.

eq "printed" (string {| Z = 1 |}) "{ Z = 1 }"

printfn "DONE tests=%d failures=%d" ntests failures

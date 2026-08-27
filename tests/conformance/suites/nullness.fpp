// NULL AND DEFAULT VALUES, ported from dotnet/fsharp's
// tests/fsharp/core/nullness and the `Unchecked.defaultof` cases of
// tests/fsharp/core/libtest.
//
// F# keeps null at arm's length: an F#-declared record, union or function
// type has no null value, but a .NET type like `string` does, and
// `Unchecked.defaultof<'T>` produces whatever the runtime's zero for a type
// is. The cases worth pinning are the ones where null has to be RECOGNISED —
// `isNull`, a `null` pattern, the String helpers that answer for it — and
// the conversions between a null reference and an option, which is how F#
// code normally launders one at the boundary.
//
// DROPPED: `[<AllowNullLiteral>]` on an F# class, the F# 9 nullable-reference
// annotations (`string | null`), and passing null into a function that
// declares an F# type — the compiler rejects the literal there, and the
// negative gate owns compile errors.
module Core_nullness

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

// ---- isNull recognises it ----------------------------------------------------

let nullStr : string = null
let realStr : string = "x"
let emptyStr : string = ""

test "isNull-of-null" (isNull nullStr)
test "isNull-of-a-value" (not (isNull realStr))
test "isNull-of-the-empty-string" (not (isNull emptyStr))

// the empty string is NOT null, which is the distinction the String helpers
// exist to blur on purpose
test "empty-is-not-null" (not (isNull emptyStr))
test "empty-has-length-zero" (emptyStr.Length = 0)

// through a binding and through a function
let viaBinding = nullStr
test "isNull-through-a-binding" (isNull viaBinding)

let checkNull (s : string) : bool = isNull s
test "isNull-through-a-parameter" (checkNull nullStr)
test "isNull-through-a-parameter-value" (not (checkNull "a"))

// ---- equality against null ---------------------------------------------------

test "null-equals-null" (nullStr = null)
test "a-value-does-not-equal-null" (realStr <> null)
test "two-nulls-are-equal" ((null : string) = (null : string))
test "null-is-not-the-empty-string" (nullStr <> emptyStr)

// ---- a `null` PATTERN --------------------------------------------------------

let describe (s : string) : string =
    match s with
    | null -> "null"
    | "" -> "empty"
    | v -> "value:" + v

eq "pattern-null" (describe nullStr) "null"
eq "pattern-empty" (describe emptyStr) "empty"
eq "pattern-value" (describe realStr) "value:x"

// the null clause is not reached by a value, whatever its order
let describeReordered (s : string) : string =
    match s with
    | "" -> "empty"
    | null -> "null"
    | _ -> "value"

eq "reordered-null" (describeReordered nullStr) "null"
eq "reordered-empty" (describeReordered emptyStr) "empty"
eq "reordered-value" (describeReordered realStr) "value"

// null inside a larger pattern
let pairOf (a : string, b : string) : string =
    match a, b with
    | null, null -> "both"
    | null, _ -> "first"
    | _, null -> "second"
    | _ -> "neither"

eq "both-null" (pairOf (null, null)) "both"
eq "first-null" (pairOf (null, "b")) "first"
eq "second-null" (pairOf ("a", null)) "second"
eq "neither-null" (pairOf ("a", "b")) "neither"

// ---- the String helpers that answer for null --------------------------------

test "IsNullOrEmpty-of-null" (System.String.IsNullOrEmpty nullStr)
test "IsNullOrEmpty-of-empty" (System.String.IsNullOrEmpty emptyStr)
test "IsNullOrEmpty-of-a-value" (not (System.String.IsNullOrEmpty realStr))

test "IsNullOrWhiteSpace-of-null" (System.String.IsNullOrWhiteSpace nullStr)
test "IsNullOrWhiteSpace-of-empty" (System.String.IsNullOrWhiteSpace emptyStr)
test "IsNullOrWhiteSpace-of-spaces" (System.String.IsNullOrWhiteSpace "   ")
test "IsNullOrWhiteSpace-of-a-value" (not (System.String.IsNullOrWhiteSpace realStr))
test "IsNullOrWhiteSpace-of-padded-text" (not (System.String.IsNullOrWhiteSpace " x "))

// ---- Unchecked.defaultof -----------------------------------------------------

// the numeric zeroes
eq "default-int" (string (Unchecked.defaultof<int>)) "0"
eq "default-int64" (string (Unchecked.defaultof<int64>)) "0"
eq "default-float" (string (Unchecked.defaultof<float>)) "0"
eq "default-float32" (string (Unchecked.defaultof<float32>)) "0"

// bool and char
test "default-bool-is-false" (not (Unchecked.defaultof<bool>))
eq "default-char-code" (string (int (Unchecked.defaultof<char>))) "0"

// a reference type defaults to NULL
test "default-string-is-null" (isNull (Unchecked.defaultof<string>))

// the default of a type is what an uninitialised array slot holds
let ints : int[] = Array.zeroCreate 3
eq "array-of-int-is-zeroed" (String.concat "," (List.ofArray (Array.map string ints))) "0,0,0"

let strs : string[] = Array.zeroCreate 2
test "array-of-string-is-nulled" (isNull strs.[0])
test "array-of-string-is-nulled-throughout" (isNull strs.[1])

let bools : bool[] = Array.zeroCreate 2
test "array-of-bool-is-false" (not bools.[0])

// writing over a slot replaces the default
strs.[0] <- "here"
eq "written-slot" strs.[0] "here"
test "unwritten-slot-still-null" (isNull strs.[1])

// ---- laundering null into an OPTION ------------------------------------------

test "ofObj-of-null-is-none" (Option.isNone (Option.ofObj nullStr))
test "ofObj-of-a-value-is-some" (Option.isSome (Option.ofObj realStr))
eq "ofObj-carries-the-value" (Option.defaultValue "?" (Option.ofObj realStr)) "x"
eq "ofObj-of-null-takes-the-default" (Option.defaultValue "?" (Option.ofObj nullStr)) "?"

// the empty string is a VALUE, so it survives the trip
test "ofObj-of-empty-is-some" (Option.isSome (Option.ofObj emptyStr))
eq "ofObj-of-empty-carries-it" (Option.defaultValue "?" (Option.ofObj emptyStr)) ""

// and back out again
test "toObj-of-none-is-null" (isNull (Option.toObj (None : string option)))
eq "toObj-of-some" (Option.toObj (Some "y")) "y"

// a round trip through the option
let launder (s : string) : string = Option.defaultValue "(none)" (Option.ofObj s)
eq "round-trip-null" (launder nullStr) "(none)"
eq "round-trip-value" (launder realStr) "x"
eq "round-trip-empty" (launder emptyStr) ""

// mapping over the option never runs the function for null
let mutable ran = 0
let mapped (s : string) : string =
    match Option.map (fun (v : string) -> ran <- ran + 1; v + "!") (Option.ofObj s) with
    | Some v -> v
    | None -> "(skipped)"

eq "mapped-a-value" (mapped realStr) "x!"
eq "mapped-ran-once" (string ran) "1"
eq "mapped-null" (mapped nullStr) "(skipped)"
eq "mapped-did-not-run-again" (string ran) "1"

// ---- null flowing through ordinary code --------------------------------------

// a null string may be BOUND and passed around; only using it as a string
// would fail, and nothing here does
let holdsNull : string list = [ null; "a"; null ]
eq "nulls-in-a-list" (string (List.length holdsNull)) "3"
eq "count-the-nulls" (string (List.length (List.filter isNull holdsNull))) "2"
eq "count-the-values" (string (List.length (List.filter (fun s -> not (isNull s)) holdsNull))) "1"

// filtered out, the rest are ordinary strings
eq "survivors-concatenate" (String.concat "" (List.filter (fun s -> not (isNull s)) holdsNull)) "a"

// a null in a RECORD field
type Holder = { Name : string; Tag : string }

let h = { Name = "n"; Tag = null }
test "record-field-is-null" (isNull h.Tag)
test "the-other-field-is-not" (not (isNull h.Name))

// copy-and-update replaces it
let h2 = { h with Tag = "t" }
eq "updated-field" h2.Tag "t"
test "the-original-still-null" (isNull h.Tag)

// and the other way
let h3 = { h2 with Tag = null }
test "nulled-again" (isNull h3.Tag)

// ---- obj, where anything may be null -----------------------------------------

let asObj : obj = null
test "obj-null" (isNull asObj)

let boxed : obj = box 5
test "boxed-value-is-not-null" (not (isNull boxed))

// a type test against a null answers false, it does not throw
test "type-test-on-null-is-false" (not (asObj :? string))
test "type-test-on-a-value" (boxed :? int)

printfn "DONE tests=%d failures=%d" ntests failures

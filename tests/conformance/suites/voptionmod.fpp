// ValueOption, ported from dotnet/fsharp's
// tests/FSharp.Core.UnitTests/FSharp.Core/Microsoft.FSharp.Core/ValueOptionModule
// and the voption cases of tests/fsharp/core/optionalArgs.
//
// `ValueSome`/`ValueNone` answer everything `Some`/`None` do — the whole
// point is that the two are interchangeable in behaviour and differ only in
// representation, which is why the checks below are the Option ones with the
// names swapped, plus the conversions BETWEEN the two.
//
// DROPPED: `[<Struct>]`-ness itself. In .NET a voption is a struct and an
// option is a reference; here neither is observable from inside the language
// and the representation is this compiler's business (see DIVERGENCES.md).
// Also dropped: `ValueOption.ofObj`/`toObj`, which F# does not have on the
// value flavour, though this prelude does.
module Core_voptionmod

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

let some5 = ValueSome 5
let none1 : int voption = ValueNone
let someS = ValueSome "a"
let noneS : string voption = ValueNone

// ---- construction and matching -----------------------------------------------

eq "match-some" (string (match some5 with ValueSome v -> v | ValueNone -> 0)) "5"
eq "match-none" (string (match none1 with ValueSome v -> v | ValueNone -> 0)) "0"
eq "match-string-some" (match someS with ValueSome v -> v | ValueNone -> "?") "a"
eq "match-string-none" (match noneS with ValueSome v -> v | ValueNone -> "?") "?"

// a nested one
let nested = ValueSome (ValueSome 1)
eq "nested-match"
   (string (match nested with
            | ValueSome (ValueSome v) -> v
            | ValueSome ValueNone -> -1
            | ValueNone -> -2))
   "1"

// ---- the MEMBERS -------------------------------------------------------------

test "IsSome-of-some" some5.IsSome
test "IsSome-of-none" (not none1.IsSome)
test "IsNone-of-none" none1.IsNone
test "IsNone-of-some" (not some5.IsNone)
eq "Value-of-some" (string some5.Value) "5"
eq "Value-of-a-string-some" someS.Value "a"

// the members through a FUNCTION, where the receiver is a parameter
let describe (o : int voption) : string =
    if o.IsSome then "some:" + string o.Value else "none"

eq "member-through-a-parameter-some" (describe some5) "some:5"
eq "member-through-a-parameter-none" (describe none1) "none"

// ---- the MODULE --------------------------------------------------------------

test "isSome" (ValueOption.isSome some5)
test "isNone" (ValueOption.isNone none1)
test "isSome-of-none" (not (ValueOption.isSome none1))
test "isNone-of-some" (not (ValueOption.isNone some5))

eq "map-over-some" (string (ValueOption.map (fun v -> v * 2) some5)) "10"
eq "map-over-none" (string (ValueOption.map (fun v -> v * 2) none1)) "ValueNone"
eq "map-changes-the-type" (ValueOption.defaultValue "?" (ValueOption.map string some5)) "5"

eq "bind-over-some" (string (ValueOption.bind (fun v -> ValueSome (v + 1)) some5)) "6"
eq "bind-to-none" (string (ValueOption.bind (fun _ -> (ValueNone : int voption)) some5)) "ValueNone"
eq "bind-over-none" (string (ValueOption.bind (fun v -> ValueSome (v + 1)) none1)) "ValueNone"

eq "filter-keeps" (string (ValueOption.filter (fun v -> v > 1) some5)) "5"
eq "filter-drops" (string (ValueOption.filter (fun v -> v > 9) some5)) "ValueNone"
eq "filter-of-none" (string (ValueOption.filter (fun v -> v > 1) none1)) "ValueNone"

test "forall-over-some-true" (ValueOption.forall (fun v -> v = 5) some5)
test "forall-over-some-false" (not (ValueOption.forall (fun v -> v = 4) some5))
test "forall-over-none-is-true" (ValueOption.forall (fun v -> v = 4) none1)
test "exists-over-some" (ValueOption.exists (fun v -> v = 5) some5)
test "exists-over-none-is-false" (not (ValueOption.exists (fun v -> v = 5) none1))

eq "defaultValue-of-some" (string (ValueOption.defaultValue 9 some5)) "5"
eq "defaultValue-of-none" (string (ValueOption.defaultValue 9 none1)) "9"
eq "defaultWith-of-some" (string (ValueOption.defaultWith (fun () -> 9) some5)) "5"
eq "defaultWith-of-none" (string (ValueOption.defaultWith (fun () -> 9) none1)) "9"

// defaultWith does not RUN its function when there is a value
let mutable calls = 0
eq "defaultWith-some-value" (string (ValueOption.defaultWith (fun () -> calls <- calls + 1; 0) some5)) "5"
eq "defaultWith-did-not-run" (string calls) "0"
eq "defaultWith-none-value" (string (ValueOption.defaultWith (fun () -> calls <- calls + 1; 7) none1)) "7"
eq "defaultWith-ran-once" (string calls) "1"

eq "orElse-of-some" (string (ValueOption.orElse (ValueSome 9) some5)) "5"
eq "orElse-of-none" (string (ValueOption.orElse (ValueSome 9) none1)) "9"
eq "orElseWith-of-none" (string (ValueOption.orElseWith (fun () -> ValueSome 8) none1)) "8"

eq "count-of-some" (string (ValueOption.count some5)) "1"
eq "count-of-none" (string (ValueOption.count none1)) "0"

eq "fold-over-some" (string (ValueOption.fold (fun s v -> s + v) 10 some5)) "15"
eq "fold-over-none" (string (ValueOption.fold (fun s v -> s + v) 10 none1)) "10"
eq "foldBack-over-some" (string (ValueOption.foldBack (fun v s -> s + v) some5 10)) "15"
eq "foldBack-over-none" (string (ValueOption.foldBack (fun v s -> s + v) none1 10)) "10"

eq "toList-of-some" (String.concat "," (List.map string (ValueOption.toList some5))) "5"
eq "toList-of-none" (string (List.length (ValueOption.toList none1))) "0"
eq "toArray-of-some" (string (ValueOption.toArray some5).Length) "1"
eq "toArray-of-none" (string (ValueOption.toArray none1).Length) "0"

eq "flatten-of-nested-some" (string (ValueOption.flatten (ValueSome (ValueSome 1)))) "1"
eq "flatten-of-inner-none" (string (ValueOption.flatten (ValueSome (ValueNone : int voption)))) "ValueNone"
eq "flatten-of-outer-none" (string (ValueOption.flatten (ValueNone : int voption voption))) "ValueNone"

// iter runs exactly once for a value and not at all for none
let mutable seen = 0
ValueOption.iter (fun v -> seen <- seen + v) some5
eq "iter-over-some" (string seen) "5"
ValueOption.iter (fun v -> seen <- seen + v) none1
eq "iter-over-none" (string seen) "5"

// ---- converting to and from Option -------------------------------------------

eq "toOption-of-some" (string (ValueOption.toOption some5)) "Some(5)"
eq "toOption-of-none" (string (ValueOption.toOption none1)) ""
eq "ofOption-of-some" (string (ValueOption.ofOption (Some 3))) "3"
eq "ofOption-of-none" (string (ValueOption.ofOption (None : int option))) "ValueNone"

// a round trip preserves both shapes
eq "round-trip-some" (string (ValueOption.ofOption (ValueOption.toOption some5))) "5"
eq "round-trip-none" (string (ValueOption.ofOption (ValueOption.toOption none1))) "ValueNone"

// ---- equality, comparison and printing ---------------------------------------

test "some-equals-itself" (some5 = ValueSome 5)
test "some-differs-by-payload" (some5 <> ValueSome 6)
test "none-equals-none" (none1 = ValueNone)
test "some-differs-from-none" (some5 <> none1)

test "none-sorts-before-some" (compare none1 some5 < 0)
test "somes-compare-by-payload" (compare (ValueSome 1) (ValueSome 2) < 0)
// .NET UNWRAPS a ValueSome here and keeps the wrapper for a Some. Not a
// symmetry anyone would design; it is what the oracle answers.
eq "printed-some" (string some5) "5"
eq "printed-none" (string none1) "ValueNone"

// ---- voption in ordinary data structures -------------------------------------

let xs = [ ValueSome 1; ValueNone; ValueSome 3 ]
eq "list-length" (string (List.length xs)) "3"
eq "count-the-somes" (string (List.length (List.filter ValueOption.isSome xs))) "2"
eq "sum-the-payloads"
   (string (List.fold (fun acc o -> acc + ValueOption.defaultValue 0 o) 0 xs))
   "4"
eq "mapped-list" (String.concat "," (List.map (fun o -> string (ValueOption.defaultValue 0 o)) xs)) "1,0,3"

// as a record field
type Row = { Key : string; Val : int voption }

let rows = [ { Key = "a"; Val = ValueSome 1 }; { Key = "b"; Val = ValueNone } ]
eq "field-some" (string (List.head rows).Val) "1"
eq "present-rows" (string (List.length (List.filter (fun r -> r.Val.IsSome) rows))) "1"

printfn "DONE tests=%d failures=%d" ntests failures

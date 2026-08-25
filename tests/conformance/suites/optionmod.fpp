// THE OPTION AND RESULT MODULES, ported from dotnet/fsharp's
// tests/FSharp.Core.UnitTests/FSharp.Core/Microsoft.FSharp.Core (OptionModule,
// ResultModule) and the option cases of Conformance/Expressions.
//
// Both are ordinary unions with a module of functions over them, so the
// interesting part is what each function does with the EMPTY case and in what
// order it runs effects — `defaultWith` must not evaluate its fallback when
// there is a value, `orElse` must not build its alternative.
//
// DROPPED: `Option.ofObj`/`toObj` and `ofNullable` (no null-valued reference
// types here), and the `Result` interop with exceptions.
module Core_optionmod

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- construction and inspection -----------------------------------------

let some5 : int option = Some 5
let none0 : int option = None

test "isSome" (Option.isSome some5 && not (Option.isSome none0))
test "isNone" (Option.isNone none0 && not (Option.isNone some5))
test "get" (Option.get some5 = 5)
test "count" (Option.count some5 = 1 && Option.count none0 = 0)
test "match-some" (match some5 with Some v -> v = 5 | None -> false)
test "match-none" (match none0 with Some _ -> false | None -> true)

// ---- map / bind / iter ----------------------------------------------------

test "map-some" (Option.map (fun v -> v * 2) some5 = Some 10)
test "map-none" (Option.map (fun v -> v * 2) none0 = None)
test "bind-some" (Option.bind (fun v -> Some (v + 1)) some5 = Some 6)
test "bind-to-none" (Option.bind (fun _ -> None) some5 = None)
test "bind-none" (Option.bind (fun v -> Some (v + 1)) none0 = None)

let mutable iterated = 0
Option.iter (fun v -> iterated <- iterated + v) some5
test "iter-some" (iterated = 5)
Option.iter (fun v -> iterated <- iterated + v) none0
test "iter-none-does-nothing" (iterated = 5)

// map does NOT run its function on None
let mutable mapped = 0
let _ = Option.map (fun v -> mapped <- mapped + 1; v) none0
test "map-none-does-not-call" (mapped = 0)

// ---- defaults -------------------------------------------------------------

test "defaultValue-some" (Option.defaultValue 9 some5 = 5)
test "defaultValue-none" (Option.defaultValue 9 none0 = 9)
test "defaultWith-some" (Option.defaultWith (fun () -> 9) some5 = 5)
test "defaultWith-none" (Option.defaultWith (fun () -> 9) none0 = 9)

// the fallback is not built when there is a value
let mutable fellBack = 0
let _ = Option.defaultWith (fun () -> fellBack <- fellBack + 1; 9) some5
test "defaultWith-lazy" (fellBack = 0)

test "orElse-some" (Option.orElse (Some 9) some5 = Some 5)
test "orElse-none" (Option.orElse (Some 9) none0 = Some 9)
test "orElseWith-none" (Option.orElseWith (fun () -> Some 9) none0 = Some 9)

// ---- filter / exists / forall / fold --------------------------------------

test "filter-keeps" (Option.filter (fun v -> v > 1) some5 = Some 5)
test "filter-drops" (Option.filter (fun v -> v > 9) some5 = None)
test "filter-none" (Option.filter (fun v -> v > 1) none0 = None)
test "exists-some" (Option.exists (fun v -> v = 5) some5)
test "exists-none" (not (Option.exists (fun v -> v = 5) none0))
test "forall-some" (Option.forall (fun v -> v = 5) some5)
test "forall-none-is-true" (Option.forall (fun v -> v = 9) none0)
test "fold" (Option.fold (fun acc v -> acc + v) 1 some5 = 6)
test "fold-none" (Option.fold (fun acc v -> acc + v) 1 none0 = 1)
test "contains" (Option.contains 5 some5 && not (Option.contains 9 some5))

// ---- conversions ----------------------------------------------------------

test "toList" (Option.toList some5 = [ 5 ] && Option.toList none0 = [])
test "toArray" (Array.toList (Option.toArray some5) = [ 5 ])
test "flatten" (Option.flatten (Some (Some 5)) = Some 5)
test "flatten-inner-none" (Option.flatten (Some (None : int option)) = None)

// ---- equality, comparison and nesting -------------------------------------

test "eq" (Some 1 = Some 1 && Some 1 <> Some 2)
test "eq-none" (none0 = None)
test "order" (compare (None : int option) (Some 1) < 0)
test "order-some" (compare (Some 1) (Some 2) < 0)
test "sort" (List.sort [ Some 2; None; Some 1 ] = [ None; Some 1; Some 2 ])
test "nested" (Some (Some 1) = Some (Some 1))
test "option-of-tuple" (Some (1, "a") = Some (1, "a"))
test "in-list" (List.choose (fun v -> if v > 1 then Some v else None) [ 1; 2; 3 ] = [ 2; 3 ])

// ---- Result ---------------------------------------------------------------

let ok5 : Result<int, string> = Ok 5
let err : Result<int, string> = Error "bad"

test "result-match-ok" (match ok5 with Ok v -> v = 5 | Error _ -> false)
test "result-match-error" (match err with Ok _ -> false | Error m -> m = "bad")
test "result-map" (Result.map (fun v -> v * 2) ok5 = Ok 10)
test "result-map-error-passes" (Result.map (fun v -> v * 2) err = Error "bad")
test "result-mapError" (Result.mapError (fun m -> m + "!") err = Error "bad!")
test "result-mapError-ok-passes" (Result.mapError (fun m -> m + "!") ok5 = Ok 5)
test "result-bind" (Result.bind (fun v -> Ok (v + 1)) ok5 = Ok 6)
test "result-bind-to-error" (Result.bind (fun _ -> Error "no") ok5 = Error "no")
test "result-bind-error" (Result.bind (fun v -> Ok (v + 1)) err = Error "bad")
test "result-eq" (Ok 1 = Ok 1 && (Ok 1 : Result<int, string>) <> Error "x")

printfn "DONE tests=%d failures=%d" ntests failures

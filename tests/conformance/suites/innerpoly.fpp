// Ported from dotnet/fsharp tests/fsharp/core/innerpoly/test.fsx into the
// common F#/F++ subset. Dropped: TestNullIsGeneralizeable (System List/null),
// type functions (`let f<'a> = ...` — TestOptimizationOfTypeFunctions...,
// FSharp_1_0_Bug1024*), the System.Nullable / constraint-micro modules
// (%A printing, Unchecked.defaultof, constraint syntax), the SRTP sincos and
// Clampage witness modules, and Bug11620 (interface casts). The heart of the
// original — let-polymorphism through non-trivial patterns, kept verbatim —
// plus the polymorphic-inner-function prints.
module Core_innerpoly

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// compile-only in the original: a partially-polymorphic inner letrec used at
// several instantiations (calling it would loop)
let f (x : 'a) =
    let rec g1 y z = g2 y z
    and g2 y z = g1 y z in
    g1 "a" 1, g1 1 "a", g2 "a" "b", g2 3 4

let id2 x = x

type r<'a, 'b> = { a : 'a list; b : 'b list list }
type r2<'a, 'b> = R2 of 'a list * 'b list list

let () =
    // let-polymorphism for non-trivial patterns
    let a, b = None, None in
    let _ = (a : int option) in
    let _ = (a : string option) in
    let _ = (b : int option) in
    let _ = (b : string option) in
    let f (x : 'a) (y : 'b) =
        let _ = (a : 'a option) in
        let _ = (a : 'b option) in
        let _ = (b : 'a option) in
        let _ = (b : 'b option) in
        () in
    f 1 "a";
    f 1 1;
    let { a = a; b = b } = { a = []; b = [ [] ] } in
    let _ = (a : int list) in
    let _ = (a : string list) in
    let _ = (b : int list list) in
    let _ = (b : string list list) in
    let f (x : 'a) (y : 'b) =
        let _ = (a : 'a list) in
        let _ = (a : 'a list) in
        let _ = (b : 'b list list) in
        let _ = (b : 'b list list) in
        () in
    f 1 "a";
    f 1 1;
    let (R2 (a, b)) = R2 ([], [ [] ]) in
    let _ = (a : int list) in
    let _ = (a : string list) in
    let _ = (b : int list list) in
    let _ = (b : string list list) in
    let f (x : 'a) (y : 'b) =
        let _ = (a : 'a list) in
        let _ = (a : 'a list) in
        let _ = (b : 'b list list) in
        let _ = (b : 'b list list) in
        () in
    f 1 "a";
    f 1 1;
    let (R2 ((a as a2), (b as b2))) = R2 ([], [ [] ]) in
    let _ = (a2 : int list) in
    let _ = (a2 : string list) in
    let _ = (b2 : int list list) in
    let _ = (b2 : string list list) in
    let f (x : 'a) (y : 'b) =
        let _ = (a2 : 'a list) in
        let _ = (a2 : 'a list) in
        let _ = (b2 : 'b list list) in
        let _ = (b2 : 'b list list) in
        () in
    f 1 "a";
    f 1 1;
    // possibly-failing versions of the above
    let [ (a, b) ] = [ (None, None) ] in
    let _ = (a : int option) in
    let _ = (a : string option) in
    let _ = (b : int option) in
    let _ = (b : string option) in
    let f (x : 'a) (y : 'b) =
        let _ = (a : 'a option) in
        let _ = (a : 'b option) in
        let _ = (b : 'a option) in
        let _ = (b : 'b option) in
        () in
    f 1 "a";
    f 1 1;
    let [ { a = a; b = b } ] = [ { a = []; b = [ [] ] } ] in
    let _ = (a : int list) in
    let _ = (a : string list) in
    let _ = (b : int list list) in
    let _ = (b : string list list) in
    let f (x : 'a) (y : 'b) =
        let _ = (a : 'a list) in
        let _ = (a : 'a list) in
        let _ = (b : 'b list list) in
        let _ = (b : 'b list list) in
        () in
    f 1 "a";
    f 1 1;
    let [ (R2 (a, b)) ] = [ R2 ([], [ [] ]) ] in
    let _ = (a : int list) in
    let _ = (a : string list) in
    let _ = (b : int list list) in
    let _ = (b : string list list) in
    let f (x : 'a) (y : 'b) =
        let _ = (a : 'a list) in
        let _ = (a : 'a list) in
        let _ = (b : 'b list list) in
        let _ = (b : 'b list list) in
        () in
    f 1 "a";
    f 1 1;
    let [ (R2 ((a as a2), (b as b2))) ] = [ R2 ([], [ [] ]) ] in
    let _ = (a2 : int list) in
    let _ = (a2 : string list) in
    let _ = (b2 : int list list) in
    let _ = (b2 : string list list) in
    let f (x : 'a) (y : 'b) =
        let _ = (a2 : 'a list) in
        let _ = (a2 : 'a list) in
        let _ = (b2 : 'b list list) in
        let _ = (b2 : 'b list list) in
        () in
    f 1 "a";
    f 1 1;
    ()

test "innerpoly-compiled" true

// a polymorphic inner function applied to two different printf partials
let _ =
    let f x = x in
    f (printfn "%s") "Hello, world!";
    f (printfn "%d") 3;
    f (printfn "%s") "Hello, world!"

let test5365 () =
    let f x = x in
    f (printfn "%s") "Hello, world!";
    f (printfn "%d") 3;
    f (printfn "%s") "Hello, world!"

test5365 ()
test5365 ()

test "innerpoly-prints" true

printfn "DONE tests=%d failures=%d" ntests failures

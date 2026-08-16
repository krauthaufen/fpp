// Ported from dotnet/fsharp tests/fsharp/core/lift/test.fsx into the
// common F#/F++ subset. The original reports through stderr; here the
// failures print to stdout under the harness convention. Test content is
// kept intact: closed-lambda lifting shapes and the ref-cell case that
// guards against lifting effectful expressions.
module Core_lift

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// one lifted binding, one lifted expression
let test2924 () =
    let constt = [ 2; 3; 4 ] in
    List.map (fun i -> i + 2) constt

test "iniiu9" (test2924 () = [ 4; 5; 6 ])

// two lifted expressions
let test2925 () = List.map (fun i -> i + 6) [ 2; 3; 4 ]

test "iniiu9h39" (test2925 () = [ 8; 9; 10 ])

// one lifted binding, one lifted expression
let test2926 () =
    let f = fun i -> i + i + i in
    List.map f [ 2; 3; 4 ]

test "iui2iu284" (test2926 () = [ 6; 9; 12 ])

// one lifted binding, one lifted nested binding, one lifted expression
let test2946 () =
    let f = fun i -> i + i + i in
    List.map f ((let g = (fun j -> j + j) in g 1) :: [ 3; 4 ])

test "72uiu284" (test2946 () = [ 6; 9; 12 ])

// make sure references don't get lifted
let test2947 () =
    let f () = let x = ref 1 in (fun i -> x := !x + i; !x)
    test "jd23er84" (f () 3 = 4)
    // this would fail if we had lifted the "ref" expression
    test "jdbtr284" (f () 3 = 4)
    // no silly optimizations in the presence of side effects
    let f2 = f ()
    test "jd2dvr4" (f2 3 = 4)
    test "jd232d" (f2 3 = 7)

test2947 ()

printfn "DONE tests=%d failures=%d" ntests failures

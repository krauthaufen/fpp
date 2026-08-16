// Ported from dotnet/fsharp tests/fsharp/core/apporder/test.fsx into the
// common F#/F++ subset. Dropped: the `obj <- f` captured variants (function
// boxed into an obj-typed mutable), AppTwoRecGeneric/AppOneRecGeneric
// (generic member constraints on local classes), MemberAppOrder's overload
// blocks, RecordInitialisationWithDifferentTypes' float/decimal mix.
// `%A` tracing prints from the original are made typed or dropped; the
// tracing that MATTERS (evaluation-order strings via `out`) is kept intact.
module Core_apporder

let mutable ntests = 0
let mutable failures = 0
let report_failure (s : string) =
    failures <- failures + 1
    printfn "NO: %s" s

let out (r : string list ref) (s : string) = r := !r @ [ s ]

let check (s : string) (actual : string list) (expected : string list) =
    ntests <- ntests + 1
    if actual = expected then printfn "%s: OK" s
    else report_failure s

let checki (s : string) (actual : int * int) (expected : int * int) =
    ntests <- ntests + 1
    if actual = expected then printfn "%s: OK" s
    else report_failure s

let check3 (s : string) (actual : int * int * int) (expected : int * int * int) =
    ntests <- ntests + 1
    if actual = expected then printfn "%s: OK" s
    else report_failure s

let checks (s : string) (actual : string) (expected : string) =
    ntests <- ntests + 1
    if actual = expected then printfn "%s: OK" s
    else report_failure s

// ---- mutation of argument values in other arguments ---------------------

module CheckMutationOfArgumentValuesInOtherArguments =
    let test1232 () =
        let mutable cell1 = 1
        let f1 x = (fun y -> (x, y))
        let f2 x y = (x, y)
        cell1 <- 1
        let res = f1 (cell1 <- 11; cell1) cell1
        checki "test1232 - test1" res (11, 11)
        cell1 <- 1
        let res = f1 cell1 (cell1 <- 21; cell1)
        checki "test1232 - test2" res (1, 21)
        cell1 <- 1
        let res = (f1 (cell1 <- 11; cell1)) cell1
        checki "test1232 - test3" res (11, 11)
        cell1 <- 1
        let res = (f1 cell1) (cell1 <- 21; cell1)
        checki "test1232 - test4" res (1, 21)
        cell1 <- 1
        let res = f2 (cell1 <- 11; cell1) cell1
        checki "test1232 - test5" res (11, 11)
        cell1 <- 1
        let res = f2 cell1 (cell1 <- 21; cell1)
        checki "test1232 - test6" res (1, 21)
        cell1 <- 1
        let res = (f2 cell1) (cell1 <- 21; cell1)
        checki "test1232 - test7" res (1, 21)

    test1232 ()

    let test1233 () =
        let cell1 = ref 1
        let f1 x = cell1 := 4; (fun y -> (x, y, !cell1))
        let f2 x y = (x, y, !cell1)
        cell1 := 1
        let res = f1 (cell1 := 11; !cell1) (!cell1)
        check3 "test1233 - test1" res (11, 11, 4)
        cell1 := 1
        let res = (f1 (cell1 := 11; !cell1)) (!cell1)
        check3 "test1233 - test2" res (11, 4, 4)
        cell1 := 1
        let res = f1 (!cell1) (cell1 := 21; !cell1)
        check3 "test1233 - test3" res (1, 21, 4)
        cell1 := 1
        let res = (f1 (!cell1)) (cell1 := 21; !cell1)
        check3 "test1233 - test4" res (1, 21, 21)
        cell1 := 1
        let res = f2 (cell1 := 11; !cell1) (!cell1)
        check3 "test1233 - test5" res (11, 11, 11)

    test1233 ()

// ---- application order, two args at a time ------------------------------

module AppTwo =
    let test1 () =
        let r = ref []
        let f x = out r "app1"; (fun y -> out r "app2")
        f (out r "1") (out r "2")
        check "(two args at a time) test1" (!r) [ "1"; "2"; "app1"; "app2" ]

    let test2 () =
        let r = ref []
        let f x y = out r "app1"; out r "app2"
        f (out r "1") (out r "2")
        check "(two args at a time) test2" (!r) [ "1"; "2"; "app1"; "app2" ]

    let test3 () =
        let r = ref []
        let f = out r "f0"; (fun x -> out r "app1"; (fun y -> out r "app2"))
        f (out r "1") (out r "2")
        check "(two args at a time) test3" (!r) [ "f0"; "1"; "2"; "app1"; "app2" ]

    let test1top =
        let r = ref []
        let f x = out r "app1"; (fun y -> out r "app2")
        f (out r "1") (out r "2")
        fun () -> check "(two args at a time) test1top" (!r) [ "1"; "2"; "app1"; "app2" ]

    let run () =
        test1 ()
        test2 ()
        test3 ()
        test1top ()

AppTwo.run ()

// ---- application order, one arg at a time -------------------------------

module AppOne =
    let test1 () =
        let r = ref []
        let f x = out r "app1"; (fun y -> out r "app2")
        (f (out r "1")) (out r "2")
        check "(one arg at a time) test1" (!r) [ "1"; "app1"; "2"; "app2" ]

    let test2 () =
        let r = ref []
        let f x y = out r "app1"; out r "app2"
        (f (out r "1")) (out r "2")
        check "(one arg at a time) test2" (!r) [ "1"; "2"; "app1"; "app2" ]

    let test3 () =
        let r = ref []
        let f = out r "f0"; (fun x -> out r "app1"; (fun y -> out r "app2"))
        (f (out r "1")) (out r "2")
        check "(one arg at a time) test3" (!r) [ "f0"; "1"; "app1"; "2"; "app2" ]

    let run () =
        test1 ()
        test2 ()
        test3 ()

AppOne.run ()

// ---- same, through a recursive function ---------------------------------

module AppTwoRec =
    let test1 () =
        let r = ref []
        let rec f x = out r "app1"; (fun y -> out r "app2")
        f (out r "1") (out r "2")
        check "(rec two args) test1" (!r) [ "1"; "2"; "app1"; "app2" ]

    let test2 () =
        let r = ref []
        let rec f x y = out r "app1"; out r "app2"
        f (out r "1") (out r "2")
        check "(rec two args) test2" (!r) [ "1"; "2"; "app1"; "app2" ]

    let run () =
        test1 ()
        test2 ()

AppTwoRec.run ()

// ---- order of record initialisation -------------------------------------

type R3 = { A : int; B : int; C : int }

module OrderOfRecordInitialisation =
    let expected = { A = 1; B = 2; C = 3 }

    let checkR (s : string) (actual : R3) =
        ntests <- ntests + 1
        if actual = expected then printfn "%s: OK" s
        else report_failure s

    let shouldInit1 () =
        let order = ref ""
        let actual =
            { A = (order := !order + "1"; 1)
              B = (order := !order + "2"; 2)
              C = (order := !order + "3"; 3) }
        checkR "cnclewlecp2" actual
        checks "ceiewoi" (!order) "123"

    let shouldInit2 () =
        let order = ref ""
        let actual =
            { A = (order := !order + "1"; 1)
              C = (order := !order + "2"; 3)
              B = (order := !order + "3"; 2) }
        checkR "cd33289e0ewn1" actual
        checks "ewlknewv90we2" (!order) "123"

    let shouldInit3 () =
        let order = ref ""
        let actual =
            { B = (order := !order + "1"; 2)
              A = (order := !order + "2"; 1)
              C = (order := !order + "3"; 3) }
        checkR "cewekcjnwe3" actual
        checks "cewekcjnwe4" (!order) "123"

    let shouldInit5 () =
        let order = ref ""
        let actual =
            { C = (order := !order + "1"; 3)
              A = (order := !order + "2"; 1)
              B = (order := !order + "3"; 2) }
        checkR "cewekcjnwe7" actual
        checks "cewekcjnwe8" (!order) "123"

OrderOfRecordInitialisation.shouldInit1 ()
OrderOfRecordInitialisation.shouldInit2 ()
OrderOfRecordInitialisation.shouldInit3 ()
OrderOfRecordInitialisation.shouldInit5 ()

printfn "DONE tests=%d failures=%d" ntests failures

// Lazy values, from dotnet/fsharp tests/fsharp/core/lazy/test.fsx in the
// common F#/F++ subset. Dropped: the Microsoft.FSharp.Control module-path
// aliases (F++ spells Lazy members directly), the threading Bug5770 module
// and the .NET null-interface checks.
module Core_lazy

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let x = lazy 3
test "fewoin" (x.Force () = 3)

test "fedeoin1" (((lazy (lazy 3)).Force ()).Force () = 3)
test "fedeoin2" (let x = 3 in ((lazy (lazy x)).Force ()).Force () = 3)
test "fedeoin3" (let x = 3 in ((lazy (lazy (x + x))).Force ()).Force () = 6)

// force twice: the body runs ONCE
test "fedeoin4"
    (let c = ref 3
     let y = lazy (c := !c + 1; 6)
     ignore (y.Force ())
     ignore (y.Force ())
     !c = 4)
test "fedeoin5"
    (let c = ref 3
     let y = lazy (c := !c + 1; "abc")
     ignore (y.Force ())
     ignore (y.Force ())
     !c = 4)

// not created until forced
test "isv1"
    (let y = lazy 5
     let before = y.IsValueCreated
     ignore (y.Force ())
     not before && y.IsValueCreated)

// a lazy value closing over mutable state reads it at FORCE time
test "late1"
    (let c = ref 10
     let y = lazy (!c * 2)
     c := 21
     y.Force () = 42)

printfn "DONE tests=%d failures=%d" ntests failures

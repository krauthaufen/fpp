// A `module X` HEADER IS FILE-LEVEL, WHATEVER COLUMN IT LANDS ON.
//
// A nested module is spelled `module X = …`; a header with no `=` declares a
// module for what follows it. Read as a nested declaration — which is what an
// INDENTED one used to be — the header silently renames the module, and every
// reference to it resolves to nothing: a stub, and a trap when reached.
//
// It is not a hypothetical indentation: the ports CONCATENATE their sources
// (a workaround for the cross-file init bug), and `cat` glues the next file's
// first line onto a file that ends without a trailing newline. One missing
// newline in fpp.rendering's `task.fpp` indented the whole `DemoEffects`
// header by four spaces, and the port read the result as "a call into a
// sibling module stubs at program scale" (~/claude/fpp-base-snags.md #55).
//
// F# has one module declaration per file, so there is no oracle for the
// multi-header form itself — but everything below is ordinary nesting that
// fsi checks, and the indented header is the one line it cannot see.
module Core_modulelevel

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

// a nested module, spelled with `=`, is nested
module Outer =
    let inside : int = 1
    module Inner =
        let deeper : int = 2

eq "a-nested-module" (string Outer.inside) "1"
eq "and-one-inside-it" (string Outer.Inner.deeper) "2"

// a module and its members, reached from a later one
module First =
    let value : int = 7
    let twice (n : int) : int = n * 2

module Second =
    let fromFirst : int = First.twice First.value

eq "a-later-module-reaches-an-earlier-one" (string Second.fromFirst) "14"

// a nested module whose body ENDS where the next declaration is less indented
module Third =
    let a : int = 3
let afterThird : int = Third.a + 1
eq "a-body-ends-at-the-dedent" (string afterThird) "4"

printfn "DONE tests=%d failures=%d" ntests failures

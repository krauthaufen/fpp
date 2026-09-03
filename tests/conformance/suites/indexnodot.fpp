// INDEXING WITHOUT THE DOT, ported from dotnet/fsharp's
// tests/fsharp/core/array-no-dot.
//
// F# 6 made `a[i]` mean `a.[i]`. What separates indexing from application is
// ADJACENCY and nothing else: `a[i]` indexes, `f [i]` applies f to a list.
// So every case here is really about where the space is, and the suite is
// mostly pairs that differ only by one.
//
// Before this, `a[1]` parsed as `a [1]` — an application of an array to a
// list — and the error landed wherever that type went, never at the bracket.
//
// DROPPED: `expr1[expr2]` in ARGUMENT position (`printfn "%d" m[1][0]`),
// which F# refuses to disambiguate (FS3369) and this compiler indexes. The
// divergence is recorded rather than tested, since the file must compile
// under both.
module Core_indexnodot

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// ---- an ARRAY ----------------------------------------------------------------

let a = [| 10; 20; 30 |]

eq "first" (string a[0]) "10"
eq "middle" (string a[1]) "20"
eq "last" (string a[2]) "30"

// the dotted form still means the same thing
eq "dotted-form-agrees" (string a.[1]) "20"
eq "both-forms-equal" (string (a[1] = a.[1])) "True"

// the index is an EXPRESSION
let i = 2
eq "index-by-name" (string a[i]) "30"
eq "index-arithmetic" (string a[i - 1]) "20"
eq "index-from-a-call" (string a[a.Length - 1]) "30"

// in a larger expression
eq "sum-of-two" (string (a[0] + a[2])) "40"
eq "in-a-comparison" (string (a[0] < a[1])) "True"

// ---- ASSIGNMENT through it ----------------------------------------------------

let b = [| 1; 2; 3 |]
b[0] <- 99
eq "assigned" (string b[0]) "99"
b[1] <- b[0] + 1
eq "assigned-from-itself" (string b[1]) "100"
eq "the-rest-is-untouched" (string b[2]) "3"

// ---- a LIST and a STRING ------------------------------------------------------

let l = [ 1; 2; 3 ]
eq "list-index" (string l[0]) "1"
eq "list-index-last" (string l[2]) "3"

let s = "hello"
eq "string-index" (string s[1]) "e"
eq "string-index-first" (string s[0]) "h"

// ---- CHAINED, outside argument position ---------------------------------------

let m = [| [| 1; 2 |]; [| 3; 4 |] |]
let inner = m[1]
eq "index-of-an-index-in-two-steps" (string inner[0]) "3"

let chained = m[1][0]
eq "chained-in-a-binding" (string chained) "3"
eq "chained-mixed-with-the-dot" (string m[0].[1]) "2"

// ---- THE SPACE IS THE WHOLE RULE ----------------------------------------------
// With a space it is application, which is what lets a function take a list
// literal. These two lines differ by one character and mean different things.

let takesList (xs : int list) : int = List.length xs
eq "space-means-application" (string (takesList [ 1; 2; 3 ])) "3"

let arr = [| 5; 6 |]
eq "no-space-means-indexing" (string arr[0]) "5"

// an array literal is still an array literal where nothing precedes it
let fresh = [| 7; 8 |]
eq "array-literal-unaffected" (string fresh[1]) "8"

// a list literal as an argument, with the function named by a binding
let idOf = List.length
eq "application-through-a-binding" (string (idOf [ 1; 2 ])) "2"

// ---- inside other shapes -------------------------------------------------------

let insideLambda = List.map (fun (k : int) -> a[k]) [ 0; 2 ]
eq "index-in-a-lambda" (String.concat "," (List.map string insideLambda)) "10,30"

let mutable total = 0
for k in 0 .. 2 do total <- total + a[k]
eq "index-in-a-loop" (string total) "60"

let describe (k : int) : string =
    if a[k] > 15 then "big" else "small"
eq "index-in-a-condition" (describe 0 + describe 1) "smallbig"

let viaMatch =
    match a[0] with
    | 10 -> "ten"
    | _ -> "other"
eq "index-as-a-scrutinee" viaMatch "ten"

printfn "DONE tests=%d failures=%d" ntests failures

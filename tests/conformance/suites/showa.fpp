// `%A` — the structural renderer. F# prints a string quoted, a char in
// ticks, an int64 with its L, a list with semicolons, a union case with its
// payload, and a record ONE FIELD PER LINE with each continuation lined up
// under the column it starts at. All of that is here.
//
// The output is compared to the oracle byte for byte, so every line below is
// also a check on the LAYOUT, not just the content.
//
// DROPPED: a collection long enough to wrap. F# breaks a rendering that
// passes ~80 columns onto the next line; this renderer does not
// (DIVERGENCES.md).
module Core_showa

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// the values are printed rather than compared: `%A` IS the thing under test,
// so the oracle's own bytes are the assertion
let inner (x : int) (y : int) = x + y

type Point = { X : int; Y : int }
type Single = { Only : int }
type Named = { Name : string; At : Point }
type Shape =
    | Dot
    | Circle of float
    | Rect of int * int
    | Nested of Point

printfn "int %A" 42
printfn "neg %A" (0 - 7)
printfn "float %A" 1.5
printfn "float-exp %A" 1e300
printfn "int64 %A" 3L
printfn "uint %A" 3u
printfn "bool %A" true
printfn "char %A" 'q'
printfn "string %A" "hi"
printfn "unit %A" ()

printfn "tuple %A" (1, "a")
printfn "tuple3 %A" (1, 'c', 2.5)
printfn "list %A" [ 1; 2; 3 ]
printfn "list-empty %A" ([] : int list)
printfn "list-str %A" [ "a"; "b" ]
printfn "array %A" [| 1; 2 |]
printfn "array-empty %A" ([||] : int[])
printfn "option %A" (Some 3)
printfn "option-none %A" (None : int option)
printfn "option-tuple %A" (Some (1, 2))
printfn "nested-list %A" [ [ 1 ]; [ 2; 3 ] ]
printfn "list-option %A" [ Some 1; None ]

printfn "record1 %A" { Only = 1 }
printfn "record2 %A" { X = 1; Y = 2 }
printfn "record-nested %A" { Name = "n"; At = { X = 1; Y = 2 } }
printfn "record-in-tuple %A" ({ X = 1; Y = 2 }, 5)
printfn "record-in-list %A" [ { X = 1; Y = 2 }; { X = 3; Y = 4 } ]
printfn "record-in-option %A" (Some { X = 1; Y = 2 })
printfn "record-in-array %A" [| { X = 1; Y = 2 } |]

printfn "union-nullary %A" Dot
printfn "union-one %A" (Circle 1.5)
printfn "union-two %A" (Rect (2, 3))
printfn "union-record %A" (Nested { X = 1; Y = 2 })
printfn "union-list %A" [ Dot; Circle 2.0 ]
printfn "union-option %A" (Some Dot)

test "placeholder" true
printfn "DONE tests=%d failures=%d" ntests failures

// `%A` — the structural renderer. F# prints a string quoted, a char in
// ticks, an int64 with its L, a list with semicolons, a union case with its
// payload, and a record ONE FIELD PER LINE with each continuation lined up
// under the column it starts at. All of that is here.
//
// The output is compared to the oracle byte for byte, so every line below is
// also a check on the LAYOUT, not just the content.
//
// A collection long enough to WRAP is here too: F# breaks a rendering that
// would pass 80 columns and lines the continuation up under the first
// element, which is the last thing this renderer learned.
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

// the wrap: 22 one- and two-digit elements fill a line exactly, the 23rd
// starts the next one, and an array's continuation aligns under its `[|`
printfn "wrap-none %A" [ 1 .. 22 ]
printfn "wrap-two %A" [ 1 .. 24 ]
printfn "wrap-more %A" [ 1 .. 60 ]
printfn "wrap-array %A" [| 1 .. 30 |]
printfn "wrap-strings %A" [ "aaaaaaaaaa"; "bbbbbbbbbb"; "cccccccccc"; "dddddddddd"; "eeeeeeeeee"; "ffffffffff" ]
printfn "wrap-nested %A" [ [ 1 .. 12 ]; [ 13 .. 24 ] ]

// ---- `string x` beside `%A` -------------------------------------------
// .NET renders the two differently: a record or union keeps the structured
// form (quotes and all), while a tuple, list or option renders its parts
// through their OWN ToString — so nested strings and chars lose their
// quotes and an int64 loses its suffix.
//
// DROPPED: the cases where .NET answers a CLR TYPE NAME rather than a
// rendering (`string [| 1; 2 |]` is "System.Int32[]", and Result and
// ValueOption are the same story) — see DIVERGENCES.md.

let eqs (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got [%s] want [%s]" name got want

let named = { Name = "hi"; At = { X = 1; Y = 2 } }

// a record and a union keep the structured form, nested strings QUOTED
eqs "string-record" (string named) (sprintf "%A" named)
eqs "string-record-plain" (string { X = 1; Y = 2 }) (sprintf "%A" { X = 1; Y = 2 })
eqs "string-union-nullary" (string Dot) "Dot"
eqs "string-union-payload" (string (Rect (1, 2))) "Rect (1, 2)"
eqs "string-union-one" (string (Circle 1.5)) "Circle 1.5"

// a tuple, list or option does NOT quote what is inside it
eqs "string-tuple" (string (1, "a", 'c')) "(1, a, c)"
eqs "string-tuple2" (string (1, 2)) "(1, 2)"
eqs "string-tuple-mixed" (string (true, 2L, 1.5)) "(True, 2, 1.5)"
eqs "string-list" (string [ "a"; "b" ]) "[a; b]"
eqs "string-list-int" (string [ 1; 2 ]) "[1; 2]"
eqs "string-list-empty" (string ([] : int list)) "[]"
eqs "string-list-char" (string [ 'a'; 'b' ]) "[a; b]"
eqs "string-list-nested" (string [ [ 1 ]; [ 2 ] ]) "[[1]; [2]]"
eqs "string-option-some" (string (Some "a")) "Some(a)"
eqs "string-option-none" (string (None : int option)) ""
eqs "string-option-of-tuple" (string (Some (1, "a"))) "Some((1, a))"

// a record inside a list keeps ITS form, so the two renderings meet
eqs "string-list-of-records" (string [ named ]) ("[" + sprintf "%A" named + "]")

// the primitives are the ordinary conversion, not `%A`
eqs "string-int" (string 5) "5"
eqs "string-int64" (string 5L) "5"
eqs "string-bool" (string true) "True"
eqs "string-float" (string 2.5) "2.5"
eqs "string-char" (string 'c') "c"
eqs "string-string" (string "hi") "hi"
eqs "string-unit" (string ()) ""

// interpolation renders through `string`, so it inherits all of it
eqs "interp-record" $"{named}" (string named)
// a string literal inside a hole is an error in F# too (FS3373), so the
// values are bound first
let tup = (1, "a")
let lst = [ "a" ]
eqs "interp-tuple" $"{tup}" "(1, a)"
eqs "interp-list" $"{lst}" "[a]"

test "placeholder" true
printfn "DONE tests=%d failures=%d" ntests failures

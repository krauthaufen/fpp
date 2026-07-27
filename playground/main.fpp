module Main

open Vec
open Classes

// ---- generic math at three types from ONE definition -------------------
// Hover `double`: its scheme shows the inferred Add constraint.
let double x = x + x

let ints    = printfn "double 21      = %d" (double 21)
let floats  = printfn "double 1.5     = %f" (double 1.5)
let strings = printfn "double \"ab\"    = %s" (double "ab")

// ---- vectors through the same operators --------------------------------
let p = { X = 3.0; Y = 4.0 }
let q = { X = 1.0; Y = 2.0 }

// go-to-definition on `dot`, `lengthOf`, `clamp` jumps into vec.fpp
let v1 = printfn "p + q          = (%f, %f)" (p + q).X (p + q).Y
let v2 = printfn "2 * p          = (%f, %f)" (2.0 * p).X (2.0 * p).Y
let v3 = printfn "dot p q        = %f" (dot p q)
let v4 = printfn "length p       = %f" (lengthOf p)
let v5 = printfn "clamp          = (%f, %f)" (clamp Zero One p).X (clamp Zero One p).Y

// one generic body, stamped per type — ints, vectors, halves
let s1 = printfn "sum ints       = %d" (sumOf [| 1; 2; 3; 4 |] 0)
let s2 = printfn "sum vecs (X)   = %f" (sumOf [| p; q |] Zero).X

// ---- float16: 2 bytes per element, arithmetic bit-exact ----------------
let halves = [| 1.5h; 2.25h; 0.25h |]
let h1 = printfn "sum halves     = %f" (float (sumOf halves Zero))

// ---- lazy sequences over the enumerator protocol ------------------------
let seqDemo =
    [ 1; 2; 3; 4; 5; 6 ]
    |> Seq.filter (fun v -> v % 2 = 0)
    |> Seq.map (sprintf "%A")
    |> String.concat "; "
    |> printfn "evens          = [%s]"

// ---- hover `compare`, `min`, `sqrt`: constraints in the signature ------
let ordDemo = printfn "compare 2 9    = %d" (compare 2 9)

// ---- the playground's own typeclasses (classes.fpp) --------------------
let c1 = printfn "%s" (describe "answer" 42)
let c2 = printfn "%s" (describe "pi-ish" 3.14)
let c3 = printfn "%s" (describe "ready" true)
let c4 = printfn "%s" (describe "p" p)

let m1 = printfn "mconcat ints   = %d" (mconcat [ 1; 2; 3; 4 ])
let m2 = printfn "mconcat strs   = %s" (mconcat [ "a"; "b"; "c" ])
let m3 = printfn "mconcat vecs   = (%f, %f)" (mconcat [ p; q ]).X (mconcat [ p; q ]).Y

let n1 = printfn "norm p         = %f" (norm p)
let n2 = printfn "norm -2.5      = %f" (norm (0.0 - 2.5))

// Uncomment to watch diagnostics appear as you type:
//let bad1 : int = "not an int"
//let bad2 = 1 + "x"
//let bad3 = 1.5 % 2.0y

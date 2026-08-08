// The browser-interop gate program: DOM through the generic primitives, a
// captured-state callback, string round-trips, and ZERO-COPY TypedArray
// aliasing over a pinned struct array — both directions.
module JsDemo

[<Struct>]
type P2 = { mutable X : float32; mutable Y : float32 }

let pts = [| { X = 1.5f; Y = 2.5f }; { X = 3.5f; Y = 4.5f } |]

// a TYPED per-operation import: one dedicated wasm import, the app
// supplies the JS side at instantiation ({ jsx: { mix: ... } })
[<JsImport>]
extern let mix : float -> int -> float
let mutable clicks = 0

[<Export>]
let getClicks (_x : int) : int = clicks

[<Export>]
let readX0 (_x : int) : int =
    // after JS wrote through the view, the ARRAY must show it (aliasing)
    int (pts.[0].X * 10.0f)

let go =
    let doc = Js.global_ "document"
    let btn = Js.call1 doc "createElement" (Js.ofString "button")
    Js.set btn "id" (Js.ofString "made")
    Js.set btn "textContent" (Js.ofString "hello from F++")
    let body = Js.get doc "body"
    Js.call1 body "appendChild" btn |> ignore
    // numbers, typed accessors (one crossing each way)
    Js.setNum btn "tabIndex" 7.0
    print (int (Js.getNum btn "tabIndex"))
    // strings: out and back
    print (Js.getStr btn "id")
    // a callback with CAPTURED state
    let onClick = Js.callback (fun _e -> clicks <- clicks + 1)
    Js.call2 btn "addEventListener" (Js.ofString "click") onClick |> ignore
    // zero-copy: pin, view, publish — JS sees the array's real storage
    let pv = Js.viewF32 (Array.pin pts) 4
    Js.set (Js.global_ "window") "fppView" pv
    // `new Date(0).getUTCFullYear()` — construction across the boundary
    let date = Js.new1 (Js.global_ "Date") (Js.ofNum 0.0)
    print (int (Js.toNum (Js.call0 date "getUTCFullYear")))
    print (int (mix 4.0 7))
    print "ready"

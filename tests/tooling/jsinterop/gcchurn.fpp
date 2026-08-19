// The gc-churn leg: REAL collections under the browser reactor. 500 short-
// lived wrappers, each watched two ways — a cleanup closure (kind 1) and a
// JS-handle watch (kind 0) — plus enough garbage per wrapper to force
// natural collections mid-loop. GC.Collect must fire every cleanup exactly
// once, and the glue's drain must reclaim the JS table entries.
module GcChurn

let mutable cleanups = 0

[<Export>]
let cleanupCount (_x : int) : int = cleanups

type W(h : JsObj) =
    member x.H = h

let spawn (doc : JsObj) : unit =
    let el = Js.call1 doc "createElement" (Js.ofString "div")
    let id = Js.register el
    let w = W (Js.handle id)
    Js.watch (box w) id
    GC.OnCleanup (box w) (fun () -> cleanups <- cleanups + 1)
    // ~32KB of garbage per wrapper: the 16MB heap collects many times
    let junk = Array.create 8192 id
    ignore junk

let go =
    let doc = Js.global_ "document"
    let mutable i = 0
    while i < 500 do
        spawn doc
        i <- i + 1
    print "spawned"
    GC.Collect ()
    print ("cleanups " + string cleanups)
    // the boundary still works after all those collections
    let el = Js.call1 doc "createElement" (Js.ofString "span")
    print (Js.getStr el "tagName")
    print "churn-done"

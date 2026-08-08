// The typed-DOM gate: the SAME behaviors the raw-primitives gate checks,
// through the curated hierarchy — construction, inherited members at every
// level, settable properties, typed events with captured state, styles.
module DomDemo

let mutable clicks = 0
let mutable lastX = 0

[<Export>]
let getClicks (_x : int) : int = clicks

[<Export>]
let getLastX (_x : int) : int = lastX

let go =
    let doc = Dom.Document ()
    let btn = doc.CreateElement "button"
    btn.Id <- "typed"
    btn.TextContent <- "hello typed café"
    btn.Title <- "t€xt"
    btn.TabIndex <- 5.0
    btn.Style.SetProperty ("width", "123px")
    // an inherited member THROUGH the chain: AppendChild is Node's,
    // reached from HTMLElement via Element -> Node
    doc.Body.AppendChild btn |> ignore
    // events: listener + downcast-by-rewrap, captured state
    btn.AddEventListener ("click", (fun e ->
        clicks <- clicks + 1
        match e with
        | :? MouseEvent as me -> lastX <- int me.ClientX
        | _ -> ()))
    print btn.Id
    print btn.TextContent
    print btn.Title
    print btn.TabIndex
    print (btn.Style.GetPropertyValue "width")
    print btn.TagName
    // upcast is FREE: an HTMLElement is a Node
    let asNode : Node = btn
    print asNode.TextContent
    let found = doc.GetElementById "typed"
    print found.ClassName
    found.ClassName <- "big"
    print found.ClassName
    print (doc.QuerySelector "#typed").TagName
    print (int (doc.Body.ChildNodes.Length))
    // the factory wraps at the DYNAMIC type: a canvas answers the test
    let cv = doc.CreateElement "canvas"
    (match cv with
     | :? HTMLCanvasElement as c ->
         c.Width <- 32.0
         print ("canvas " + string (int c.Width))
     | _ -> print "no-canvas")
    (match doc.CreateElement "span" with
     | :? HTMLCanvasElement -> print "wat"
     | el -> print ("span " + el.TagName))
    print "dom-ready"

// The curated DOM layer: the browser's own object model, typed. The
// hierarchy is the platform's — EventTarget -> Node -> Element ->
// HTMLElement -> the concrete elements — and every member is the browser
// member, PascalCased. Properties are properties, methods are methods
// (tupled), optional arguments are named optionals, numbers are doubles
// and CSS-ish values stay strings ("25px" is a string, not a unit type).
// Nothing is renamed, curried, or abstracted over.
//
// Each wrapper holds the JS handle. An upcast is free (real inheritance);
// a DOWNCAST is a rewrap — `MouseEvent e.Handle` is this layer's spelling
// of what the browser does implicitly. Property keys are literals, so
// every access rides the interned-externref path: one boundary crossing.
//
// Compile it alongside your program:
//     fpp build -o app.wasm stdlib/dom.fpp app.fpp
module Dom

type Event(h : JsObj) =
    member x.Handle = h
    member x.Type : string = Js.getStr h "type"
    member x.PreventDefault () : unit = Js.call0 h "preventDefault" |> ignore
    member x.StopPropagation () : unit = Js.call0 h "stopPropagation" |> ignore

and MouseEvent(h : JsObj) =
    inherit Event(h)
    member x.ClientX : float = Js.getNum h "clientX"
    member x.ClientY : float = Js.getNum h "clientY"
    member x.OffsetX : float = Js.getNum h "offsetX"
    member x.OffsetY : float = Js.getNum h "offsetY"
    member x.Button : float = Js.getNum h "button"

and KeyboardEvent(h : JsObj) =
    inherit Event(h)
    member x.Key : string = Js.getStr h "key"
    member x.Code : string = Js.getStr h "code"

and EventTarget(h : JsObj) =
    member x.Handle = h
    member x.IsNull : bool = Js.isNull h
    member x.AddEventListener (name : string, listener : Event -> unit, ?capture : bool) : unit =
        let cb = Js.callback (fun e -> listener (Wrap.Event e))
        (match capture with
         | Some c -> Js.call3 h "addEventListener" (Js.ofString name) cb (Js.ofBool c)
         | None -> Js.call2 h "addEventListener" (Js.ofString name) cb)
        |> ignore

and CSSStyleDeclaration(h : JsObj) =
    member x.Handle = h
    member x.SetProperty (name : string, value : string) : unit =
        Js.call2 h "setProperty" (Js.ofString name) (Js.ofString value) |> ignore
    member x.GetPropertyValue (name : string) : string =
        Js.toString (Js.call1 h "getPropertyValue" (Js.ofString name))
    member x.RemoveProperty (name : string) : unit =
        Js.call1 h "removeProperty" (Js.ofString name) |> ignore

and Node(h : JsObj) =
    inherit EventTarget(h)
    member x.TextContent
        with get () : string = Js.getStr h "textContent"
        and set (v : string) = Js.set h "textContent" (Js.ofString v)
    member x.AppendChild (child : Node) : Node =
        Node (Js.call1 h "appendChild" child.Handle)
    member x.RemoveChild (child : Node) : Node =
        Node (Js.call1 h "removeChild" child.Handle)
    member x.InsertBefore (newNode : Node, referenceNode : Node) : Node =
        Node (Js.call2 h "insertBefore" newNode.Handle referenceNode.Handle)
    member x.ParentNode : Node = Node (Js.get h "parentNode")
    member x.FirstChild : Node = Node (Js.get h "firstChild")
    member x.LastChild : Node = Node (Js.get h "lastChild")
    member x.NextSibling : Node = Node (Js.get h "nextSibling")
    member x.ChildNodes : NodeList = NodeList (Js.get h "childNodes")
    member x.CloneNode (?deep : bool) : Node =
        (match deep with
         | Some d -> Node (Js.call1 h "cloneNode" (Js.ofBool d))
         | None -> Node (Js.call0 h "cloneNode"))

and NodeList(h : JsObj) =
    member x.Handle = h
    member x.Length : float = Js.getNum h "length"
    member x.Item (index : int) : Node = Node (Js.item h index)

and Element(h : JsObj) =
    inherit Node(h)
    member x.Id
        with get () : string = Js.getStr h "id"
        and set (v : string) = Js.set h "id" (Js.ofString v)
    member x.ClassName
        with get () : string = Js.getStr h "className"
        and set (v : string) = Js.set h "className" (Js.ofString v)
    member x.TagName : string = Js.getStr h "tagName"
    member x.InnerHTML
        with get () : string = Js.getStr h "innerHTML"
        and set (v : string) = Js.set h "innerHTML" (Js.ofString v)
    member x.SetAttribute (name : string, value : string) : unit =
        Js.call2 h "setAttribute" (Js.ofString name) (Js.ofString value) |> ignore
    member x.GetAttribute (name : string) : string =
        Js.toString (Js.call1 h "getAttribute" (Js.ofString name))
    member x.HasAttribute (name : string) : bool =
        Js.toBool (Js.call1 h "hasAttribute" (Js.ofString name))
    member x.ScrollTop
        with get () : float = Js.getNum h "scrollTop"
        and set (v : float) = Js.setNum h "scrollTop" v
    member x.ScrollLeft
        with get () : float = Js.getNum h "scrollLeft"
        and set (v : float) = Js.setNum h "scrollLeft" v
    member x.ClientWidth : float = Js.getNum h "clientWidth"
    member x.ClientHeight : float = Js.getNum h "clientHeight"
    member x.QuerySelector (selectors : string) : Element =
        Wrap.Element (Js.call1 h "querySelector" (Js.ofString selectors))
    member x.QuerySelectorAll (selectors : string) : NodeList =
        NodeList (Js.call1 h "querySelectorAll" (Js.ofString selectors))
    member x.Remove () : unit = Js.call0 h "remove" |> ignore

and HTMLElement(h : JsObj) =
    inherit Element(h)
    member x.Style : CSSStyleDeclaration = CSSStyleDeclaration (Js.get h "style")
    member x.Title
        with get () : string = Js.getStr h "title"
        and set (v : string) = Js.set h "title" (Js.ofString v)
    member x.TabIndex
        with get () : float = Js.getNum h "tabIndex"
        and set (v : float) = Js.setNum h "tabIndex" v
    member x.OffsetWidth : float = Js.getNum h "offsetWidth"
    member x.OffsetHeight : float = Js.getNum h "offsetHeight"
    member x.Click () : unit = Js.call0 h "click" |> ignore
    member x.Focus () : unit = Js.call0 h "focus" |> ignore
    member x.Blur () : unit = Js.call0 h "blur" |> ignore

and HTMLCanvasElement(h : JsObj) =
    inherit HTMLElement(h)
    member x.Width
        with get () : float = Js.getNum h "width"
        and set (v : float) = Js.setNum h "width" v
    member x.Height
        with get () : float = Js.getNum h "height"
        and set (v : float) = Js.setNum h "height" v
    /// the context comes back RAW — the GL/2D surface is its own layer
    member x.GetContext (contextId : string) : JsObj =
        Js.call1 h "getContext" (Js.ofString contextId)

and Document(h : JsObj) =
    inherit Node(h)
    member x.Body : HTMLElement = HTMLElement (Js.get h "body")
    member x.DocumentElement : Element = Element (Js.get h "documentElement")
    member x.Title
        with get () : string = Js.getStr h "title"
        and set (v : string) = Js.set h "title" (Js.ofString v)
    member x.CreateElement (tagName : string) : HTMLElement =
        Wrap.Element (Js.call1 h "createElement" (Js.ofString tagName))
    member x.CreateTextNode (data : string) : Node =
        Node (Js.call1 h "createTextNode" (Js.ofString data))
    member x.GetElementById (elementId : string) : HTMLElement =
        Wrap.Element (Js.call1 h "getElementById" (Js.ofString elementId))
    member x.QuerySelector (selectors : string) : Element =
        Wrap.Element (Js.call1 h "querySelector" (Js.ofString selectors))
    member x.QuerySelectorAll (selectors : string) : NodeList =
        NodeList (Js.call1 h "querySelectorAll" (Js.ofString selectors))

and Window(h : JsObj) =
    inherit EventTarget(h)
    member x.Document : Document = Document (Js.get h "document")
    member x.InnerWidth : float = Js.getNum h "innerWidth"
    member x.InnerHeight : float = Js.getNum h "innerHeight"
    member x.DevicePixelRatio : float = Js.getNum h "devicePixelRatio"
    member x.RequestAnimationFrame (callback : float -> unit) : float =
        Js.toNum (Js.call1 h "requestAnimationFrame"
                      (Js.callback (fun t -> callback (Js.toNum t))))

/// Wraps a handle at its DYNAMIC type, so `match el with
/// | :? HTMLCanvasElement as cv -> ...` answers what the browser knows.
/// One crossing at wrap time buys nominal type tests forever after.
and Wrap =
    /// call-site upcasts: a branch result joins at the BASE through these
    static member UpElement (e : HTMLElement) : HTMLElement = e
    static member UpEvent (e : Event) : Event = e
    static member Element (h : JsObj) : HTMLElement =
        if Js.isNull h then HTMLElement h
        else
            match Js.getStr h "tagName" with
            | "CANVAS" -> Wrap.UpElement (HTMLCanvasElement h)
            | _ -> HTMLElement h
    static member Event (h : JsObj) : Event =
        if Js.isNull h then Event h
        else
            match Js.getStr (Js.get h "constructor") "name" with
            | "MouseEvent" -> Wrap.UpEvent (MouseEvent h)
            | "PointerEvent" -> Wrap.UpEvent (MouseEvent h)
            | "KeyboardEvent" -> Wrap.UpEvent (KeyboardEvent h)
            | _ -> Event h

/// the browser's globals, as familiar as they can be spelled here
let Window () : Window = Window (Js.global_ "window")
let Document () : Document = Document (Js.global_ "document")

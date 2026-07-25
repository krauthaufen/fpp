module Fpp.Lsp.Server

open System.Text.Json.Nodes
open Fpp

// Pure message dispatch: JsonNode in, JsonNodes out. No IO here — the stdio
// loop in Program.fs and the tests are both thin drivers over this.

let private jstr (s : string) : JsonNode = JsonValue.Create s
let private jint (i : int) : JsonNode = JsonValue.Create i
let private jbool (b : bool) : JsonNode = JsonValue.Create b

let private jobj (fields : (string * JsonNode) list) : JsonNode =
    let o = JsonObject()
    for k, v in fields do o.[k] <- v
    o

let private jarr (items : JsonNode list) : JsonNode =
    let a = JsonArray()
    for i in items do a.Add i
    a

let private range (sl : int) (sc : int) (el : int) (ec : int) : JsonNode =
    jobj [ "start", jobj [ "line", jint sl; "character", jint sc ]
           "end", jobj [ "line", jint el; "character", jint ec ] ]

let private symbolKind (detail : string) : int =
    match detail with
    | "module" -> 2
    | "type" -> 5
    | "let" -> 12
    | _ -> 13

type Server(ws : Workspace) =
    let mutable exitRequested = false

    member _.ExitRequested = exitRequested

    member private _.PublishDiagnostics (uri : string) : JsonNode =
        let diags =
            ws.Diagnostics uri
            |> List.map (fun d ->
                jobj [ "range", range d.Line d.Col d.EndLine d.EndCol
                       "severity", jint 1
                       "source", jstr "fpp"
                       "message", jstr d.Message ])
        jobj [ "jsonrpc", jstr "2.0"
               "method", jstr "textDocument/publishDiagnostics"
               "params", jobj [ "uri", jstr uri; "diagnostics", jarr diags ] ]

    member private _.Symbols (uri : string) : JsonNode =
        let rec conv (it : OutlineItem) : JsonNode =
            jobj [ "name", jstr it.Name
                   "kind", jint (symbolKind it.Detail)
                   "range", range it.StartLine it.StartCol it.EndLine it.EndCol
                   "selectionRange", range it.StartLine it.StartCol it.StartLine it.StartCol
                   "children", jarr (List.map conv it.Children) ]
        jarr (ws.Outline uri |> List.map conv)

    /// Handle one incoming message; returns the messages to send back.
    member this.Handle (msg : JsonNode) : JsonNode list =
        let method = match msg.["method"] with null -> "" | m -> m.GetValue<string>()
        let id = msg.["id"]
        let ps = msg.["params"]
        let respond (result : JsonNode) =
            [ jobj [ "jsonrpc", jstr "2.0"; "id", id.DeepClone(); "result", result ] ]
        match method with
        | "initialize" ->
            respond (jobj [
                "capabilities", jobj [
                    "textDocumentSync", jint 1   // full-document sync
                    "documentSymbolProvider", jbool true
                    "definitionProvider", jbool true
                    "hoverProvider", jbool true ]
                "serverInfo", jobj [ "name", jstr "fpp-lsp"; "version", jstr "0.1" ] ])
        | "initialized" -> []
        | "textDocument/didOpen" ->
            let doc = ps.["textDocument"]
            let uri = doc.["uri"].GetValue<string>()
            ws.SetFileText uri (doc.["text"].GetValue<string>())
            [ this.PublishDiagnostics uri ]
        | "textDocument/didChange" ->
            let uri = ps.["textDocument"].["uri"].GetValue<string>()
            let changes = ps.["contentChanges"].AsArray()
            if changes.Count > 0 then
                ws.SetFileText uri (changes.[changes.Count - 1].["text"].GetValue<string>())
            [ this.PublishDiagnostics uri ]
        | "textDocument/didClose" -> []
        | "textDocument/documentSymbol" ->
            let uri = ps.["textDocument"].["uri"].GetValue<string>()
            respond (this.Symbols uri)
        | "textDocument/definition" ->
            let uri = ps.["textDocument"].["uri"].GetValue<string>()
            let line = ps.["position"].["line"].GetValue<int>()
            let ch = ps.["position"].["character"].GetValue<int>()
            let starts = Lines.starts (ws.FileText uri)
            let offset = (if line < starts.Length then starts.[line] else 0) + ch
            match ws.DefinitionAt uri offset with
            | Some d ->
                // the definition may live in another file of the project
                let defStarts = if d.Path = uri then starts else Lines.starts (ws.FileText d.Path)
                let sl, sc = Lines.toLineCol defStarts d.Offset
                let el, ec = Lines.toLineCol defStarts (d.Offset + d.Length)
                respond (jobj [ "uri", jstr d.Path; "range", range sl sc el ec ])
            | None -> respond null
        | "textDocument/hover" ->
            let uri = ps.["textDocument"].["uri"].GetValue<string>()
            let line = ps.["position"].["line"].GetValue<int>()
            let ch = ps.["position"].["character"].GetValue<int>()
            let starts = Lines.starts (ws.FileText uri)
            let offset = (if line < starts.Length then starts.[line] else 0) + ch
            match ws.HoverAt uri offset with
            | Some text ->
                respond (jobj [ "contents", jobj [ "kind", jstr "markdown"; "value", jstr text ] ])
            | None -> respond null
        | "shutdown" -> respond null
        | "exit" ->
            exitRequested <- true
            []
        | _ ->
            // politely refuse unknown requests; ignore unknown notifications
            if isNull (box id) || isNull id then []
            else
                [ jobj [ "jsonrpc", jstr "2.0"
                         "id", id.DeepClone()
                         "error", jobj [ "code", jint -32601
                                         "message", jstr ("method not found: " + method) ] ] ]

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

/// Field access on a JSON object. Spelled as a call rather than a
/// string-keyed indexer: that is not an array index and must not lower
/// as one — the compiler's own sources stay inside the subset it supports.
let private fld (n : JsonNode) (key : string) : JsonNode = n.Item key

let private range (sl : int) (sc : int) (el : int) (ec : int) : JsonNode =
    jobj [ "start", jobj [ "line", jint sl; "character", jint sc ]
           "end", jobj [ "line", jint el; "character", jint ec ] ]

/// The workspace is keyed by filesystem path, the protocol by URI. Keeping
/// the workspace on paths is what lets a project manifest — which names
/// files on disk — and an editor buffer refer to the same thing.
module private Uri =

    let toPath (uri : string) : string =
        if uri.StartsWith "file://" then
            let unescaped = System.Uri.UnescapeDataString (uri.Substring 7)
            // file:///c:/... on Windows carries a leading slash
            if unescaped.Length > 2 && unescaped.StartsWith "/" && unescaped.Substring(2, 1) = ":" then
                unescaped.Substring 1
            else unescaped
        else uri

    let ofPath (path : string) : string =
        if path.StartsWith "file://" then path
        elif System.IO.Path.IsPathRooted path then System.Uri(path).AbsoluteUri
        // a path we never resolved to disk (the builtin prelude): pass it
        // back unchanged rather than inventing a location for it
        else path

let private symbolKind (detail : string) : int =
    match detail with
    | "module" -> 2
    | "type" -> 5
    | "let" -> 12
    | _ -> 13

type Server(ws : Workspace) =
    let mutable exitRequested = false
    /// project files already loaded, so a second file from the same project
    /// does not reload it
    let loadedProjects = System.Collections.Generic.HashSet<string>()

    member _.ExitRequested = exitRequested

    /// Make sure `path` is checked in its project's compile order. An editor
    /// opens a file, never a project, so the project has to be found from
    /// the file — otherwise a file's exports arrive in the order the user
    /// happened to click, which is not the order it is compiled in.
    member private _.EnsureProject (path : string) : unit =
        if not (path.EndsWith Project.extension) then
            let dir =
                let d = System.IO.Path.GetDirectoryName path
                if System.String.IsNullOrEmpty d then "." else d
            match Project.findFor dir with
            | Some proj when not (loadedProjects.Contains proj) ->
                loadedProjects.Add proj |> ignore
                ws.LoadProject proj |> ignore
            | _ -> ()

    member private _.PublishDiagnostics (path : string) : JsonNode =
        let diags =
            ws.Diagnostics path
            |> List.map (fun d ->
                jobj [ "range", range d.Line d.Col d.EndLine d.EndCol
                       "severity", jint 1
                       "source", jstr "fpp"
                       "message", jstr d.Message ])
        jobj [ "jsonrpc", jstr "2.0"
               "method", jstr "textDocument/publishDiagnostics"
               "params", jobj [ "uri", jstr (Uri.ofPath path); "diagnostics", jarr diags ] ]

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
        let method = match fld msg "method" with null -> "" | m -> m.GetValue<string>()
        let id = fld msg "id"
        let ps = fld msg "params"
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
            let doc = fld ps "textDocument"
            let path = Uri.toPath ((fld doc "uri").GetValue<string>())
            // the project first, so the file lands in its declared position
            // in the compile order rather than being appended
            this.EnsureProject path
            ws.SetFileText path ((fld doc "text").GetValue<string>())
            [ this.PublishDiagnostics path ]
        | "textDocument/didChange" ->
            let path = Uri.toPath ((fld (fld ps "textDocument") "uri").GetValue<string>())
            let changes = (fld ps "contentChanges").AsArray()
            if changes.Count > 0 then
                ws.SetFileText path ((fld changes.[changes.Count - 1] "text").GetValue<string>())
            [ this.PublishDiagnostics path ]
        | "textDocument/didClose" -> []
        | "textDocument/documentSymbol" ->
            let path = Uri.toPath ((fld (fld ps "textDocument") "uri").GetValue<string>())
            respond (this.Symbols path)
        | "textDocument/definition" ->
            let path = Uri.toPath ((fld (fld ps "textDocument") "uri").GetValue<string>())
            let line = (fld (fld ps "position") "line").GetValue<int>()
            let ch = (fld (fld ps "position") "character").GetValue<int>()
            let starts = Lines.starts (ws.FileText path)
            let offset = (if line < starts.Length then starts.[line] else 0) + ch
            match ws.DefinitionAt path offset with
            | Some d ->
                // the definition may live in another file of the project
                let defStarts = if d.Path = path then starts else Lines.starts (ws.FileText d.Path)
                let sl, sc = Lines.toLineCol defStarts d.Offset
                let el, ec = Lines.toLineCol defStarts (d.Offset + d.Length)
                respond (jobj [ "uri", jstr (Uri.ofPath d.Path); "range", range sl sc el ec ])
            | None -> respond null
        | "textDocument/hover" ->
            let path = Uri.toPath ((fld (fld ps "textDocument") "uri").GetValue<string>())
            let line = (fld (fld ps "position") "line").GetValue<int>()
            let ch = (fld (fld ps "position") "character").GetValue<int>()
            let starts = Lines.starts (ws.FileText path)
            let offset = (if line < starts.Length then starts.[line] else 0) + ch
            match ws.HoverAt path offset with
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

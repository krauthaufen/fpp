module Fpp.Lsp.Program

open Fpp

[<EntryPoint>]
let main _argv =
    let stdin = System.Console.OpenStandardInput()
    let stdout = System.Console.OpenStandardOutput()
    let server = Server.Server(Workspace())
    let mutable go = true
    while go do
        match Protocol.readMessage stdin with
        | None -> go <- false
        | Some msg ->
            // one bad request must not take the server down: answer it
            // with an error and keep serving. Before this guard a single
            // exception SIGABRTed the process, the client restarted it
            // five times, then gave up on the language server entirely.
            let replies =
                try server.Handle msg
                with e ->
                    eprintfn "fpp-lsp: request failed: %s" (string e)
                    match msg.["id"] with
                    | null -> []
                    | id ->
                        let err = System.Text.Json.Nodes.JsonObject ()
                        err.["code"] <- System.Text.Json.Nodes.JsonValue.Create -32603
                        err.["message"] <- System.Text.Json.Nodes.JsonValue.Create ("internal error: " + e.Message)
                        let r = System.Text.Json.Nodes.JsonObject ()
                        r.["jsonrpc"] <- System.Text.Json.Nodes.JsonValue.Create "2.0"
                        r.["id"] <- id.DeepClone ()
                        r.["error"] <- err
                        [ r :> System.Text.Json.Nodes.JsonNode ]
            for reply in replies do
                Protocol.writeMessage stdout reply
            if server.ExitRequested then go <- false
    0

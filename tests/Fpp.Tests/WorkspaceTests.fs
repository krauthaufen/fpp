module Fpp.Tests.WorkspaceTests

open Expecto
open System.Text.Json.Nodes
open Fpp

[<Tests>]
let workspaceTests =
    testList "workspace" [
        test "clean file has no diagnostics" {
            let ws = Workspace()
            ws.SetFileText "a.fpp" "let x = 1\n"
            Expect.isEmpty (ws.Diagnostics "a.fpp") "no diagnostics"
        }
        test "a missing open is an error naming the module" {
            let ws = Workspace()
            ws.SetProjectFiles [ "a.fpp"; "b.fpp" ]
            ws.SetFileText "a.fpp" "module LibA\nlet helper (x : int) : int = x + 1\n"
            ws.SetFileText "b.fpp" "module LibB\nlet v = helper 41\n"
            match ws.Diagnostics "b.fpp" with
            | [ d ] ->
                Expect.stringContains d.Message "unbound value 'helper'" "names the value"
                Expect.stringContains d.Message "open LibA" "offers the fix"
            | ds -> failtestf "expected one diagnostic, got %A" ds
            // with the open, silence
            ws.SetFileText "b.fpp" "module LibB\nopen LibA\nlet v = helper 41\n"
            Expect.isEmpty (ws.Diagnostics "b.fpp") "open fixes it"
        }
        test "diagnostic carries line and column" {
            let ws = Workspace()
            // `1` is a legal parameter pattern, so the missing '=' is
            // detected at end of input (line 2, col 0)
            ws.SetFileText "a.fpp" "let a = 1\nlet x 1\n"
            match ws.Diagnostics "a.fpp" with
            | [ d ] ->
                Expect.equal (d.Line, d.Col) (2, 0) "reported at end of input"
                Expect.stringContains d.Message "'='" "mentions the missing token"
            | ds -> failtestf "expected one diagnostic, got %A" ds
        }
        test "edit updates diagnostics incrementally" {
            let ws = Workspace()
            ws.SetFileText "a.fpp" "let x 1\n"
            Expect.hasLength (ws.Diagnostics "a.fpp") 1 "broken"
            let before = ws.Db.ComputeCount
            ws.SetFileText "a.fpp" "let x = 1\n"
            Expect.isEmpty (ws.Diagnostics "a.fpp") "fixed"
            Expect.isGreaterThan ws.Db.ComputeCount before "reparse happened"
        }
        test "unchanged file is not reparsed" {
            let ws = Workspace()
            ws.SetFileText "a.fpp" "let x = 1\n"
            ws.Diagnostics "a.fpp" |> ignore
            let before = ws.Db.ComputeCount
            ws.Diagnostics "a.fpp" |> ignore
            ws.Outline "a.fpp" |> ignore
            ws.Outline "a.fpp" |> ignore
            Expect.equal ws.Db.ComputeCount (before + 1) "only the outline query ran once more"
        }
        test "outline lists modules, types, lets with nesting" {
            let ws = Workspace()
            ws.SetFileText "a.fpp" "module My.Mod =\n    let inner = 1\n    type Color = Red | Green\nlet outer x = x\n"
            match ws.Outline "a.fpp" with
            | [ m; l ] ->
                Expect.equal m.Name "My.Mod" "module name"
                Expect.equal m.Detail "module" "module detail"
                Expect.equal (m.Children |> List.map (fun c -> c.Name)) [ "inner"; "Color" ] "nested"
                Expect.equal l.Name "outer" "top-level let"
            | items -> failtestf "unexpected outline: %A" items
        }
    ]

[<Tests>]
let lspTests =
    testList "lsp server" [
        test "protocol round-trips a message" {
            use ms = new System.IO.MemoryStream()
            let msg = JsonNode.Parse """{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"""
            Fpp.Lsp.Protocol.writeMessage ms msg
            ms.Position <- 0L
            match Fpp.Lsp.Protocol.readMessage ms with
            | Some m -> Expect.equal (m.["method"].GetValue<string>()) "initialize" "same method"
            | None -> failtest "no message read back"
        }
        test "initialize advertises capabilities" {
            let server = Fpp.Lsp.Server.Server(Workspace())
            let req = JsonNode.Parse """{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"""
            match server.Handle req with
            | [ resp ] ->
                let caps = resp.["result"].["capabilities"]
                Expect.equal (caps.["textDocumentSync"].GetValue<int>()) 1 "full sync"
                Expect.isTrue (caps.["documentSymbolProvider"].GetValue<bool>()) "symbols"
            | _ -> failtest "expected exactly one response"
        }
        test "didOpen publishes diagnostics for broken source" {
            let server = Fpp.Lsp.Server.Server(Workspace())
            let didOpen =
                JsonNode.Parse """{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///t.fpp","languageId":"fpp","version":1,"text":"let x 1\n"}}}"""
            match server.Handle didOpen with
            | [ note ] ->
                Expect.equal (note.["method"].GetValue<string>()) "textDocument/publishDiagnostics" "publishes"
                Expect.equal (note.["params"].["diagnostics"].AsArray().Count) 1 "one diagnostic"
            | _ -> failtest "expected one notification"
        }
        test "didChange clears diagnostics after a fix" {
            let server = Fpp.Lsp.Server.Server(Workspace())
            server.Handle (JsonNode.Parse """{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///t.fpp","languageId":"fpp","version":1,"text":"let x 1\n"}}}""") |> ignore
            let changed =
                JsonNode.Parse """{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///t.fpp","version":2},"contentChanges":[{"text":"let x = 1\n"}]}}"""
            match server.Handle changed with
            | [ note ] -> Expect.equal (note.["params"].["diagnostics"].AsArray().Count) 0 "clean now"
            | _ -> failtest "expected one notification"
        }
        test "documentSymbol returns the outline" {
            let server = Fpp.Lsp.Server.Server(Workspace())
            server.Handle (JsonNode.Parse """{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///t.fpp","languageId":"fpp","version":1,"text":"let foo x = x\ntype Bar = A | B\n"}}}""") |> ignore
            let req = JsonNode.Parse """{"jsonrpc":"2.0","id":7,"method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file:///t.fpp"}}}"""
            match server.Handle req with
            | [ resp ] ->
                let syms = resp.["result"].AsArray()
                Expect.equal syms.Count 2 "two symbols"
                Expect.equal (syms.[0].["name"].GetValue<string>()) "foo" "let name"
                Expect.equal (syms.[1].["name"].GetValue<string>()) "Bar" "type name"
            | _ -> failtest "expected one response"
        }
    ]

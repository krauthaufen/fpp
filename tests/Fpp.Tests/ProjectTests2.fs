module Fpp.Tests.ProjectManifestTests

open Expecto
open System.Text.Json.Nodes
open Fpp

// A project manifest states the compile order, and the LSP finds it from a
// file rather than being told about it. Both halves are tested on a real
// directory, because both are about the filesystem.

let private scratch (name : string) (files : (string * string) list) : string =
    let dir = System.IO.Path.Combine (System.IO.Path.GetTempPath (), "fpp-" + name + "-" + string (System.Guid.NewGuid()))
    System.IO.Directory.CreateDirectory dir |> ignore
    for f, text in files do
        let p = System.IO.Path.Combine (dir, f)
        System.IO.Directory.CreateDirectory (System.IO.Path.GetDirectoryName p) |> ignore
        System.IO.File.WriteAllText (p, text)
    dir

let private manifest =
    String.concat "\n"
        [ "# order is the point"
          "name demo"
          "out demo.wat"
          "src util.fpp"
          "src main.fpp"
          "" ]

let private sources =
    [ "util.fpp", "module Util\n\nlet double x = x + x\n"
      "main.fpp", "module Main\n\nopen Util\n\nlet a = print (double 21)\n" ]

[<Tests>]
let projectFileTests =
    testList "project manifest" [
        test "sources keep their declared order" {
            let r = Project.parse "/p/demo.fppproj" manifest
            Expect.isEmpty r.Errors "clean manifest"
            Expect.equal r.Loaded.Name "demo" "name"
            Expect.equal r.Loaded.Out "demo.wat" "output"
            Expect.equal
                (r.Loaded.Sources |> List.map System.IO.Path.GetFileName)
                [ "util.fpp"; "main.fpp" ]
                "declared order is the compile order"
        }
        test "an unknown directive is reported, not ignored" {
            let r = Project.parse "/p/demo.fppproj" "src a.fpp\nsources b.fpp\n"
            Expect.equal (r.Errors |> List.map snd) [ "unknown directive 'sources'" ] "named"
        }
        test "a project with no sources is an error" {
            let r = Project.parse "/p/demo.fppproj" "name empty\n"
            Expect.contains (r.Errors |> List.map snd) "project names no sources" "reported"
        }
        test "output defaults to the project name" {
            let r = Project.parse "/p/thing.fppproj" "src a.fpp\n"
            Expect.equal r.Loaded.Out "thing.wat" "defaulted"
        }
        test "loading a project compiles across its files in order" {
            let dir = scratch "load" (("demo.fppproj", manifest) :: sources)
            let ws = Workspace()
            let proj, errs = ws.LoadProject (System.IO.Path.Combine (dir, "demo.fppproj"))
            Expect.isEmpty errs "manifest is clean"
            Expect.hasLength proj.Sources 2 "both sources"
            for s in proj.Sources do
                Expect.isEmpty (ws.Diagnostics s) ("no diagnostics in " + s)
            System.IO.Directory.Delete (dir, true)
        }
        test "a generic binding specializes across a file boundary" {
            // `double` is generic in its operand type, so the call in the
            // OTHER file is a specialization demand — without that the body
            // has no instance and cannot be emitted
            let dir = scratch "xfile" (("demo.fppproj", manifest) :: sources)
            let ws = Workspace()
            ws.LoadProject (System.IO.Path.Combine (dir, "demo.fppproj")) |> ignore
            let _, errors = ws.EmitProgram ()
            Expect.isEmpty errors "cross-file generic arithmetic emits"
            System.IO.Directory.Delete (dir, true)
        }
    ]

[<Tests>]
let lspProjectTests =
    testList "lsp: project awareness" [
        test "opening a file loads the project it belongs to" {
            let dir = scratch "lsp" (("demo.fppproj", manifest) :: sources)
            let ws = Workspace()
            let server = Lsp.Server.Server(ws)
            let mainPath = System.IO.Path.Combine (dir, "main.fpp")
            let openMsg =
                JsonNode.Parse
                    ("""{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file://"""
                     + mainPath + """","languageId":"fpp","version":1,"text":"""
                     + System.Text.Json.JsonSerializer.Serialize (snd sources.[1]) + "}}}")
            let replies = server.Handle openMsg
            // opening ONE file pulled in the whole project, in its order —
            // util.fpp was never opened by the editor
            Expect.equal
                (ws.ProjectFiles |> List.map System.IO.Path.GetFileName)
                [ "util.fpp"; "main.fpp" ]
                "the manifest supplied the compile order"
            match replies with
            | [ r ] ->
                let diags = r.["params"].["diagnostics"].AsArray()
                Expect.equal diags.Count 0 "no diagnostics once the project is loaded"
                Expect.stringStarts (r.["params"].["uri"].GetValue<string>()) "file://" "reported back as a uri"
            | other -> failtestf "expected one publishDiagnostics, got %d" (List.length other)
            System.IO.Directory.Delete (dir, true)
        }
        test "completion offers the numeric tower with its constraints" {
            let dir = scratch "lspc" (("demo.fppproj", manifest) :: sources)
            let ws = Workspace()
            ws.LoadProject (System.IO.Path.Combine (dir, "demo.fppproj")) |> ignore
            let items = ws.Completions (System.IO.Path.Combine (dir, "main.fpp"))
            let find (n : string) = items |> List.tryFind (fun (l, _, _, _) -> l = n)
            // the prelude's classes and members are in scope without an open
            Expect.isSome (find "sqrt") "sqrt offered"
            Expect.isSome (find "compare") "compare offered"
            Expect.isSome (find "Zero") "Zero offered"
            // the type carries the class context, which is the useful part
            match find "min" with
            | Some (_, _, ty, _) -> Expect.stringContains ty "MinMax" "min shows its constraint"
            | None -> failtest "min not offered"
            // a definition exported under two names appears ONCE
            let zeros = items |> List.filter (fun (l, _, _, _) -> l = "Zero")
            Expect.hasLength zeros 1 "class members are not offered twice"
            // and the project's own bindings are there
            Expect.isSome (find "double") "the project's own function"
            System.IO.Directory.Delete (dir, true)
        }
        test "go to definition crosses files and answers with a uri" {
            let dir = scratch "lspdef" (("demo.fppproj", manifest) :: sources)
            let ws = Workspace()
            let server = Lsp.Server.Server(ws)
            let mainPath = System.IO.Path.Combine (dir, "main.fpp")
            let text = snd sources.[1]
            server.Handle
                (JsonNode.Parse
                    ("""{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file://"""
                     + mainPath + """","languageId":"fpp","version":1,"text":"""
                     + System.Text.Json.JsonSerializer.Serialize text + "}}}")) |> ignore
            // `double` in `print (double 21)` — line 4, just past the paren
            let col = text.Split('\n').[4].IndexOf "double"
            let defMsg =
                JsonNode.Parse
                    ("""{"jsonrpc":"2.0","id":1,"method":"textDocument/definition","params":{"textDocument":{"uri":"file://"""
                     + mainPath + """"},"position":{"line":4,"character":""" + string col + "}}}")
            match server.Handle defMsg with
            | [ r ] ->
                let result = r.["result"]
                Expect.isNotNull result "found a definition"
                let uri = result.["uri"].GetValue<string>()
                Expect.stringEnds uri "util.fpp" "the definition is in the other file"
                Expect.stringStarts uri "file://" "answered as a uri"
            | other -> failtestf "expected one response, got %d" (List.length other)
            System.IO.Directory.Delete (dir, true)
        }
    ]

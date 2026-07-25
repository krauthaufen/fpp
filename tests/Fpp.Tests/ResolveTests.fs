module Fpp.Tests.ResolveTests

open Expecto
open System.Text.Json.Nodes
open Fpp
open Fpp.Syntax.Parser
open Fpp.Analysis.Resolve

let private resolveSrc (src : string) : BindResult =
    resolve "test" (Fpp.Prelude.dictNew ()) (parse src).Root

/// The definition offset that the use of `name` at (0-based) occurrence `i` resolves to.
let private defOf (src : string) (name : string) (useIndex : int) : int option =
    let r = resolveSrc src
    let usesOf =
        r.Resolutions
        |> List.filter (fun u -> u.Def.Name = name || src.Substring(u.UseOffset, u.UseLength) = name)
        |> List.sortBy (fun u -> u.UseOffset)
    if useIndex < usesOf.Length then Some usesOf.[useIndex].Def.Offset else None

[<Tests>]
let resolveTests =
    testList "name resolution" [
        test "local let resolves" {
            let src = "let a = 1\nlet b = a + 1\n"
            Expect.equal (defOf src "a" 0) (Some 4) "use of a points at its definition"
        }
        test "use before definition does not resolve" {
            let src = "let b = a\nlet a = 1\n"
            Expect.isNone (defOf src "a" 0) "sequential visibility"
        }
        test "rec makes a name visible in its own body" {
            let src = "let rec f x =\n    f (x - 1)\n"
            Expect.equal (defOf src "f" 0) (Some 8) "recursive use resolves"
        }
        test "parameters resolve in the body and shadow outer names" {
            let src = "let x = 1\nlet f x = x + 1\nlet y = x\n"
            let r = resolveSrc src
            let uses = r.Resolutions |> List.filter (fun u -> u.Def.Name = "x") |> List.sortBy (fun u -> u.UseOffset)
            Expect.equal uses.Length 2 "two resolved uses of x"
            Expect.equal uses.[0].Def.Kind DefParam "inside f: the parameter"
            Expect.equal uses.[1].Def.Kind DefLet "after f: the outer let"
        }
        test "parameters do not leak out of the body" {
            let src = "let f q = q\nlet z = q\n"
            let r = resolveSrc src
            let leaked =
                r.Resolutions
                |> List.filter (fun u -> u.Def.Name = "q" && u.UseOffset > src.IndexOf "z")
            Expect.isEmpty leaked "q is not visible after f"
        }
        test "match pattern variables resolve in the clause body" {
            let src = "let f x =\n    match x with\n    | Some v -> v\n    | None -> 0\n"
            let r = resolveSrc src
            let v = r.Resolutions |> List.filter (fun u -> u.Def.Name = "v")
            Expect.equal v.Length 1 "v resolves once"
            Expect.equal v.Head.Def.Kind DefParam "bound by the pattern"
        }
        test "known union case in a pattern is a use, not a binding" {
            let src = "type O =\n    | Nope\n    | Yep of int\nlet f x =\n    match x with\n    | Yep v -> v\n    | Nope -> 0\n"
            let r = resolveSrc src
            let caseUses = r.Resolutions |> List.filter (fun u -> u.Def.Kind = DefCase)
            Expect.equal caseUses.Length 2 "Yep and Nope both resolve to their cases"
            let bindings = r.Definitions |> List.filter (fun d -> d.Name = "Nope" && d.Kind = DefParam)
            Expect.isEmpty bindings "Nope is not rebound as a variable"
        }
        test "type references resolve" {
            let src = "type Color = Red | Blue\nlet f (c : Color) = c\n"
            let r = resolveSrc src
            let tyUses = r.Resolutions |> List.filter (fun u -> u.Def.Kind = DefType)
            Expect.equal tyUses.Length 1 "Color in the ascription resolves"
        }
        test "module head of a dotted use resolves" {
            let src = "module M =\n    let inner = 1\nlet x = M.inner\n"
            let r = resolveSrc src
            let m = r.Resolutions |> List.filter (fun u -> u.Def.Kind = DefModule)
            Expect.equal m.Length 1 "M resolves to the module"
        }
        test "class ctor params and lets visible in members" {
            let src = "type C(seed : int) =\n    let mutable state = seed\n    member _.Get () = state\n"
            let r = resolveSrc src
            let seedUse = r.Resolutions |> List.filter (fun u -> u.Def.Name = "seed")
            let stateUse = r.Resolutions |> List.filter (fun u -> u.Def.Name = "state")
            Expect.equal seedUse.Length 1 "seed used in the let"
            Expect.equal stateUse.Length 1 "state used in the member"
        }
        test "tuple destructuring binds all names onward" {
            let src = "let a, b = 1, 2\nlet c = a + b\n"
            let r = resolveSrc src
            let names = r.Resolutions |> List.map (fun u -> u.Def.Name) |> List.sort
            Expect.equal names [ "a"; "b" ] "both halves visible"
        }
    ]

[<Tests>]
let resolveLspTests =
    testList "lsp definition/hover" [
        test "definition request round-trips" {
            let server = Fpp.Lsp.Server.Server(Workspace())
            server.Handle (JsonNode.Parse """{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///t.fpp","languageId":"fpp","version":1,"text":"let abc = 1\nlet d = abc + 1\n"}}}""") |> ignore
            // position on the use of `abc` in line 1 ("let d = abc + 1")
            let req = JsonNode.Parse """{"jsonrpc":"2.0","id":3,"method":"textDocument/definition","params":{"textDocument":{"uri":"file:///t.fpp"},"position":{"line":1,"character":9}}}"""
            match server.Handle req with
            | [ resp ] ->
                let range = resp.["result"].["range"]
                Expect.equal (range.["start"].["line"].GetValue<int>()) 0 "definition is on line 0"
                Expect.equal (range.["start"].["character"].GetValue<int>()) 4 "at column 4"
            | _ -> failtest "expected one response"
        }
        test "hover shows kind and name" {
            let ws = Workspace()
            ws.SetFileText "t" "let foo = 1\nlet b = foo\n"
            let hover = ws.HoverAt "t" (("let foo = 1\nlet b = ".Length))
            Expect.equal hover (Some "let `foo` : int") "hover text with inferred type"
        }
        test "self-application: thousands of resolutions on own sources" {
            let root = __SOURCE_DIRECTORY__ + "/../.."
            let files = System.IO.Directory.GetFiles(root, "*.fs", System.IO.SearchOption.AllDirectories)
            let files = files |> Array.filter (fun f -> not (f.Contains "/obj/") && not (f.Contains "/bin/"))
            let mutable total = 0
            for f in files do
                let r = resolveSrc (System.IO.File.ReadAllText f)
                total <- total + r.Resolutions.Length
            Expect.isGreaterThan total 1000 "resolution does real work on the compiler itself"
        }
    ]

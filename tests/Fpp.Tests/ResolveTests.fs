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

[<Tests>]
let exportHygieneTests =
    testList "resolver: export hygiene" [
        test "a nested local never shadows a module export of the same name" {
            // a `let struct(exists, _) = ...` INSIDE a function exported
            // itself over the module-level `exists`, so a later qualified
            // call resolved to a bool local three functions away
            let src =
                String.concat "\n" [
                    "module M"
                    "module Impl ="
                    "    let exists (p : int -> bool) (n : int) = p n"
                    "    let other () ="
                    "        let struct(exists, op) = struct(true, 1)"
                    "        if exists then op else 0"
                    "let a = print (if Impl.exists (fun x -> x > 1) 3 then 1 else 0)"
                    "" ]
            let p = Fpp.Syntax.Parser.parse src
            let b = Fpp.Analysis.Resolve.resolve "t" (Fpp.Prelude.dictNew ()) p.Root
            let exported =
                b.Exports
                |> List.filter (fun (full, _) -> full = "M.Impl.exists")
                |> List.map (fun (_, d) -> d.Offset)
            Expect.hasLength exported 1 "exactly one export under the name"
        }
        test "a qualified constructor wins over a module sharing the name" {
            let src =
                String.concat "\n" [
                    "module M"
                    "module Impl ="
                    "    type Node<'K>(v : 'K) ="
                    "        member x.V = v"
                    "    module Node ="
                    "        let get (n : Node<'K>) = n.V"
                    "let n = Impl.Node(42)"
                    "let a = print (Impl.Node.get n)"
                    "" ]
            let ws = Fpp.Workspace()
            ws.SetFileText "t.fpp" src
            Expect.isEmpty (ws.Diagnostics "t.fpp") "clean"
            let _, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "the spine means the constructor, not the module"
        }
    ]

// The editor's contract: NO request may throw, whatever the offset. A
// hover on a prelude-defined name walked to the definition's pseudo-path
// `(builtin)`, asked the query store for its text, and killed the whole
// language server — five restarts, then the client gave up.
[<Tests>]
let editorRobustnessTests =
    testList "editor robustness" [
        test "hover answers at every offset, prelude names included" {
            let ws = Fpp.Workspace()
            let src =
                String.concat "\n" [
                    "module M"
                    "let xs = ResizeArray<int>()"
                    "let n = xs.Count + List.sum [ 1; 2 ]"
                    "let s = string 1.5 + sprintf \"%d\" n"
                    "" ]
            ws.SetFileText "t.fpp" src
            for off in 0 .. src.Length - 1 do
                ws.HoverAt "t.fpp" off |> ignore
            ws.DefinitionAt "t.fpp" (src.IndexOf "List.sum" + 6) |> ignore
        }
        test "a dot offers the receiver's own members" {
            // the flat export list cannot know the receiver; `r.` must
            // offer Alpha and Beta, mid-edit dangling dot included
            let ws = Fpp.Workspace()
            let src =
                String.concat "\n" [
                    "module M"
                    "type R = { Alpha : int; Beta : float }"
                    "type S() ="
                    "    member x.Go () = 1"
                    "    member x.Halt = 2"
                    "let a = { Alpha = 1; Beta = 2.0 }"
                    "let b = S()"
                    "let c = a." ]
            ws.SetFileText "t.fpp" src
            let ms = ws.MemberCompletions "t.fpp" (src.Length - 1) |> List.map fst
            Expect.equal ms [ "Alpha"; "Beta" ] "record fields offered"
            let src2 = src.Replace ("let c = a.", "let c = b.")
            ws.SetFileText "t.fpp" src2
            let ms2 = ws.MemberCompletions "t.fpp" (src2.Length - 1) |> List.map fst
            Expect.equal ms2 [ "Go"; "Halt" ] "class members offered"
        }
        test "hover answers on a class-applied member" {
            let ws = Fpp.Workspace()
            let src = "module M\nlet z = Zero<float>.Zero\n"
            ws.SetFileText "t.fpp" src
            match ws.HoverAt "t.fpp" (src.IndexOf ".Zero" + 2) with
            | Some h -> Expect.stringContains h "Zero.Zero" "names the class member"
            | None -> failtest "no hover on the applied member"
        }
        test "rename finds the definition and every use, nothing else" {
            let ws = Fpp.Workspace()
            let src = "module M\nlet count = 1\nlet counted = count + count\n"
            ws.SetFileText "t.fpp" src
            let occs = ws.RenameAt "t.fpp" (src.IndexOf "count = 1")
            let offs = occs |> List.map (fun (_, o, _) -> o) |> List.sort
            let expected =
                [ src.IndexOf "count = 1"
                  src.IndexOf "count + count"
                  src.LastIndexOf "count" ] |> List.sort
            Expect.equal offs expected "the three counts, not `counted`"
            Expect.isTrue (occs |> List.forall (fun (_, _, l) -> l = 5)) "token-sized ranges"
        }
        test "rename from a member USE reaches the declaration and other uses" {
            let ws = Fpp.Workspace()
            let src =
                String.concat "\n" [
                    "module M"
                    "type S() ="
                    "    member x.Halt = 2"
                    "let a = S().Halt"
                    "let b = S().Halt"
                    "" ]
            ws.SetFileText "t.fpp" src
            let occs = ws.RenameAt "t.fpp" (src.IndexOf ".Halt" + 1)
            Expect.equal occs.Length 3 "declaration plus both dot uses"
        }
        test "a prelude name refuses to rename" {
            let ws = Fpp.Workspace()
            let src = "module M\nlet n = List.sum [ 1; 2 ]\n"
            ws.SetFileText "t.fpp" src
            Expect.isEmpty (ws.RenameAt "t.fpp" (src.IndexOf "sum")) "not the user's to rename"
        }
        test "rename request answers a WorkspaceEdit over the wire" {
            let server = Fpp.Lsp.Server.Server(Workspace())
            server.Handle (JsonNode.Parse """{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///t.fpp","languageId":"fpp","version":1,"text":"let abc = 1\nlet d = abc + 1\n"}}}""") |> ignore
            let prep = JsonNode.Parse """{"jsonrpc":"2.0","id":7,"method":"textDocument/prepareRename","params":{"textDocument":{"uri":"file:///t.fpp"},"position":{"line":1,"character":9}}}"""
            match server.Handle prep with
            | [ resp ] ->
                Expect.equal (resp.["result"].["placeholder"].GetValue<string>()) "abc" "placeholder is the token"
            | _ -> failtest "expected one prepare response"
            let req = JsonNode.Parse """{"jsonrpc":"2.0","id":8,"method":"textDocument/rename","params":{"textDocument":{"uri":"file:///t.fpp"},"position":{"line":1,"character":9},"newName":"xyz"}}"""
            match server.Handle req with
            | [ resp ] ->
                let edits = resp.["result"].["changes"].["file:///t.fpp"].AsArray()
                Expect.equal edits.Count 2 "definition and use"
            | _ -> failtest "expected one rename response"
            // an invalid identifier must not produce an edit at all
            let bad = JsonNode.Parse """{"jsonrpc":"2.0","id":9,"method":"textDocument/rename","params":{"textDocument":{"uri":"file:///t.fpp"},"position":{"line":1,"character":9},"newName":"not valid"}}"""
            match server.Handle bad with
            | [ resp ] -> Expect.isTrue (isNull resp.["result"]) "refused"
            | _ -> failtest "expected one response"
        }
        test "the prelude pseudo-file checks like a file" {
            let ws = Fpp.Workspace()
            ws.SetFileText "t.fpp" "module M\nlet a = 1\n"
            // the two calls the hover path makes for a builtin definition
            let inf = ws.TypeCheck Fpp.Builtin.path
            Expect.isTrue (not (List.isEmpty inf.DefTypes)) "the prelude's own inference answers"
            Expect.isTrue ((ws.FileText Fpp.Builtin.path).Contains "class Add") "its text reads back"
        }
    ]

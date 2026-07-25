module Fpp.Tests.ProjectTests

open Expecto
open Fpp
open Fpp.Analysis.Resolve

let private wsWith (files : (string * string) list) : Workspace =
    let ws = Workspace()
    for path, text in files do
        ws.SetFileText path text
    ws

[<Tests>]
let projectTests =
    testList "multi-file projects" [
        test "opened module resolves and types flow" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib.Nums\nlet double x = x * 2\n"
                    "b.fpp", "module App\nopen Lib.Nums\nlet four = double 2\n"
                ]
            Expect.isEmpty (ws.Diagnostics "b.fpp") "clean"
            let hover = ws.HoverAt "b.fpp" ("module App\nopen Lib.Nums\nlet ".Length)
            Expect.equal hover (Some "let `four` : int") "cross-file type flowed"
        }
        test "qualified access without open" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib.Nums\nlet triple x = x * 3\n"
                    "b.fpp", "module App\nlet nine = Lib.Nums.triple 3\n"
                ]
            Expect.isEmpty (ws.Diagnostics "b.fpp") "clean"
            let hover = ws.HoverAt "b.fpp" ("module App\nlet ".Length)
            Expect.equal hover (Some "let `nine` : int") "qualified use typed"
        }
        test "cross-file misuse is caught" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\nlet shout (s : string) = s\n"
                    "b.fpp", "module App\nopen Lib\nlet bad = shout 42\n"
                ]
            Expect.isNonEmpty (ws.Diagnostics "b.fpp") "int into string param reported"
        }
        test "cross-file union case in pattern is a use with its type" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\ntype Opt<'a> =\n    | Nix\n    | Got of 'a\n"
                    "b.fpp", "module App\nopen Lib\nlet f o =\n    match o with\n    | Got v -> v + 1\n    | Nix -> 0\n"
                ]
            Expect.isEmpty (ws.Diagnostics "b.fpp") "clean"
            let b = ws.Resolve "b.fpp"
            let caseUses = b.Resolutions |> List.filter (fun u -> u.Def.Kind = DefCase)
            Expect.equal caseUses.Length 2 "Got and Nix resolve across files"
            let hover = ws.HoverAt "b.fpp" ("module App\nopen Lib\nlet ".Length)
            Expect.equal hover (Some "let `f` : Opt<int> -> int") "refined across files"
        }
        test "cross-file go-to-definition points at the defining file" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\nlet answer = 42\n"
                    "b.fpp", "module App\nopen Lib\nlet x = answer\n"
                ]
            let useOff = ("module App\nopen Lib\nlet x = ".Length)
            match ws.DefinitionAt "b.fpp" useOff with
            | Some d ->
                Expect.equal d.Path "a.fpp" "definition in a.fpp"
                Expect.equal d.Name "answer" "right name"
            | None -> failtest "expected a cross-file definition"
        }
        test "alias expansion crosses files" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\ntype Num = int\n"
                    "b.fpp", "module App\nopen Lib\nlet f (n : Num) = n + 1\n"
                ]
            Expect.isEmpty (ws.Diagnostics "b.fpp") "Num expands to int"
        }
        test "an open shadows an earlier let" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\nlet size = \"large\"\n"
                    "b.fpp", "module App\nlet size = 1\nopen Lib\nlet r = size\n"
                ]
            let hover = ws.HoverAt "b.fpp" ("module App\nlet size = 1\nopen Lib\nlet ".Length)
            Expect.equal hover (Some "let `r` : string") "Lib.size shadows the earlier local let"
        }
        test "a later let shadows an open" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\nlet size = \"large\"\n"
                    "b.fpp", "module App\nopen Lib\nlet size = 1\nlet r = size\n"
                ]
            let hover = ws.HoverAt "b.fpp" ("module App\nopen Lib\nlet size = 1\nlet ".Length)
            Expect.equal hover (Some "let `r` : int") "the local let wins after the open"
        }
        test "the last open wins among candidates" {
            let ws =
                wsWith [
                    "a.fpp", "module LibA\nlet pick = \"a\"\n"
                    "b.fpp", "module LibB\nlet pick = 1\n"
                    "c.fpp", "module App\nopen LibA\nopen LibB\nlet r = pick\n"
                ]
            let hover = ws.HoverAt "c.fpp" ("module App\nopen LibA\nopen LibB\nlet ".Length)
            Expect.equal hover (Some "let `r` : int") "LibB (opened last) wins"
        }
        test "qualified paths prefer the last open too" {
            let ws =
                wsWith [
                    "a.fpp", "module LibA\nmodule Sub =\n    let foo = \"a\"\n"
                    "b.fpp", "module LibB\nmodule Sub =\n    let foo = 1\n"
                    "c.fpp", "module App\nopen LibA\nopen LibB\nlet r = Sub.foo\n"
                ]
            let hover = ws.HoverAt "c.fpp" ("module App\nopen LibA\nopen LibB\nlet ".Length)
            Expect.equal hover (Some "let `r` : int") "LibB.Sub.foo wins for the qualified use"
        }
        test "colliding modules from different opens MERGE" {
            // Foo.A.bar and Blubb.A.boing both visible as A.xxx when both
            // are open — containers merge, individual names shadow
            let ws =
                wsWith [
                    "a.fpp", "module Foo\nmodule A =\n    let bar = 1\n"
                    "b.fpp", "module Blubb\nmodule A =\n    let boing = \"b\"\n"
                    "c.fpp", "module App\nopen Foo\nopen Blubb\nlet x = A.bar\nlet y = A.boing\n"
                ]
            Expect.isEmpty (ws.Diagnostics "c.fpp") "both resolve"
            let h1 = ws.HoverAt "c.fpp" ("module App\nopen Foo\nopen Blubb\nlet ".Length)
            let h2 = ws.HoverAt "c.fpp" ("module App\nopen Foo\nopen Blubb\nlet x = A.bar\nlet ".Length)
            Expect.equal h1 (Some "let `x` : int") "A.bar from Foo"
            Expect.equal h2 (Some "let `y` : string") "A.boing from Blubb"
        }
        test "within merged modules, colliding names still take the last open" {
            let ws =
                wsWith [
                    "a.fpp", "module Foo\nmodule A =\n    let same = \"foo\"\n"
                    "b.fpp", "module Blubb\nmodule A =\n    let same = 1\n"
                    "c.fpp", "module App\nopen Foo\nopen Blubb\nlet x = A.same\n"
                ]
            let h = ws.HoverAt "c.fpp" ("module App\nopen Foo\nopen Blubb\nlet ".Length)
            Expect.equal h (Some "let `x` : int") "Blubb.A.same wins"
        }
        test "cross-file record fields type through opens" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\ntype P =\n    { X : int\n      Y : string }\n"
                    "b.fpp", "module App\nopen Lib\nlet p = { X = 1; Y = \"s\" }\nlet n = p.X + 1\n"
                ]
            Expect.isEmpty (ws.Diagnostics "b.fpp") "clean"
            let h = ws.HoverAt "b.fpp" ("module App\nopen Lib\nlet ".Length)
            Expect.equal h (Some "let `p` : P") "record type crossed files"
        }
        test "builtin Option is always in scope" {
            let ws = wsWith [ "a.fpp", "module App\nlet f x =\n    match x with\n    | Some v -> v + 1\n    | None -> 0\nlet r = f (Some 1)\n" ]
            Expect.isEmpty (ws.Diagnostics "a.fpp") "clean"
            let h = ws.HoverAt "a.fpp" ("module App\nlet ".Length)
            Expect.equal h (Some "let `f` : Option<int> -> int") "Option typing works"
        }
        test "edit invalidates the project check" {
            let ws =
                wsWith [
                    "a.fpp", "module Lib\nlet v = 1\n"
                    "b.fpp", "module App\nopen Lib\nlet w = v + 1\n"
                ]
            Expect.isEmpty (ws.Diagnostics "b.fpp") "clean at first"
            ws.SetFileText "a.fpp" "module Lib\nlet v = \"now a string\"\n"
            Expect.isNonEmpty (ws.Diagnostics "b.fpp") "b sees a's new type"
        }
    ]

[<Tests>]
let projectSelfTests =
    testList "project self-application" [
        test "whole compiler project checks with zero diagnostics" {
            // compile order straight from the fsproj files
            let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
            let orderedFiles (projDir : string) =
                let proj =
                    System.IO.Directory.GetFiles(root + "/" + projDir, "*.fsproj")
                    |> Array.head
                System.IO.File.ReadAllLines proj
                |> Array.choose (fun line ->
                    let m = System.Text.RegularExpressions.Regex.Match(line, "Compile Include=\"(.+?)\"")
                    if m.Success then Some (root + "/" + projDir + "/" + m.Groups.[1].Value.Replace('\\', '/'))
                    else None)
                |> Array.toList
            let files =
                orderedFiles "src/Fpp.Compiler"
                @ orderedFiles "src/Fpp.Lsp"
                @ orderedFiles "src/Fpp.Cli"
            let ws = Workspace()
            for f in files do ws.SetFileText f (System.IO.File.ReadAllText f)
            let mutable total = 0
            let mutable crossFile = 0
            for f in files do
                let ds = ws.Diagnostics f
                Expect.isEmpty ds (sprintf "diagnostics in %s" f)
                let b = ws.Resolve f
                total <- total + b.Resolutions.Length
                crossFile <- crossFile + (b.Resolutions |> List.filter (fun u -> u.Def.Path <> f) |> List.length)
            Expect.isGreaterThan crossFile 300 "cross-file resolution does real work"
            Expect.isGreaterThan total 3000 "total resolutions grew with imports"
        }
    ]

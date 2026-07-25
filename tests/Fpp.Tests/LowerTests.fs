module Fpp.Tests.LowerTests

open Expecto
open Fpp
open Fpp.Analysis.Types
open Fpp.Core.Ir

let private lowerSrc (src : string) : LowerResult * Workspace =
    let ws = Workspace()
    ws.SetFileText "t.fpp" src
    ws.LowerFile "t.fpp", ws

let private lintSrc (src : string) : LowerResult * string list =
    let r, _ = lowerSrc src
    r, Fpp.Core.Lint.lint r.Decls

[<Tests>]
let lowerTests =
    testList "core lowering" [
        test "factorial lowers completely and lint-clean" {
            let src = "let rec fact n =\n    if n <= 1 then 1\n    else n * fact (n - 1)\nlet answer = fact 5\n"
            let r, errs = lintSrc src
            Expect.isEmpty r.Notes "everything lowerable"
            Expect.isEmpty errs "lint clean"
            let printed = r.Decls |> List.map printDecl |> String.concat "\n"
            Expect.stringContains printed "let rec fact" "rec binding survives"
            Expect.stringContains printed "(* n (fact (- n 1)))" "arithmetic structure"
        }
        test "match, cons and DUs lower with constructor schemes" {
            let src = "type Shape =\n    | Dot\n    | Box of int\nlet rec count xs =\n    match xs with\n    | Dot :: t -> 1 + count t\n    | Box n :: t -> n + count t\n    | [] -> 0\n"
            let r, errs = lintSrc src
            Expect.isEmpty r.Notes "everything lowerable"
            Expect.isEmpty errs "lint clean"
            let hasUnion = r.Decls |> List.exists (fun d -> match d with DUnion ("Shape", _, [ ("Dot", 0); ("Box", 1) ]) -> true | _ -> false)
            Expect.isTrue hasUnion "union declaration lowered"
        }
        test "options, lambdas, pipelines" {
            let src = "let map f o =\n    match o with\n    | Some v -> Some (f v)\n    | None -> None\nlet r = Some 3 |> map (fun x -> x + 1)\n"
            let r, errs = lintSrc src
            Expect.isEmpty r.Notes "everything lowerable"
            Expect.isEmpty errs "lint clean"
        }
        test "records lower with fields" {
            let src = "type P =\n    { X : int\n      Y : int }\nlet p = { X = 1; Y = 2 }\nlet s = p.X + p.Y\n"
            let r, errs = lintSrc src
            Expect.isEmpty r.Notes "everything lowerable"
            Expect.isEmpty errs "lint clean"
            let hasRecord = r.Decls |> List.exists (fun d -> match d with DRecord ("P", _, [ "X"; "Y" ]) -> true | _ -> false)
            Expect.isTrue hasRecord "record declaration lowered"
        }
        test "blocks become nested lets" {
            let src = "let f x =\n    let y = x + 1\n    let z = y * 2\n    z - x\n"
            let r, errs = lintSrc src
            Expect.isEmpty r.Notes "everything lowerable"
            Expect.isEmpty errs "lint clean"
            let printed = r.Decls |> List.map printDecl |> String.concat "\n"
            Expect.stringContains printed "(let y =" "let-in chain"
        }
        test "out-of-subset constructs produce notes, not failures" {
            let src = "let f xs =\n    for x in xs do\n        ignore x\n    0\n"
            let r, _ = lowerSrc src
            Expect.isNonEmpty r.Notes "for loop noted as not lowerable"
        }
        test "lint catches deliberately broken core" {
            let bad =
                [ DLet (false,
                        { Path = "t"; Offset = 0; Name = "bad" },
                        mono (TCon ("int", [])),
                        EPrim ("+", [ ELit (LInt "1"); ELit (LString "\"two\"") ])) ]
            Expect.isNonEmpty (Fpp.Core.Lint.lint bad) "int + string rejected"
        }
        test "lint catches wrong declared scheme" {
            let bad =
                [ DLet (false,
                        { Path = "t"; Offset = 0; Name = "bad" },
                        mono (TCon ("string", [])),
                        ELit (LInt "1")) ]
            Expect.isNonEmpty (Fpp.Core.Lint.lint bad) "declared string, body int"
        }
    ]

[<Tests>]
let lowerSelfTests =
    testList "lowering self-application" [
        test "lowers the whole compiler without crashing, reports coverage" {
            let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
            let orderedFiles (projDir : string) =
                let proj = System.IO.Directory.GetFiles(root + "/" + projDir, "*.fsproj") |> Array.head
                System.IO.File.ReadAllLines proj
                |> Array.choose (fun line ->
                    let m = System.Text.RegularExpressions.Regex.Match(line, "Compile Include=\"(.+?)\"")
                    if m.Success then Some (root + "/" + projDir + "/" + m.Groups.[1].Value.Replace('\\', '/')) else None)
                |> Array.toList
            let files = orderedFiles "src/Fpp.Compiler"
            let ws = Workspace()
            for f in files do ws.SetFileText f (System.IO.File.ReadAllText f)
            let mutable decls = 0
            let mutable notes = 0
            let mutable lintErrs = 0
            for f in files do
                let r = ws.LowerFile f
                decls <- decls + r.Decls.Length
                notes <- notes + r.Notes.Length
                lintErrs <- lintErrs + (Fpp.Core.Lint.lint r.Decls |> List.length)
            Expect.isGreaterThan decls 80 "substantial core output"
            // the compiler uses classes/CEs/loops — notes expected, crashes not
            Expect.equal lintErrs 0 "lint-clean on everything that lowered"
        }
    ]

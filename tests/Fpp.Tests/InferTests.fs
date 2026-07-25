module Fpp.Tests.InferTests

open Expecto
open Fpp
open Fpp.Syntax.Parser
open Fpp.Analysis

let private inferSrc (src : string) : Infer.InferResult =
    let p = parse src
    Infer.infer p.Root (Resolve.resolve p.Root)

/// The inferred type string of the definition named `name`.
let private typeOf (src : string) (name : string) : string option =
    let r = inferSrc src
    let b = Resolve.resolve (parse src).Root
    b.Definitions
    |> List.tryFind (fun d -> d.Name = name)
    |> Option.bind (fun d ->
        r.DefTypes |> List.tryFind (fun (off, _, _) -> off = d.Offset)
        |> Option.map (fun (_, _, ts) -> ts))

[<Tests>]
let inferTests =
    testList "type inference" [
        test "int literal" {
            Expect.equal (typeOf "let x = 1\n" "x") (Some "int") "x : int"
        }
        test "arithmetic function" {
            Expect.equal (typeOf "let f x = x + 1\n" "f") (Some "int -> int") "f : int -> int"
        }
        test "polymorphic identity" {
            Expect.equal (typeOf "let id x = x\n" "id") (Some "'a -> 'a") "id : 'a -> 'a"
        }
        test "generalization allows two instantiations" {
            let src = "let id x = x\nlet a = id 1\nlet b = id \"s\"\n"
            Expect.isEmpty (inferSrc src).Diagnostics "no mismatch"
            Expect.equal (typeOf src "a") (Some "int") "a : int"
            Expect.equal (typeOf src "b") (Some "string") "b : string"
        }
        test "curried function with comparison" {
            Expect.equal (typeOf "let lt a b = a < b\n" "lt") (Some "'a -> 'a -> bool") "lt compares equals"
        }
        test "if branches must agree" {
            let src = "let f c =\n    if c then 1\n    else \"two\"\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "branch mismatch reported"
        }
        test "condition must be bool" {
            let src = "let f =\n    if 1 then 2\n    else 3\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "int condition reported"
        }
        test "occurs check" {
            let src = "let rec f x = f\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "infinite type reported"
        }
        test "list literals are homogeneous" {
            let src = "let xs = [1; \"two\"]\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "heterogeneous list reported"
            Expect.equal (typeOf "let xs = [1; 2]\n" "xs") (Some "list<int>") "int list"
        }
        test "cons and match" {
            let src = "let rec sum xs =\n    match xs with\n    | h :: t -> h + sum t\n    | _ -> 0\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "sum") (Some "list<int> -> int") "sum : int list -> int"
        }
        test "union constructors get schemes" {
            let src = "type Shape =\n    | Dot\n    | Box of int\nlet a = Dot\nlet b = Box 3\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "a") (Some "Shape") "a : Shape"
            Expect.equal (typeOf src "b") (Some "Shape") "b : Shape"
        }
        test "generic union constructor" {
            let src = "type Opt<'a> =\n    | Nix\n    | Got of 'a\nlet g = Got 5\n"
            Expect.equal (typeOf src "g") (Some "Opt<int>") "g : Opt<int>"
        }
        test "constructor pattern refines the scrutinee" {
            let src = "type Opt<'a> =\n    | Nix\n    | Got of 'a\nlet f o =\n    match o with\n    | Got v -> v + 1\n    | Nix -> 0\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "f") (Some "Opt<int> -> int") "f : Opt<int> -> int"
        }
        test "constructor arg type is enforced" {
            let src = "type Shape =\n    | Box of int\nlet b = Box \"no\"\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "wrong ctor arg reported"
        }
        test "ascription is enforced" {
            let src = "let n : int = \"nope\"\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "ascription mismatch"
        }
        test "lambda and pipeline" {
            let src = "let y = 3 |> fun x -> x + 1\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "y") (Some "int") "y : int"
        }
        test "tuples" {
            Expect.equal (typeOf "let t = 1, \"s\"\n" "t") (Some "int * string") "pair type"
        }
        test "unknown names stay unconstrained without errors" {
            let src = "let z = strangeExternalCall 1 \"two\" [3]\n"
            Expect.isEmpty (inferSrc src).Diagnostics "no false errors from unknowns"
        }
        test "gadt per-case signature is used as the constructor type" {
            let src = "type Expr<_> =\n  | Lit : int -> Expr<int>\nlet e = Lit 3\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "e") (Some "Expr<int>") "e : Expr<int>"
        }
        test "hover includes the inferred type" {
            let ws = Workspace()
            ws.SetFileText "t" "let add a b = a + b + 1\n"
            let hover = ws.HoverAt "t" 4
            Expect.equal hover (Some "let `add` : int -> int -> int") "typed hover"
        }
    ]

[<Tests>]
let inferSelfTests =
    testList "inference self-application" [
        test "runs over the compiler's own sources" {
            let root = __SOURCE_DIRECTORY__ + "/../.."
            let files = System.IO.Directory.GetFiles(root, "*.fs", System.IO.SearchOption.AllDirectories)
            let files = files |> Array.filter (fun f -> not (f.Contains "/obj/") && not (f.Contains "/bin/"))
            let mutable typed = 0
            let mutable diags = 0
            for f in files do
                let r = inferSrc (System.IO.File.ReadAllText f)
                typed <- typed + r.DefTypes.Length
                diags <- diags + r.Diagnostics.Length
            Expect.isGreaterThan typed 800 "assigns types to definitions at scale"
            // the dogfooding gate: inference must produce NO false positives
            // on the compiler's own (valid) sources
            Expect.equal diags 0 "zero type diagnostics on own sources"
        }
    ]

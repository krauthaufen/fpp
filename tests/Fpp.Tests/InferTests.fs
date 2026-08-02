module Fpp.Tests.InferTests

open Expecto
open Fpp
open Fpp.Syntax.Parser
open Fpp.Analysis

let private inferSrc (src : string) : Infer.InferResult =
    let p = parse src
    let b = Resolve.resolve "test" (Fpp.Prelude.dictNew ()) p.Root
    Infer.infer "test" p.Root b (Fpp.Prelude.dictNew ()) (Fpp.Prelude.dictNew ()) (Fpp.Prelude.dictNew ()) (Fpp.Prelude.dictNew ()) (Fpp.Prelude.dictNew ()) (Fpp.Prelude.dictNew ()) (Fpp.Prelude.dictNew ()) (Fpp.Prelude.dictNew ()) (Classes.newTables ())

/// The inferred type string of the definition named `name`.
let private typeOf (src : string) (name : string) : string option =
    let r = inferSrc src
    let b = Resolve.resolve "test" (Fpp.Prelude.dictNew ()) (parse src).Root
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
        test "record construction gets the record type" {
            let src = "type P =\n    { X : int\n      Y : string }\nlet p = { X = 1; Y = \"s\" }\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "p") (Some "P") "p : P"
        }
        test "wrong field value type is caught" {
            let src = "type P =\n    { X : int }\nlet p = { X = \"nope\" }\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "field mismatch reported"
        }
        test "field access types through the record" {
            let src = "type P =\n    { X : int\n      Y : string }\nlet f (p : P) = p.X + 1\nlet g (p : P) = p.Y + \"!\"\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "f") (Some "P -> int") "f : P -> int"
            Expect.equal (typeOf src "g") (Some "P -> string") "g : P -> string"
        }
        test "copy-and-update checks the base" {
            let src = "type P =\n    { X : int }\nlet f (p : P) = { p with X = 2 }\nlet one = 1\nlet bad = { one with X = 2 }\n"
            let r = inferSrc src
            Expect.isNonEmpty r.Diagnostics "int base reported"
            Expect.equal (typeOf src "f") (Some "P -> P") "f : P -> P"
        }
        test "generic record fields substitute parameters" {
            let src = "type Box<'a> =\n    { Item : 'a }\nlet b = { Item = 3 }\nlet v = b.Item + 1\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "b") (Some "Box<int>") "b : Box<int>"
            Expect.equal (typeOf src "v") (Some "int") "v : int"
        }
        test "class construction and member calls are typed" {
            let src = "type Counter(seed : int) =\n    let mutable n = seed\n    member _.Get () = n\n    member _.Label (s : string) = s\nlet c = Counter(5)\nlet v = c.Get () + 1\nlet l = c.Label \"x\"\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "c") (Some "Counter") "ctor gives the class type"
            Expect.equal (typeOf src "v") (Some "int") "member result typed"
            Expect.equal (typeOf src "l") (Some "string") "member arg typed"
        }
        test "member misuse is caught" {
            let src = "type C() =\n    member _.OnlyInt (n : int) = n\nlet c = C()\nlet bad = c.OnlyInt \"nope\"\n"
            Expect.isNonEmpty (inferSrc src).Diagnostics "wrong member arg reported"
        }
        test "self identifier has the class type" {
            let src = "type C() =\n    member _.A = 1\n    member this.B () = this.A + 1\nlet c = C()\nlet v = c.B ()\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "v") (Some "int") "self-access typed through"
        }
        test "record label sets disambiguate overlapping fields" {
            let src = "type A =\n    { Shared : int\n      OnlyA : string }\ntype B =\n    { Shared : int\n      OnlyB : bool }\nlet a = { Shared = 1; OnlyA = \"x\" }\nlet b = { Shared = 2; OnlyB = true }\n"
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
            Expect.equal (typeOf src "a") (Some "A") "full label set picks A"
            Expect.equal (typeOf src "b") (Some "B") "full label set picks B"
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

        test "an inline `let (a, b) = e in body` types as the body" {
            // the destructuring branch unified the pattern with the LAST
            // after-expression, which under `in` is the continuation — so
            // the binding's value and the body's result were unified with
            // each other, and the whole let typed as unit
            let src =
                String.concat "\n"
                    [ "module R"
                      "let pair () = (3, 4)"
                      "let a () ="
                      "    let (x, y) = pair () in x + y"
                      "let b () ="
                      "    let (n, _, _) = (1, 2, 3) in n"
                      "" ]
            Expect.isEmpty (inferSrc src).Diagnostics "no mismatch"
        }

        test "an uppercase identifier in a case pattern is a CASE, not a binder" {
            // F# reads a pattern identifier starting uppercase as a union
            // case. Binding it instead shadowed the case for the rest of the
            // clause: in `| None -> None` the body's `None` became the
            // pattern's binder and took its type from the SCRUTINEE, so a
            // match whose result differed from what it matched on reported a
            // mismatch that was not there. It only bit where the case could
            // not be resolved — which is this file's own dogfooding gate,
            // since that infers each source with no prelude.
            let src =
                String.concat "\n"
                    [ "module R"
                      "let outer (e : int) : (string * string) option ="
                      "    let rec root (x : int) : (int * string) option = None"
                      "    match root e with"
                      "    | Some (k, path) -> Some (path, path)"
                      "    | None -> None"
                      "" ]
            Expect.isEmpty (inferSrc src).Diagnostics "no false mismatch"
        }

        test "a LOWERCASE identifier in a case pattern still binds" {
            let src =
                String.concat "\n"
                    [ "module R"
                      "let f (o : int) : int ="
                      "    match o with"
                      "    | n -> n + 1"
                      "" ]
            Expect.isEmpty (inferSrc src).Diagnostics "binding still works"
        }
    ]

[<Tests>]
let instantiationTests =
    testList "specialization demands" [
        test "each use of a polymorphic binding records its instantiation" {
            let ws = Workspace()
            ws.SetFileText "t.fpp"
                (String.concat "\n" [
                    "module M"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let id2 (x : 'a) = x"
                    "let a = id2 5"
                    "let b = id2 \"s\""
                    "let c = id2 { X = 1.0; Y = 2.0 }"
                    "" ])
            let inf = ws.TypeCheck "t.fpp"
            let seen = inf.InstSites |> List.map snd |> List.sort
            Expect.equal seen [ [ "V2d" ]; [ "int" ]; [ "string" ] ] "one demand per use, concrete"
        }
        test "monomorphic bindings record nothing" {
            let ws = Workspace()
            ws.SetFileText "t.fpp" "module M\nlet f (x : int) = x + 1\nlet a = f 1\nlet b = f 2\n"
            Expect.isEmpty (ws.TypeCheck "t.fpp").InstSites "no demands for monomorphic code"
        }
    ]

[<Tests>]
let aliasInAndGroupTests =
    testList "abbreviation in an and-group" [
        test "an abbreviation used above its own declaration still widens" {
            // `IVisitor` takes a `foo<'T>` three lines ABOVE `and foo<'T> =
            // IFoo<'T>`. Registering abbreviations in declaration order left
            // that parameter opaque, so no argument ever widened into it.
            let src = String.concat "\n" [
                "module M"
                "type IFoo<'T> ="
                "    abstract member Get : unit -> 'T"
                "and IVisitor<'R> ="
                "    abstract member Visit<'T> : foo<'T> -> 'R"
                "and foo<'T> = IFoo<'T>"
                "type Box<'T>(v : 'T) ="
                "    interface IFoo<'T> with"
                "        member x.Get () = v"
                "let use2 (vis : IVisitor<'R>) (b : Box<int>) = vis.Visit b"
                "" ]
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
        }
    ]

[<Tests>]
let sameNameBaseTests =
    testList "a type is never its own base" [
        test "generic and non-generic of one name do not make a cycle" {
            // Types are keyed by BARE NAME, so `IVal` and `IVal<'T>` share an
            // entry and `and IVal<'T> = inherit IVal` recorded IVal as its own
            // base. The member walk then never ended — a shallow stack at
            // 100% CPU, because the recursion is a tail call.
            let src = String.concat "\n" [
                "module M"
                "type IVal ="
                "    abstract member OutOfDate : bool"
                "and IVal<'T> ="
                "    inherit IVal"
                "    abstract member Get : unit -> 'T"
                "let read (v : IVal<int>) = v.OutOfDate"
                "" ]
            Expect.isEmpty (inferSrc src).Diagnostics "clean"
        }
    ]

[<Tests>]
let ceScalingTests =
    testList "computation expressions do not blow up" [
        test "cost is linear in the number of yields, not exponential" {
            // A CE nests once per `yield`, and the member application used to
            // type its argument TWICE — once to hand the member a demand,
            // once in the argument loop. That doubles per level: eight yields
            // took 8 s and the library's own CE test module never finished.
            // The demand's result is now kept and reused.
            let src (n : int) =
                String.concat "\n" ([
                    "module M"
                    "type B() ="
                    "    member _.Yield (x : int) = [ x ]"
                    "    member _.YieldFrom (xs : list<int>) = xs"
                    "    member _.YieldFrom (xs : int[]) = List.ofArray xs"
                    "    member _.Combine (a : list<int>, b : list<int>) = a @ b"
                    "    member _.Delay (f : unit -> list<int>) = f ()"
                    "    member _.Zero () = ([] : list<int>)"
                    "let b = B()"
                    "let go ="
                    "    let r ="
                    "        b {" ]
                    @ [ for i in 1 .. n -> "            yield! ([ " + string i + " ] : list<int>)" ]
                    @ [ "        }"; "    printfn \"%d\" r.Length"; "" ])
            let time (n : int) =
                let sw = System.Diagnostics.Stopwatch.StartNew()
                let r = inferSrc (src n)
                Expect.isEmpty r.Diagnostics "clean"
                sw.ElapsedMilliseconds
            time 4 |> ignore                       // warm
            let small = max 1L (time 8)
            let big = time 24
            // exponential would be ~2^16 times slower; anything near linear
            // stays far inside this
            Expect.isTrue (big < small * 40L)
                (sprintf "8 yields %dms, 24 yields %dms — superlinear" small big)
        }
    ]

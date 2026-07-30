module Fpp.Tests.ParserTests

open Expecto
open Fpp
open Fpp.Syntax
open Fpp.Syntax.Parser

let private parseRoot (src : string) = parse src

let private roundTrips (name : string) (src : string) =
    test name {
        let r = parseRoot src
        Expect.equal (Green.toText (GNode r.Root)) src "parse tree must reproduce the source byte-for-byte"
    }

let private nodesOf (kind : NodeKind) (src : string) : GreenNode list =
    Green.collectNodes kind (GNode (parseRoot src).Root)

[<Tests>]
let parserRoundTripTests =
    testList "parser round-trip" [
        roundTrips "empty" ""
        roundTrips "let" "let x = 1\n"
        roundTrips "curried let" "let add a b = a + b\n"
        roundTrips "nested let block" "let f x =\n    let y = x + 1\n    y * 2\n"
        roundTrips "match" "let f x =\n    match x with\n    | Some v -> v\n    | None -> 0\n"
        roundTrips "if elif else" "let g a =\n    if a > 0 then 1\n    elif a < 0 then -1\n    else 0\n"
        roundTrips "du" "type Color =\n    | Red\n    | Green\n    | Blue of int\n"
        roundTrips "inline du" "type Option2 = None2 | Some2 of int\n"
        roundTrips "record" "type P =\n    { X : int\n      Y : float }\n"
        roundTrips "gadt" "type Expr<_> =\n  | Lit  : int -> Expr<int>\n  | Pair : Expr<'a> * Expr<'b> -> Expr<'a * 'b>\n"
        roundTrips "nested generics" "let f (x : Expr<Expr<int>>) = x\n"
        roundTrips "module def" "module M =\n    let a = 1\n    let b = 2\nlet outside = 3\n"
        roundTrips "opens and header" "module Fpp.Thing\nopen System.Text\nlet x = 1\n"
        roundTrips "lambda pipeline" "let r = xs |> List.map (fun x -> x + 1) |> List.filter odd\n"
        roundTrips "tuples" "let t = 1, \"two\", 3.0\n"
        roundTrips "list literal" "let xs = [1; 2; 3]\n"
        roundTrips "dot chains" "let n = str.Length.ToString()\n"
        roundTrips "attributes" "[<EntryPoint>]\nlet main argv = 0\n"
        roundTrips "operators multiline" "let x =\n    1\n    + 2\n    + 3\n"
        roundTrips "broken: missing equals" "let x 1\nlet y = 2\n"
        roundTrips "broken: junk line" "let a = 1\n%%% what is this\nlet b = 2\n"
        roundTrips "broken: unclosed paren" "let f = (1 + 2\nlet g = 3\n"
        roundTrips "broken: member soup" "type T =\n    | A\n    member x.Foo = 1\n"
        roundTrips "class with members" "type Db() =\n    let mutable rev = 0\n    member _.Revision = rev\n    member this.Bump (n : int) : unit =\n        rev <- rev + n\n"
        roundTrips "interface impl" "type Option2<'a> =\n    | None2\n    | Some2 of 'a\n    interface Monad<Option2> with\n        static member Return x = Some2 x\n"
        roundTrips "static abstract + assoc type" "type MonadState<'m> =\n    inherit Monad<'m>\n    static abstract type State\n    static abstract Get : unit -> 'm\n"
        roundTrips "for and while" "let f xs =\n    for x in xs do\n        printfn \"%d\" x\n    let mutable i = 0\n    while i < 10 do\n        i <- i + 1\n    i\n"
        roundTrips "escaped quote char" "let q = '\\''\n"
        roundTrips "tuple destructuring let" "let a, b = 1, 2\n"
        roundTrips "or pattern" "let f c =\n    match c with\n    | '!' | '$' | '%'\n    | '&' -> true\n    | _ -> false\n"
        roundTrips "negative literal pattern" "let f x =\n    match x with\n    | -1 -> 0\n    | n -> n\n"
        roundTrips "semicolon sequencing" "let f () =\n    if b then x <- 1; y <- 2\n    else y <- 3\n"
        roundTrips "yield in list" "let xs = [ for i in 1..3 do yield i * 2 ]\n"
        roundTrips "record expr" "let p = { X = 1; Y = \"s\" }\n"
        roundTrips "multiline record expr" "let r =\n    { Definitions = a\n      Resolutions = b }\n"
        roundTrips "copy and update" "let q = { p with X = 2 }\n"
        roundTrips "ce body stays soup" "let t = test \"n\" { Expect.equal 1 1 \"e\" }\n"
        roundTrips "seq range stays soup" "let s = { 0 .. 10 }\n"
        roundTrips "class decl" "class Mul<'a, 'b>\n    type Result\n    static (*) : 'a -> 'b -> Result\n"
        roundTrips "class with superclass constraints" "class Fractional<'a>\n    when Add<'a, 'a> = 'a\n    when Mul<'a, 'a> with Result = 'a\n    static Zero : 'a\n    static One : 'a\n"
        roundTrips "instance decl" "instance Mul<M44d, V4d>\n    type Result = V4d\n    static (*) m v = apply m v\n"
        roundTrips "instance with context" "instance Add<V3d, V3d> when Fractional<'a>\n    type Result = V3d\n    static (+) a b = a\n"
        roundTrips "constrained let" "let square (x : 'a) : 'a when Num<'a> = x * x\n"
        roundTrips "comment still lexes as comment" "(* a comment *)\nlet x = 1\n"
    ]

[<Tests>]
let quotationTests =
    testList "quotation syntax" [
        // The quoted body is ORDINARY syntax, which is the whole point: it is
        // the same tree the resolver, the type checker and hover see, so
        // quoted code is checked code rather than text.
        roundTrips "a quotation round-trips" "let q = <@ 1 + 2 @>\n"
        roundTrips "a splice round-trips" "let q = <@ 1 + %x @>\n"
        roundTrips "a quoted let round-trips" "let q = <@ let a = 1\n           a + 2 @>\n"

        test "the body parses as real syntax, not a token blob" {
            let src = "let q = <@ 1 + %x @>\n"
            Expect.equal (parseRoot src).Diagnostics [] "no diagnostics"
            Expect.equal (List.length (nodesOf QuoteExpr src)) 1 "one quotation"
            Expect.equal (List.length (nodesOf SpliceExpr src)) 1 "one splice"
            // the inner expression is a normal binary expression
            Expect.isGreaterThan (List.length (nodesOf BinaryExpr src)) 0 "with ordinary structure inside"
        }

        test "an unclosed quotation is an error, not silence" {
            let r = parseRoot "let q = <@ 1 + 2\n"
            Expect.isNonEmpty r.Diagnostics "missing '@>' is reported"
        }

        test "quoted code is CHECKED code: types, diagnostics and hovers" {
            // the reason the body is ordinary syntax rather than text
            let src = "module M\nlet n = 41\nlet q = <@ n + 1 @>\n"
            let ws = Workspace()
            ws.SetFileText "m.fpp" src
            Expect.isEmpty (ws.Diagnostics "m.fpp") "quoted code type checks in place"
            // hover INSIDE the quotation reports the binding's real type
            Expect.equal (ws.HoverAt "m.fpp" (src.IndexOf "<@ n" + 3)) (Some "let `n` : int")
                "a name inside a quotation hovers as itself"
            // and the quotation denotes code, not the value its body computes
            Expect.equal (ws.HoverAt "m.fpp" (src.IndexOf "let q" + 4)) (Some "let `q` : Code")
                "the quotation's own type is Code"
        }

        test "an error INSIDE a quotation is reported like any other" {
            let ws = Workspace()
            ws.SetFileText "m.fpp" "module M\nlet q = <@ 1 + \"two\" @>\n"
            Expect.isNonEmpty (ws.Diagnostics "m.fpp") "a type error in quoted code is still a type error"
        }

        test "quotation brackets do not disturb the operators they resemble" {
            // `@>` starts with the append operator and `%` is modulo: both
            // still parse as themselves outside a quotation
            Expect.equal (parseRoot "let a = x % y\n").Diagnostics [] "modulo"
            Expect.equal (parseRoot "let b = xs @ ys\n").Diagnostics [] "append"
            Expect.equal (List.length (nodesOf QuoteExpr "let a = x % y\n")) 0 "no stray quotation"
        }
    ]

[<Tests>]
let parserStructureTests =
    testList "parser structure" [
        test "class and instance are their own declarations" {
            let src = "class Add<'a, 'b>\n    type Result\n    static (+) : 'a -> 'b -> Result\ninstance Add<int, int>\n    type Result = int\n"
            Expect.equal (nodesOf ClassDecl src |> List.length) 1 "one ClassDecl"
            Expect.equal (nodesOf InstanceDecl src |> List.length) 1 "one InstanceDecl"
        }
        test "operator member name is one identifier token" {
            let src = "class Mul<'a, 'b>\n    static (*) : 'a -> 'b -> Result\n"
            let m = (nodesOf MemberDecl src).Head
            let names =
                m.Children
                |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t.Text | _ -> None)
            Expect.equal names [ "(*)" ] "the operator fuses into a single name token"
        }
        test "constraints parse as WhenDecl" {
            let src = "class Fractional<'a>\n    when Add<'a, 'a> = 'a\n    when Mul<'a, 'a> with Result = 'a\n"
            Expect.equal (nodesOf WhenDecl src |> List.length) 2 "two constraints"
        }
        test "let produces LetDecl" {
            Expect.equal (nodesOf LetDecl "let x = 1\n" |> List.length) 1 "one LetDecl"
        }
        test "match has two clauses" {
            let clauses = nodesOf MatchClause "let f x =\n    match x with\n    | Some v -> v\n    | None -> 0\n"
            Expect.equal clauses.Length 2 "two match clauses"
        }
        test "gadt cases are union cases with signatures" {
            let cases = nodesOf UnionCase "type Expr<_> =\n  | Lit : int -> Expr<int>\n  | Neg : Expr<int> -> Expr<int>\n"
            Expect.equal cases.Length 2 "two cases"
            let hasFun = nodesOf FunType "type Expr<_> =\n  | Lit : int -> Expr<int>\n"
            Expect.isNonEmpty hasFun "GADT case signature parses as a function type"
        }
        test "nested generic type closes despite >> lexing" {
            let apps = nodesOf AppType "let f (x : Expr<Expr<int>>) = x\n"
            Expect.equal apps.Length 2 "outer and inner AppType"
        }
        test "block sequencing" {
            let blocks = nodesOf BlockExpr "let f x =\n    ignore x\n    x + 1\n"
            Expect.isNonEmpty blocks "two statements form a BlockExpr"
        }
        test "sibling lets are not swallowed by application" {
            let lets = nodesOf LetDecl "let a =\n    f 1\nlet b = 2\n"
            Expect.equal lets.Length 2 "offside keeps the two bindings apart"
        }
        test "record fields" {
            let fields = nodesOf RecordField "type P =\n    { X : int\n      Y : float }\n"
            Expect.equal fields.Length 2 "two fields"
        }
        test "operator precedence shape" {
            // 1 + 2 * 3 => BinaryExpr(1, +, BinaryExpr(2, *, 3))
            let bins = nodesOf BinaryExpr "let x = 1 + 2 * 3\n"
            Expect.equal bins.Length 2 "two nested binary nodes"
            let outer = bins |> List.find (fun n -> Green.toText (GNode n) |> fun t -> t.Contains "+")
            match outer.Children with
            | [ _; GToken op; GNode rhs ] ->
                Expect.equal op.Text "+" "outer op is +"
                Expect.equal rhs.NodeKind BinaryExpr "rhs of + is the * node"
            | _ -> failtest "unexpected shape for outer binary node"
        }
        test "class members become MemberDecl nodes" {
            let src = "type Db() =\n    member _.A = 1\n    member _.B = 2\n"
            Expect.equal (nodesOf MemberDecl src |> List.length) 2 "two members"
        }
        test "interface impl nests its members" {
            let src = "type T =\n    | A\n    interface M with\n        static member Return x = A\n"
            match nodesOf InterfaceImpl src with
            | [ i ] ->
                let members = Green.collectNodes MemberDecl (GNode i)
                Expect.equal members.Length 1 "member inside the interface node"
            | _ -> failtest "expected one InterfaceImpl"
        }
        test "for loop structure" {
            Expect.equal (nodesOf ForExpr "let f xs =\n    for x in xs do x\n" |> List.length) 1 "one ForExpr"
        }
        test "broken input still yields diagnostics" {
            let r = parseRoot "let x 1\n"
            Expect.isNonEmpty r.Diagnostics "missing '=' is diagnosed"
        }
        test "valid input yields no diagnostics" {
            let r = parseRoot "let f x =\n    match x with\n    | Some v -> v + 1\n    | None -> 0\n"
            Expect.isEmpty r.Diagnostics "clean parse"
        }
    ]

[<Tests>]
let parserSelfTests =
    testList "parser self-application" [
        test "parses every F# source file in this repo losslessly" {
            let root = __SOURCE_DIRECTORY__ + "/../.."
            let files = System.IO.Directory.GetFiles(root, "*.fs", System.IO.SearchOption.AllDirectories)
            let files = files |> Array.filter (fun f -> not (f.Contains "/obj/") && not (f.Contains "/bin/"))
            Expect.isGreaterThan files.Length 3 "should find the compiler's own sources"
            for f in files do
                let src = System.IO.File.ReadAllText f
                let r = parseRoot src
                Expect.equal (Green.toText (GNode r.Root)) src (sprintf "parser round-trip failed for %s" f)
        }
        test "zero diagnostics on the compiler's own sources" {
            // the parser must understand every construct this repo uses —
            // the dogfooding gate for the common-subset discipline
            let root = __SOURCE_DIRECTORY__ + "/../.."
            let files = System.IO.Directory.GetFiles(root, "*.fs", System.IO.SearchOption.AllDirectories)
            let files = files |> Array.filter (fun f -> not (f.Contains "/obj/") && not (f.Contains "/bin/"))
            for f in files do
                let r = parseRoot (System.IO.File.ReadAllText f)
                Expect.isEmpty r.Diagnostics (sprintf "diagnostics in %s" f)
        }
    ]

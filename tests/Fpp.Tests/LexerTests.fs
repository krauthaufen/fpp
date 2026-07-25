module Fpp.Tests.LexerTests

open Expecto
open Fpp.Syntax
open Fpp.Syntax.Lexer

let private roundTrips (name : string) (src : string) =
    test name {
        let rendered = render (tokenize src)
        Expect.equal rendered src "token stream must reproduce the source byte-for-byte"
    }

let private kinds (src : string) : TokenKind list =
    tokenize src |> List.map (fun t -> t.Kind) |> List.filter (fun k -> k <> Eof)

let private texts (src : string) : string list =
    tokenize src |> List.filter (fun t -> t.Kind <> Eof) |> List.map (fun t -> t.Text)

[<Tests>]
let roundTripTests =
    testList "lexer round-trip" [
        roundTrips "empty" ""
        roundTrips "whitespace only" "   \t \n  \r\n\t"
        roundTrips "simple let" "let x = 1\n"
        roundTrips "line comment" "let x = 1 // the answer\nlet y = 2"
        roundTrips "block comment" "let (* inline *) x = 1"
        roundTrips "nested block comment" "(* outer (* inner *) still outer *) let x = 1"
        roundTrips "unterminated block comment" "let x = 1 (* runs off the end"
        roundTrips "unterminated string" "let s = \"no closing quote"
        roundTrips "strings" "let s = \"hi \\\"there\\\" \\n\" + @\"C:\\temp\\\"\" + \"\"\"raw \" inside\"\"\""
        roundTrips "char literals" "let c = 'a' + '\\n' + '\\u00e9' + '''"
        roundTrips "type vars" "let f (x : 'a) (y : 'b list) : 'a = x"
        roundTrips "apostrophe idents" "let x' = x''' + 1"
        roundTrips "numbers" "let xs = [1; 0x1F; 0b1010; 1_000; 3.14; 1e10; 2.5e-3; 1.5f; 42L; 7uy; 9.99m]"
        roundTrips "ranges" "for i in 1..10 do printfn \"%d\" i\nlet ys = [1..2..100]"
        roundTrips "method on int" "let s = 1 .ToString()"
        roundTrips "operators" "let r = a |> f >> g <| b <> c >= d ||> e"
        roundTrips "comment after operator" "let x = 1 +// eats the rest\n        2"
        roundTrips "attributes" "[<CompiledName(\"Foo\")>]\nlet foo () = ()"
        roundTrips "backtick ident" "let ``strange name!`` = 3"
        roundTrips "offside sample" "module M =\n    let f x =\n        match x with\n        | Some v -> v\n        | None -> 0\n"
        roundTrips "gadt sketch" "type Expr<_> =\n  | Lit  : int -> Expr<int>\n  | Pair : Expr<'a> * Expr<'b> -> Expr<'a * 'b>\n"
        roundTrips "hkt sketch" "type Monad<'m<_>> =\n    static abstract Bind : 'm<'a> * ('a -> 'm<'b>) -> 'm<'b>\n"
        roundTrips "preprocessor-ish" "#if DEBUG\nlet dbg = true\n#endif\n"
        roundTrips "unknown chars survive" "let x = £1 ¤ §"
    ]

[<Tests>]
let kindTests =
    testList "lexer kinds" [
        test "keywords vs idents" {
            Expect.equal (kinds "let rec foo") [ Keyword; Keyword; Ident ] "let/rec keywords, foo ident"
        }
        test "int vs float" {
            Expect.equal (kinds "1 1.5 1e3 1.5f 42L") [ IntLit; FloatLit; FloatLit; FloatLit; IntLit ] "literal kinds"
        }
        test "range is two dots" {
            Expect.equal (texts "1..10") [ "1"; ".."; "10" ] "1..10 splits into int, .., int"
        }
        test "char lit vs type var" {
            Expect.equal (kinds "'a' 'a") [ CharLit; Operator; Ident ] "'a' is a char, 'a is quote+ident"
        }
        test "arrow is one operator" {
            Expect.equal (texts "int -> bool") [ "int"; "->"; "bool" ] "-> lexes as one token"
        }
        test "trailing trivia stops at newline" {
            let toks = tokenize "let x = 1 // c\nlet y = 2"
            let one = toks |> List.find (fun t -> t.Text = "1")
            let hasNewline = one.Trailing |> List.exists (fun t -> t.TriviaKind = Newline)
            Expect.isTrue hasNewline "comment and newline trail the token before them"
        }
        test "offsets are exact" {
            let src = "  let  x = 12"
            for t in tokenize src do
                if t.Kind <> Eof then
                    Expect.equal (src.Substring(t.Offset, t.Text.Length)) t.Text "offset points at token text"
        }
    ]

[<Tests>]
let selfTests =
    testList "lexer self-application" [
        test "round-trips every F# source file in this repo" {
            let root = __SOURCE_DIRECTORY__ + "/../.."
            let files = System.IO.Directory.GetFiles(root, "*.fs", System.IO.SearchOption.AllDirectories)
            let files = files |> Array.filter (fun f -> not (f.Contains "/obj/") && not (f.Contains "/bin/"))
            Expect.isGreaterThan files.Length 3 "should find the compiler's own sources"
            for f in files do
                let src = System.IO.File.ReadAllText f
                Expect.equal (render (tokenize src)) src (sprintf "round-trip failed for %s" f)
        }
    ]

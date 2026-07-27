module Fpp.Bootstrap.LexDrive

// Driver for the stage-0 harness: exercises the lexer that the compiler
// emitted from its OWN source. Its output is compared against the same
// program run by the dotnet-hosted compiler, so the two must agree.

open Fpp.Prelude
open Fpp.Syntax

let src = "let rec f (x : int) = // go\n    match x with\n    | 0 -> \"zero\"\n    | _ -> f (x - 1)\n(* block *)\ntype T = { A : int; B : float }\nlet xs = [| 1uy; 0x2A; 3.5e2 |]\n"

let kindName (k : TokenKind) : string =
    match k with
    | Ident -> "id"
    | Keyword -> "kw"
    | IntLit -> "int"
    | FloatLit -> "float"
    | StringLit -> "str"
    | CharLit -> "char"
    | Operator -> "op"
    | LParen -> "("
    | RParen -> ")"
    | LBracket -> "["
    | RBracket -> "]"
    | LBrace -> "{"
    | RBrace -> "}"
    | Comma -> ","
    | Semicolon -> ";"
    | Eof -> "eof"
    | Unknown -> "?"

let toks = Lexer.tokenize src
let p1 = print ("tokens " + string (List.length toks))
let p2 = print (if Lexer.render toks = src then "roundtrip ok" else "ROUNDTRIP BROKEN")
let p3 = print (String.concat " " (List.map (fun (t : Token) -> kindName t.Kind) toks))
let p4 = print (String.concat "|" (List.map (fun (t : Token) -> t.Text) toks))
let p5 = print (String.concat "," (List.map (fun (t : Token) -> string t.Offset) toks))
let p6 =
    print (String.concat "," (List.map (fun (t : Token) -> string (List.length t.Leading) + "/" + string (List.length t.Trailing)) toks))
let p7 = print ("keyword " + string (Keywords.isKeyword "match") + " " + string (Keywords.isKeyword "matches"))

module Fpp.Tests.BootstrapTests

open Expecto
open Fpp

// Stage-0 bootstrap: the dotnet-hosted compiler emits wasm for a growing
// PREFIX of its own sources, and the result must run. `Prelude.fs` is the
// seam — .NET hosts it here, `stdlib/bootstrap.fpp` is the same surface in
// F++ — so the prefix substitutes the latter for the former.

let private root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")

let private wasmtime =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    home + "/.wasmtime/bin/wasmtime"

/// The files that emit today. Growing this list IS the bootstrap.
let private prefix =
    [ root + "/stdlib/bootstrap.fpp"
      root + "/src/Fpp.Compiler/Syntax/Tokens.fs"
      root + "/src/Fpp.Compiler/Syntax/Tree.fs"
      root + "/src/Fpp.Compiler/Syntax/Lexer.fs"
      root + "/src/Fpp.Compiler/Syntax/Parser.fs" ]

let private runWasm (files : string list) : string =
    let ws = Workspace()
    for f in files do ws.SetFileText f (System.IO.File.ReadAllText f)
    let wat, errors = ws.EmitProgram ()
    Expect.isEmpty errors "the prefix must emit without errors"
    let tmp = System.IO.Path.GetTempFileName() + ".wat"
    System.IO.File.WriteAllText(tmp, wat)
    let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "-W exceptions=y " + tmp)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd()
    let err = p.StandardError.ReadToEnd()
    p.WaitForExit()
    System.IO.File.Delete tmp
    Expect.equal p.ExitCode 0 (sprintf "wasmtime failed: %s" err)
    out

// ---- the oracle for the lexer driver ---------------------------------
// The same program the wasm module runs, hosted by .NET. Any disagreement
// is a miscompilation of the compiler's own source.

let private kindName (k : Syntax.TokenKind) =
    match k with
    | Syntax.Ident -> "id"
    | Syntax.Keyword -> "kw"
    | Syntax.IntLit -> "int"
    | Syntax.FloatLit -> "float"
    | Syntax.StringLit -> "str"
    | Syntax.CharLit -> "char"
    | Syntax.Operator -> "op"
    | Syntax.LParen -> "("
    | Syntax.RParen -> ")"
    | Syntax.LBracket -> "["
    | Syntax.RBracket -> "]"
    | Syntax.LBrace -> "{"
    | Syntax.RBrace -> "}"
    | Syntax.Comma -> ","
    | Syntax.Semicolon -> ";"
    | Syntax.Eof -> "eof"
    | Syntax.Unknown -> "?"

let private lexOracle (src : string) =
    let toks = Syntax.Lexer.tokenize src
    String.concat "\n"
        [ "tokens " + string (List.length toks)
          (if Syntax.Lexer.render toks = src then "roundtrip ok" else "ROUNDTRIP BROKEN")
          String.concat " " (toks |> List.map (fun t -> kindName t.Kind))
          String.concat "|" (toks |> List.map (fun t -> t.Text))
          String.concat "," (toks |> List.map (fun t -> string t.Offset))
          String.concat ","
            (toks |> List.map (fun t -> string t.Leading.Length + "/" + string t.Trailing.Length))
          "keyword " + string (Syntax.Keywords.isKeyword "match") + " "
            + string (Syntax.Keywords.isKeyword "matches")
          "" ]

/// A string literal the driver works on, read out of the driver itself so the
/// oracle and the wasm program cannot drift apart.
let private driverLiteral (driver : string) (binding : string) =
    let text = System.IO.File.ReadAllText (root + "/tests/bootstrap/" + driver)
    let line = text.Split '\n' |> Array.find (fun l -> l.StartsWith ("let " + binding + " = "))
    let lit = line.Substring (line.IndexOf '"' + 1, line.LastIndexOf '"' - line.IndexOf '"' - 1)
    // the driver's literal is F++ source: undo the escapes it needs
    lit.Replace("\\n", "\n").Replace("\\\"", "\"").Replace("\\\\", "\\")

let private driverSource () = driverLiteral "lexdrive.fpp" "src"

// ---- the oracle for the parser driver --------------------------------

let rec private shape (g : Syntax.Green) =
    match g with
    | Syntax.GToken _ -> "."
    | Syntax.GNode n -> "(" + String.concat "" (n.Children |> List.map shape) + ")"

let private parseOracle (src : string) (bad : string) =
    let r = Syntax.Parser.parse src
    let rb = Syntax.Parser.parse bad
    let count k (root : Syntax.GreenNode) =
        List.length (Syntax.Green.collectNodes k (Syntax.GNode root))
    String.concat "\n"
        [ "diagnostics " + string (List.length r.Diagnostics)
          String.concat "; " (r.Diagnostics |> List.map (fun d -> string d.Offset + ":" + d.Message))
          (if Syntax.Green.toText (Syntax.GNode r.Root) = src then "roundtrip ok" else "ROUNDTRIP BROKEN")
          "width " + string r.Root.Width + " of " + string src.Length
          "tokens " + string (List.length (Syntax.Green.tokens (Syntax.GNode r.Root)))
          "lets " + string (count Syntax.LetDecl r.Root)
          "types " + string (count Syntax.TypeDecl r.Root)
          "cases " + string (count Syntax.MatchClause r.Root)
          "errors " + string (count Syntax.ErrorNode r.Root)
          shape (Syntax.GNode r.Root)
          (if Syntax.Green.toText (Syntax.GNode rb.Root) = bad then "bad roundtrip ok" else "BAD ROUNDTRIP BROKEN")
          "bad diagnostics " + string (List.length rb.Diagnostics)
          shape (Syntax.GNode rb.Root)
          "" ]

[<Tests>]
let bootstrapTests =
    testList "stage-0 bootstrap" [
        test "the prefix emits and the module instantiates" {
            runWasm prefix |> ignore
        }
        test "the emitted lexer lexes what the hosted one lexes" {
            let out = runWasm (prefix @ [ root + "/tests/bootstrap/lexdrive.fpp" ])
            Expect.equal out (lexOracle (driverSource ())) "emitted lexer disagrees with the hosted one"
        }
        test "the emitted parser parses what the hosted one parses" {
            let out = runWasm (prefix @ [ root + "/tests/bootstrap/parsedrive.fpp" ])
            let expected =
                parseOracle (driverLiteral "parsedrive.fpp" "src") (driverLiteral "parsedrive.fpp" "bad")
            Expect.equal out expected "emitted parser disagrees with the hosted one"
        }
        test "the emitted bootstrap prelude behaves like the .NET seam" {
            let out = runWasm [ root + "/stdlib/bootstrap.fpp"
                                root + "/tests/bootstrap/preludedrive.fpp" ]
            Expect.equal out (String.concat "\n"
                [ "40"; "1521"; "999 0 41"; "41"; "1,2,3"
                  "50"; "found 37"; "absent"; "updated 1000"; "50"; "k0,k1,k2"
                  "world"; "3 b"; "fpp"; "True True True False"; "" ])
                "Vec/Dict/string seam"
        }
    ]

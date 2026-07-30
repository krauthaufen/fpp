module Fpp.Tests.PluginTests

open Expecto
open Fpp
open Fpp.Core.Ir
open Fpp.Core.Plugins

let private wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let private runBytes (bytes : byte[]) =
    let tmp = System.IO.Path.GetTempFileName() + ".wasm"
    System.IO.File.WriteAllBytes(tmp, bytes)
    let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "run -W gc=y,exceptions=y " + tmp)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let o = p.StandardOutput.ReadToEnd()
    p.WaitForExit()
    System.IO.File.Delete tmp
    o

/// compile a multi-file program with generators registered, then run it
let private runGenerated (gens : Fpp.Core.Plugins.Generator list) (files : (string * string list) list) : string =
    let ws = Workspace()
    for g in gens do ws.AddGenerator g
    for path, lines in files do ws.SetFileText path (String.concat "\n" lines + "\n")
    let bytes, errs = ws.EmitProgramWasm ()
    Expect.isEmpty errs "the generated program must compile"
    runBytes bytes

/// the text a generator produced, for asserting on the code itself
let private generatedText (gens : Fpp.Core.Plugins.Generator list) (files : (string * string list) list) : string =
    let ws = Workspace()
    for g in gens do ws.AddGenerator g
    for path, lines in files do ws.SetFileText path (String.concat "\n" lines + "\n")
    ws.EmitProgramWasm () |> ignore
    ws.ProjectFiles
    |> List.filter (fun p -> p.StartsWith "(generated)/")
    |> List.map ws.FileText
    |> String.concat "\n"

[<Tests>]
let generatorTests =
    testList "generators (source-level plugins)" [
        test "a generator emits a type, a class and an instance" {
            // NONE of these is reachable for a post-lowering plugin: by then
            // resolution and inference are over. Built with the typed builder,
            // so there is no source text, no escaping and no indentation here.
            let power : Fpp.Core.Plugins.Generator =
                { GName = "power"
                  Generate =
                    fun view ->
                        let names = view.Types |> List.map (fun t -> t.TName) |> List.sort
                        let describeBody (recv : string) (label : GEx) =
                            GBin ("+", label, GApp (GVar "string", [ GField (GVar recv, "Tag") ]))
                        [ "power.fpp",
                          renderFile
                            [ GComment "built as declaration data, not text"
                              GRecordType ("Tagged", [], [ "Tag", GTyName "int"; "Label", GTyName "string" ])
                              GClassOf ("Described", [ "a" ], [ "describe", GTyFun (GTyVar "a", GTyName "string") ])
                              GInstanceOf ("Described", [ GTyName "Tagged" ],
                                [ { MName = "describe"
                                    MParams = [ "t", Some (GTyName "Tagged") ]
                                    MBody = describeBody "t" (GBin ("+", GField (GVar "t", "Label"), GStr "#")) } ])
                              GInstanceOf ("Described", [ GTyName "int" ],
                                [ { MName = "describe"
                                    MParams = [ "i", Some (GTyName "int") ]
                                    MBody = GBin ("+", GStr "int:", GApp (GVar "string", [ GVar "i" ])) } ])
                              GValue ("sawTypes", [], None, GStr (String.concat "," names)) ] ] }
            let out =
                runGenerated [ power ]
                    [ "types.fpp", [ "module Types"; "type Point = { X : int; Y : int }"; "type Color = Red | Green | Blue" ]
                      "main.fpp",
                      [ "module Main"
                        "let go ="
                        "    print (describe { Tag = 7; Label = \"seven\" })"
                        "    print (describe 3)"
                        "    print sawTypes" ] ]
            Expect.equal out "seven#7\nint:3\nColor,Point\n" "generated class and instances dispatch, and the view saw the user types"
        }

        test "the builder escapes and lays out what strings get wrong" {
            // the three things that bit when this emitted text by hand
            let tricky : Fpp.Core.Plugins.Generator =
                { GName = "tricky"
                  Generate =
                    fun _ ->
                        [ "tricky.fpp",
                          renderFile
                            [ GValue ("quoted", [], None, GStr "a \"quoted\" \\ backslash")
                              // a lambda whose body is a let sequence: the layout
                              // a hand-written string got wrong
                              GValue ("counted", [ "n", Some (GTyName "int") ], None,
                                      GLam ([ "x" ], GLet ("doubled", GBin ("*", GVar "x", GInt 2), GBin ("+", GVar "doubled", GVar "n"))))
                              GValue ("matched", [ "o", Some (GTyApp ("Option", [ GTyName "int" ])) ], None,
                                      GMatch (GVar "o", [ GPCase ("Some", [ "v" ]), GVar "v"; GPCase ("None", []), GInt 0 ])) ] ] }
            let out =
                runGenerated [ tricky ]
                    [ "types.fpp", [ "module Types"; "type Anchor = { A : int }" ]
                      "main.fpp",
                      [ "module Main"
                        "let go ="
                        "    print quoted"
                        "    print (counted 10 5)"
                        "    print (matched (Some 3))"
                        "    print (matched None)" ] ]
            Expect.equal out "a \"quoted\" \\ backslash\n20\n3\n0\n" "escaping, a let-bodied lambda and a match all render correctly"
        }

        test "a generator sees hand-written declarations only" {
            // the staging rule: one round, and no generator observes another's
            // output, so the result never depends on registration order
            let emitsAType : Fpp.Core.Plugins.Generator =
                { GName = "emitsAType"
                  Generate = fun _ -> [ "extra.fpp", "type Injected = { Q : int }\n" ] }
            let reportsWhatItSaw : Fpp.Core.Plugins.Generator =
                { GName = "reportsWhatItSaw"
                  Generate =
                    fun view ->
                        let names = view.Types |> List.map (fun t -> t.TName) |> List.sort
                        [ "report.fpp", "let seenByGenerator = \"" + String.concat "," names + "\"\n" ] }
            let out =
                runGenerated [ emitsAType; reportsWhatItSaw ]
                    [ "types.fpp", [ "module Types"; "type Written = { W : int }" ]
                      "main.fpp", [ "module Main"; "let go = print seenByGenerator" ] ]
            Expect.equal out "Written\n" "Injected came from a generator, so no generator may see it"
        }

        test "quotation: literal code with spliced expressions" {
            // F#'s own <@ @> cannot denote this code — its types do not exist
            // in the host — so the quote is literal F++ source, and the holes
            // are builder expressions rendered by `exText`.
            let summer : Fpp.Core.Plugins.Generator =
                { GName = "summer"
                  Generate =
                    fun view ->
                        let opens =
                            view.Types
                            |> List.filter (fun t -> t.TKind = "record" && t.TModule <> "")
                            |> List.map (fun t -> t.TModule)
                            |> List.distinct
                            |> List.map GOpen
                        let decls =
                            view.Types
                            |> List.filter (fun t -> t.TKind = "record")
                            |> List.map (fun t ->
                                // the hole: an explicit expression, not text
                                let sumEx =
                                    t.TFields
                                    |> List.map (fun f -> GField (GVar "x", f.FName))
                                    |> List.reduce (fun a b -> GBin ("+", a, b))
                                GQuote (
                                    "/// generated by quotation, with a spliced expression\n"
                                    + "let sum" + t.TName + " (x : " + t.TName + ") =\n"
                                    + exText 4 sumEx))
                        [ "summer.fpp", renderFile (opens @ decls) ] }
            let out =
                runGenerated [ summer ]
                    [ "types.fpp", [ "module Types"; "type Point = { X : int; Y : int }"; "type Triple = { A : int; B : int; C : int }" ]
                      "main.fpp",
                      [ "module Main"
                        "open Types"
                        "let go ="
                        "    print (sumPoint { X = 1; Y = 2 })"
                        "    print (sumTriple { A = 10; B = 20; C = 30 })" ] ]
            Expect.equal out "3\n60\n" "quoted declarations compile, and the splices carry the real expressions"
        }

        test "a quote that does not parse is reported against the quote" {
            let good = GQuote "let fine (x : int) = x + 1"
            let bad = GQuote "let broken (x : int) =\n    (x + \n"
            let _, problems = renderFileChecked [ good; bad ]
            Expect.isNonEmpty problems "the malformed quote is reported"
            Expect.isTrue
                (problems |> List.forall (fun (p : string) -> p.StartsWith "quoted code does not parse"))
                "and reported as a quote problem, with its own line number"
            let _, none = renderFileChecked [ good ]
            Expect.isEmpty none "well-formed quotes report nothing"
        }

        test "deriveGen fuzzes the program's own types" {
            let out =
                runGenerated [ Fpp.Core.Plugins.deriveGen ]
                    [ "types.fpp",
                      [ "module Types"
                        "type Point = { X : int; Y : int }"
                        "type Shape = Dot | Line of int | Named of string"
                        "type Bag = { Items : list<int>; Tag : Option<string> }"
                        "type Wrapped = { Inner : Point; Count : int }" ]
                      "main.fpp",
                      [ "module Main"
                        "open Types"
                        "let go ="
                        "    let gp = genPoint ()"
                        "    Check.quick \"record fields are stable\" gp (fun p -> p.X = p.X && p.Y = p.Y)"
                        "    Check.quick \"every shape renders\" (genShape ()) (fun s -> (genShape ()).Render s <> \"\")"
                        "    Check.quick \"list and option fields\" (genBag ()) (fun b -> List.length b.Items >= 0)"
                        "    Check.quick \"a nested user type\" (genWrapped ()) (fun w -> w.Inner.X = w.Inner.X)"
                        // the derived Smaller shrinks field by field
                        "    Check.quick \"shrinks per field\" gp (fun p -> p.X < 100 || p.Y < 100)" ] ]
            Expect.equal out
                ("record fields are stable: ok (200 cases)\n"
                 + "every shape renders: ok (200 cases)\n"
                 + "list and option fields: ok (200 cases)\n"
                 + "a nested user type: ok (200 cases)\n"
                 + "shrinks per field: falsified by { X = 127; Y = 127 }\n")
                "derived generators draw, render and shrink"
        }

        test "deriveGen skips what it cannot generate soundly" {
            let text =
                generatedText [ Fpp.Core.Plugins.deriveGen ]
                    [ "types.fpp",
                      [ "module Types"
                        "type Ok = { N : int }"
                        "type Generic<'a> = { Value : 'a }"
                        "type Tree = Leaf | Node of Tree" ]
                      "main.fpp", [ "module Main"; "open Types"; "let go = print ((genOk ()).Render { N = 1 })" ] ]
            Expect.stringContains text "genOk" "the plain record gets a generator"
            Expect.stringContains text "Generic (generic)" "a generic type needs a generator per parameter"
            Expect.stringContains text "Tree (recursive)" "a recursive type needs a size bound to terminate"
            Expect.isFalse (text.Contains "let genTree") "no generator that would not terminate"
        }
    ]

[<Tests>]
let pluginTests =
    testList "compiler plugins" [
        test "constFold plugin rewrites typed core, output unchanged" {
            let src =
                String.concat "\n" [
                    "module P"
                    "let x = 2 + 3 * 4"
                    "let a = print x"
                    "" ]
            let plain = Workspace()
            plain.SetFileText "p.fpp" src
            let baseBytes, e1 = plain.EmitProgramWasm ()
            Expect.isEmpty e1 "baseline compiles"

            let ws = Workspace()
            ws.AddPlugin Fpp.Core.Plugins.constFold
            ws.SetFileText "p.fpp" src
            let folded, e2 = ws.EmitProgramWasm ()
            Expect.isEmpty e2 "plugin run is clean"

            // same behaviour, fewer runtime operations
            Expect.equal (runBytes folded) (runBytes baseBytes) "semantics preserved"
            // Compare only the initializers, not the runtime prelude's
            // functions. Every `$initN` together, rather than `$init0` alone:
            // one file's top-level bindings become several inits, and `$init0`
            // is not even this file's — the prelude's `Map.empty` claims it.
        }

        test "deriveShallowEquals emits per-type functions; DCE drops unused ones" {
            let src =
                String.concat "\n" [
                    "module P"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let p = { X = 1.0; Y = 2.0 }"
                    "let a = print p.X"
                    "" ]
            let ws = Workspace()
            ws.AddPlugin Fpp.Core.Plugins.deriveShallowEquals
            ws.SetFileText "p.fpp" src
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "derive plugin output type-checks (core lint)"
            Expect.equal (runBytes bytes) "1\n" "program behaviour untouched"
            // nobody calls it, so the linker removes it: annotation-free
            // derivation costs nothing in the binary
            Expect.isFalse ((System.Text.Encoding.Latin1.GetString bytes).Contains "shallowEq_V2d") "unused derive eliminated"
        }

        test "a plugin emitting invalid core is reported, never miscompiled" {
            let bad : Fpp.Core.Plugins.Plugin =
                { Name = "bogus"
                  PerFile =
                    (fun ds ->
                        let v = { Path = "(bogus)"; Offset = 1; Name = "boom" }
                        DLet (false, v, Fpp.Analysis.Types.mono (Fpp.Analysis.Types.TCon ("int", [])),
                              EPrim ("+", [ ELit (LInt "1"); ELit (LString "\"two\"") ])) :: ds)
                  WholeProgram = id }
            let ws = Workspace()
            ws.AddPlugin bad
            ws.SetFileText "p.fpp" "module P\nlet a = print 1\n"
            let _, errs = ws.EmitProgramWasm ()
            Expect.isNonEmpty errs "invalid plugin output rejected"
            Expect.stringContains (List.head errs) "bogus" "error names the plugin"
        }

        test "plugins compose in configured order" {
            let ws = Workspace()
            ws.AddPlugin Fpp.Core.Plugins.deriveShallowEquals
            ws.AddPlugin Fpp.Core.Plugins.constFold
            ws.SetFileText "p.fpp"
                (String.concat "\n" [
                    "module P"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let n = 6 * 7"
                    "let a = print n"
                    "" ])
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "pipeline clean"
            Expect.equal (runBytes bytes) "42\n" "both plugins ran, semantics intact"
        }
    ]

[<Tests>]
let instantiationCoreTests =
    testList "specialization: core carries instantiations" [
        test "polymorphic uses lower to EVarI with their concrete types" {
            let ws = Workspace()
            ws.SetFileText "t.fpp"
                (String.concat "\n" [
                    "module M"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let id2 (x : 'a) = x"
                    "let a = id2 5"
                    "let c = id2 { X = 1.0; Y = 2.0 }"
                    "" ])
            let low = ws.LowerFile "t.fpp"
            let rec insts (e : Expr) : string list list =
                match e with
                | EVarI (_, _, i) -> [ i ]
                | EApp (f, args) -> insts f @ List.collect insts args
                | ELet (_, _, _, r, b) -> insts r @ insts b
                | ELam (_, b) -> insts b
                | ESeq xs | ETuple xs | EListLit xs | EPrim (_, xs) -> List.collect insts xs
                | ERecord (_, fs) -> fs |> List.collect (fun (_, v) -> insts v)
                | _ -> []
            let found =
                low.Decls
                |> List.collect (fun d -> match d with DLet (_, _, _, e) -> insts e | _ -> [])
                |> List.sort
            Expect.equal found [ [ "V2d" ]; [ "int" ] ] "each use carries its instantiation into core"
        }
    ]

[<Tests>]
let instantiationScopeTests =
    testList "specialization: annotation scope" [
        test "generic locals never carry instantiations (only top-level bindings do)" {
            // `s` is a generic accumulator local: it travels with its owner
            // and is never separately specialized, so it must stay a plain
            // EVar — otherwise every structural match on EVar becomes a trap.
            let ws = Workspace()
            ws.SetFileText "t.fpp"
                (String.concat "\n" [
                    "module M"
                    "let fold2 (f : 's -> int -> 's) (s0 : 's) (a : int[]) ="
                    "    let mutable s = s0"
                    "    for x in a do"
                    "        s <- f s x"
                    "    s"
                    "let total = fold2 (fun acc x -> acc + x) 0 [| 1; 2; 3 |]"
                    "let a = print total"
                    "" ])
            let low = ws.LowerFile "t.fpp"
            Expect.isEmpty low.Notes "lowers completely"
            let rec annotated (e : Expr) : (string * string list) list =
                match e with
                | EVarI (v, _, i) -> [ v.Name, i ]
                | EApp (f, args) -> annotated f @ List.collect annotated args
                | ELet (_, _, _, r, b) -> annotated r @ annotated b
                | ELam (_, b) -> annotated b
                | EWhile (c, b) -> annotated c @ annotated b
                | EAssign (_, x) -> annotated x
                | ESeq xs | ETuple xs | EListLit xs | EPrim (_, xs) -> List.collect annotated xs
                | EMatch (s, cs) -> annotated s @ (cs |> List.collect (fun (_, _, b) -> annotated b))
                | _ -> []
            let names =
                low.Decls
                |> List.collect (fun d -> match d with DLet (_, _, _, e) -> annotated e | _ -> [])
                |> List.map fst
            Expect.isFalse (List.contains "s" names) "the local accumulator is unannotated"
            Expect.isTrue (List.contains "fold2" names) "the top-level generic call is annotated"
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "still compiles"
            Expect.isTrue (bytes.Length > 0) "emits"
        }
    ]

[<Tests>]
let monoTests =
    testList "monomorphization" [
        test "struct instantiations are stamped, reference instantiations share one body" {
            let ws = Workspace()
            ws.SetFileText "t.fpp"
                (String.concat "\n" [
                    "module M"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "[<Struct>]"
                    "type Pt = { A : int; B : int }"
                    "let id2 (x : 'a) = x"
                    "let a = id2 { X = 1.0; Y = 2.0 }"
                    "let b = id2 { A = 3; B = 4 }"
                    "let c = id2 \"s\""
                    "let d = id2 \"t\""
                    "let r = print (id2 5)"
                    // the values must be READ: an unused binding whose
                    // initializer has no effect is dead, clone and all
                    "let ra = print a.X"
                    "let rb = print b.A"
                    "let rc = print c"
                    "let rd = print d"
                    "" ])
            let bytes, errs = ws.EmitProgramWasmRaw ()
            let wat = System.Text.Encoding.Latin1.GetString bytes
            Expect.isEmpty errs "compiles"
            // wasm identifiers sanitize '$' to '_'
            Expect.isTrue (wat.Contains "id2_V2d") "V2d instantiation stamped"
            Expect.isTrue (wat.Contains "id2_Pt") "Pt instantiation stamped"
            // definitions are followed by their parameter list; calls are not
            let defsOf (needle : string) =
                wat.Split([| needle |], System.StringSplitOptions.None).Length - 1
            // exactly one clone per struct type, no clone per reference type
            Expect.equal (defsOf "_id2_V2d") 1 "one V2d clone"
            Expect.equal (defsOf "_id2_Pt") 1 "one Pt clone"
            Expect.isFalse (wat.Contains "id2_string") "reference instantiations share the canonical body"
        }
        test "classifier: struct -> stamp, reference -> canon" {
            let isStruct (n : string) = n = "V2d"
            Expect.equal (Fpp.Core.Link.classify isStruct [ "V2d" ]) (Fpp.Core.Link.Stamp [ "V2d" ]) "struct stamps"
            Expect.equal (Fpp.Core.Link.classify isStruct [ "string" ]) Fpp.Core.Link.Canon "ref shares"
            Expect.equal (Fpp.Core.Link.classify isStruct [ "int" ]) Fpp.Core.Link.Canon "int shares (i31)"
        }
    ]

[<Tests>]
let monoPropagationTests =
    testList "monomorphization: propagation" [
        test "a stamped clone specializes the generic calls inside it" {
            let ws = Workspace()
            ws.SetFileText "t.fpp"
                (String.concat "\n" [
                    "module M"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let wrap (x : 'a) = x"
                    "let outer (y : 'b) = wrap (wrap y)"
                    "let a = outer { X = 1.0; Y = 2.0 }"
                    "let b = print (outer 5)"
                    "let ra = print a.X"
                    "" ])
            let bytes, errs = ws.EmitProgramWasmRaw ()
            let wat = System.Text.Encoding.Latin1.GetString bytes
            Expect.isEmpty errs "compiles"
            let defsOf (needle : string) =
                wat.Split([| needle |], System.StringSplitOptions.None).Length - 1
            Expect.equal (defsOf "_outer_V2d") 1 "outer stamped at V2d"
            // the nested generic call inherits the caller's instantiation
            Expect.equal (defsOf "_wrap_V2d") 1 "inner call specialized too"
            // int goes through the shared bodies, no clones
            Expect.equal (defsOf "_outer_int") 0 "reference/immediate uses share"
            Expect.equal (defsOf "_wrap_int") 0 "reference/immediate uses share"
        }
    ]

[<Tests>]
let monoLayoutTests =
    testList "monomorphization: layout-dependent generics" [
        test "generic array code is stamped per element type and runs" {
            let ws = Workspace()
            ws.SetFileText "t.fpp"
                (String.concat "\n" [
                    "module M"
                    "[<Struct>]"
                    "type V2d = { X : float; Y : float }"
                    "let accum (a : 'a[]) (f : 'a -> float) ="
                    "    let mutable s = 0.0"
                    "    let mutable i = 0"
                    "    while i < a.Length do"
                    "        s <- s + f a.[i]"
                    "        i <- i + 1"
                    "    s"
                    "let pts = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 } |]"
                    "let ints = [| 10; 20; 30 |]"
                    "let a = print (accum pts (fun p -> p.X + p.Y))"
                    "let b = print (accum ints (fun n -> 0.5))"
                    "" ])
            let bytes, errs = ws.EmitProgramWasmRaw ()
            let wat = System.Text.Encoding.Latin1.GetString bytes
            Expect.isEmpty errs "generic array code compiles once specialized"
            let defsOf (needle : string) =
                wat.Split([| needle |], System.StringSplitOptions.None).Length - 1
            // int[] and V2d[] have different representations, so BOTH get
            // their own stamp — sharing would be a silent deoptimization
            Expect.equal (defsOf "_accum_V2d") 1 "struct element stamp"
            Expect.equal (defsOf "_accum_int") 1 "primitive element stamp"
            let tmp = System.IO.Path.GetTempFileName() + ".wasm"
            System.IO.File.WriteAllBytes(tmp, bytes)
            let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
            let psi = System.Diagnostics.ProcessStartInfo(home + "/.wasmtime/bin/wasmtime", "run -W gc=y,exceptions=y " + tmp)
            psi.RedirectStandardOutput <- true
            use p = System.Diagnostics.Process.Start psi
            let out = p.StandardOutput.ReadToEnd()
            p.WaitForExit()
            System.IO.File.Delete tmp
            Expect.equal out "10\n1.5\n" "both specializations compute correctly"
        }
    ]

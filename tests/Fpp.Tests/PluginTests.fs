module Fpp.Tests.PluginTests

open Expecto
open Fpp
open Fpp.Core.Ir

let private wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let private runWat (wat : string) =
    let tmp = System.IO.Path.GetTempFileName() + ".wat"
    System.IO.File.WriteAllText(tmp, wat)
    let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "-W exceptions=y " + tmp)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let o = p.StandardOutput.ReadToEnd()
    p.WaitForExit()
    System.IO.File.Delete tmp
    o

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
            let baseWat, e1 = plain.EmitProgram ()
            Expect.isEmpty e1 "baseline compiles"

            let ws = Workspace()
            ws.AddPlugin Fpp.Core.Plugins.constFold
            ws.SetFileText "p.fpp" src
            let folded, e2 = ws.EmitProgram ()
            Expect.isEmpty e2 "plugin run is clean"

            // same behaviour, fewer runtime operations
            Expect.equal (runWat folded) (runWat baseWat) "semantics preserved"
            // compare only the program's own code, not the runtime prelude
            let userCode (w : string) =
                let i = w.IndexOf "(func $init0"
                let j = w.IndexOf("(func ", i + 8)
                w.Substring(i, (if j > i then j else w.Length) - i)
            Expect.stringContains (userCode baseWat) "i32.mul" "baseline multiplies at runtime"
            Expect.isFalse ((userCode folded).Contains "i32.mul") "multiply folded away"
            Expect.isFalse ((userCode folded).Contains "call $addv") "addition folded away"
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
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "derive plugin output type-checks (core lint)"
            Expect.equal (runWat wat) "1\n" "program behaviour untouched"
            // nobody calls it, so the linker removes it: annotation-free
            // derivation costs nothing in the binary
            Expect.isFalse (wat.Contains "shallowEq_V2d") "unused derive eliminated"
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
            let _, errs = ws.EmitProgram ()
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
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "pipeline clean"
            Expect.equal (runWat wat) "42\n" "both plugins ran, semantics intact"
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
            let wat, errs = ws.EmitProgram ()
            Expect.isEmpty errs "still compiles"
            Expect.stringContains wat "func" "emits"
        }
    ]

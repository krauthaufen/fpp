module Fpp.Core.Plugins

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir

// Compiler plugins: deterministic TAST -> TAST transforms over typed core.
// Registered in project config (never via source annotations), run in order
// after lowering and before linking; the core linter validates each
// plugin's output, so a broken plugin is a compiler error naming it rather
// than a miscompilation. Annotation-free derivation is practical because
// dead-code elimination drops whatever nobody calls.

type Plugin =
    { Name : string
      /// per-file: sees one file's declarations, returns replacements
      PerFile : Decl list -> Decl list
      /// whole-program: sees everything at link time (registries, tables)
      WholeProgram : Decl list -> Decl list }

let idPlugin (name : string) =
    { Name = name; PerFile = id; WholeProgram = id }

// ---- constant folding: the simplest real TAST -> TAST rewrite ------------

let constFold =
    let rec foldE (e : Expr) : Expr =
        match e with
        | EPrim (op, [ a; b ]) ->
            let a2 = foldE a
            let b2 = foldE b
            (match a2, b2 with
             | ELit (LInt x), ELit (LInt y) ->
                 let xi = int x
                 let yi = int y
                 (match op with
                  | "+" -> ELit (LInt (string (xi + yi)))
                  | "-" -> ELit (LInt (string (xi - yi)))
                  | "*" -> ELit (LInt (string (xi * yi)))
                  | _ -> EPrim (op, [ a2; b2 ]))
             | _ -> EPrim (op, [ a2; b2 ]))
        | EPrim (op, xs) -> EPrim (op, List.map foldE xs)
        | EVarI (v, s, i) -> EVarI (v, s, i)
        | ELam (ps, b) -> ELam (ps, foldE b)
        | EApp (f, args) -> EApp (foldE f, List.map foldE args)
        | ELet (r, v, s, rhs, body) -> ELet (r, v, s, foldE rhs, foldE body)
        | EIf (c, t, f) -> EIf (foldE c, foldE t, foldE f)
        | EMatch (s, cs) -> EMatch (foldE s, cs |> List.map (fun (p, g, b) -> p, Option.map foldE g, foldE b))
        | ETuple xs -> ETuple (List.map foldE xs)
        | EListLit xs -> EListLit (List.map foldE xs)
        | ESeq xs -> ESeq (List.map foldE xs)
        | ECtor (n, s, xs) -> ECtor (n, s, List.map foldE xs)
        | ERecord (n, fs) -> ERecord (n, fs |> List.map (fun (f, v) -> f, foldE v))
        | EField (r, f, o) -> EField (foldE r, f, o)
        | EFieldSet (r, f, o, v) -> EFieldSet (foldE r, f, o, foldE v)
        | EIfaceCall (i, m, r, args) -> EIfaceCall (i, m, foldE r, List.map foldE args)
        | ECast (t, e, d) -> ECast (t, foldE e, d)
        | EWhile (c, b) -> EWhile (foldE c, foldE b)
        | EAssign (v, x) -> EAssign (v, foldE x)
        | EArray (n, xs) -> EArray (n, List.map foldE xs)
        | EIndex (n, a, i) -> EIndex (n, foldE a, foldE i)
        | EIndexSet (n, a, i, v) -> EIndexSet (n, foldE a, foldE i, foldE v)
        | EArrayLen (n, a) -> EArrayLen (n, foldE a)
        | EArrayCreate (n, a, b) -> EArrayCreate (n, foldE a, foldE b)
        | ETry (b, cs) -> ETry (foldE b, cs |> List.map (fun (p, g, x) -> p, Option.map foldE g, foldE x))
        | other -> other
    let perFile (ds : Decl list) =
        ds |> List.map (fun d ->
            match d with
            | DLet (r, v, s, e) -> DLet (r, v, s, foldE e)
            | other -> other)
    { Name = "constFold"; PerFile = perFile; WholeProgram = id }

// ---- derive shallowEquals for every record/struct type ------------------
// Emits `shallowEq_<Type> a b` comparing fields one level deep: scalars by
// value, references by identity. No annotations; DCE removes unused ones.

let deriveShallowEquals =
    let perFile (ds : Decl list) =
        let extra = vecNew<Decl> ()
        let mutable off = 900000
        for d in ds do
            match d with
            | DRecord (name, _, fields, _) when not (List.isEmpty fields) ->
                off <- off + 1
                let path = "(derive)"
                let fn = { Path = path; Offset = off; Name = "shallowEq_" + name }
                let av = { Path = path; Offset = off + 100000; Name = "a" }
                let bv = { Path = path; Offset = off + 200000; Name = "b" }
                let sch = mono (TCon ("?", []))
                let cmpField (f : string, kind : string) =
                    let ea = EField (EVar (av, sch), f, name)
                    let eb = EField (EVar (bv, sch), f, name)
                    if kind = "r" then EApp (EUnknown "refEq", [ ea; eb ])
                    else EPrim ("=", [ ea; eb ])
                let body =
                    fields
                    |> List.map cmpField
                    |> List.reduce (fun x y -> EPrim ("&&", [ x; y ]))
                vecAdd extra (DLet (false, fn, sch, ELam ([ av, sch; bv, sch ], body)))
            | _ -> ()
        ds @ vecToList extra
    { Name = "deriveShallowEquals"; PerFile = perFile; WholeProgram = id }

let builtinPlugins = [ constFold; deriveShallowEquals ]

let byName (n : string) : Plugin option =
    builtinPlugins |> List.tryFind (fun p -> p.Name = n)

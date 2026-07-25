module Fpp.Core.Link

open Fpp.Prelude
open Fpp.Core.Ir

// The link step, v0: demand-closure over symbols. Roots are the program's
// top-level value initializers; only reachable functions survive. Tier-1
// instantiation stamping plugs in here once call sites carry instantiations.

let deadCodeEliminate (decls : Decl list) : Decl list =
    let keep = dictNew<string * int, bool> ()
    let bodies = dictNew<string * int, Expr> ()
    for d in decls do
        match d with
        | DLet (_, v, _, e) -> dictSet bodies (v.Path, v.Offset) e
        | _ -> ()
    let work = vecNew<string * int> ()
    let demand (k : string * int) =
        if not (dictTryFind keep k).IsSome then
            dictSet keep k true
            vecAdd work k
    let rec scan (e : Expr) =
        match e with
        | EVar (v, _) -> demand (v.Path, v.Offset)
        | ELam (_, b) -> scan b
        | EApp (f, args) -> scan f; List.iter scan args
        | ELet (_, _, _, r, b) -> scan r; scan b
        | EIf (a, b, c) -> scan a; scan b; scan c
        | EMatch (s, cs) ->
            scan s
            for _, g, b in cs do
                (match g with Some g -> scan g | None -> ())
                scan b
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> List.iter scan xs
        | ECtor (_, _, xs) -> List.iter scan xs
        | ERecord (_, fs) -> for _, v in fs do scan v
        | EField (r, _) -> scan r
        | EWhile (c, b) -> scan c; scan b
        | EAssign (v, e) -> demand (v.Path, v.Offset); scan e
        | ETry (b, cs) ->
            scan b
            for _, g, e in cs do
                (match g with Some g -> scan g | None -> ())
                scan e
        | EArray (_, xs) -> List.iter scan xs
        | EIndex (_, a, i) -> scan a; scan i
        | EIndexSet (_, a, i, v) -> scan a; scan i; scan v
        | EArrayLen (_, a) -> scan a
        | EArrayCreate (_, n, v) -> scan n; scan v
        | EArrayPin (_, a) -> scan a
        | EArrayUnpin (_, a) -> scan a
        | _ -> ()
    // roots: value initializers (program effects)
    for d in decls do
        match d with
        | DLet (_, v, _, e) ->
            (match e with
             | ELam _ -> ()
             | _ ->
                 demand (v.Path, v.Offset)
                 scan e)
        | _ -> ()
    let mutable i = 0
    while i < vecLen work do
        let k = vecGet work i
        (match dictTryFind bodies k with
         | Some body -> scan body
         | None -> ())
        i <- i + 1
    decls
    |> List.filter (fun d ->
        match d with
        | DLet (_, v, _, ELam _) -> (dictTryFind keep (v.Path, v.Offset)).IsSome
        | DExtern (v, _) -> (dictTryFind keep (v.Path, v.Offset)).IsSome
        | _ -> true)

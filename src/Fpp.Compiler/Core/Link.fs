module Fpp.Core.Link

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir

// ---- tier-1 monomorphization ---------------------------------------------
// One stamped copy per distinct STRUCT instantiation; ONE shared body for
// all reference-type instantiations (__Canon). Unclassifiable instantiations
// are errors, never a silent uniform fallback.

type Classification =
    | Stamp of string list      // struct instantiation -> specialize
    | Canon                     // all-reference instantiation -> share
    | Unclassifiable of string  // compile error

/// `isStructName` decides which type names are value types needing layout.
let classify (isStructName : string -> bool) (inst : string list) : Classification =
    // "#id" = instantiated at the enclosing binding's type variable. In the
    // UNSTAMPED generic body that is exactly the canonical (uniform) case;
    // inside a stamped clone these have already been substituted away.
    if inst |> List.exists (fun t -> t = "" || t.StartsWith "#") then Canon
    elif inst |> List.exists isStructName then Stamp inst
    else Canon

/// substitute a symbolic element/type name ("#id") with the concrete one
let private substName (subst : Dict<string, string>) (n : string) =
    if n.StartsWith "#" then
        match dictTryFind subst n with
        | Some concrete -> concrete
        | None -> n
    else n

let private mangleInst (name : string) (inst : string list) =
    name + "$" + String.concat "$" inst

/// Substitute the quantified vars of a scheme with concrete named types.
let private substScheme (inst : string list) (sch : Scheme) : Scheme =
    if List.isEmpty sch.Quantified || sch.Quantified.Length <> inst.Length then sch
    else
        let m = dictNew<int, Type> ()
        List.zip sch.Quantified inst |> List.iter (fun (v, n) -> dictSet m v.Id (TCon (n, [])))
        let rec go (t : Type) : Type =
            match prune t with
            | TVar v -> (match dictTryFind m v.Id with Some c -> c | None -> TVar v)
            | TCon (n, args) -> TCon (n, List.map go args)
            | TFun (a, b) -> TFun (go a, go b)
            | TTuple ts -> TTuple (List.map go ts)
        { Quantified = []; Body = go sch.Body }

let rec private mapExpr (f : Expr -> Expr) (e : Expr) : Expr =
    let r = mapExpr f
    let e2 =
        match e with
        | ELam (ps, b) -> ELam (ps, r b)
        | EApp (g, args) -> EApp (r g, List.map r args)
        | ELet (rc, v, s, rhs, b) -> ELet (rc, v, s, r rhs, r b)
        | EIf (a, b, c) -> EIf (r a, r b, r c)
        | EMatch (s, cs) -> EMatch (r s, cs |> List.map (fun (p, g, b) -> p, Option.map r g, r b))
        | ETuple xs -> ETuple (List.map r xs)
        | EListLit xs -> EListLit (List.map r xs)
        | ESeq xs -> ESeq (List.map r xs)
        | EPrim (op, xs) -> EPrim (op, List.map r xs)
        | ECtor (n, s, xs) -> ECtor (n, s, List.map r xs)
        | ERecord (n, fs) -> ERecord (n, fs |> List.map (fun (k, v) -> k, r v))
        | EField (x, fn) -> EField (r x, fn)
        | EWhile (c, b) -> EWhile (r c, r b)
        | EAssign (v, x) -> EAssign (v, r x)
        | EArray (n, xs) -> EArray (n, List.map r xs)
        | EIndex (n, a, i) -> EIndex (n, r a, r i)
        | EIndexSet (n, a, i, v) -> EIndexSet (n, r a, r i, r v)
        | EArrayLen (n, a) -> EArrayLen (n, r a)
        | EArrayCreate (n, a, b) -> EArrayCreate (n, r a, r b)
        | EArrayPin (n, a) -> EArrayPin (n, r a)
        | EArrayUnpin (n, a) -> EArrayUnpin (n, r a)
        | ETry (b, cs) -> ETry (r b, cs |> List.map (fun (p, g, x) -> p, Option.map r g, r x))
        | other -> other
    f e2

/// Stamp one specialized copy per struct instantiation, rewrite the calls,
/// and report anything that cannot be classified.
let monomorphize (isStructName : string -> bool) (decls : Decl list) : Decl list * string list =
    let errors = vecNew<string> ()
    let bodies = dictNew<string * int, bool * VarId * Scheme * Expr> ()
    for d in decls do
        match d with
        | DLet (rc, v, sch, e) -> dictSet bodies (v.Path, v.Offset) (rc, v, sch, e)
        | _ -> ()
    // A body that performs array/layout operations at a type-variable
    // element type cannot be shared: int[], string[] and struct[] have
    // different representations. Such functions are stamped at EVERY
    // instantiation, not just struct ones.
    let layoutDependent = dictNew<string * int, bool> ()
    let rec usesLayoutVar (e : Expr) : bool =
        let anyOf xs = xs |> List.exists usesLayoutVar
        let symbolic (n : string) = n.StartsWith "#"
        match e with
        | EArray (n, xs) -> symbolic n || anyOf xs
        | EIndex (n, a, i) -> symbolic n || usesLayoutVar a || usesLayoutVar i
        | EIndexSet (n, a, i, v) -> symbolic n || anyOf [ a; i; v ]
        | EArrayLen (n, a) -> symbolic n || usesLayoutVar a
        | EArrayCreate (n, a, b) -> symbolic n || anyOf [ a; b ]
        | EArrayPin (n, a) | EArrayUnpin (n, a) -> symbolic n || usesLayoutVar a
        | ELam (_, b) -> usesLayoutVar b
        | EApp (f, args) -> usesLayoutVar f || anyOf args
        | ELet (_, _, _, r, b) -> usesLayoutVar r || usesLayoutVar b
        | EIf (a, b, c) -> anyOf [ a; b; c ]
        | EMatch (s, cs) -> usesLayoutVar s || (cs |> List.exists (fun (_, _, b) -> usesLayoutVar b))
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> anyOf xs
        | ECtor (_, _, xs) -> anyOf xs
        | ERecord (_, fs) -> fs |> List.exists (fun (_, v) -> usesLayoutVar v)
        | EField (r, _) -> usesLayoutVar r
        | EWhile (c, b) -> usesLayoutVar c || usesLayoutVar b
        | EAssign (_, x) -> usesLayoutVar x
        | ETry (b, cs) -> usesLayoutVar b || (cs |> List.exists (fun (_, _, x) -> usesLayoutVar x))
        | _ -> false
    for d in decls do
        match d with
        | DLet (_, v, _, e) -> dictSet layoutDependent (v.Path, v.Offset) (usesLayoutVar e)
        | _ -> ()
    // transitive: calling a layout-dependent generic at a symbolic
    // instantiation makes the caller layout-dependent too (fixpoint)
    let rec callsLayoutDep (e : Expr) : bool =
        let anyOf xs = xs |> List.exists callsLayoutDep
        match e with
        | EVarI (v, _, inst) ->
            (dictTryFind layoutDependent (v.Path, v.Offset)) = Some true
            && inst |> List.exists (fun t -> t = "" || t.StartsWith "#")
        | ELam (_, b) -> callsLayoutDep b
        | EApp (f, args) -> callsLayoutDep f || anyOf args
        | ELet (_, _, _, r, b) -> callsLayoutDep r || callsLayoutDep b
        | EIf (a, b, c) -> anyOf [ a; b; c ]
        | EMatch (s, cs) -> callsLayoutDep s || (cs |> List.exists (fun (_, _, b) -> callsLayoutDep b))
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> anyOf xs
        | ECtor (_, _, xs) -> anyOf xs
        | ERecord (_, fs) -> fs |> List.exists (fun (_, v) -> callsLayoutDep v)
        | EField (r, _) -> callsLayoutDep r
        | EWhile (c, b) -> callsLayoutDep c || callsLayoutDep b
        | EAssign (_, x) -> callsLayoutDep x
        | EArray (_, xs) -> anyOf xs
        | EIndex (_, a, i) -> anyOf [ a; i ]
        | EIndexSet (_, a, i, v) -> anyOf [ a; i; v ]
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) -> callsLayoutDep a
        | EArrayCreate (_, a, b) -> anyOf [ a; b ]
        | ETry (b, cs) -> callsLayoutDep b || (cs |> List.exists (fun (_, _, x) -> callsLayoutDep x))
        | _ -> false
    let mutable changed = true
    while changed do
        changed <- false
        for d in decls do
            match d with
            | DLet (_, v, _, e) ->
                if (dictTryFind layoutDependent (v.Path, v.Offset)) <> Some true && callsLayoutDep e then
                    dictSet layoutDependent (v.Path, v.Offset) true
                    changed <- true
            | _ -> ()

    let stamped = dictNew<string, Decl> ()      // mangled name -> clone
    let queue = vecNew<(string * int) * string list> ()
    let seen = dictNew<string, bool> ()

    // rewrite EVarI uses: struct instantiations point at the stamped clone,
    // reference instantiations keep the shared body
    // `isTemplate` marks the original body of a layout-dependent generic:
    // it is never emitted (every use is stamped, DCE drops it), so demands
    // that are still symbolic there are not errors — they resolve in clones.
    let rewrite (owner : string) (subst : Dict<string, string>) (isTemplate : bool) (e : Expr) : Expr =
        e |> mapExpr (fun x ->
            match x with
            | EVarI (v, sch, inst0) ->
                // propagate the caller's instantiation into nested demands
                let inst =
                    inst0 |> List.map (fun t ->
                        if t.StartsWith "#" then
                            match dictTryFind subst t with
                            | Some concrete -> concrete
                            | None -> t
                        else t)
                let needsLayout = (dictTryFind layoutDependent (v.Path, v.Offset)) = Some true
                let cls =
                    if needsLayout then
                        if inst |> List.exists (fun t -> t = "" || t.StartsWith "#") then
                            Unclassifiable "element layout is not statically known here"
                        else Stamp inst
                    else classify isStructName inst
                (match cls with
                 | Canon -> EVar (v, sch)
                 | Unclassifiable why ->
                     if not isTemplate then
                         vecAdd errors ("cannot specialize '" + v.Name + "' in " + owner + ": " + why)
                     EVar (v, sch)
                 | Stamp i ->
                     let mangled = mangleInst v.Name i
                     let key = (v.Path, v.Offset)
                     (match dictTryFind bodies key with
                      | Some (_, _, _, _) ->
                          if not (dictTryFind seen mangled).IsSome then
                              dictSet seen mangled true
                              vecAdd queue (key, i)
                          EVar ({ Path = v.Path; Offset = v.Offset + 7000000 + (abs (hash mangled) % 1000000)
                                  Name = mangled }, substScheme i sch)
                      | None ->
                          // a struct instantiation whose body we cannot see
                          // would have to run on the uniform representation:
                          // that is a silent deoptimization, so it is an error
                          if not isTemplate then
                              vecAdd errors
                                ("cannot specialize '" + v.Name + "' at struct instantiation <"
                                 + String.concat ", " i + "> in " + owner
                                 + ": the body is not available for stamping")
                          EVar (v, sch)))
            | EArray (n, xs) -> EArray (substName subst n, xs)
            | EIndex (n, a, i) -> EIndex (substName subst n, a, i)
            | EIndexSet (n, a, i, v) -> EIndexSet (substName subst n, a, i, v)
            | EArrayLen (n, a) -> EArrayLen (substName subst n, a)
            | EArrayCreate (n, a, b) -> EArrayCreate (substName subst n, a, b)
            | EArrayPin (n, a) -> EArrayPin (substName subst n, a)
            | EArrayUnpin (n, a) -> EArrayUnpin (substName subst n, a)
            | other -> other)

    let out = vecNew<Decl> ()
    for d in decls do
        match d with
        | DLet (rc, v, sch, e) ->
            let isTemplate = (dictTryFind layoutDependent (v.Path, v.Offset)) = Some true
            vecAdd out (DLet (rc, v, sch, rewrite v.Name (dictNew ()) isTemplate e))
        | other -> vecAdd out other

    // transitive closure: stamping a clone may demand further stamps
    let mutable i = 0
    while i < vecLen queue do
        let key, inst = vecGet queue i
        (match dictTryFind bodies key with
         | Some (rc, v, sch, e) ->
             let mangled = mangleInst v.Name inst
             let nv = { Path = v.Path; Offset = v.Offset + 7000000 + (abs (hash mangled) % 1000000); Name = mangled }
             // map the callee's quantified vars to this instantiation so
             // demands nested in the body specialize too
             let subst = dictNew<string, string> ()
             if sch.Quantified.Length = inst.Length then
                 List.zip sch.Quantified inst
                 |> List.iter (fun (qv, n) -> dictSet subst ("#" + string qv.Id) n)
             let clone = DLet (rc, nv, substScheme inst sch, rewrite mangled subst false e)
             dictSet stamped mangled clone
         | None -> ())
        i <- i + 1

    // layout-dependent templates are never callable: every use is stamped
    // (or an error), so they are removed by construction rather than left
    // for reachability to maybe drop
    let emitted =
        vecToList out
        |> List.filter (fun d ->
            match d with
            // only FUNCTION templates are unreachable-by-construction;
            // value initializers are program effects and must never be cut
            | DLet (_, v, _, ELam _) -> (dictTryFind layoutDependent (v.Path, v.Offset)) <> Some true
            | _ -> true)
    emitted @ (dictPairs stamped |> List.map snd), vecToList errors

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
        | EVarI (v, _, _) -> demand (v.Path, v.Offset)
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

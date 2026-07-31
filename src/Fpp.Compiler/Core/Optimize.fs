module Fpp.Core.Optimize

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir

// Optimization passes over the CORE IR, after monomorphization and before
// emission. They live here rather than in the backend on purpose: these are
// decisions that need TYPES and shapes, which the backend has already thrown
// away, and every backend wants them. wasm goes through Cranelift and a
// native backend would go through LLVM — neither can undo a representation
// or a call the front end already committed to.
//
// The gate is the bootstrap: these passes change what is emitted, so the
// stage-0/stage-1 fixpoint stops being a check that the OUTPUT is stable and
// remains a check that the compiler agrees with itself. The behavioural
// gate is the test suite.

/// Rebuild a node with `r` applied to its immediate children. Separate from
/// `mapExpr` so a TOP-DOWN rewrite can drive its own recursion:
/// `uncurryTupleArgs` must recognise `EApp (EVar f, ...)` before the
/// `EVar f` inside it is rewritten into something else.
let rec private mapChildrenWith (r : Expr -> Expr) (e : Expr) : Expr =
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
        | ERecordExt (n, bse, fs) -> ERecordExt (n, r bse, fs |> List.map (fun (k, v) -> k, r v))
        | EField (x, fn, o) -> EField (r x, fn, o)
        | EIfaceCall (i, m, recv, args) -> EIfaceCall (i, m, r recv, List.map r args)
        | ECast (t, x, d) -> ECast (t, r x, d)
        | ETypeTest (t, x) -> ETypeTest (t, r x)
        | EFieldSet (x, fn, o, v) -> EFieldSet (r x, fn, o, r v)
        | EWhile (c, b) -> EWhile (r c, r b)
        | EAssign (v, x) -> EAssign (v, r x)
        | EArray (n, xs) -> EArray (n, List.map r xs)
        | EIndex (n, a, i) -> EIndex (n, r a, r i)
        | EIndexSet (n, a, i, v) -> EIndexSet (n, r a, r i, r v)
        | EArrayLen (n, a) -> EArrayLen (n, r a)
        | EArrayCreate (n, a, b) -> EArrayCreate (n, r a, r b)
        | EArrayPin (n, a) -> EArrayPin (n, r a)
        | EArrayUnpin (n, a) -> EArrayUnpin (n, r a)
        | EArrayBytes (n, a) -> EArrayBytes (n, r a)
        | ETry (b, cs) -> ETry (r b, cs |> List.map (fun (p, g, x) -> p, Option.map r g, r x))
        | other -> other

and private mapExpr (f : Expr -> Expr) (e : Expr) : Expr =
    f (mapChildrenWith (mapExpr f) e)

let rec private sizeOf (e : Expr) : int =
    let sum xs = List.fold (fun a x -> a + sizeOf x) 0 xs
    match e with
    | ELam (_, b) -> 1 + sizeOf b
    | EApp (g, args) -> 1 + sizeOf g + sum args
    | ELet (_, _, _, rhs, b) -> 1 + sizeOf rhs + sizeOf b
    | EIf (a, b, c) -> 1 + sizeOf a + sizeOf b + sizeOf c
    | EMatch (s, cs) ->
        1 + sizeOf s
        + List.fold (fun a (_, g, b) -> a + sizeOf b + (match g with Some x -> sizeOf x | None -> 0)) 0 cs
    | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | EArray (_, xs) -> 1 + sum xs
    | ECtor (_, _, xs) -> 1 + sum xs
    | ERecord (_, fs) -> 1 + List.fold (fun a (_, v) -> a + sizeOf v) 0 fs
    | ERecordExt (_, b, fs) -> 1 + sizeOf b + List.fold (fun a (_, v) -> a + sizeOf v) 0 fs
    | EField (x, _, _) -> 1 + sizeOf x
    | EIfaceCall (_, _, recv, args) -> 1 + sizeOf recv + sum args
    | ECast (_, x, _) | ETypeTest (_, x) -> 1 + sizeOf x
    | EFieldSet (x, _, _, v) -> 1 + sizeOf x + sizeOf v
    | EWhile (c, b) -> 1 + sizeOf c + sizeOf b
    | EAssign (_, x) -> 1 + sizeOf x
    | EIndex (_, a, i) -> 1 + sizeOf a + sizeOf i
    | EIndexSet (_, a, i, v) -> 1 + sizeOf a + sizeOf i + sizeOf v
    | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) -> 1 + sizeOf a
    | EArrayCreate (_, a, b) -> 1 + sizeOf a + sizeOf b
    | ETry (b, cs) -> 1 + sizeOf b + List.fold (fun a (_, _, x) -> a + sizeOf x) 0 cs
    | _ -> 1

/// Does `e` mention any of these definitions? Used to keep a function from
/// being inlined into itself, directly or through a cycle.
let private mentions (keys : Dict<string * int, bool>) (e : Expr) : bool =
    let mutable found = false
    mapExpr
        (fun x ->
            (match x with
             | EVar (v, _) | EVarI (v, _, _) | EAssign (v, _) ->
                 if (dictTryFind keys (v.Path, v.Offset)).IsSome then found <- true
             | _ -> ())
            x)
        e |> ignore
    found

/// Every binder in `e` gets a FRESH identity. Substituting a body into a
/// call site without this lets the body's `let x` capture, or be captured
/// by, an `x` already live at the site — and the two are only distinguished
/// by (path, offset). A synthetic path keeps the fresh ones out of every
/// range a real source file can produce.
let private freshenBinders (counter : Vec<int>) (e : Expr) : Expr =
    let subst = dictNew<string * int, VarId> ()
    let fresh (v : VarId) =
        if (dictTryFind subst (v.Path, v.Offset)).IsNone then
            let n = vecGet counter 0
            vecSet counter 0 (n + 1)
            dictSet subst (v.Path, v.Offset) { Path = "$inline"; Offset = n; Name = v.Name }
    let rec bindPat (p : Pat) =
        match p with
        | PVar (v, _) -> fresh v
        | PAs (inner, v, _) -> fresh v; bindPat inner
        | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.iter bindPat ps
        | PCons (h, t) -> bindPat h; bindPat t
        | PWild | PLit _ | PTypeTest _ -> ()
    mapExpr
        (fun x ->
            (match x with
             | ELam (ps, _) -> for v, _ in ps do fresh v
             | ELet (_, v, _, _, _) -> fresh v
             | EMatch (_, cs) -> for p, _, _ in cs do bindPat p
             | ETry (_, cs) -> for p, _, _ in cs do bindPat p
             | _ -> ())
            x)
        e |> ignore
    if dictPairs subst |> List.isEmpty then e
    else
    let sub (v : VarId) =
        match dictTryFind subst (v.Path, v.Offset) with
        | Some nv -> nv
        | None -> v
    let rec subPat (p : Pat) =
        match p with
        | PVar (v, sc) -> PVar (sub v, sc)
        | PAs (inner, v, sc) -> PAs (subPat inner, sub v, sc)
        | PCtor (n, sc, ps) -> PCtor (n, sc, List.map subPat ps)
        | PTuple ps -> PTuple (List.map subPat ps)
        | PListLit ps -> PListLit (List.map subPat ps)
        | POr ps -> POr (List.map subPat ps)
        | PCons (h, t) -> PCons (subPat h, subPat t)
        | other -> other
    mapExpr
        (fun x ->
            match x with
            | EVar (v, s) -> EVar (sub v, s)
            | EVarI (v, s, i) -> EVarI (sub v, s, i)
            | ELam (ps, b) -> ELam (ps |> List.map (fun (v, s) -> sub v, s), b)
            | ELet (rc, v, s, rhs, b) -> ELet (rc, sub v, s, rhs, b)
            | EAssign (v, x2) -> EAssign (sub v, x2)
            | EMatch (s, cs) -> EMatch (s, cs |> List.map (fun (p, g, b) -> subPat p, g, b))
            | ETry (b, cs) -> ETry (b, cs |> List.map (fun (p, g, x2) -> subPat p, g, x2))
            | other -> other)
        e

/// A tuple that is BUILT and immediately TAKEN APART never has to exist.
///
/// The tuple stays a reference value — this changes no representation and no
/// semantics, and `(a, b)` is still a heap object wherever anything can
/// observe it. It simply is not allocated when the very next thing to happen
/// is destructuring it. `match (a, b) with (x, y) -> body` becomes
/// `let x = a in let y = b in body`, which evaluates a then b then the body,
/// exactly as before.
///
/// Only irrefutable, unguarded, single-case matches on a tuple LITERAL
/// qualify. That looks narrow, and on its own it is: the shape that matters
/// appears when a tupled function is inlined, because `f (a, b)` becomes
/// `let t = (a, b) in match t with (x, y) -> ...` and the chain shows up.
/// This is the pass that makes inlining worth anything.
let fuseTuples (decls : Decl list) : Decl list =
    let rewrite (e : Expr) : Expr =
        match e with
        | EMatch (ETuple xs, [ (PTuple ps, None, body) ]) when
              ps.Length = xs.Length
              && ps |> List.forall (fun p -> match p with PVar _ -> true | _ -> false) ->
            List.fold2
                (fun acc p x ->
                    match p with
                    | PVar (v, sch) -> ELet (false, v, sch, x, acc)
                    | _ -> acc)
                body (List.rev ps) (List.rev xs)
        | other -> other
    decls
    |> List.map (fun d ->
        match d with
        | DLet (rc, v, sch, body) -> DLet (rc, v, sch, mapExpr rewrite body)
        | other -> other)

/// `f (a, b)` compiles to a TWO-ARGUMENT CALL. The convention:
///
///   f (a, b)    a two-argument call, no tuple
///   f t         `match t with (x, y) -> f x y` at the call site — the
///               caller's tuple still exists, it just is not REBUILT to be
///               pulled apart again
///   f as value  one shared tupled SHIM per function (an ordinary top-level
///               decl the backend already knows how to emit), not a fresh
///               lambda per use site; dead-code elimination drops the ones
///               nobody reaches. The shim keeps the SOURCE (tupled) scheme,
///               which is what a first-class consumer applies it at.
///
/// The traversal is BOTTOM-UP through plain `mapExpr`, on purpose. Children
/// rebuild before parents, so by the time a call node is visited its head
/// `EVar` has already been rewritten to the shim — and the call case UNDOES
/// that (shim identities are invertible) into a direct multi-argument call.
/// A top-down formulation with a local recursive `go` passed first-class
/// into the traversal was tried twice and MISCOMPILES under self-hosting
/// (the pass runs correctly under dotnet and builds a cyclic expression when
/// the compiler runs as wasm); until that is hunted down, nothing in this
/// pass hands a local recursive closure to another function.
///
/// Excluded candidates, each for a reason found by compiling the compiler:
/// - **over-applied functions**: `f (a, b) extra` lowers FLATTENED to
///   `EApp (f, [tuple; extra])`, so rewriting the definition would bind
///   tuple->a, extra->b — garbage;
/// - **a body that still mentions the tuple parameter** after destructuring;
/// - anything in DClass/DMembers/DExtern lists (fixed-signature machinery).
///
/// The EXPORTED signature is untouched: `BuildLibrary` serializes the
/// pre-optimization decls, so `a -> b -> r` and `(a * b) -> r` stay
/// distinguishable to consumers, who re-derive this convention themselves.
let private shimBase = 33000000

let uncurryTupleArgs (decls : Decl list) : Decl list =
    let pinned = dictNew<string * int, bool> ()
    for d in decls do
        match d with
        | DClass (_, _, own, impls) ->
            for _, v in own do dictSet pinned (v.Path, v.Offset) true
            for _, ms in impls do
                for _, v in ms do dictSet pinned (v.Path, v.Offset) true
        | DMembers (_, own) -> for _, v in own do dictSet pinned (v.Path, v.Offset) true
        | DExtern (v, _) -> dictSet pinned (v.Path, v.Offset) true
        | DExport (v, _) -> dictSet pinned (v.Path, v.Offset) true
        | _ -> ()
    let candInfo = dictNew<string * int, string * (VarId * Scheme) list * Scheme> ()
    for d in decls do
        match d with
        | DLet (_, v, sch, ELam ([ (pv, _) ], EMatch (EVar (sv, _), [ (PTuple ps, None, mbody) ]))) when
              (sv.Path, sv.Offset) = (pv.Path, pv.Offset)
              && not (dictTryFind pinned (v.Path, v.Offset)).IsSome
              && ps.Length >= 2
              && ps |> List.forall (fun p -> match p with PVar _ -> true | _ -> false) ->
            let selfK = dictNew<string * int, bool> ()
            dictSet selfK (pv.Path, pv.Offset) true
            if not (mentions selfK mbody) then
                dictSet candInfo (v.Path, v.Offset)
                    (v.Name,
                     ps |> List.map (fun p -> match p with PVar (bv, bs) -> bv, bs | _ -> pv, mono (TCon ("?", []))),
                     sch)
        | _ -> ()
    // disqualify over-applied candidates
    let overApplied = vecNew<string * int> ()
    for d in decls do
        match d with
        | DLet (_, _, _, body) ->
            mapExpr
                (fun x ->
                    (match x with
                     | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when
                           List.length args > 1 && (dictTryFind candInfo (v.Path, v.Offset)).IsSome ->
                         vecAdd overApplied (v.Path, v.Offset)
                     | _ -> ())
                    x)
                body |> ignore
        | _ -> ()
    for k in vecToList overApplied do dictRemove candInfo k
    if dictPairs candInfo |> List.isEmpty then decls
    else
    let isCand (v : VarId) = (dictTryFind candInfo (v.Path, v.Offset)).IsSome
    let shimOf (pth : string) (off : int) (name : string) : VarId =
        { Path = pth; Offset = off + shimBase; Name = name + "$tupled" }
    let isShim (v : VarId) =
        v.Offset >= shimBase && (dictTryFind candInfo (v.Path, v.Offset - shimBase)).IsSome
    let ucount = vecNew<int> ()
    vecAdd ucount 0
    // the BACKEND-FACING signature uncurries with the parameters; the
    // exported one was serialized before this pass ran
    let uncurryScheme (n : int) (sch : Scheme) : Scheme =
        match prune sch.Body with
        | TFun (TTuple ts, r) when ts.Length = n ->
            { sch with Body = List.foldBack (fun t acc -> TFun (t, acc)) ts r }
        | _ -> sch
    /// `match arg with (x0, x1, ...) -> f x0 x1 ... rest`, with FRESH
    /// binders — the definition's own binder VarIds must not be rebound in
    /// another function (backend local state is keyed per VarId).
    let destructuredCall (fv : VarId) (fsch : Scheme) (bs : (VarId * Scheme) list) (arg : Expr) (rest : Expr list) : Expr =
        let fresh =
            bs |> List.map (fun (bv, bsch) ->
                let n = vecGet ucount 0
                vecSet ucount 0 (n + 1)
                ({ Path = "$untuple"; Offset = n; Name = bv.Name } : VarId), bsch)
        EMatch (arg,
                [ (PTuple (fresh |> List.map (fun (nv, ns) -> PVar (nv, ns))),
                   None,
                   EApp (EVar (fv, fsch), (fresh |> List.map (fun (nv, ns) -> EVar (nv, ns))) @ rest)) ])
    let rewriteNode (x : Expr) : Expr =
        match x with
        // every bare candidate reference becomes the shim — including call
        // heads, which the EApp case below converts back
        | EVar (f, fsch) when isCand f ->
            let nm, _, _ = (dictTryFind candInfo (f.Path, f.Offset)).Value
            EVar (shimOf f.Path f.Offset nm, fsch)
        | EVarI (f, fsch, _) when isCand f ->
            let nm, _, _ = (dictTryFind candInfo (f.Path, f.Offset)).Value
            EVar (shimOf f.Path f.Offset nm, fsch)
        // a DIRECT call: the head arrived here already shimmed (children
        // rebuild first); undo that into the multi-argument call
        | EApp (EVar (s, ssch), arg :: rest) when isShim s ->
            let orig = (s.Path, s.Offset - shimBase)
            let nm, bs, sch = (dictTryFind candInfo orig).Value
            let fv : VarId = { Path = s.Path; Offset = s.Offset - shimBase; Name = nm }
            let usch = uncurryScheme bs.Length sch
            (match arg with
             | ETuple xs when xs.Length = bs.Length -> EApp (EVar (fv, usch), xs @ rest)
             | other -> destructuredCall fv usch bs other rest)
        | other -> other
    let rewritten =
        decls
        |> List.map (fun d ->
            match d with
            | DLet (rc, v, sch, ELam ([ _ ], EMatch (_, [ (_, None, mbody) ]))) when isCand v ->
                let _, bs, _ = (dictTryFind candInfo (v.Path, v.Offset)).Value
                DLet (rc, v, uncurryScheme bs.Length sch, ELam (bs, mapExpr rewriteNode mbody))
            | DLet (rc, v, sch, body) -> DLet (rc, v, sch, mapExpr rewriteNode body)
            | other -> other)
    let shims =
        dictPairs candInfo
        |> List.map (fun ((pth, off), (nm, bs, sch)) ->
            let tupTy = match prune sch.Body with TFun (a, _) -> a | _ -> TCon ("?", [])
            let tv : VarId = { Path = "$untuple$t"; Offset = off; Name = "t" }
            let fv : VarId = { Path = pth; Offset = off; Name = nm }
            DLet (false, shimOf pth off nm, sch,
                  ELam ([ tv, mono tupTy ],
                        destructuredCall fv (uncurryScheme bs.Length sch) bs (EVar (tv, mono tupTy)) [])))
    rewritten @ shims

/// A body small enough that the call costs more than the code. Measured in
/// IR nodes; a call is an allocation-free direct call in the best case and a
/// closure application in the worst, so the threshold is not tiny.
let private inlineThreshold = 6

/// Inline non-recursive functions at FULL-ARITY call sites.
///
/// Arguments are bound to `let`s rather than substituted into the body: F++
/// has mutable locals and assignment, so substituting an argument used twice
/// would evaluate it twice, and one used under a branch would move its
/// effects. Binding preserves both the order and the count.
let inlineCalls (decls : Decl list) : Decl list =
    let counter = vecNew<int> ()
    vecAdd counter 0
    // candidates: non-recursive top-level functions with small bodies
    let bodies = dictNew<string * int, (VarId * Scheme) list * Expr> ()
    let selfKeys = dictNew<string * int, bool> ()
    for d in decls do
        match d with
        | DLet (false, v, _, ELam (ps, body)) ->
            if sizeOf body <= inlineThreshold then
                let k = dictNew<string * int, bool> ()
                dictSet k (v.Path, v.Offset) true
                // a body that names itself is recursive whatever the
                // declaration says, and inlining it would not terminate
                if not (mentions k body) then
                    dictSet bodies (v.Path, v.Offset) (ps, body)
                    dictSet selfKeys (v.Path, v.Offset) true
        | _ -> ()
    if dictPairs bodies |> List.isEmpty then decls
    else
    let expand (owner : string * int) (e : Expr) : Expr =
        mapExpr
            (fun x ->
                match x with
                | EApp (EVar (f, _), args) when (f.Path, f.Offset) <> owner ->
                    (match dictTryFind bodies (f.Path, f.Offset) with
                     | Some (ps, body) when ps.Length = args.Length ->
                         let fresh = freshenBinders counter (ELam (ps, body))
                         (match fresh with
                          | ELam (ps2, body2) ->
                              // innermost-last so the first argument binds
                              // outermost, which is the evaluation order the
                              // call site had
                              List.fold2
                                  (fun acc (pv, psch) a -> ELet (false, pv, psch, a, acc))
                                  body2 (List.rev ps2) (List.rev args)
                          | _ -> x)
                     | _ -> x)
                | other -> other)
            e
    // two rounds: inlining exposes call sites that were behind a call. A
    // fixpoint would be unbounded, and the second round already reaches the
    // cases that matter (an accessor behind an accessor).
    let mutable out = decls
    let mutable round = 0
    while round < 1 do
        out <-
            out
            |> List.map (fun d ->
                match d with
                | DLet (rc, v, sch, body) -> DLet (rc, v, sch, expand (v.Path, v.Offset) body)
                | other -> other)
        round <- round + 1
    out

/// Every pass, in order.
///
/// `inlineCalls` is NOT among them yet, and the reason is measured rather
/// than assumed. On a fixed corpus, the compiler built with inlining ran
/// 1492-1506ms against 1481-1636ms without it — indistinguishable — for 3.6%
/// more code. Inlining the whole self-compile at a threshold of 24 was worse
/// still: 43s -> 55s and 6.26MB -> 8.51MB of emitted wat.
///
/// That is not a bug in the pass; it is what inlining is worth on an IR
/// where every value is `anyref`. A wasm direct call is cheap, and the body
/// that gets copied in still boxes and unboxes exactly as it did. Inlining
/// pays when it ENABLES something — unboxed arithmetic fusing across the
/// call, a constant reaching a branch, a closure that stops being built —
/// and none of those passes exist yet. It is kept, correct and gated, to be
/// turned on with the unboxing work, which is when it starts to.
let optimize (decls : Decl list) : Decl list = decls |> uncurryTupleArgs |> fuseTuples

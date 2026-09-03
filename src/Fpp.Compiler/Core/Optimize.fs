module Fpp.Core.Optimize

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir

/// Digits only, no `System.Int32.TryParse`: the SELF-HOSTED compiler has no
/// such API, so a flag reader written with one answers differently in stage-0
/// and stage-1 — and the fixpoint then reports a byte mismatch that is really
/// the two stages configuring themselves differently, not a miscompile.
let private intOr (dflt : int) (s : string) : int =
    if isNull s || s = "" then dflt
    else
        let mutable ok = true
        let mutable acc = 0
        for i in 0 .. strLen s - 1 do
            let c = s.[i]
            if c >= '0' && c <= '9' then acc <- acc * 10 + (int c - int '0')
            else ok <- false
        if ok then acc else dflt



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
        | PCtor (_, _, ps) | PTuple ps | PListLit ps | PArrLit (_, ps) | POr ps -> List.iter bindPat ps
        | PAnd (a, b) -> bindPat a; bindPat b
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
    // NO early return when there is nothing to rename. The second walk is what
    // gives the copy FRESH NODES, and the lambda lift keys a closure by node
    // REFERENCE — hand two inlined copies the same ELam object and both get one
    // lifted function with one set of captures. Returning `e` unchanged here is
    // exactly that: `List.sort` and `Array.sort` each inlined fine on their own
    // and trapped in a program containing both.
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
        | PArrLit (k, ps) -> PArrLit (k, List.map subPat ps)
        | PAnd (a, b) -> PAnd (subPat a, subPat b)
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
    let allPVar (ps : Pat list) = ps |> List.forall (fun p -> match p with PVar _ -> true | _ -> false)
    let rewrite (e : Expr) : Expr =
        match e with
        // the shape INLINING actually produces. A tupled parameter is bound by
        // the inliner as an ordinary argument let, so the scrutinee is that
        // VARIABLE and not the literal — matching only the literal meant the
        // pass never fired on inlined code, and every inlined tupled call
        // built a real tuple. On ray-triangle that was 886 MB of tuples that
        // the by-value ABI had been keeping in registers.
        | ELet (false, tv, _, ETuple xs, EMatch ((EVar (sv, _) | EVarI (sv, _, _)), [ (PTuple ps, None, body) ])) when
              (sv.Path, sv.Offset) = (tv.Path, tv.Offset)
              && ps.Length = xs.Length && allPVar ps
              // the binding exists only to be destructured: any OTHER use of
              // it needs the tuple to be a real value
              && not (mentions (let d = dictNew<string * int, bool> () in dictSet d (tv.Path, tv.Offset) true; d) body) ->
            List.fold2
                (fun acc p x ->
                    match p with
                    | PVar (v, sch) -> ELet (false, v, sch, x, acc)
                    | _ -> acc)
                body (List.rev ps) (List.rev xs)
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
        // the `$inline` marker is a hint, not an export — it must not pin
        // its function against the shim rewrite
        | DExport (v, nm) -> if nm <> "$inline" then dictSet pinned (v.Path, v.Offset) true
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
let private inlineThreshold =
    // FPP_INLINE_THRESHOLD overrides it for measurement; see the note on
    // `optimize` for why the default sat at 6 for so long.
    intOr 120 (System.Environment.GetEnvironmentVariable "FPP_INLINE_THRESHOLD")

/// Inline non-recursive functions at FULL-ARITY call sites.
///
/// Arguments are bound to `let`s rather than substituted into the body: F++
/// has mutable locals and assignment, so substituting an argument used twice
/// would evaluate it twice, and one used under a branch would move its
/// effects. Binding preserves both the order and the count.
/// Every variable this expression BINDS, as (path, offset) keys.
///
/// Needed because the copy keeps the original binders (see `expand`), and
/// monomorphized clones of one source function share their VarIds — inlining
/// `f<int>` into `f<float>` would then bind one key twice in a single body
/// and the two would share a register.
let rec private binderKeys (e : Expr) (acc : Vec<string * int>) : unit =
    let rec patKeys (p : Pat) =
        match p with
        | PVar (v, _) -> vecAdd acc (v.Path, v.Offset)
        | PAs (inner, v, _) -> vecAdd acc (v.Path, v.Offset); patKeys inner
        | PCtor (_, _, ps) | PTuple ps | PListLit ps | PArrLit (_, ps) | POr ps -> List.iter patKeys ps
        | PAnd (a, b) -> patKeys a; patKeys b
        | PCons (h, t) -> patKeys h; patKeys t
        | PWild | PLit _ | PTypeTest _ -> ()
    (match e with
     | ELam (ps, _) -> for v, _ in ps do vecAdd acc (v.Path, v.Offset)
     | ELet (_, v, _, _, _) -> vecAdd acc (v.Path, v.Offset)
     | EMatch (_, cs) -> for p, _, _ in cs do patKeys p
     | ETry (_, cs) -> for p, _, _ in cs do patKeys p
     | _ -> ())
    mapChildrenWith (fun c -> binderKeys c acc; c) e |> ignore

/// Is every binder in this body REPRESENTATION-MONOMORPHIC?
///
/// A generic local rides the uniform word; a concrete scalar rides raw. The
/// call boundary is where one becomes the other, and inlining removes the
/// boundary — so a body that binds `'a` locals and is handed concrete
/// arguments ends up storing a RAW int where a uniform word belongs. The
/// stepped-range builder does exactly that: `[ 3 .. -1 .. -3 ]` inlined put a
/// raw -2 in a list, and comparing the list read it as a pointer (wasm
/// address 0xfffffffe). Checking the SIGNATURE is not enough; the locals have
/// to be concrete too.
let rec private monoBinders (e : Expr) : bool =
    let schOk (sch : Scheme) = List.isEmpty (freeVars sch.Body)
    let rec patOk (p : Pat) =
        match p with
        | PVar (_, sch) -> schOk sch
        | PAs (inner, _, sch) -> schOk sch && patOk inner
        | PCtor (_, _, ps) | PTuple ps | PListLit ps | PArrLit (_, ps) | POr ps -> List.forall patOk ps
        | PAnd (a, b) -> patOk a && patOk b
        | PCons (h, t) -> patOk h && patOk t
        | PWild | PLit _ | PTypeTest _ -> true
    let here =
        match e with
        | ELam (ps, _) -> ps |> List.forall (fun (_, sch) -> schOk sch)
        | ELet (_, _, sch, _, _) -> schOk sch
        | EMatch (_, cs) -> cs |> List.forall (fun (p, _, _) -> patOk p)
        | ETry (_, cs) -> cs |> List.forall (fun (p, _, _) -> patOk p)
        | _ -> true
    if not here then false
    else
        let ok = vecNew<bool> ()
        vecAdd ok true
        mapChildrenWith (fun c -> (if not (monoBinders c) then vecSet ok 0 false); c) e |> ignore
        vecGet ok 0

/// A structural COPY: same binders, same offsets, brand-new nodes.
///
/// The inliner must not splice the callee's own `Expr` objects into the
/// caller. Several analyses key on node IDENTITY — the bounds proof marks a
/// safe access in a `refMap` keyed by the node, and the lambda lift names a
/// closure the same way — so a shared node carries one context's conclusion
/// into the other. Renaming the binders as well is wrong for a different
/// reason (see `expand`): inference keys decisions by the variable the SOURCE
/// bound. Copy the nodes, keep the names.
let rec private deepCopy (e : Expr) : Expr = mapChildrenWith deepCopy e

/// FPP_INLINE_MAX=<n>: inline only the first n sites, in a deterministic
/// order. A bisection handle — the pass is otherwise all-or-nothing, and
/// "which site breaks the self-host" is not answerable without one.
/// Read with `intOr`, not `Int32.TryParse`/`Int32.MaxValue`: the self-hosted
/// compiler has neither, and it did not fail on them — it read MaxValue as
/// ZERO, so stage-1 capped itself at "inline no sites" and produced a smaller
/// binary than stage-0 from the same source and the same flags. That is what
/// the byte mismatch was; the inliner itself was fine.
let private inlineMax = intOr 2147483647 (System.Environment.GetEnvironmentVariable "FPP_INLINE_MAX")

let inlineCalls (decls : Decl list) : Decl list =
    let counter = vecNew<int> ()
    vecAdd counter 0
    let sites = vecNew<int> ()
    vecAdd sites 0
    // FPP_INLINE_REPEAT=1: inline a callee MORE THAN ONCE per caller, with the
    // copy's binders renamed. Vector math calls the same three-line helper
    // several times in one function (Moeller-Trumbore: Dot four times, Cross
    // twice), and one copy per caller leaves every repeat as a call passing a
    // V3d by value and returning through sret.
    // ON by default; FPP_INLINE_REPEAT=0 turns it off. Worth, on V8's
    // optimising tier: Trafo3d.TransformPos 31 -> 13 ms. It costs box-extend
    // ~8% in code size with nothing to win back, which is the trade.
    //
    // It was ruled INCORRECT for a while on the strength of an out-parameter
    // test, and that verdict was wrong: the fault was the backend aliasing a
    // binder to a CELL variable's root slot (which holds the pointer to the
    // cell, not the value). Repeat inlining only moved a second copy onto the
    // cell receiver that exposed it. The alias guard checks both ends now.
    let repeatOn = System.Environment.GetEnvironmentVariable "FPP_INLINE_REPEAT" <> "0"
    // How deep to keep expanding INSIDE a body just inlined. ONE is the
    // measured sweet spot: ray/triangle goes 59 -> 20 ms at depth 1 and stays
    // at 20 for 2 and 3, while the compile cost keeps climbing (transform:
    // 40 s at depth 0, 53 s at 1, 122 s at 2) because the inliner revisits
    // exponentially more of each copy. The emitted code barely moves — 494 KB
    // to 493 KB — so this buys nothing past the first level.
    let inlineDepth = intOr 1 (System.Environment.GetEnvironmentVariable "FPP_INLINE_DEPTH")
    // A CALLER'S GROWTH BUDGET, in Core nodes. Every size test until now was
    // on the CALLEE, so nothing bounded how much one function could take on:
    // expanding recursively took the self-hosted compiler from 21 MB to 33 MB
    // of wasm, which then ran out of wasm32 address space. A hot loop needs a
    // few small bodies, not an unbounded supply.
    let inlineBudget = intOr 600 (System.Environment.GetEnvironmentVariable "FPP_INLINE_BUDGET")
    let freshCounter = vecNew<int> ()
    vecAdd freshCounter 0
    // candidates: non-recursive top-level functions with small bodies
    // (params, body, SIZE). The size is a property of the candidate, not of the
    // call site, but the budget guard below asked for it at every site and
    // `sizeOf` walks the whole body — with thousands of sites against hundreds
    // of candidates that is the pass re-measuring the same trees all day.
    let bodies = dictNew<string * int, (VarId * Scheme) list * Expr * int> ()
    let selfKeys = dictNew<string * int, bool> ()
    // `let inline` (the `$inline` DExport marker from Lower): the writer
    // asked for the body at every call site, so the SIZE threshold and the
    // caller's growth budget both step aside — that is what F# means by the
    // keyword once SRTP is out of scope. The soundness guards do NOT step
    // aside: a body that crosses an obj boundary, binds a type variable, or
    // is a stamped clone is wrong to copy no matter what the writer asked.
    let inlineMarked = dictNew<string * int, bool> ()
    for d in decls do
        match d with
        | DExport (v, "$inline") -> dictSet inlineMarked (v.Path, v.Offset) true
        | _ -> ()
    for d in decls do
        match d with
        | DLet (false, v, vsch, ELam (ps, body)) ->
            // ONLY a fully CONCRETE signature. A call is where the uniform-ABI
            // coercion happens: a generic parameter takes a boxed word, and a
            // raw scalar argument is boxed on the way in. The inliner replaces
            // the call with `let p = arg`, which performs no coercion at all —
            // so a generic parameter then reads a RAW scalar as a pointer.
            // `List.sort [ 3u; 4000000000u ]` faulted at wasm address
            // 0xee6b2800, which is 4000000000 itself. Monomorphization has
            // already made the struct math concrete, which is the code this
            // pass exists for; generic code keeps its call.
            let concrete (sch : Scheme) = List.isEmpty (freeVars sch.Body)
            // `obj` is the UNIFORM representation, and widening to it is a box
            // the call boundary performs — on the way in for a parameter, on
            // the way out for a result. `let returnsObjOf (v : int) : obj = v`
            // inlines to `let v = 5 in v`, which boxes nothing, and the
            // `:?> int` that follows then unboxes a value that was never a
            // box. Neither side may be obj.
            let rec resultOf (t : Type) (n : int) : Type =
                if n <= 0 then t
                else match prune t with
                     | TFun (_, r) -> resultOf r (n - 1)
                     | other -> other
            let isObj (t : Type) = match prune t with TCon ("obj", _) -> true | _ -> false
            let objFree (sch : Scheme) = not (isObj sch.Body)
            // never a COMPILER-SYNTHESIZED function ($ordD@…, $eqD@…, the
            // derived comparers and hashers). Those are stamped, and the
            // stamp is context the body only has by BEING its own function:
            // a `compare` over a payload with no bare type-var expression to
            // key on reads the enclosing function's witness. Inlined, that
            // witness is gone and the call falls back to the structural
            // walker, which reads a raw uint32 as a pointer.
            // A HOST EXTERN is intercepted by NAME in the backend
            // (`preludeSourceRaw` becomes the baked prelude constant,
            // `readTextRaw` and friends become WASI calls). Those
            // interceptions depend on where the call sits, so a copy can
            // escape them: inlining `preludeSource` into
            // `EmitProgramWasmLinearWith` is what made the self-hosted
            // compiler trap, and it is the ONLY site that did — found by
            // bisecting 2444 inline sites down to one.
            // ... and EVERY extern, not just the five host ones. An extern's
            // lowering depends on the CALL SITE too: a `[<JsImport>]` one is
            // emitted as a jsxl boundary import recognised at the call, so a
            // copy that lands somewhere else leaves the name unresolved. That
            // is what a second inlining round did to `gpuRun` — the webgpu
            // demo stubbed its initializer and only `--strict` said so.
            let hostExtern =
                [ "preludeSourceRaw"; "readTextRaw"; "existsRaw"
                  "listDirRaw"; "canonicalizeRaw" ]
                @ (decls |> List.choose (fun d ->
                    match d with
                    | DExtern (ev, _) -> Some ev.Name
                    | _ -> None))
            let rec touchesHost (x : Expr) : bool =
                match x with
                | EVar (hv, _) | EVarI (hv, _, _) -> List.contains hv.Name hostExtern
                | EUnknown n -> List.contains n hostExtern
                | _ ->
                    let hit = vecNew<bool> ()
                    vecAdd hit false
                    mapChildrenWith (fun c -> (if touchesHost c then vecSet hit 0 true); c) x |> ignore
                    vecGet hit 0
            let skipped =
                match System.Environment.GetEnvironmentVariable "FPP_INLINE_SKIP" with
                | null | "" -> false
                | s -> s.Split ',' |> Array.exists (fun x -> x = v.Name)
            if (sizeOf body <= inlineThreshold
                || (dictTryFind inlineMarked (v.Path, v.Offset)).IsSome)
               && not skipped
               && not (touchesHost body)
               // never a STAMPED clone either. `dictSlot$int$bool` is a
               // monomorphization, and a stamp is context the body has only by
               // being its own function — the backend threads hidden witness
               // arguments to it. Inlined, those are gone. The earlier rule
               // caught only names STARTING with `$` (the derived comparers);
               // a stamp puts its instantiation after the name.
               && not (v.Name.Contains "$")
               && ps |> List.forall (fun (_, sch) -> concrete sch && objFree sch)
               && monoBinders body
               && not (isObj (resultOf vsch.Body (List.length ps))) then
                let k = dictNew<string * int, bool> ()
                dictSet k (v.Path, v.Offset) true
                // a body that names itself is recursive whatever the
                // declaration says, and inlining it would not terminate
                if not (mentions k body) then
                    dictSet bodies (v.Path, v.Offset) (ps, body, sizeOf body)
                    dictSet selfKeys (v.Path, v.Offset) true
        | _ -> ()
    if dictPairs bodies |> List.isEmpty then decls
    else
    let expand (owner : string * int) (e : Expr) : Expr =
        // nodes of inlined material this caller has taken on
        let spent = vecNew<int> ()
        vecAdd spent 0
        // ONE inlining per callee per caller, and NO renaming of the binders.
        //
        // Renaming looks obviously right and is what broke the derived
        // comparers: a binder carries more here than its scheme, because
        // decisions taken during inference are keyed by the variable the
        // SOURCE bound, and a `$inline` VarId with a synthetic offset matches
        // none of them. `compare` on an option's `uint32` payload then fell
        // back to the structural walker, which read the raw 4000000000 as a
        // pointer. Keeping the original binders keeps every one of those
        // lookups — and the one thing renaming was for, the same key bound
        // twice in one function, cannot arise if a callee is inlined at most
        // once per caller.
        let used = dictNew<string * int, bool> ()
        // keys the CALLER already binds: a copy that re-binds one of them
        // would share its register with the caller's own variable
        let ownKeys = dictNew<string * int, bool> ()
        (let acc = vecNew<string * int> ()
         binderKeys e acc
         for k in vecToList acc do dictSet ownKeys k true)
        // RECURSIVE at the point of insertion. The calls that matter are the
        // ones that arrive WITH a copied body — `IntersectTriangle` brings
        // twelve Dot/Cross calls in with it, and a single sweep never looks
        // at them again. Expanding the copy immediately reaches exactly those,
        // where a second global round would re-sweep everything and grow the
        // whole program (the self-host then runs out of wasm32 address space).
        let rec go (depth : int) (e2 : Expr) : Expr =
            mapExpr
                (fun x ->
                    match x with
                    | EApp (EVar (f, _), args) when
                            (f.Path, f.Offset) <> owner
                            && (repeatOn || (dictTryFind used (f.Path, f.Offset)).IsNone) ->
                        (match dictTryFind bodies (f.Path, f.Offset) with
                         | Some (ps, body, bsize) when
                                vecGet sites 0 < inlineMax
                                && (vecGet spent 0 + bsize <= inlineBudget
                                    || (dictTryFind inlineMarked (f.Path, f.Offset)).IsSome)
                                && ps.Length = args.Length
                                && (repeatOn
                                    || (let acc = vecNew<string * int> ()
                                        binderKeys (ELam (ps, body)) acc
                                        vecToList acc
                                        |> List.forall (fun k ->
                                            (dictTryFind ownKeys k).IsNone))) ->
                             dictSet used (f.Path, f.Offset) true
                             vecSet spent 0 (vecGet spent 0 + bsize)
                             vecSet sites 0 (vecGet sites 0 + 1)
                             if System.Environment.GetEnvironmentVariable "FPP_INLINE_DBG" = "1" then
                                 eprintfn "SITE %d %s into %s:%d" (vecGet sites 0) f.Name (fst owner) (snd owner)
                             (let acc = vecNew<string * int> ()
                              binderKeys (ELam (ps, body)) acc
                              for k in vecToList acc do dictSet ownKeys k true)
                             (match (if repeatOn then freshenBinders freshCounter (ELam (ps, body))
                                     else deepCopy (ELam (ps, body))) with
                              | ELam (ps2, body2raw) ->
                                  // expand what came in with it
                                  let body2 =
                                      if depth < inlineDepth then go (depth + 1) body2raw
                                      else body2raw
                                  // innermost-last so the first argument binds
                                  // outermost, which is the evaluation order the
                                  // call site had
                                  List.fold2
                                      (fun acc (pv, psch) a -> ELet (false, pv, psch, a, acc))
                                      body2 (List.rev ps2) (List.rev args)
                              | _ -> x)
                         | _ -> x)
                    | other -> other)
                e2
        go 0 e
    // Inlining exposes call sites that were behind a call, so the pass is
    // swept more than once. Measured on the fpp.base benchmarks it SATURATES
    // at two rounds (ray-triangle 103 -> 97 ms, then 96 at four and eight) —
    // past that nothing new is reached and the extra code costs box-extend
    // 158 -> 164 ms. The wall is not the round count: a second `Dot` in the
    // same caller needs a renamed copy, which is `FPP_INLINE_REPEAT`.
    let mutable out = decls
    let mutable round = 0
    // FPP_INLINE_ROUNDS: inlining is a FIXPOINT, not a single pass. One round
    // inlines `IntersectTriangle` into its caller and stops, so the Dot/Cross
    // calls that came in WITH the copied body are never looked at — the
    // ray/triangle loop kept five calls to three-component vector helpers.
    let rounds = intOr 1 (System.Environment.GetEnvironmentVariable "FPP_INLINE_ROUNDS")
    while round < rounds do
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
/// LOOP-INVARIANT CODE MOTION.
///
/// A `let` inside a loop whose right-hand side depends on nothing the loop
/// changes computes the same value every iteration. Moeller-Trumbore is the
/// case that made this visible: `e1`, `e2`, `pv`, `det` and `inv` are built
/// from the triangle and the ray direction, none of which move, and the
/// ray/triangle benchmark recomputed all five two million times. Hoisting
/// them by hand took it from 98 ms to 44; clang's wasm does the same thing
/// and its inner loop holds 8 multiplies where the source has 15.
///
/// Only SPECULABLE right-hand sides move: evaluating one early must be
/// invisible. That rules out anything that can trap (integer division, an
/// array index and its bounds check), anything with an effect (an assignment,
/// a store, a call — a call could do either), and anything inside a nested
/// LAMBDA, whose body does not run here at all. Float arithmetic cannot trap,
/// so it travels freely.
///
/// This runs AFTER inlining on purpose: an un-inlined call hides its
/// arithmetic behind a name this pass must refuse to move, so the two passes
/// only pay off together.
let private nonTrappingOp (op : string) : bool =
    // an integer divide traps on zero; the float ones are IEEE and do not.
    // `?`-prefixed ops are prelude CALLS and `@` marks a class dispatch —
    // neither is ours to speculate.
    if op.StartsWith "?" || op.Contains "@" then false
    elif op.StartsWith "/" || op.StartsWith "%" then op.EndsWith "f" || op.EndsWith "s"
    else true

let rec private speculable (e : Expr) : bool =
    match e with
    | ELit _ -> true
    | EVar (_, _) | EVarI (_, _, _) -> true
    | EField (x, _, _) -> speculable x
    | ERecord (_, fs) -> fs |> List.forall (fun (_, x) -> speculable x)
    | ETuple xs -> xs |> List.forall speculable
    | EPrim (op, xs) -> nonTrappingOp op && (xs |> List.forall speculable)
    | EIf (a, b, c) -> speculable a && speculable b && speculable c
    | _ -> false

/// Does `e` READ memory that something else could write — a field, an array
/// element, an array length? Pure arithmetic over locals does not.
let rec private readsMemory (e : Expr) : bool =
    match e with
    | EField (_, _, _) | EIndex (_, _, _) | EArrayLen (_, _) | EArrayBytes (_, _) -> true
    | _ -> children e |> List.exists readsMemory

/// Does `e` WRITE memory, or call something that might? A call is opaque: it
/// can store through any reference it can reach.
let rec private writesMemory (e : Expr) : bool =
    match e with
    | EFieldSet (_, _, _, _) | EIndexSet (_, _, _, _) -> true
    // a builtin CONVERSION (`?float#i`, and every other name carrying the
    // result type before the '#') computes a scalar from a scalar and writes
    // nothing. Treating it as opaque cost the ray/triangle loop its hoists —
    // its only remaining call is the int->float on the loop counter.
    | EApp (EUnknown n, args) when n.Contains "#" -> args |> List.exists writesMemory
    | EApp (_, _) | EIfaceCall (_, _, _, _) -> true
    | _ -> children e |> List.exists writesMemory

/// every variable ASSIGNED anywhere in `e` — the loop's moving parts
let private assignedKeys (e : Expr) (acc : Dict<string * int, bool>) : unit =
    mapExpr
        (fun x ->
            (match x with
             | EAssign (v, _) -> dictSet acc (v.Path, v.Offset) true
             | _ -> ())
            x)
        e |> ignore

/// every variable READ in `e`
let private usedKeys (e : Expr) (acc : Vec<string * int>) : unit =
    mapExpr
        (fun x ->
            (match x with
             | EVar (v, _) | EVarI (v, _, _) -> vecAdd acc (v.Path, v.Offset)
             | _ -> ())
            x)
        e |> ignore

/// the hoistable lets of a loop body, OUTERMOST first, not descending into a
/// lambda (its body runs elsewhere, so nothing inside it is loop-invariant here)
let rec private collectHoists
        (moving : Dict<string * int, bool>) (bound : Dict<string * int, bool>)
        (loopWrites : bool) (e : Expr) (acc : Vec<VarId * Scheme * Expr>) : unit =
    match e with
    | ELam (_, _) -> ()
    | ELet (false, v, sch, rhs, body) ->
        // A read of MUTABLE memory may only move if the loop writes none and
        // calls nothing: `moving` tracks assignments to VARIABLES, so a field
        // or element the loop stores into looks invariant to it. That is what
        // broke 45 of the 100 adaptive tests — its graph nodes are mutated
        // through fields, and a hoisted read floated above the write.
        if speculable rhs
           && (not loopWrites || not (readsMemory rhs))
           && (dictTryFind moving (v.Path, v.Offset)).IsNone
           && (let us = vecNew<string * int> ()
               usedKeys rhs us
               vecToList us
               |> List.forall (fun k ->
                   (dictTryFind moving k).IsNone && (dictTryFind bound k).IsNone)) then
            vecAdd acc (v, sch, rhs)
        else
            // its own binder is loop-local from here on
            dictSet bound (v.Path, v.Offset) true
        collectHoists moving bound loopWrites rhs acc
        collectHoists moving bound loopWrites body acc
    | _ ->
        for c in children e do collectHoists moving bound loopWrites c acc

let private hoisted = vecNew<int> ()
let private hoistedInit = vecAdd hoisted 0

let hoistInvariants (decls : Decl list) : Decl list =
    let rewrite (e : Expr) : Expr =
        match e with
        | EWhile (cond, body) ->
            // what the loop CHANGES: anything it assigns
            let moving = dictNew<string * int, bool> ()
            assignedKeys cond moving
            assignedKeys body moving
            // and what it BINDS: those are not available before it runs
            let bound = dictNew<string * int, bool> ()
            (let bs = vecNew<string * int> ()
             binderKeys body bs
             for k in vecToList bs do dictSet bound k true)
            let hoists = vecNew<VarId * Scheme * Expr> ()
            // the FULL binder set, not an empty one: `collectHoists` only
            // tracks the binders of `let`s it walks past, so a PATTERN binder
            // (a match arm's variable) counted as outside the loop and an
            // expression reading one could be hoisted above the match that
            // binds it. Seeding with every binder in the body is the
            // conservative answer, and the fixpoint below recovers what it
            // costs: a binding hoisted this round is gone from the body next
            // round, so its dependents become invariant then.
            let loopWrites = writesMemory cond || writesMemory body
            collectHoists moving bound loopWrites body hoists
            // a hoist is only legal if the binder is not also bound elsewhere
            // in the loop under a different value
            let chosen =
                vecToList hoists
                |> List.filter (fun (v, _, _) ->
                    (dictTryFind moving (v.Path, v.Offset)).IsNone)
            if List.isEmpty chosen then e
            else
                vecSet hoisted 0 (vecGet hoisted 0 + List.length chosen)
                let drop = dictNew<string * int, bool> ()
                for v, _, _ in chosen do dictSet drop (v.Path, v.Offset) true
                // take the bindings OUT of the body, keeping their continuation
                let body2 =
                    mapExpr
                        (fun x ->
                            match x with
                            | ELet (false, v, _, _, k) when (dictTryFind drop (v.Path, v.Offset)).IsSome -> k
                            | other -> other)
                        body
                // ... and wrap the loop in them, outermost first
                List.foldBack
                    (fun (v, sch, rhs) acc -> ELet (false, v, sch, rhs, acc))
                    chosen (EWhile (cond, body2))
        | other -> other
    let pass (d : Decl) : Decl =
        match d with
        | DLet (rc, v, sch, body) -> DLet (rc, v, sch, mapExpr rewrite body)
        | other -> other
    // TO A FIXPOINT. One sweep only reaches the outermost layer: inlining
    // binds a callee's parameters to fresh loop-LOCAL lets, so `e1 = p1 - p0`
    // reads two names that are themselves invariant but not yet hoisted, and
    // the free-variable test rejects it. Hoisting those first makes `e1`
    // invariant on the next sweep. Bounded, because each sweep that changes
    // nothing stops it.
    let mutable out = decls
    let mutable go = true
    let mutable rounds = 0
    while go && rounds < 12 do
        vecSet hoisted 0 0
        out <- out |> List.map pass
        go <- vecGet hoisted 0 > 0
        rounds <- rounds + 1
    out

let optimize (decls : Decl list) : Decl list = decls |> uncurryTupleArgs |> fuseTuples

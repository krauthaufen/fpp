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
        | ETry (b, cs) -> ETry (r b, cs |> List.map (fun (p, g, x) -> p, Option.map r g, r x))
        | other -> other
    f e2

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
    | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) -> 1 + sizeOf a
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

/// `f (a, b)` must compile to a TWO-ARGUMENT CALL.
///
/// `let f (a, b) = ...` types as taking one tuple, and it still does — the
/// signature is not a lie and the tuple is still a reference value. But the
/// call site allocated a `$tup2`, wrote two fields, and the body immediately
/// matched it apart to read them back: allocate, write, read, discard, per
/// call. F# compiles these to multi-parameter functions and materializes the
/// tuple only where the function is used as a VALUE.
///
/// A function is rewritten only when EVERY occurrence of it in the program
/// is a direct call with a tuple literal of the right width. That keeps the
/// change local and total: there is no use left that expects the old shape,
/// so no wrapper has to reconstruct the tuple. A function used first-class
/// keeps the tupled signature untouched.
let uncurryTupleArgs (decls : Decl list) : Decl list =
    // candidates: fun (t) -> match t with (x, y, ...) -> body
    let cands = dictNew<string * int, (VarId * Scheme) list> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam ([ (pv, _) ], EMatch (EVar (sv, _), [ (PTuple ps, None, _) ]))) when
              (sv.Path, sv.Offset) = (pv.Path, pv.Offset)
              && ps.Length >= 2
              && ps |> List.forall (fun p -> match p with PVar _ -> true | _ -> false) ->
            let binders = ps |> List.map (fun p -> match p with PVar (bv, bs) -> bv, bs | _ -> pv, mono (TCon ("?", [])))
            dictSet cands (v.Path, v.Offset) binders
        | _ -> ()
    if dictPairs cands |> List.isEmpty then decls
    else
    // a candidate survives only if every mention of it is a direct call
    // carrying a tuple literal of exactly its width
    let seen = dictNew<string * int, int> ()
    let good = dictNew<string * int, int> ()
    let bump (t : Dict<string * int, int>) (k : string * int) =
        dictSet t k (match dictTryFind t k with Some n -> n + 1 | None -> 1)
    for d in decls do
        match d with
        | DLet (_, _, _, body) ->
            mapExpr
                (fun x ->
                    (match x with
                     | EVar (v, _) | EVarI (v, _, _) ->
                         if (dictTryFind cands (v.Path, v.Offset)).IsSome then bump seen (v.Path, v.Offset)
                     | _ -> ())
                    (match x with
                     | EApp (EVar (v, _), [ ETuple xs ]) ->
                         (match dictTryFind cands (v.Path, v.Offset) with
                          | Some bs when bs.Length = xs.Length -> bump good (v.Path, v.Offset)
                          | _ -> ())
                     | _ -> ())
                    x)
                body |> ignore
        | _ -> ()
    let eligible (k : string * int) =
        match dictTryFind cands k, dictTryFind seen k, dictTryFind good k with
        | Some _, Some n, Some g -> n = g
        | _ -> false
    // the SIGNATURE uncurries with the parameters: (a * b) -> r becomes
    // a -> b -> r, which is what the backend reads arity and kinds from
    let uncurryScheme (n : int) (sch : Scheme) : Scheme =
        match prune sch.Body with
        | TFun (TTuple ts, r) when ts.Length = n ->
            { sch with Body = List.foldBack (fun t acc -> TFun (t, acc)) ts r }
        | _ -> sch
    decls
    |> List.map (fun d ->
        let d2 =
            match d with
            | DLet (rc, v, sch, ELam ([ _ ], EMatch (_, [ (_, None, body) ]))) when eligible (v.Path, v.Offset) ->
                let bs = (dictTryFind cands (v.Path, v.Offset)).Value
                DLet (rc, v, uncurryScheme bs.Length sch, ELam (bs, body))
            | other -> other
        match d2 with
        | DLet (rc, v, sch, body) ->
            DLet (rc, v, sch,
                  mapExpr
                      (fun x ->
                          match x with
                          | EApp (EVar (f, fs), [ ETuple xs ]) when eligible (f.Path, f.Offset) ->
                              EApp (EVar (f, fs), xs)
                          | other -> other)
                      body)
        | other -> other)

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

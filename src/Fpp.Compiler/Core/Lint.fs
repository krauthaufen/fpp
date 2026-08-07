module Fpp.Core.Lint

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir

// The core linter: an independent bottom-up typecheck of core terms. It
// shares nothing with surface inference except the Type/Scheme machinery,
// so elaboration bugs show up as lint errors long before emission.

let lint (decls : Decl list) : string list =
    let st = TypeState()
    let errors = vecNew<string> ()
    // local binder types by (path, offset)
    let env = dictNew<string * int, Type> ()
    // top-level bindings already checked: their uses re-instantiate the
    // declared scheme instead of sharing one monotype, so a polymorphic
    // helper may be used at several types further down the file
    let generalized = dictNew<string * int, bool> ()

    let keyOf (v : VarId) = v.Path, v.Offset

    let fail (ctx : string) (msg : string) : unit =
        vecAdd errors (ctx + ": " + msg)

    let unifyC (ctx : string) (a : Type) (b : Type) : unit =
        // `obj` is the top type: anything widens to it, and `unbox` narrows
        // back out of it. The unifier has no notion of subtyping, so the one
        // place it matters is allowed here rather than weakening unification
        let isObj (t : Type) = match prune t with TCon ("obj", []) -> true | _ -> false
        if isObj a || isObj b then ()
        else
            match unify a b with
            | Some msg -> fail ctx msg
            | None -> ()

    /// Instantiate with ALL variables freshened — schemes come from another
    /// inference run and must not leak links into the lint world.
    let freshInstance (s : Scheme) : Type =
        let subst = dictNew<int, Type> ()
        let rec go (t : Type) : Type =
            match prune t with
            | TVar v ->
                (match dictTryFind subst v.Id with
                 | Some f -> f
                 | None ->
                     let f = st.Fresh ()
                     dictSet subst v.Id f
                     f)
            | TCon ("?", _) -> st.Fresh ()   // unknown-scheme placeholder
            | TCon (c, xs) -> TCon (c, List.map go xs)
            | TFun (a, b) -> TFun (go a, go b)
            | TTuple ts -> TTuple (List.map go ts)
            | TApp (h, xs) -> TApp (go h, List.map go xs)
        go s.Body

    let litType (l : Lit) : Type =
        match l with
        // the suffix decides: `0L` typed as int against an int64 operand
        // was a false mismatch on every `v = 0L` in the compiler
        | LInt t ->
            if t.EndsWith "L" then TCon ("int64", [])
            elif t.EndsWith "UL" || t.EndsWith "uL" then TCon ("uint64", [])
            elif t.EndsWith "us" || t.EndsWith "US" then TCon ("uint16", [])
            elif t.EndsWith "s" || t.EndsWith "S" then TCon ("int16", [])
            elif t.EndsWith "u" || t.EndsWith "U" then TCon ("uint32", [])
            else tInt
        | LFloat _ -> tFloat
        | LString _ -> tString
        | LChar _ -> tChar
        | LBool _ -> tBool
        | LNull -> st.Fresh ()   // null inhabits any reference type
        | LUnit -> tUnit

    let rec patType (p : Pat) : Type =
        match p with
        | PWild -> st.Fresh ()
        | PTypeTest tn -> TCon (tn, [])
        | PLit l -> litType l
        | PVar (v, _) ->
            let t = st.Fresh ()
            dictSet env (keyOf v) t
            t
        | PCtor (name, sch, args) ->
            let ctorTy = freshInstance sch
            let argTys = List.map patType args
            let res = st.Fresh ()
            let expected = List.foldBack (fun a acc -> TFun (a, acc)) argTys res
            (match args with
             | [] -> ctorTy   // nullary: the ctor type IS the result
             | _ ->
                 unifyC ("pattern " + name) ctorTy expected
                 res)
        | PTuple ps -> TTuple (List.map patType ps)
        | PCons (h, t) ->
            let ht = patType h
            let tt = patType t
            unifyC "cons pattern" tt (tList ht)
            tt
        | PListLit ps ->
            let elem = st.Fresh ()
            for p in ps do unifyC "list pattern" (patType p) elem
            tList elem
        | PAs (p, v, _) ->
            let t = patType p
            dictSet env (keyOf v) t
            t
        | POr ps ->
            let t = st.Fresh ()
            for p in ps do unifyC "or-pattern" (patType p) t
            t

    let primType (op : string) (args : Type list) (ctx : string) : Type =
        match op, args with
        | ("&&" | "||"), [ a; b ] ->
            unifyC ctx a tBool
            unifyC ctx b tBool
            tBool
        | ("=" | "<>" | "<" | ">" | "<=" | ">="), [ a; b ] ->
            unifyC ctx a b
            tBool
        | ("&&&" | "|||" | "^^^" | "<<<" | ">>>"), [ a; b ] ->
            unifyC ctx a tInt
            unifyC ctx b tInt
            tInt
        | "u~~~", [ a ] ->
            unifyC ctx a tInt
            tInt
        | ("+" | "-" | "*" | "/" | "%" | "**"), [ a; b ] ->
            unifyC ctx a b
            a
        | "::", [ h; t ] ->
            unifyC ctx t (tList h)
            t
        | "@", [ a; b ] ->
            unifyC ctx a b
            a
        | "unot", [ a ] ->
            unifyC ctx a tBool
            tBool
        | "u-", [ a ] -> a
        | ("<-" | ":="), _ -> tUnit
        | _ -> st.Fresh ()

    let rec exprType (e : Expr) : Type =
        match e with
        | ELit l -> litType l
        | EVarI (v, sch, _) -> exprType (EVar (v, sch))
        | EVar (v, sch) when (dictTryFind generalized (keyOf v)).IsSome -> freshInstance sch
        | EVar (v, sch) ->
            (match dictTryFind env (keyOf v) with
             | Some t -> t                     // local binder
             | None -> freshInstance sch)      // top-level / imported
        | EUnknown _ -> st.Fresh ()
        | ELam (ps, body) ->
            let paramTys =
                ps |> List.map (fun (v, _) ->
                    let t = st.Fresh ()
                    dictSet env (keyOf v) t
                    t)
            let b = exprType body
            List.foldBack (fun p acc -> TFun (p, acc)) paramTys b
        | EApp (f, args) ->
            let mutable ft = exprType f
            for a in args do
                let at = exprType a
                let res = st.Fresh ()
                // an argument may WIDEN to the parameter (a list where a seq
                // is declared, a subclass where a base is). The lint has no
                // inheritance tables, so it decomposes and skips the nominal
                // head where the names differ — argument-position soundness
                // stays with inference; the lint still checks everything else
                (match prune ft with
                 | TFun (pt, rt) ->
                     (match prune pt, prune at with
                      // a seq parameter accepts anything enumerable, and must
                      // not pull a still-free argument var to IEnumerable —
                      // the argument's real type may be the list that WIDENS
                      | TCon (("IEnumerable" | "seq"), _), _ -> ()
                      | TCon (pn, _), TCon (an, _) when pn <> an -> ()
                      | p, a2 -> unifyC "application" p a2)
                     unifyC "application" res rt
                 | _ -> unifyC "application" ft (TFun (at, res)))
                ft <- res
            ft
        | ELet (isRec, v, sch, rhs, body) ->
            let t = st.Fresh ()
            if isRec then dictSet env (keyOf v) t
            let rt = exprType rhs
            unifyC ("let " + v.Name) t rt
            dictSet env (keyOf v) rt
            // A POLYMORPHIC local is used at several types, and sharing one
            // monotype across its uses is the same monomorphization that was
            // fixed for top-level bindings: the first use would pin `'a` and
            // every other one would disagree. Its own scheme is the general
            // one, so uses re-instantiate it — recursive uses inside the RHS
            // stay monomorphic, exactly as above.
            if not (List.isEmpty sch.Quantified) then dictSet generalized (keyOf v) true
            exprType body
        | EIf (c, t, f) ->
            unifyC "if condition" (exprType c) tBool
            let tt = exprType t
            let ft = exprType f
            unifyC "if branches" tt ft
            tt
        | EMatch (s, cases) ->
            let sc = exprType s
            let result = st.Fresh ()
            for pat, guard, body in cases do
                unifyC "match pattern" (patType pat) sc
                (match guard with
                 | Some g -> unifyC "match guard" (exprType g) tBool
                 | None -> ())
                unifyC "match result" (exprType body) result
            result
        | ETuple xs -> TTuple (List.map exprType xs)
        | EListLit xs ->
            let elem = st.Fresh ()
            for x in xs do unifyC "list element" (exprType x) elem
            tList elem
        | ECtor (name, sch, args) ->
            let ctorTy = freshInstance sch
            (match args with
             | [] -> ctorTy
             | _ ->
                 let mutable ft = ctorTy
                 for a in args do
                     let at = exprType a
                     let res = st.Fresh ()
                     unifyC ("constructor " + name) ft (TFun (at, res))
                     ft <- res
                 ft)
        | ERecord (_, fields) ->
            for _, v in fields do exprType v |> ignore
            st.Fresh ()
        | ERecordExt (_, b, fields) ->
            exprType b |> ignore
            for _, v in fields do exprType v |> ignore
            st.Fresh ()
        | EField (r, _, _) ->
            exprType r |> ignore
            st.Fresh ()
        | EFieldSet (r, _, _, v) ->
            exprType r |> ignore
            exprType v |> ignore
            tUnit
        | EPrim (op, args) -> primType op (List.map exprType args) ("prim " + op)
        | ESeq xs ->
            let mutable last = tUnit
            for x in xs do last <- exprType x
            last
        | EWhile (c, b) ->
            unifyC "while condition" (exprType c) tBool
            exprType b |> ignore
            tUnit
        | EAssign (v, e) ->
            (match dictTryFind env (keyOf v) with
             | Some t -> unifyC ("assign " + v.Name) (exprType e) t
             | None -> exprType e |> ignore)
            tUnit
        | ETry (b, cs) ->
            let result = exprType b
            for pat, guard, body in cs do
                patType pat |> ignore
                (match guard with Some g -> unifyC "try guard" (exprType g) tBool | None -> ())
                unifyC "try result" (exprType body) result
            result
        | EArray (_, xs) ->
            let elem = st.Fresh ()
            for x in xs do unifyC "array element" (exprType x) elem
            TCon ("array", [ elem ])
        | EIndex (_, a, i) ->
            exprType a |> ignore
            unifyC "index" (exprType i) tInt
            st.Fresh ()
        | EIndexSet (_, a, i, v) ->
            exprType a |> ignore
            unifyC "index" (exprType i) tInt
            exprType v |> ignore
            tUnit
        | EArrayLen (_, a) ->
            exprType a |> ignore
            tInt
        | EArrayCreate (_, n, v) ->
            unifyC "create length" (exprType n) tInt
            exprType v |> ignore
            st.Fresh ()
        | EArrayPin (_, a) ->
            exprType a |> ignore
            tInt
        | EArrayUnpin (_, a) ->
            exprType a |> ignore
            tInt
        | EArrayBytes (_, a) ->
            exprType a |> ignore
            tInt
        | EIfaceCall (_, _, recv, args) ->
            exprType recv |> ignore
            for a in args do exprType a |> ignore
            st.Fresh ()
        | ECast (tn, e, _) ->
            exprType e |> ignore
            TCon (tn, [])
        | ETypeTest (_, e) ->
            exprType e |> ignore
            tBool

    for d in decls do
        match d with
        | DLet (isRec, v, sch, rhs) ->
            let declared = freshInstance sch
            if isRec then dictSet env (keyOf v) declared
            let rt = exprType rhs
            unifyC ("top-level " + v.Name) declared rt
            dictSet generalized (keyOf v) true
        | DExtern _ | DExport _ | DUnion _ | DRecord _ | DInterface _ | DClass _ | DEnum _ | DMembers _ | DBaseInst _ -> ()

    vecToList errors

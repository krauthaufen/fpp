module Fpp.Core.Lower

open Fpp.Prelude
open Fpp.Syntax
open Fpp.Analysis
open Fpp.Analysis.Types
open Fpp.Core.Ir

// Surface tree -> typed core, for the v1 emission subset: the functional
// language (let/rec, lambdas, application, match, if, tuples, lists,
// records, DUs, operators). Everything else lowers to EUnknown with a note
// — lossless in spirit: lowering never fails, it reports.

type private LetShape =
    | SimpleLet of bool * VarId * Scheme * Expr * Expr option
    | DestructureLet of Pat * Expr * Expr option

let lower (path : string) (root : GreenNode) (binder : Resolve.BindResult)
          (schemes : Dict<string, Scheme>) (opKinds : Dict<int, string>)
          (arrKinds : Dict<int, string>) (instSites : Dict<int, string list>)
          (memberSites : Dict<int, string>) : LowerResult =

    let notes = vecNew<int * string> ()
    let decls = vecNew<Decl> ()
    let mutable pendingStruct = false
    // offsets of top-level `let` bindings in this file — the only symbols
    // Link can clone, hence the only uses that carry instantiations
    let topLevelDefs = dictNew<int, bool> ()
    let rec collectTop (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            match n.NodeKind with
            | LetDecl ->
                (match n.Children
                       |> List.tryPick (fun c ->
                            match c with
                            | GNode p when p.NodeKind = IdentPat ->
                                Green.tokens (GNode p) |> List.tryFind (fun t -> t.Kind = Ident)
                            | _ -> None) with
                 | Some t -> dictSet topLevelDefs t.Offset true
                 | None -> ())
            | ModuleDef -> n.Children |> List.iter collectTop
            | _ -> ()
    root.Children |> List.iter collectTop
    let structNames = vecNew<string> ()

    let useDefs = dictNew<int, Resolve.Definition> ()
    for u in binder.Resolutions do dictSet useDefs u.UseOffset u.Def
    let defsAt = dictNew<int, Resolve.Definition> ()
    for d in binder.Definitions do dictSet defsAt d.Offset d
    // "TypeName.MemberName" -> the member's definition; a use site picks the
    // entry named by the receiver's inferred type (Infer.MemberSites)
    let memberIndex = dictNew<string, Resolve.Definition> ()
    for k, d in binder.Members do dictSet memberIndex k d

    // while lowering a class body: the receiver, and the class-level
    // bindings that became instance fields
    let mutable currentSelf : (VarId * Scheme) option = None
    let mutable currentClass = ""
    let fieldOfVar = dictNew<string * int, string> ()

    /// `C.Foo` where C names a type: a static member, so no receiver.
    let isStaticUse (n : GreenNode) : bool =
        match n.Children |> List.tryPick (fun c -> match c with GNode m -> Some m | _ -> None) with
        | Some head when head.NodeKind = IdentExpr ->
            (match head.Children |> List.tryPick (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None) with
             | Some t -> (dictTryFind useDefs t.Offset |> Option.map (fun d -> d.Kind = Resolve.DefType)) = Some true
             | None -> false)
        | _ -> false

    /// The member a dot-access binds to, if inference typed its receiver.
    let memberAt (t : Token) : (string * Resolve.Definition) option =
        match dictTryFind memberSites t.Offset with
        | Some owner ->
            (match dictTryFind memberIndex (owner + "." + t.Text) with
             | Some d -> Some (owner, d)
             | None -> None)
        | None -> None

    let schemeOf (d : Resolve.Definition) : Scheme =
        match dictTryFind schemes (d.Path + ":" + string d.Offset) with
        | Some s -> s
        | None -> mono (TCon ("?", []))

    let note (offset : int) (why : string) : Expr =
        vecAdd notes (offset, why)
        EUnknown why

    let nodesOf (n : GreenNode) = n.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)
    let tokensOf (n : GreenNode) = n.Children |> List.choose (fun c -> match c with GToken t -> Some t | _ -> None)
    let offsetOf (n : GreenNode) =
        match Green.tokens (GNode n) |> List.tryHead with
        | Some t -> t.Offset
        | None -> 0

    let isPatKind (k : NodeKind) =
        k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat
    let isTypeKind (k : NodeKind) =
        k = NamedType || k = VarType || k = AnonType || k = TupleType
        || k = FunType || k = AppType || k = PostfixType || k = ParenType
    let isExprish (k : NodeKind) = not (isPatKind k) && not (isTypeKind k) && k <> TyParams

    let litOf (t : Token) : Lit option =
        match t.Kind with
        | IntLit -> Some (LInt t.Text)
        | FloatLit -> Some (LFloat t.Text)
        | StringLit -> Some (LString t.Text)
        | CharLit -> Some (LChar t.Text)
        | Keyword when t.Text = "true" -> Some (LBool true)
        | Keyword when t.Text = "false" -> Some (LBool false)
        | _ -> None

    let varIdOf (d : Resolve.Definition) : VarId =
        { Path = d.Path; Offset = d.Offset; Name = d.Name }

    // ---- patterns ---------------------------------------------------------

    let rec lowerPat (n : GreenNode) : Pat =
        match n.NodeKind with
        | WildcardPat -> PWild
        | LiteralPat ->
            (match tokensOf n |> List.tryLast |> Option.bind litOf with
             | Some l -> PLit l
             | None -> PWild)
        | IdentPat ->
            (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
             | Some t ->
                 (match dictTryFind defsAt t.Offset with
                  | Some d -> PVar (varIdOf d, schemeOf d)
                  | None ->
                      // constructor reference
                      (match dictTryFind useDefs t.Offset with
                       | Some d -> PCtor (d.Name, schemeOf d, [])
                       | None -> PWild))
             | None -> PWild)
        | AppPat ->
            (match nodesOf n with
             | head :: args ->
                 let ctorName, ctorSch =
                     match tokensOf head |> List.tryHead |> Option.bind (fun t -> dictTryFind useDefs t.Offset) with
                     | Some d -> d.Name, schemeOf d
                     | None -> "?", mono (TCon ("?", []))
                 PCtor (ctorName, ctorSch, args |> List.filter (fun m -> isPatKind m.NodeKind) |> List.map lowerPat)
             | [] -> PWild)
        | TuplePat -> PTuple (nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) |> List.map lowerPat)
        | ConsPat ->
            (match nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) with
             | [ h; t ] -> PCons (lowerPat h, lowerPat t)
             | _ -> PWild)
        | ListPat -> PListLit (nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) |> List.map lowerPat)
        | ParenPat ->
            let hasBar = tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = "|")
            (match nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) with
             | [] -> PLit LUnit
             | [ one ] -> lowerPat one
             | many when hasBar -> POr (List.map lowerPat many)
             | many -> PTuple (List.map lowerPat many))
        | AsPat ->
            (match nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) with
             | [ inner; GNodePat ] ->
                 (match tokensOf GNodePat |> List.tryFind (fun t -> t.Kind = Ident) |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
                  | Some d -> PAs (lowerPat inner, varIdOf d, schemeOf d)
                  | None -> lowerPat inner)
             | [ inner ] -> lowerPat inner
             | _ -> PWild)
        | _ -> PWild

    // ---- expressions ------------------------------------------------------

    let paramBinds (pats : GreenNode list) : (VarId * Scheme) list * Pat list =
        // simple variable params become ELam binders; anything structured
        // becomes a synthetic match (v1: keep simple — represent structured
        // params as PVar-less lam over a fresh name is overkill; instead we
        // keep the pattern and let emission handle simple cases)
        let binds =
            pats
            |> List.map (fun p ->
                match lowerPat p with
                | PVar (v, s) -> Some (v, s), PVar (v, s)
                | PLit LUnit -> Some ({ Path = path; Offset = offsetOf p; Name = "_unit" }, mono tUnit), PLit LUnit
                | other -> None, other)
        if binds |> List.forall (fun (b, _) -> b.IsSome) then
            binds |> List.map (fun (b, _) -> b.Value), []
        else
            [], binds |> List.map snd

    let rec lowerExpr (g : Green) : Expr =
        match g with
        | GToken t ->
            (match litOf t with
             | Some l -> ELit l
             | None -> EUnknown t.Text)
        | GNode n ->
            match n.NodeKind with
            | LiteralExpr ->
                (match tokensOf n |> List.tryHead |> Option.bind litOf with
                 | Some l -> ELit l
                 | None ->
                     match tokensOf n |> List.tryHead with
                     | Some t when t.Text = "null" -> ELit LUnit
                     | _ -> note (offsetOf n) "literal")
            | IdentExpr ->
                (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
                 | Some t ->
                     (match dictTryFind useDefs t.Offset with
                      | Some d when d.Kind = Resolve.DefCase -> ECtor (d.Name, schemeOf d, [])
                      | Some d when (dictTryFind fieldOfVar (d.Path, d.Offset)).IsSome && currentSelf.IsSome ->
                          // a class-level binding read from inside a member:
                          // it lives on the instance, not in a local
                          let sv, ssch = currentSelf.Value
                          EField (EVar (sv, ssch), (dictTryFind fieldOfVar (d.Path, d.Offset)).Value, currentClass)
                      | Some d ->
                          (match dictTryFind instSites t.Offset with
                           | Some inst when
                                not (List.isEmpty inst)
                                && d.Path = path
                                && (dictTryFind topLevelDefs d.Offset).IsSome ->
                               EVarI (varIdOf d, schemeOf d, inst)
                           | _ -> EVar (varIdOf d, schemeOf d))
                      | None -> EUnknown t.Text)
                 | None -> note (offsetOf n) "type-variable expression")
            | AppExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | head :: args ->
                     let f = lowerExpr (GNode head)
                     let loweredArgs = args |> List.map (fun a -> lowerExpr (GNode a))
                     (match f, loweredArgs with
                      // `recv.M args`: the member access already applied the
                      // receiver, so fold the arguments into that same call
                      // instead of building a closure for the receiver
                      | EApp (EVar (mv, msch), [ recv ]), _ when
                            head.NodeKind = DotExpr
                            && (match Green.tokens (GNode head) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                                | Some t -> (memberAt t |> Option.map (fun (_, d) -> d.Offset = mv.Offset && d.Path = mv.Path)) = Some true
                                | None -> false) ->
                          EApp (EVar (mv, msch), recv :: loweredArgs)
                      | EVar (bv, _), [ pa ] when bv.Name = "pin" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          EArrayPin (nm, pa)
                      | EVar (bv, _), [ pa ] when bv.Name = "unpin" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          EArrayUnpin (nm, pa)
                      | EVar (bv, _), [ cn; cv ] when bv.Name = "create" && bv.Path = "(builtin)" ->
                          let nm =
                              match dictTryFind arrKinds (offsetOf n) with
                              | Some x -> x
                              | None -> ""
                          EArrayCreate (nm, cn, cv)
                      | EField (EUnknown "Array", "create", _), [ cn; cv ] ->
                          let nm =
                              match dictTryFind arrKinds (offsetOf n) with
                              | Some x -> x
                              | None -> ""
                          EArrayCreate (nm, cn, cv)
                      | ECtor (cn, cs, []), _ when not (List.isEmpty loweredArgs) -> ECtor (cn, cs, loweredArgs)
                      | _ -> EApp (f, loweredArgs))
                 | [] -> note (offsetOf n) "empty application")
            | BinaryExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind), tokensOf n with
                 | [ l; r ], [ op ] ->
                     (match op.Text with
                      | "<-" ->
                          (match lowerExpr (GNode l) with
                           | EVar (v, _) -> EAssign (v, lowerExpr (GNode r))
                           | EIndex (nm, a, i) -> EIndexSet (nm, a, i, lowerExpr (GNode r))
                           | EField (recv, fname, owner) -> EFieldSet (recv, fname, owner, lowerExpr (GNode r))
                           | _ -> note (offsetOf n) "assignment target")
                      | "|>" -> EApp (lowerExpr (GNode r), [ lowerExpr (GNode l) ])
                      | "<|" -> EApp (lowerExpr (GNode l), [ lowerExpr (GNode r) ])
                      | _ ->
                          // typed prims: inference resolved the operand kind
                          // (equality stays unsuffixed — structural $equal)
                          let suffixable =
                              List.contains op.Text [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">=" ]
                          let suffix =
                              if not suffixable then ""
                              else
                                  match dictTryFind opKinds op.Offset with
                                  | Some k -> k
                                  | None -> ""
                          EPrim (op.Text + suffix, [ lowerExpr (GNode l); lowerExpr (GNode r) ]))
                 | _ -> note (offsetOf n) "operator shape")
            | PrefixExpr ->
                (match tokensOf n |> List.tryHead, nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | Some op, [ a ] when op.Text = "-" || op.Text = "not" || op.Text = "~~~" ->
                     let suffix =
                         match dictTryFind opKinds op.Offset with
                         | Some k -> k
                         | None -> ""
                     EPrim ("u" + op.Text + suffix, [ lowerExpr (GNode a) ])
                 | Some op, [] when (litOf op).IsSome -> ELit (litOf op).Value
                 | _, [ a ] -> lowerExpr (GNode a)
                 | _ ->
                     // negative literal: [-; lit] as tokens
                     (match tokensOf n with
                      | [ m; l ] when m.Text = "-" && (litOf l).IsSome ->
                          (match litOf l with
                           | Some (LInt s) -> ELit (LInt ("-" + s))
                           | Some (LFloat s) -> ELit (LFloat ("-" + s))
                           | _ -> note (offsetOf n) "prefix")
                      | _ -> note (offsetOf n) "prefix"))
            | ParenExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | [] -> ELit LUnit
                 | [ one ] -> lowerExpr (GNode one)
                 | many -> ESeq (List.map (fun m -> lowerExpr (GNode m)) many))
            | TupleExpr -> ETuple (nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) |> List.map (fun m -> lowerExpr (GNode m)))
            | ListExpr ->
                let items = vecNew<Expr> ()
                let mutable comprehension = false
                let rec add (m : GreenNode) =
                    if m.NodeKind = BlockExpr then nodesOf m |> List.iter add
                    elif m.NodeKind = ForExpr || m.NodeKind = WhileExpr || m.NodeKind = LetDecl then comprehension <- true
                    elif isExprish m.NodeKind then vecAdd items (lowerExpr (GNode m))
                nodesOf n |> List.iter add
                if comprehension then note (offsetOf n) "list comprehension"
                else EListLit (vecToList items)
            | LambdaExpr ->
                let pats = nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind)
                let body =
                    nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                    |> List.map (fun m -> lowerExpr (GNode m))
                let bodyE = match List.tryLast body with Some b -> b | None -> ELit LUnit
                (match paramBinds pats with
                 | binds, [] -> ELam (binds, bodyE)
                 | _, structuredPats ->
                     // structured lambda params: match on a synthetic arg
                     let arg = { Path = path; Offset = offsetOf n; Name = "_arg" }
                     let sch = mono (TCon ("?", []))
                     (match structuredPats with
                      | [ p ] -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ p, None, bodyE ]))
                      | ps -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ PTuple ps, None, bodyE ]))))
            | IfExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | cond :: rest ->
                     let c = lowerExpr (GNode cond)
                     (match rest with
                      | [ t ] -> EIf (c, lowerExpr (GNode t), ELit LUnit)
                      | [ t; f ] -> EIf (c, lowerExpr (GNode t), lowerExpr (GNode f))
                      | _ -> note (offsetOf n) "if shape")
                 | [] -> note (offsetOf n) "if shape")
            | MatchExpr ->
                let scrut =
                    nodesOf n
                    |> List.tryFind (fun m -> m.NodeKind <> MatchClause && isExprish m.NodeKind)
                let cases =
                    nodesOf n
                    |> List.filter (fun m -> m.NodeKind = MatchClause)
                    |> List.map (fun cl ->
                        let pats = nodesOf cl |> List.filter (fun m -> isPatKind m.NodeKind)
                        let hasWhen = tokensOf cl |> List.exists (fun t -> t.Kind = Keyword && t.Text = "when")
                        let exprs = nodesOf cl |> List.filter (fun m -> isExprish m.NodeKind)
                        let guard, body =
                            match hasWhen, exprs with
                            | true, [ g; b ] -> Some (lowerExpr (GNode g)), lowerExpr (GNode b)
                            | _, es ->
                                (match List.tryLast es with
                                 | Some b -> None, lowerExpr (GNode b)
                                 | None -> None, ELit LUnit)
                        let pat =
                            match pats with
                            | [ p ] -> lowerPat p
                            | [] -> PWild
                            | ps -> POr (List.map lowerPat ps)   // bar-separated alternatives
                        pat, guard, body)
                (match scrut with
                 | Some s -> EMatch (lowerExpr (GNode s), cases)
                 | None -> note (offsetOf n) "match without scrutinee")
            | BlockExpr ->
                lowerBlock (nodesOf n)
            | LetDecl ->
                (match lowerLetParts n with
                 | Some (SimpleLet (isRec, v, sch, rhs, cont)) ->
                     ELet (isRec, v, sch, rhs, (match cont with Some c -> c | None -> ELit LUnit))
                 | Some (DestructureLet (pat, rhs, cont)) ->
                     EMatch (rhs, [ pat, None, (match cont with Some c -> c | None -> ELit LUnit) ])
                 | None -> note (offsetOf n) "let shape")
            | RecordExpr ->
                let fields =
                    nodesOf n
                    |> List.filter (fun m -> m.NodeKind = RecordExprField)
                    |> List.choose (fun f ->
                        let name = tokensOf f |> List.tryFind (fun t -> t.Kind = Ident)
                        let value = nodesOf f |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast
                        match name, value with
                        | Some t, Some v -> Some (t.Text, lowerExpr (GNode v))
                        | _ -> None)
                ERecord ("?", fields)   // type name filled by lint/emission from inference if needed
            | ArrayExpr ->
                let elemName =
                    match dictTryFind arrKinds (offsetOf n) with
                    | Some nm -> nm
                    | None -> ""
                EArray (elemName, nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) |> List.map (fun m -> lowerExpr (GNode m)))
            | DotExpr when (match nodesOf n with [ _; ix ] -> ix.NodeKind = ListExpr | _ -> false) ->
                // index access: a.[i]
                (match nodesOf n with
                 | [ lhs; ix ] ->
                     let idx =
                         nodesOf ix |> List.filter (fun m -> isExprish m.NodeKind)
                         |> List.map (fun m -> lowerExpr (GNode m))
                     let nm =
                         match dictTryFind arrKinds (offsetOf n) with
                         | Some x -> x
                         | None -> ""
                     (match idx with
                      | [ i ] -> EIndex (nm, lowerExpr (GNode lhs), i)
                      | _ -> note (offsetOf n) "index shape")
                 | _ -> note (offsetOf n) "index shape")
            | DotExpr when
                (Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                 |> Option.map (fun t -> t.Text) = Some "Length")
                && (dictTryFind arrKinds (offsetOf n)).IsSome ->
                (match nodesOf n |> List.tryHead with
                 | Some lhs -> EArrayLen ((dictTryFind arrKinds (offsetOf n)).Value, lowerExpr (GNode lhs))
                 | None -> note (offsetOf n) "length shape")
            | DotExpr when
                (match Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some t -> (memberAt t).IsSome
                 | None -> false) ->
                // member access: inference bound it to one type's member, and
                // that member is a top-level function taking the receiver
                let t = Green.tokens (GNode n) |> List.filter (fun x -> x.Kind = Ident) |> List.last
                let _, d = (memberAt t).Value
                let fn = EVar (varIdOf d, schemeOf d)
                if isStaticUse n then fn
                else
                    (match nodesOf n |> List.tryHead with
                     | Some lhs -> EApp (fn, [ lowerExpr (GNode lhs) ])
                     | None -> note (offsetOf n) "member access without a receiver")
            | DotExpr ->
                (match nodesOf n |> List.tryHead, Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some lhs, Some name ->
                     // qualified value (resolver linked it) or field access
                     (match dictTryFind useDefs name.Offset |> Option.filter (fun d -> d.Kind <> Resolve.DefMember) with
                      | Some d when d.Kind = Resolve.DefCase -> ECtor (d.Name, schemeOf d, [])
                      | Some d ->
                          (match dictTryFind instSites name.Offset with
                           | Some inst when
                                not (List.isEmpty inst)
                                && d.Path = path
                                && (dictTryFind topLevelDefs d.Offset).IsSome ->
                               EVarI (varIdOf d, schemeOf d, inst)
                           | _ -> EVar (varIdOf d, schemeOf d))
                      | None ->
                          let owner = match dictTryFind memberSites name.Offset with Some o -> o | None -> ""
                          EField (lowerExpr (GNode lhs), name.Text, owner))
                 | _ -> note (offsetOf n) "dot shape")
            | ForExpr ->
                // range-for: `for i in a .. b do body` — desugars to a while
                let pats = nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind)
                let exprs = nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                (match pats, exprs with
                 | [ ip ], [ range; body ] ->
                     (match lowerPat ip, lowerExpr (GNode range) with
                      | PVar (iv, isch), EPrim ("..", [ lo; hi ]) ->
                          let hiV = { Path = iv.Path; Offset = iv.Offset + 1000000; Name = "_hi" }
                          ELet (false, iv, isch, lo,
                            ELet (false, hiV, isch, hi,
                              EWhile (EPrim ("<=", [ EVar (iv, isch); EVar (hiV, isch) ]),
                                ESeq [ lowerExpr (GNode body)
                                       EAssign (iv, EPrim ("+", [ EVar (iv, isch); ELit (LInt "1") ])) ])))
                      | PVar (iv, isch), coll ->
                          // for x in arr do body  ==>  indexed while loop
                          let nm =
                              match dictTryFind arrKinds (offsetOf range) with
                              | Some x -> x
                              | None -> ""
                          if nm = "" then note (offsetOf n) "for-in (unknown element type)"
                          else
                              let av = { Path = iv.Path; Offset = iv.Offset + 2000000; Name = "_arr" }
                              let ix = { Path = iv.Path; Offset = iv.Offset + 3000000; Name = "_ix" }
                              let ish = mono (TCon ("int", []))
                              ELet (false, av, isch, coll,
                                ELet (false, ix, ish, ELit (LInt "0"),
                                  EWhile (EPrim ("<", [ EVar (ix, ish); EArrayLen (nm, EVar (av, isch)) ]),
                                    ELet (false, iv, isch, EIndex (nm, EVar (av, isch), EVar (ix, ish)),
                                      ESeq [ lowerExpr (GNode body)
                                             EAssign (ix, EPrim ("+", [ EVar (ix, ish); ELit (LInt "1") ])) ]))))
                      | _, _ -> note (offsetOf n) "for loop (non-range)")
                 | _ -> note (offsetOf n) "for loop shape")
            | WhileExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | [ c; b ] -> EWhile (lowerExpr (GNode c), lowerExpr (GNode b))
                 | _ -> note (offsetOf n) "while shape")
            | TryExpr ->
                let body =
                    nodesOf n
                    |> List.filter (fun m -> m.NodeKind <> MatchClause && isExprish m.NodeKind)
                    |> List.map (fun m -> lowerExpr (GNode m))
                let cases =
                    nodesOf n
                    |> List.filter (fun m -> m.NodeKind = MatchClause)
                    |> List.map (fun cl ->
                        let pats = nodesOf cl |> List.filter (fun m -> isPatKind m.NodeKind)
                        let hasWhen = tokensOf cl |> List.exists (fun t -> t.Kind = Keyword && t.Text = "when")
                        let exprs = nodesOf cl |> List.filter (fun m -> isExprish m.NodeKind)
                        let guard, cbody =
                            match hasWhen, exprs with
                            | true, [ g; b ] -> Some (lowerExpr (GNode g)), lowerExpr (GNode b)
                            | _, es ->
                                (match List.tryLast es with
                                 | Some b -> None, lowerExpr (GNode b)
                                 | None -> None, ELit LUnit)
                        let pat =
                            match pats with
                            | [ p ] -> lowerPat p
                            | [] -> PWild
                            | ps -> POr (List.map lowerPat ps)
                        pat, guard, cbody)
                (match List.tryLast body with
                 | Some b -> ETry (b, cases)
                 | None -> note (offsetOf n) "try shape")
            | BraceExpr -> note (offsetOf n) "computation/sequence body"
            | ErrorNode -> note (offsetOf n) "error node"
            | _ -> note (offsetOf n) ("node " + string n.NodeKind)

    and lowerBlock (items : GreenNode list) : Expr =
        match items with
        | [] -> ELit LUnit
        | [ last ] when last.NodeKind <> LetDecl -> lowerExpr (GNode last)
        | item :: rest ->
            if item.NodeKind = LetDecl then
                match lowerLetParts item with
                | Some (SimpleLet (isRec, v, sch, rhs, cont)) ->
                    let tail =
                        match cont, rest with
                        | Some c, [] -> c
                        | Some c, _ -> ESeq [ c; lowerBlock rest ]
                        | None, _ -> lowerBlock rest
                    ELet (isRec, v, sch, rhs, tail)
                | Some (DestructureLet (pat, rhs, cont)) ->
                    let tail =
                        match cont, rest with
                        | Some c, [] -> c
                        | Some c, _ -> ESeq [ c; lowerBlock rest ]
                        | None, _ -> lowerBlock rest
                    EMatch (rhs, [ pat, None, tail ])
                | None -> ESeq [ note (offsetOf item) "let shape"; lowerBlock rest ]
            else
                match rest with
                | [] -> lowerExpr (GNode item)
                | _ ->
                    match lowerBlock rest with
                    | ESeq tail -> ESeq (lowerExpr (GNode item) :: tail)
                    | other -> ESeq [ lowerExpr (GNode item); other ]

    /// Classify and lower a LetDecl node.
    and lowerLetParts (n : GreenNode) : LetShape option =
        let isRec = tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "rec")
        let hasIn = tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "in")
        let mutable seenEq = false
        let before = vecNew<Green> ()
        let after = vecNew<Green> ()
        for c in n.Children do
            match c with
            | GToken t when t.Kind = Operator && t.Text = "=" && not seenEq -> seenEq <- true
            | c -> vecAdd (if seenEq then after else before) c
        let pats =
            vecToList before
            |> List.choose (fun c -> match c with GNode p when isPatKind p.NodeKind -> Some p | _ -> None)
        let isDestructure =
            vecToList before |> List.exists (fun c -> match c with GToken t -> t.Kind = Comma | _ -> false)
        let bodyExprs =
            vecToList after
            |> List.choose (fun c -> match c with GNode m when isExprish m.NodeKind -> Some m | _ -> None)
        // `let x = e in cont`: the last expression is the continuation
        let rhsExprs, cont =
            if hasIn && bodyExprs.Length >= 2 then
                bodyExprs |> List.take (bodyExprs.Length - 1),
                Some (lowerExpr (GNode (List.last bodyExprs)))
            else bodyExprs, None
        if isDestructure then
            match pats with
            | [] -> None
            | ps -> Some (DestructureLet (PTuple (List.map lowerPat ps), lowerBlock rhsExprs, cont))
        else
        match pats with
        | namePat :: paramPats ->
            (match Green.tokens (GNode namePat) |> List.tryFind (fun t -> t.Kind = Ident) |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
             | Some d ->
                 let body = lowerBlock rhsExprs
                 let rhs =
                     if List.isEmpty paramPats then body
                     else
                         match paramBinds paramPats with
                         | binds, [] -> ELam (binds, body)
                         | _, structured ->
                             let arg = { Path = path; Offset = d.Offset; Name = "_arg" }
                             let sch = mono (TCon ("?", []))
                             (match structured with
                              | [ p ] -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ p, None, body ]))
                              | ps -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ PTuple ps, None, body ])))
                 Some (SimpleLet (isRec, varIdOf d, schemeOf d, rhs, cont))
             | None -> None)
        | [] -> None

    // ---- declarations -----------------------------------------------------

    let lowerTypeDecl (n : GreenNode) : unit =
        let name =
            match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
            | Some t -> t.Text
            | None -> "?"
        let tyParams =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = TyParams)
            |> List.collect (fun m -> Green.tokens (GNode m))
            |> List.filter (fun t -> t.Kind = Ident && t.Text <> "_")
            |> List.map (fun t -> t.Text)
        let cases =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = UnionCase)
            |> List.choose (fun c ->
                tokensOf c
                |> List.tryFind (fun t -> t.Kind = Ident)
                |> Option.map (fun t ->
                    let hasPayload = nodesOf c |> List.exists (fun x -> isTypeKind x.NodeKind)
                    t.Text, (if hasPayload then 1 else 0)))
        let fieldKind (f : GreenNode) : string =
            let tyName =
                nodesOf f
                |> List.tryFind (fun x -> isTypeKind x.NodeKind)
                |> Option.bind (fun tn -> Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast)
                |> Option.map (fun t -> t.Text)
            match tyName with
            | Some n when List.contains n (vecToList structNames) -> "S:" + n
            | Some "float" -> "f"
            | Some "float32" -> "s"
            | Some "int64" -> "l"
            | Some "int" | Some "bool" | Some "char" -> "i"
            | _ -> "r"
        let recordFields =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = RecordRepr)
            |> List.collect nodesOf
            |> List.filter (fun m -> m.NodeKind = RecordField)
            |> List.choose (fun f ->
                tokensOf f
                |> List.tryFind (fun t -> t.Kind = Ident)
                |> Option.map (fun t -> t.Text, fieldKind f))
        let memberNodes = nodesOf n |> List.filter (fun m -> m.NodeKind = MemberDecl)
        let ctorPat = nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind)
        let classLets = nodesOf n |> List.filter (fun m -> m.NodeKind = LetDecl)
        let doNodes = nodesOf n |> List.filter (fun m -> m.NodeKind = BlockExpr)
        let isAbstract (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "abstract")
        let isStaticM (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")
        // a type whose members are all abstract declares an interface: no
        // storage, no constructor — dispatch is a separate concern
        let isInterface =
            not (List.isEmpty memberNodes) && memberNodes |> List.forall isAbstract
        // a class is anything with instance storage or a constructor
        let isClass =
            not isInterface
            && List.isEmpty cases && List.isEmpty recordFields
            && (ctorPat.IsSome || not (List.isEmpty classLets) || not (List.isEmpty memberNodes))

        // ---- instance state --------------------------------------------
        // primary-constructor parameters and class-level `let`s are the
        // fields; both are just names in the body, so members reach them
        // through the receiver
        let ctorParamDefs =
            match ctorPat with
            | Some p ->
                Green.tokens (GNode p)
                |> List.filter (fun t -> t.Kind = Ident)
                |> List.choose (fun t -> dictTryFind defsAt t.Offset)
                |> List.filter (fun d -> d.Kind = Resolve.DefParam)
            | None -> []
        let classLetParts =
            classLets
            |> List.choose (fun l ->
                match lowerLetParts l with
                | Some (SimpleLet (isRec, v, sch, rhs, _)) -> Some (isRec, v, sch, rhs)
                | _ -> None)
        let instanceFields =
            (ctorParamDefs |> List.map (fun d -> varIdOf d, schemeOf d))
            @ (classLetParts |> List.map (fun (_, v, sch, _) -> v, sch))

        if isClass then
            for v, _ in instanceFields do dictSet fieldOfVar (v.Path, v.Offset) v.Name
            vecAdd decls (DRecord (name, tyParams, instanceFields |> List.map (fun (v, _) -> v.Name, "r"), false))

            // ---- the constructor ----------------------------------------
            match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
            | Some tyDef when ctorPat.IsSome ->
                let alloc = ERecord (name, instanceFields |> List.map (fun (v, sch) -> v.Name, EVar (v, sch)))
                // `do` bodies run before the instance exists, so they cannot
                // see `this` — F# allows only side effects there
                let withDo =
                    match doNodes with
                    | [] -> alloc
                    | ds -> ESeq ((ds |> List.map (fun d -> lowerExpr (GNode d))) @ [ alloc ])
                let body =
                    List.foldBack
                        (fun (isRec, v, sch, rhs) acc -> ELet (isRec, v, sch, rhs, acc))
                        classLetParts withDo
                let rhs =
                    match paramBinds [ ctorPat.Value ] with
                    | binds, [] -> ELam (binds, body)
                    | _, structured ->
                        let arg = { Path = path; Offset = tyDef.Offset; Name = "_arg" }
                        let sch = mono (TCon ("?", []))
                        (match structured with
                         | [ p ] -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ p, None, body ]))
                         | ps -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ PTuple ps, None, body ])))
                vecAdd decls (DLet (false, varIdOf tyDef, schemeOf tyDef, rhs))
            | _ -> ()

        // ---- members ----------------------------------------------------
        // every instance member lifts to a top-level function whose first
        // parameter is the receiver; its declared scheme already says so
        if not isInterface then
            currentClass <- name
            for m in memberNodes do
                if not (isAbstract m) then
                    let mutable seenEq = false
                    let idents = vecNew<Token> ()
                    let pats = vecNew<GreenNode> ()
                    let bodies = vecNew<Green> ()
                    for c in m.Children do
                        match c with
                        | GToken t when t.Kind = Operator && t.Text = "=" && not seenEq -> seenEq <- true
                        | GToken t when not seenEq && t.Kind = Ident -> vecAdd idents t
                        | GNode pn when not seenEq && isPatKind pn.NodeKind -> vecAdd pats pn
                        | GNode b when seenEq && isExprish b.NodeKind -> vecAdd bodies c
                        | _ -> ()
                    let selfTok, nameTok =
                        match vecToList idents with
                        | [ slf; nm ] -> Some slf, Some nm
                        | [ nm ] -> None, Some nm
                        | _ -> None, None
                    match nameTok |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
                    | Some d ->
                        let sch = schemeOf d
                        let selfSch =
                            match sch.Body with
                            | TFun (a, _) -> mono a
                            | _ -> mono (TCon (name, []))
                        let selfBind =
                            match selfTok |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
                            | Some sd -> varIdOf sd, selfSch
                            | None -> { Path = path; Offset = d.Offset + 800000; Name = "this" }, selfSch
                        if not (isStaticM m) then currentSelf <- Some selfBind
                        let body = lowerBlock (vecToList bodies |> List.choose (fun c -> match c with GNode x -> Some x | _ -> None))
                        currentSelf <- None
                        let ps = vecToList pats
                        let paramPart =
                            if List.isEmpty ps then Choice1Of2 []
                            else
                                match paramBinds ps with
                                | binds, [] -> Choice1Of2 binds
                                | _, structured -> Choice2Of2 structured
                        let inner =
                            match paramPart with
                            | Choice1Of2 binds -> binds, body
                            | Choice2Of2 structured ->
                                let arg = { Path = path; Offset = d.Offset + 700000; Name = "_arg" }
                                let asch = mono (TCon ("?", []))
                                (match structured with
                                 | [ pp ] -> [ arg, asch ], EMatch (EVar (arg, asch), [ pp, None, body ])
                                 | pps -> [ arg, asch ], EMatch (EVar (arg, asch), [ PTuple pps, None, body ]))
                        let binds, mbody = inner
                        let allBinds = if isStaticM m then binds else selfBind :: binds
                        vecAdd decls (DLet (false, varIdOf d, sch, ELam (allBinds, mbody)))
                    | None -> ()
            currentClass <- ""

        if not (List.isEmpty cases) then vecAdd decls (DUnion (name, tyParams, cases))
        elif not (List.isEmpty recordFields) then
            if pendingStruct then vecAdd structNames name
            vecAdd decls (DRecord (name, tyParams, recordFields, pendingStruct))
        if nodesOf n |> List.exists (fun m -> m.NodeKind = InterfaceImpl) then
            vecAdd notes ((match tokensOf n |> List.tryHead with Some t -> t.Offset | None -> 0), "interface implementation")
        if isInterface then
            vecAdd notes ((match tokensOf n |> List.tryHead with Some t -> t.Offset | None -> 0), "interface declaration")

    let rec lowerDecl (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            match n.NodeKind with
            | LetDecl when tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "extern") ->
                (match nodesOf n |> List.tryPick (fun m -> if m.NodeKind = IdentPat then tokensOf m |> List.tryFind (fun t -> t.Kind = Ident) else None) with
                 | Some t ->
                     (match dictTryFind defsAt t.Offset with
                      | Some d -> vecAdd decls (DExtern (varIdOf d, schemeOf d))
                      | None -> vecAdd notes (offsetOf n, "extern name unresolved"))
                 | None -> vecAdd notes (offsetOf n, "extern shape"))
            | LetDecl ->
                (match lowerLetParts n with
                 | Some (SimpleLet (isRec, v, sch, rhs, _)) -> vecAdd decls (DLet (isRec, v, sch, rhs))
                 | _ -> vecAdd notes (offsetOf n, "top-level let shape"))
            | TypeDecl ->
                lowerTypeDecl n
                pendingStruct <- false
            | ModuleDef -> nodesOf n |> List.iter (fun m -> lowerDecl (GNode m))
            | AttributeList ->
                if Green.tokens g |> List.exists (fun t -> t.Kind = Ident && t.Text = "Struct") then
                    pendingStruct <- true
            | ModuleHeader | OpenDecl -> ()
            | k when isExprish k ->
                vecAdd decls (DLet (false, { Path = path; Offset = offsetOf n; Name = "_it" }, mono tUnit, lowerExpr g))
            | _ -> vecAdd notes (offsetOf n, "declaration " + string n.NodeKind)

    for c in root.Children do lowerDecl c

    { Decls = vecToList decls
      Notes = vecToList notes }

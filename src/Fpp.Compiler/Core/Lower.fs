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
    /// `let struct(a, b) = e`: bind the struct once, then read its fields
    | StructLet of (VarId * Scheme) list * string * Expr * Expr option

let lower (path : string) (root : GreenNode) (binder : Resolve.BindResult)
          (schemes : Dict<string, Scheme>) (opKinds : Dict<int, string>)
          (arrKinds : Dict<int, string>) (instSites : Dict<int, string list>)
          (memberSites : Dict<int, string>) (fieldOwners : Dict<int, string>)
          (ifaces : Dict<string, (string * int) list>) : LowerResult =

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
            | TypeDecl ->
                // a class' constructor and members are top-level functions
                // too, so their uses may carry specialization demands
                (match n.Children |> List.tryPick (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None) with
                 | Some t -> dictSet topLevelDefs t.Offset true
                 | None -> ())
                let rec collectMembers (m : GreenNode) =
                    if m.NodeKind = MemberDecl then
                        match m.Children |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None) with
                        | [ _; nm ] | [ nm ] -> dictSet topLevelDefs nm.Offset true
                        | _ -> ()
                    elif m.NodeKind = InterfaceImpl then
                        m.Children |> List.iter (fun c -> match c with GNode x -> collectMembers x | _ -> ())
                n.Children |> List.iter (fun c -> match c with GNode m -> collectMembers m | _ -> ())
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
    let fieldOfVar = dictNew<string * int, string * string> ()

    /// The name of an interface written in a type position. For a generic
    /// application the head is the interface — the LAST identifier is a type
    /// argument (`IEqualityComparer<int>` is IEqualityComparer, not int).
    let rec ifaceNameOf (tn : GreenNode) : string option =
        let sub = tn.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)
        match sub |> List.tryFind (fun m -> m.NodeKind = NamedType || m.NodeKind = AppType) with
        | Some head when tn.NodeKind = AppType -> ifaceNameOf head
        | _ ->
            Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead
            |> Option.map (fun t -> t.Text)

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
        k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat || k = StructTuplePat
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat
    let isTypeKind (k : NodeKind) =
        k = NamedType || k = VarType || k = AnonType || k = TupleType || k = StructTupleType
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
                     | Some t when t.Text = "null" -> ELit LNull
                     | _ -> note (offsetOf n) "literal")
            | IdentExpr ->
                (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
                 | Some t ->
                     (match dictTryFind useDefs t.Offset with
                      | Some d when d.Kind = Resolve.DefCase -> ECtor (d.Name, schemeOf d, [])
                      | Some d when currentSelf.IsSome
                                    && (dictTryFind fieldOfVar (d.Path, d.Offset) |> Option.map fst) = Some currentClass ->
                          // a class-level binding (or an object expression's
                          // capture) read from inside a member: it lives on
                          // the instance, not in a local
                          let sv, ssch = currentSelf.Value
                          EField (EVar (sv, ssch), snd (dictTryFind fieldOfVar (d.Path, d.Offset)).Value, currentClass)
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
            | AppExpr when
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | head :: [ _ ] when head.NodeKind = IdentExpr ->
                     (match tokensOf head |> List.tryHead with
                      | Some t -> t.Text = "print" && (dictTryFind opKinds t.Offset) = Some "w"
                      | None -> false)
                 | _ -> false) ->
                // an unsigned value prints unsigned
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | [ _; a ] -> EApp (EUnknown "printu", [ lowerExpr (GNode a) ])
                 | _ -> note (offsetOf n) "print shape")
            | AppExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | head :: args ->
                     let f = lowerExpr (GNode head)
                     let loweredArgs = args |> List.map (fun a -> lowerExpr (GNode a))
                     (match f, loweredArgs with
                      // `recv.M args`: the member access already applied the
                      // receiver, so fold the arguments into that same call
                      // instead of building a closure for the receiver
                      | EIfaceCall (iface, mname, recv, []), _ when head.NodeKind = DotExpr ->
                          EIfaceCall (iface, mname, recv, loweredArgs)
                      | EApp (EVarI (mv, msch, minst), [ recv ]), _ when
                            head.NodeKind = DotExpr
                            && (match Green.tokens (GNode head) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                                | Some t -> (memberAt t |> Option.map (fun (_, d) -> d.Offset = mv.Offset && d.Path = mv.Path)) = Some true
                                | None -> false) ->
                          EApp (EVarI (mv, msch, minst), recv :: loweredArgs)
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
                          // `recv.P <- v` calls the property's setter
                          let propSetter =
                              if l.NodeKind <> DotExpr then None
                              else
                                  match Green.tokens (GNode l) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                                  | Some t ->
                                      (match dictTryFind memberSites t.Offset with
                                       | Some owner ->
                                           (match dictTryFind memberIndex (owner + ".set_" + t.Text) with
                                            | Some sd ->
                                                (match nodesOf l |> List.tryHead with
                                                 | Some recv -> Some (sd, lowerExpr (GNode recv))
                                                 | None -> None)
                                            | None -> None)
                                       | None -> None)
                                  | None -> None
                          (match propSetter with
                           | Some (sd, recv) ->
                               EApp (EVar (varIdOf sd, schemeOf sd), [ recv; lowerExpr (GNode r) ])
                           | None ->
                          match lowerExpr (GNode l) with
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
                              List.contains op.Text
                                  [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="
                                    // unsigned shifts/division differ from signed
                                    ">>>"; "&&&"; "|||"; "^^^"; "<<<" ]
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
                     let arg = { Path = path; Offset = offsetOf n + 600000; Name = "_arg" }
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
                 | Some (StructLet (bs, tn, rhs, cont)) ->
                     structLetExpr bs tn rhs (match cont with Some c -> c | None -> ELit LUnit)
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
                let owner =
                    match dictTryFind fieldOwners (offsetOf n) with
                    | Some o -> o
                    | None -> "?"
                ERecord (owner, fields)
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
            | ObjExpr ->
                // An object expression is an anonymous class. Whatever it
                // reads from the enclosing scope becomes instance state, so
                // the closure survives as fields rather than as an env.
                let toks = Green.tokens (GNode n)
                let lo = match toks |> List.tryHead with Some t -> t.Offset | None -> 0
                let hi = match toks |> List.tryLast with Some t -> t.Offset | None -> 0
                let synth = "obj@" + string lo
                let iface =
                    nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) |> Option.bind ifaceNameOf
                // captures: uses inside the expression bound to a LOCAL
                // definition outside it (top-level bindings need no capture)
                let captured = vecNew<VarId * Scheme> ()
                let seen = dictNew<string * int, bool> ()
                for t in toks do
                    if t.Kind = Ident then
                        match dictTryFind useDefs t.Offset with
                        | Some d when (d.Kind = Resolve.DefParam || d.Kind = Resolve.DefLet)
                                      && not (d.Offset >= lo && d.Offset <= hi)
                                      && not ((d.Path = path) && (dictTryFind topLevelDefs d.Offset).IsSome)
                                      && not (dictTryFind seen (d.Path, d.Offset)).IsSome ->
                            dictSet seen (d.Path, d.Offset) true
                            vecAdd captured (varIdOf d, schemeOf d)
                        | _ -> ()
                let caps = vecToList captured
                for v, _ in caps do dictSet fieldOfVar (v.Path, v.Offset) (synth, v.Name)
                vecAdd decls (DRecord (synth, [], caps |> List.map (fun (v, _) -> v.Name, "?"), false))
                let savedClass = currentClass
                currentClass <- synth
                let bound =
                    nodesOf n
                    |> List.filter (fun m -> m.NodeKind = MemberDecl)
                    |> List.choose (liftMemberIn synth)
                currentClass <- savedClass
                vecAdd decls
                    (DClass (synth, None, [],
                             match iface with Some i -> [ i, bound ] | None -> []))
                ERecord (synth, caps |> List.map (fun (v, sch) -> v.Name, EVar (v, sch)))
            // `downcast e` / `upcast e`: inference resolved the target from
            // the context and recorded it at the keyword
            | StructTupleExpr ->
                // `struct(a, b)` builds StructTuple2<'a,'b> — an ordinary
                // generic struct, so every struct rule applies unchanged
                let rec unwrap (m : GreenNode) =
                    if m.NodeKind = ParenExpr || m.NodeKind = TupleExpr then
                        nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) |> List.collect unwrap
                    else [ m ]
                let elems =
                    nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) |> List.collect unwrap
                let tn =
                    match dictTryFind fieldOwners (offsetOf n) with
                    | Some o -> o
                    | None -> "StructTuple" + string elems.Length
                ERecord (tn, elems |> List.mapi (fun i m -> "Item" + string (i + 1), lowerExpr (GNode m)))
            | CastExpr when tokensOf n |> List.exists (fun t -> t.Kind = Keyword && (t.Text = "downcast" || t.Text = "upcast")) ->
                let kw = tokensOf n |> List.find (fun t -> t.Kind = Keyword)
                (match nodesOf n |> List.tryFind (fun m -> isExprish m.NodeKind) with
                 | Some o ->
                     let inner = lowerExpr (GNode o)
                     if kw.Text = "upcast" then inner
                     else
                         (match dictTryFind memberSites kw.Offset with
                          | Some tn -> ECast (tn, inner, true)
                          | None -> note (offsetOf n) "downcast without a known target type")
                 | None -> note (offsetOf n) "cast shape")
            | CastExpr ->
                let operand = nodesOf n |> List.tryFind (fun m -> isExprish m.NodeKind)
                let target =
                    nodesOf n
                    |> List.tryFind (fun m -> isTypeKind m.NodeKind)
                    |> Option.bind (fun tn -> Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast)
                    |> Option.map (fun t -> t.Text)
                let isDown = tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = ":?>")
                let isTest = tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = ":?")
                (match operand, target with
                 | Some o, Some tn when isTest -> ETypeTest (tn, lowerExpr (GNode o))
                 | Some o, Some tn -> ECast (tn, lowerExpr (GNode o), isDown)
                 | _ -> note (offsetOf n) "cast shape")
            // dispatch through an interface: the receiver's concrete type is
            // unknown here, so the call goes through its vtable
            | DotExpr when
                (match Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some t ->
                     (match dictTryFind memberSites t.Offset with
                      | Some owner ->
                          (match dictTryFind ifaces owner with
                           | Some ms -> ms |> List.exists (fun (m, _) -> m = t.Text)
                           | None -> false)
                      | None -> false)
                 | None -> false) ->
                let t = Green.tokens (GNode n) |> List.filter (fun x -> x.Kind = Ident) |> List.last
                let iface = (dictTryFind memberSites t.Offset).Value
                (match nodesOf n |> List.tryHead with
                 | Some lhs -> EIfaceCall (iface, t.Text, lowerExpr (GNode lhs), [])
                 | None -> note (offsetOf n) "interface call without a receiver")
            | DotExpr when
                (match Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some t -> t.Text = "defaultof" && (dictTryFind useDefs t.Offset).IsNone
                 | None -> false) ->
                // the zero of whatever type the context resolved
                let t = Green.tokens (GNode n) |> List.filter (fun x -> x.Kind = Ident) |> List.last
                (match dictTryFind memberSites t.Offset with
                 | Some "int" | Some "bool" | Some "char" | Some "uint32" -> ELit (LInt "0")
                 | Some "int64" -> ELit (LInt "0L")
                 | Some "float" -> ELit (LFloat "0.0")
                 | Some "float32" -> ELit (LFloat "0.0f")
                 | _ -> ELit LNull)
            | DotExpr when
                (match Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some t -> (memberAt t).IsSome
                 | None -> false) ->
                // member access: inference bound it to one type's member, and
                // that member is a top-level function taking the receiver
                let t = Green.tokens (GNode n) |> List.filter (fun x -> x.Kind = Ident) |> List.last
                let _, d = (memberAt t).Value
                // a member of a generic class is a generic function: carry
                // the instantiation so the linker can stamp it
                let fn =
                    match dictTryFind instSites t.Offset with
                    | Some inst when
                         not (List.isEmpty inst)
                         && d.Path = path
                         && (dictTryFind topLevelDefs d.Offset).IsSome ->
                        EVarI (varIdOf d, schemeOf d, inst)
                    | _ -> EVar (varIdOf d, schemeOf d)
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
                          let owner =
                              match dictTryFind fieldOwners name.Offset with
                              | Some o -> o
                              | None -> (match dictTryFind memberSites name.Offset with Some o -> o | None -> "")
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
                | Some (StructLet (bs, tn, rhs, cont)) ->
                    let tail =
                        match cont, rest with
                        | Some c, [] -> c
                        | Some c, _ -> ESeq [ c; lowerBlock rest ]
                        | None, _ -> lowerBlock rest
                    structLetExpr bs tn rhs tail
                | None -> ESeq [ note (offsetOf item) "let shape"; lowerBlock rest ]
            else
                match rest with
                | [] -> lowerExpr (GNode item)
                | _ ->
                    match lowerBlock rest with
                    | ESeq tail -> ESeq (lowerExpr (GNode item) :: tail)
                    | other -> ESeq [ lowerExpr (GNode item); other ]

    /// Lift one member of class `name` to a top-level function taking the
    /// receiver first, and return the name it was declared under together
    /// with the function it became.
    and liftMemberIn (name : string) (m : GreenNode) : (string * VarId) option =
        let accessorNodes = nodesOf m |> List.filter (fun a -> a.NodeKind = AccessorDecl)
        if not (List.isEmpty accessorNodes) then liftAccessors name m accessorNodes
        else liftPlainMember name m

    /// `member x.P with get() = ... and set v = ...` becomes two functions:
    /// the property reader `P` and the writer `set_P`.
    and liftAccessors (name : string) (m : GreenNode) (accessorNodes : GreenNode list) : (string * VarId) option =
        let idents = tokensOf m |> List.filter (fun t -> t.Kind = Ident)
        let selfTok, nameTok =
            match idents with
            | [ slf; nm ] -> Some slf, Some nm
            | [ nm ] -> None, Some nm
            | _ -> None, None
        match nameTok |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
        | None -> None
        | Some propDef ->
            let mutable result = None
            for acc in accessorNodes do
                let kindTok = tokensOf acc |> List.tryFind (fun t -> t.Kind = Ident)
                let isSetter = (kindTok |> Option.map (fun t -> t.Text)) = Some "set"
                let defAt =
                    if isSetter then kindTok |> Option.bind (fun t -> dictTryFind defsAt t.Offset)
                    else Some propDef
                match defAt with
                | None -> ()
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
                    currentSelf <- Some selfBind
                    let mutable seenEq = false
                    let bodies = vecNew<GreenNode> ()
                    for c in acc.Children do
                        match c with
                        | GToken t when t.Kind = Operator && t.Text = "=" -> seenEq <- true
                        | GNode b when seenEq && isExprish b.NodeKind -> vecAdd bodies b
                        | _ -> ()
                    let body = lowerBlock (vecToList bodies)
                    currentSelf <- None
                    // a lone `()` marks a no-argument getter, not a parameter
                    let ps =
                        nodesOf acc
                        |> List.filter (fun p -> isPatKind p.NodeKind)
                        |> List.filter (fun p -> not (List.isEmpty (Green.tokens (GNode p) |> List.filter (fun t -> t.Kind = Ident))))
                    let binds =
                        match paramBinds ps with
                        | bs, [] -> bs
                        | _, _ -> []
                    vecAdd decls (DLet (false, varIdOf d, sch, ELam (selfBind :: binds, body)))
                    if not isSetter then result <- Some (d.Name, varIdOf d)
            result

    and liftPlainMember (name : string) (m : GreenNode) : (string * VarId) option =
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
            let isStaticM = tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")
            if not isStaticM then currentSelf <- Some selfBind
            let body = lowerBlock (vecToList bodies |> List.choose (fun c -> match c with GNode x -> Some x | _ -> None))
            currentSelf <- None
            let ps = vecToList pats
            let binds, mbody =
                if List.isEmpty ps then [], body
                else
                    match paramBinds ps with
                    | bs, [] -> bs, body
                    | _, structured ->
                        let arg = { Path = path; Offset = d.Offset + 700000; Name = "_arg" }
                        let asch = mono (TCon ("?", []))
                        (match structured with
                         | [ pp ] -> [ arg, asch ], EMatch (EVar (arg, asch), [ pp, None, body ])
                         | pps -> [ arg, asch ], EMatch (EVar (arg, asch), [ PTuple pps, None, body ]))
            let allBinds = if isStaticM then binds else selfBind :: binds
            vecAdd decls (DLet (false, varIdOf d, sch, ELam (allBinds, mbody)))
            Some (d.Name, varIdOf d)
        | None -> None

    /// Expand `let struct(a, b) = rhs in body` into a struct binding plus
    /// one field read per binder — the struct itself is an ordinary value.
    and structLetExpr (binders : (VarId * Scheme) list) (tn : string) (rhs : Expr) (body : Expr) : Expr =
        match binders with
        | [] -> body
        | (first, fsch) :: _ ->
            let tmp = { Path = first.Path; Offset = first.Offset + 4000000; Name = "_st" }
            let tsch = mono (TCon (tn, []))
            let inner =
                List.foldBack
                    (fun (i, (v, vsch)) acc ->
                        ELet (false, v, vsch, EField (EVar (tmp, tsch), "Item" + string (i + 1), tn), acc))
                    (binders |> List.mapi (fun i b -> i, b))
                    body
            ignore fsch
            ELet (false, tmp, tsch, rhs, inner)

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
        // `let struct(a, b) = rhs`
        match pats with
        | [ sp ] when sp.NodeKind = StructTuplePat ->
            let binders =
                Green.tokens (GNode sp)
                |> List.filter (fun t -> t.Kind = Ident)
                |> List.choose (fun t -> dictTryFind defsAt t.Offset)
                |> List.map (fun d -> varIdOf d, schemeOf d)
            if List.isEmpty binders then None
            else
                let tn =
                    match dictTryFind fieldOwners (offsetOf sp) with
                    | Some o -> o
                    | None -> "StructTuple" + string binders.Length
                Some (StructLet (binders, tn, lowerBlock rhsExprs, cont))
        | _ ->
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
                             let arg = { Path = path; Offset = d.Offset + 600000; Name = "_arg" }
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
        let caseNodes = nodesOf n |> List.filter (fun m -> m.NodeKind = UnionCase)
        let cases =
            caseNodes
            |> List.choose (fun c ->
                tokensOf c
                |> List.tryFind (fun t -> t.Kind = Ident)
                |> Option.map (fun t ->
                    let hasPayload = nodesOf c |> List.exists (fun x -> isTypeKind x.NodeKind)
                    t.Text, (if hasPayload then 1 else 0)))
        // `| Leaf = 0uy` on every case makes this an enum: the cases are
        // integer constants, not constructors
        let enumCases =
            caseNodes
            |> List.choose (fun c ->
                let nameTok = tokensOf c |> List.tryFind (fun t -> t.Kind = Ident)
                let valTok =
                    nodesOf c
                    |> List.filter (fun m -> m.NodeKind = LiteralExpr)
                    |> List.tryPick (fun m -> tokensOf m |> List.tryHead)
                match nameTok, valTok with
                | Some nt, Some vt ->
                    let digits = vt.Text |> String.filter (fun ch -> (ch >= '0' && ch <= '9') || ch = '-')
                    Some (nt.Text, (if digits = "" then 0 else int digits))
                | _ -> None)
        let isEnum = not (List.isEmpty caseNodes) && enumCases.Length = caseNodes.Length
        // A field records its TYPE, not a representation. Resolving a kind
        // here would freeze a `'a` field as boxed before anyone knows what
        // it is instantiated at; the backend derives the kind once the type
        // is concrete.
        let fieldKind (f : GreenNode) : string =
            let tyNode = nodesOf f |> List.tryFind (fun x -> isTypeKind x.NodeKind)
            match tyNode with
            | Some tn when tn.NodeKind = VarType ->
                (match Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some t -> "'" + t.Text
                 | None -> "?")
            | Some tn ->
                (match Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some t when List.contains t.Text tyParams -> "'" + t.Text
                 | Some t -> t.Text
                 | None -> "?")
            | None -> "?"
        let recordFields =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = RecordRepr)
            |> List.collect nodesOf
            |> List.filter (fun m -> m.NodeKind = RecordField)
            |> List.choose (fun f ->
                tokensOf f
                |> List.tryFind (fun t -> t.Kind = Ident)
                |> Option.map (fun t -> t.Text, fieldKind f))
        let allMemberNodes = nodesOf n |> List.filter (fun m -> m.NodeKind = MemberDecl)
        let isVal (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "val")
        let isNewCtor (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "new")
        // `val mutable X : T` declares STORAGE, not a member
        let valFields =
            allMemberNodes
            |> List.filter isVal
            |> List.choose (fun m ->
                match tokensOf m |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                | Some nameTok ->
                    let tyName =
                        match nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                        | Some tn when tn.NodeKind = VarType ->
                            (match Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                             | Some t -> "'" + t.Text
                             | None -> "?")
                        | Some tn ->
                            (match Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                             | Some t when List.contains t.Text tyParams -> "'" + t.Text
                             | Some t -> t.Text
                             | None -> "?")
                        | None -> "?"
                    Some (nameTok.Text, tyName)
                | None -> None)
        let newCtorNode = allMemberNodes |> List.tryFind isNewCtor
        let memberNodes = allMemberNodes |> List.filter (fun m -> not (isVal m) && not (isNewCtor m))
        let ctorPat = nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind)
        // `inherit Base(args)`: the base contributes the object's prefix
        let inheritNode = nodesOf n |> List.tryFind (fun m -> m.NodeKind = InheritDecl)
        let baseName =
            inheritNode
            |> Option.bind (fun i -> Green.tokens (GNode i) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead)
            |> Option.map (fun t -> t.Text)
        let baseCtorCall =
            match inheritNode, baseName with
            | Some i, Some bn ->
                let bt = (Green.tokens (GNode i) |> List.filter (fun t -> t.Kind = Ident) |> List.head)
                let bdef = dictTryFind useDefs bt.Offset
                let args =
                    nodesOf i
                    |> List.filter (fun m -> isExprish m.NodeKind)
                    |> List.map (fun m -> lowerExpr (GNode m))
                (match bdef with
                 | Some d -> Some (EApp (EVar (varIdOf d, schemeOf d), (if List.isEmpty args then [ ELit LUnit ] else args)))
                 | None -> Some (note (offsetOf i) ("unknown base class " + bn)))
            | _ -> None
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
            && List.isEmpty cases && List.isEmpty recordFields && List.isEmpty valFields
            && (ctorPat.IsSome || baseName.IsSome || not (List.isEmpty classLets) || not (List.isEmpty memberNodes))

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
        // A class-level `let` may shadow a constructor parameter of the same
        // name (`let mutable key = key`). That is ONE piece of state: keep
        // the shadowing binding, since it is what the members see.
        // A constructor parameter only becomes instance state if a member
        // reads it. One that merely feeds a `let`, a `do` or the base
        // constructor lives and dies inside the constructor.
        let rec memberIdents (m : GreenNode) : Token list =
            if m.NodeKind = MemberDecl then Green.tokens (GNode m) |> List.filter (fun t -> t.Kind = Ident)
            else nodesOf m |> List.collect memberIdents
        let readByMembers =
            nodesOf n
            |> List.collect memberIdents
            |> List.choose (fun t -> dictTryFind useDefs t.Offset)
            |> List.map (fun d -> d.Path, d.Offset)
        let ctorParamDefs =
            ctorParamDefs
            |> List.filter (fun d -> List.contains (d.Path, d.Offset) readByMembers)
        let allFields =
            (ctorParamDefs |> List.map (fun d -> varIdOf d, schemeOf d))
            @ (classLetParts |> List.map (fun (_, v, sch, _) -> v, sch))
        let instanceFields =
            allFields
            |> List.filter (fun (v, _) ->
                not (allFields |> List.exists (fun (w, _) -> w.Name = v.Name && w.Offset > v.Offset)))

        if not (List.isEmpty valFields) then
            // declared storage: the type IS these fields
            if pendingStruct then vecAdd structNames name
            vecAdd decls (DRecord (name, tyParams, valFields, pendingStruct))
            (match newCtorNode, tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
             | Some nc, Some tyDef ->
                 let ps = nodesOf nc |> List.filter (fun m -> isPatKind m.NodeKind)
                 let bodies =
                     nodesOf nc
                     |> List.filter (fun m -> isExprish m.NodeKind)
                 let body =
                     match lowerBlock bodies with
                     | ERecord (_, fs) -> ERecord (name, fs)
                     | other -> other
                 let rhs =
                     match paramBinds ps with
                     | binds, [] -> ELam (binds, body)
                     | _, structured ->
                         let arg = { Path = path; Offset = tyDef.Offset + 600000; Name = "_arg" }
                         let asch = mono (TCon ("?", []))
                         (match structured with
                          | [ p ] -> ELam ([ arg, asch ], EMatch (EVar (arg, asch), [ p, None, body ]))
                          | pps -> ELam ([ arg, asch ], EMatch (EVar (arg, asch), [ PTuple pps, None, body ])))
                 vecAdd decls (DLet (false, varIdOf tyDef, schemeOf tyDef, rhs))
             | _ -> ())
        if isClass then
            for v, _ in instanceFields do dictSet fieldOfVar (v.Path, v.Offset) (name, v.Name)
            vecAdd decls (DRecord (name, tyParams, instanceFields |> List.map (fun (v, _) -> v.Name, "?"), false))

            // ---- the constructor ----------------------------------------
            match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
            | Some tyDef when ctorPat.IsSome ->
                let ownFieldVals = instanceFields |> List.map (fun (v, sch) -> v.Name, EVar (v, sch))
                let alloc =
                    match baseCtorCall with
                    | Some bc -> ERecordExt (name, bc, ownFieldVals)
                    | None -> ERecord (name, ownFieldVals)
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
                        let arg = { Path = path; Offset = tyDef.Offset + 600000; Name = "_arg" }
                        let sch = mono (TCon ("?", []))
                        (match structured with
                         | [ p ] -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ p, None, body ]))
                         | ps -> ELam ([ arg, sch ], EMatch (EVar (arg, sch), [ PTuple ps, None, body ])))
                vecAdd decls (DLet (false, varIdOf tyDef, schemeOf tyDef, rhs))
            | _ -> ()

        // ---- members ----------------------------------------------------
        // every instance member lifts to a top-level function whose first
        // parameter is the receiver; its declared scheme already says so
        let implNodes =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = InterfaceImpl)
            |> List.map (fun i ->
                let iname =
                    nodesOf i |> List.tryFind (fun x -> isTypeKind x.NodeKind) |> Option.bind ifaceNameOf
                (match iname with Some x -> x | None -> "?"),
                nodesOf i |> List.filter (fun m -> m.NodeKind = MemberDecl))
        let implemented = vecNew<string * (string * VarId) list> ()
        let ownMembers = vecNew<string * VarId> ()

        let liftMember (m : GreenNode) = liftMemberIn name m
        if not isInterface then
            currentClass <- name
            for m in memberNodes do
                if not (isAbstract m) then
                    match liftMember m with
                    | Some entry -> vecAdd ownMembers entry
                    | None -> ()
            // explicit interface implementations: same lifting, but they are
            // reached only through the vtable, never by name on the class
            for iname, ms in implNodes do
                let bound = ms |> List.choose liftMember
                vecAdd implemented (iname, bound)
            currentClass <- ""
            if isClass then vecAdd decls (DClass (name, baseName, vecToList ownMembers, vecToList implemented))

        if isEnum then vecAdd decls (DEnum (name, enumCases))
        elif not (List.isEmpty cases) then vecAdd decls (DUnion (name, tyParams, cases))
        elif not (List.isEmpty recordFields) then
            if pendingStruct then vecAdd structNames name
            vecAdd decls (DRecord (name, tyParams, recordFields, pendingStruct))
        // Abstract members declare dispatch slots whether the type is a pure
        // interface or a base class with overridable methods.
        if isInterface || (memberNodes |> List.exists isAbstract) then
            vecAdd decls
                (DInterface (name,
                    memberNodes
                    |> List.filter isAbstract
                    |> List.choose (fun m ->
                        match tokensOf m |> List.filter (fun t -> t.Kind = Ident) with
                        | [ _; nm ] | [ nm ] ->
                            Some (nm.Text, nodesOf m |> List.filter (fun p -> isPatKind p.NodeKind) |> List.length)
                        | _ -> None)))

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

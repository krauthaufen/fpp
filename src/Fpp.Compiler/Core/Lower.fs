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
          (schemes : Dict<string, Scheme>) : LowerResult =

    let notes = vecNew<int * string> ()
    let decls = vecNew<Decl> ()

    let useDefs = dictNew<int, Resolve.Definition> ()
    for u in binder.Resolutions do dictSet useDefs u.UseOffset u.Def
    let defsAt = dictNew<int, Resolve.Definition> ()
    for d in binder.Definitions do dictSet defsAt d.Offset d

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
                      | Some d -> EVar (varIdOf d, schemeOf d)
                      | None -> EUnknown t.Text)
                 | None -> note (offsetOf n) "type-variable expression")
            | AppExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | head :: args ->
                     let f = lowerExpr (GNode head)
                     let loweredArgs = args |> List.map (fun a -> lowerExpr (GNode a))
                     (match f with
                      | ECtor (cn, cs, []) when not (List.isEmpty loweredArgs) -> ECtor (cn, cs, loweredArgs)
                      | _ -> EApp (f, loweredArgs))
                 | [] -> note (offsetOf n) "empty application")
            | BinaryExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind), tokensOf n with
                 | [ l; r ], [ op ] ->
                     (match op.Text with
                      | "|>" -> EApp (lowerExpr (GNode r), [ lowerExpr (GNode l) ])
                      | "<|" -> EApp (lowerExpr (GNode l), [ lowerExpr (GNode r) ])
                      | _ -> EPrim (op.Text, [ lowerExpr (GNode l); lowerExpr (GNode r) ]))
                 | _ -> note (offsetOf n) "operator shape")
            | PrefixExpr ->
                (match tokensOf n |> List.tryHead, nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | Some op, [ a ] when op.Text = "-" || op.Text = "not" -> EPrim ("u" + op.Text, [ lowerExpr (GNode a) ])
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
            | DotExpr ->
                (match nodesOf n |> List.tryHead, Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some lhs, Some name ->
                     // qualified value (resolver linked it) or field access
                     (match dictTryFind useDefs name.Offset with
                      | Some d when d.Kind = Resolve.DefCase -> ECtor (d.Name, schemeOf d, [])
                      | Some d -> EVar (varIdOf d, schemeOf d)
                      | None -> EField (lowerExpr (GNode lhs), name.Text))
                 | _ -> note (offsetOf n) "dot shape")
            | ForExpr -> note (offsetOf n) "for loop"
            | WhileExpr -> note (offsetOf n) "while loop"
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
        let recordFields =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = RecordRepr)
            |> List.collect nodesOf
            |> List.filter (fun m -> m.NodeKind = RecordField)
            |> List.choose (fun f -> tokensOf f |> List.tryFind (fun t -> t.Kind = Ident) |> Option.map (fun t -> t.Text))
        let hasMembers =
            nodesOf n |> List.exists (fun m -> m.NodeKind = MemberDecl || m.NodeKind = InterfaceImpl)
        if not (List.isEmpty cases) then vecAdd decls (DUnion (name, tyParams, cases))
        elif not (List.isEmpty recordFields) then vecAdd decls (DRecord (name, tyParams, recordFields))
        if hasMembers then
            vecAdd notes ((match tokensOf n |> List.tryHead with Some t -> t.Offset | None -> 0), "type members")

    let rec lowerDecl (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            match n.NodeKind with
            | LetDecl ->
                (match lowerLetParts n with
                 | Some (SimpleLet (isRec, v, sch, rhs, _)) -> vecAdd decls (DLet (isRec, v, sch, rhs))
                 | _ -> vecAdd notes (offsetOf n, "top-level let shape"))
            | TypeDecl -> lowerTypeDecl n
            | ModuleDef -> nodesOf n |> List.iter (fun m -> lowerDecl (GNode m))
            | ModuleHeader | OpenDecl | AttributeList -> ()
            | k when isExprish k ->
                vecAdd decls (DLet (false, { Path = path; Offset = offsetOf n; Name = "_it" }, mono tUnit, lowerExpr g))
            | _ -> vecAdd notes (offsetOf n, "declaration " + string n.NodeKind)

    for c in root.Children do lowerDecl c

    { Decls = vecToList decls
      Notes = vecToList notes }

module Fpp.Analysis.Resolve

open Fpp.Prelude
open Fpp.Syntax

// Name resolution, v0: a single environment-threading pass over the syntax
// tree. Produces a definition index and use->def resolutions for local names.
// Names that don't resolve (BCL calls, other files) are silently skipped —
// unresolved-name diagnostics wait until multi-file resolution and a stdlib
// exist. Sequential visibility like F#: a name is visible after its binding
// (before it only under `rec`).

type DefKind =
    | DefLet
    | DefParam
    | DefType
    | DefCase
    | DefField
    | DefModule
    | DefSelf
    | DefMember

type Definition =
    { Name : string
      Kind : DefKind
      Offset : int
      Length : int }

type Resolution =
    { UseOffset : int
      UseLength : int
      Def : Definition }

type BindResult =
    { Definitions : Definition list
      Resolutions : Resolution list }

let kindLabel (k : DefKind) : string =
    match k with
    | DefLet -> "let"
    | DefParam -> "parameter"
    | DefType -> "type"
    | DefCase -> "union case"
    | DefField -> "field"
    | DefModule -> "module"
    | DefSelf -> "self"
    | DefMember -> "member"

type private Env = Map<string, Definition>

let resolve (root : GreenNode) : BindResult =
    let defs = vecNew<Definition> ()
    let uses = vecNew<Resolution> ()

    let define (kind : DefKind) (t : Token) : Definition =
        let d = { Name = t.Text; Kind = kind; Offset = t.Offset; Length = strLen t.Text }
        vecAdd defs d
        d

    let record (t : Token) (d : Definition) : unit =
        vecAdd uses { UseOffset = t.Offset; UseLength = strLen t.Text; Def = d }

    let tryRecord (env : Env) (t : Token) : unit =
        match Map.tryFind t.Text env with
        | Some d -> record t d
        | None -> ()

    let firstIdentToken (children : Green list) : Token option =
        children
        |> List.tryPick (fun c ->
            match c with
            | GToken t when t.Kind = Ident -> Some t
            | _ -> None)

    let hasKwChild (kw : string) (children : Green list) : bool =
        children
        |> List.exists (fun c ->
            match c with
            | GToken t -> t.Kind = Keyword && t.Text = kw
            | _ -> false)

    let isPatKind (k : NodeKind) =
        k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat

    let isTypeKind (k : NodeKind) =
        k = NamedType || k = VarType || k = AnonType || k = TupleType
        || k = FunType || k = AppType || k = PostfixType || k = ParenType

    // ---- types ------------------------------------------------------------

    let rec walkType (env : Env) (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            match n.NodeKind with
            | NamedType ->
                (match n.Children with
                 | GToken t :: _ when t.Kind = Ident ->
                     (match Map.tryFind t.Text env with
                      | Some d when d.Kind = DefType -> record t d
                      | _ -> ())
                 | _ -> ())
            | VarType | AnonType -> ()
            | _ -> List.iter (walkType env) n.Children

    // ---- patterns ---------------------------------------------------------

    /// Bind the names of a pattern into the environment. Identifier patterns
    /// that resolve to a known union case are uses, not bindings.
    let rec bindPat (kind : DefKind) (env : Env) (g : Green) : Env =
        match g with
        | GToken _ -> env
        | GNode n ->
            match n.NodeKind with
            | IdentPat ->
                (match n.Children with
                 | GToken t :: rest when t.Kind = Ident ->
                     if not (List.isEmpty rest) then
                         // dotted constructor reference: resolve head only
                         tryRecord env t
                         env
                     else
                         match Map.tryFind t.Text env with
                         | Some d when d.Kind = DefCase ->
                             record t d
                             env
                         | _ ->
                             if t.Text = "_" then env
                             else
                                 let d = define kind t
                                 Map.add t.Text d env
                 | _ -> env)
            | WildcardPat | LiteralPat -> env
            | AppPat ->
                (match n.Children with
                 | head :: args ->
                     // the head is a constructor use
                     (match head with
                      | GNode hn when hn.NodeKind = IdentPat ->
                          (match hn.Children with
                           | GToken t :: _ when t.Kind = Ident -> tryRecord env t
                           | _ -> ())
                      | _ -> ())
                     List.fold (bindPat kind) env args
                 | [] -> env)
            | k when isTypeKind k ->
                walkType env g
                env
            | _ -> List.fold (bindPat kind) env n.Children

    // ---- expressions ------------------------------------------------------

    /// Walk an expression; returns the environment extended by any bindings
    /// this item introduces for its sequential successors (let in a block).
    let rec walkExpr (env : Env) (g : Green) : Env =
        match g with
        | GToken _ -> env
        | GNode n ->
            match n.NodeKind with
            | IdentExpr ->
                (match n.Children with
                 | [ GToken t ] when t.Kind = Ident -> tryRecord env t
                 | _ -> ())   // quote-ident (type variable): skip
                env
            | DotExpr ->
                // only the leftmost segment resolves locally
                (match n.Children with
                 | first :: _ -> walkExpr env first |> ignore
                 | [] -> ())
                env
            | LetDecl -> walkLet env n
            | LambdaExpr ->
                let pats = n.Children |> List.filter (fun c -> match c with GNode p -> isPatKind p.NodeKind | _ -> false)
                let inner = List.fold (bindPat DefParam) env pats
                for c in n.Children do
                    match c with
                    | GNode p when isPatKind p.NodeKind -> ()
                    | GToken _ -> ()
                    | body -> walkExpr inner body |> ignore
                env
            | MatchExpr ->
                for c in n.Children do
                    match c with
                    | GNode cl when cl.NodeKind = MatchClause ->
                        let pats = cl.Children |> List.filter (fun x -> match x with GNode p -> isPatKind p.NodeKind | _ -> false)
                        let inner = List.fold (bindPat DefParam) env pats
                        for x in cl.Children do
                            match x with
                            | GNode p when isPatKind p.NodeKind -> ()
                            | GToken _ -> ()
                            | other -> walkExpr inner other |> ignore
                    | GToken _ -> ()
                    | other -> walkExpr env other |> ignore
                env
            | ForExpr ->
                let pats = n.Children |> List.filter (fun c -> match c with GNode p -> isPatKind p.NodeKind | _ -> false)
                let inner = List.fold (bindPat DefParam) env pats
                for c in n.Children do
                    match c with
                    | GNode p when isPatKind p.NodeKind -> ()
                    | GToken _ -> ()
                    | other -> walkExpr inner other |> ignore
                env
            | BraceExpr -> env   // token soup — nothing structured to resolve
            | BlockExpr ->
                let mutable e = env
                for c in n.Children do e <- walkExpr e c
                env   // block-local bindings do not escape
            | k when isTypeKind k ->
                walkType env g
                env
            | _ ->
                let mutable e = env
                for c in n.Children do e <- walkExpr e c
                env

    // ---- declarations -----------------------------------------------------

    and walkLet (env : Env) (n : GreenNode) : Env =
        let isRec = hasKwChild "rec" n.Children
        // split children at the `=` token
        let mutable seenEq = false
        let before = vecNew<Green> ()
        let after = vecNew<Green> ()
        for c in n.Children do
            match c with
            | GToken t when t.Kind = Operator && t.Text = "=" && not seenEq ->
                seenEq <- true
            | c -> vecAdd (if seenEq then after else before) c
        let pats =
            vecToList before
            |> List.filter (fun c -> match c with GNode p -> isPatKind p.NodeKind | _ -> false)
        // ascription types before `=`
        for c in vecToList before do
            match c with
            | GNode p when isTypeKind p.NodeKind -> walkType env c
            | _ -> ()
        let isDestructure =
            vecToList before
            |> List.exists (fun c -> match c with GToken t -> t.Kind = Comma | _ -> false)
        if isDestructure then
            // `let a, b = ...` — every name binds into the outer scope
            let envAll = List.fold (bindPat DefLet) env pats
            for c in vecToList after do
                walkExpr env c |> ignore
            envAll
        else
        match pats with
        | [] -> env
        | namePat :: paramPats ->
            let envWithName = bindPat DefLet env namePat
            let bodyBase = if isRec then envWithName else env
            let bodyEnv = List.fold (bindPat DefParam) bodyBase paramPats
            for c in vecToList after do
                walkExpr bodyEnv c |> ignore
            envWithName

    and walkMember (env : Env) (n : GreenNode) : unit =
        // [modifiers] [self .] name [typarams] params [: type] [= body]
        let mutable seenEq = false
        let idents = vecNew<Token> ()
        let pats = vecNew<Green> ()
        let body = vecNew<Green> ()
        for c in n.Children do
            match c with
            | GToken t when t.Kind = Operator && t.Text = "=" && not seenEq -> seenEq <- true
            | c when seenEq -> vecAdd body c
            | GToken t when t.Kind = Ident -> vecAdd idents t
            | GNode p when isPatKind p.NodeKind -> vecAdd pats c
            | GNode p when isTypeKind p.NodeKind -> walkType env c
            | _ -> ()
        let mutable inner = env
        match vecToList idents with
        | [ self; name ] ->
            if self.Text <> "_" then
                let d = define DefSelf self
                inner <- Map.add self.Text d inner
            define DefMember name |> ignore
        | [ name ] -> define DefMember name |> ignore
        | _ -> ()
        for p in vecToList pats do inner <- bindPat DefParam inner p
        for c in vecToList body do walkExpr inner c |> ignore

    and walkTypeDecl (env : Env) (n : GreenNode) : Env =
        let nameTok = firstIdentToken n.Children
        let mutable outer = env
        match nameTok with
        | Some t ->
            let d = define DefType t
            outer <- Map.add t.Text d outer
        | None -> ()
        // union cases and record fields extend the outer environment
        for c in n.Children do
            match c with
            | GNode u when u.NodeKind = UnionCase ->
                (match firstIdentToken u.Children with
                 | Some t ->
                     let d = define DefCase t
                     outer <- Map.add t.Text d outer
                 | None -> ())
                for x in u.Children do
                    match x with
                    | GNode ty when isTypeKind ty.NodeKind -> walkType outer x
                    | _ -> ()
            | GNode r when r.NodeKind = RecordRepr ->
                for f in r.Children do
                    match f with
                    | GNode fd when fd.NodeKind = RecordField ->
                        (match firstIdentToken fd.Children with
                         | Some t -> define DefField t |> ignore
                         | None -> ())
                        for x in fd.Children do
                            match x with
                            | GNode ty when isTypeKind ty.NodeKind -> walkType outer x
                            | _ -> ()
                    | _ -> ()
            | _ -> ()
        // class body: ctor params + lets visible in members
        let mutable inner = outer
        for c in n.Children do
            match c with
            | GNode p when isPatKind p.NodeKind ->
                inner <- bindPat DefParam inner c   // primary-ctor parameters
            | GNode m when m.NodeKind = MemberDecl -> walkMember inner m
            | GNode i when i.NodeKind = InterfaceImpl ->
                for x in i.Children do
                    match x with
                    | GNode m when m.NodeKind = MemberDecl -> walkMember inner m
                    | GNode ty when isTypeKind ty.NodeKind -> walkType inner x
                    | _ -> ()
            | GNode l when l.NodeKind = LetDecl -> inner <- walkLet inner l
            | GNode b when b.NodeKind = BlockExpr -> walkExpr inner c |> ignore
            | GNode ty when isTypeKind ty.NodeKind -> walkType outer c
            | _ -> ()
        outer

    and walkDecl (env : Env) (g : Green) : Env =
        match g with
        | GToken _ -> env
        | GNode n ->
            match n.NodeKind with
            | LetDecl -> walkLet env n
            | TypeDecl -> walkTypeDecl env n
            | ModuleDef ->
                let mutable outer = env
                (match firstIdentToken n.Children with
                 | Some t ->
                     let d = define DefModule t
                     outer <- Map.add t.Text d outer
                 | None -> ())
                let mutable inner = outer
                for c in n.Children do
                    match c with
                    | GNode _ -> inner <- walkDecl inner c
                    | GToken _ -> ()
                outer
            | ModuleHeader ->
                (match firstIdentToken n.Children with
                 | Some t -> define DefModule t |> ignore
                 | None -> ())
                env
            | OpenDecl | AttributeList | TyParams -> env
            | _ -> walkExpr env g |> ignore; env

    let mutable env : Env = Map.empty
    for c in root.Children do
        env <- walkDecl env c

    { Definitions = vecToList defs
      Resolutions = vecToList uses }

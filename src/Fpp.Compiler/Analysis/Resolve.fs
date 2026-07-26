module Fpp.Analysis.Resolve

open Fpp.Prelude
open Fpp.Syntax

// Name resolution, v1: environment-threading pass with module paths, exports
// and imports. Local scoping is the same as v0 (sequential visibility, rec,
// shadowing). New: every top-level definition is exported under its full
// dotted module path; a file resolves against the exports of the files
// before it in the project (imports), consulting `open`ed prefixes and its
// own module path. Unresolved names are still silently skipped.

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
      /// file (workspace path/uri) this definition lives in
      Path : string
      Offset : int
      Length : int }

type Resolution =
    { UseOffset : int
      UseLength : int
      Def : Definition }

type BindResult =
    { Definitions : Definition list
      Resolutions : Resolution list
      /// full dotted path -> definition, for later files to import
      Exports : (string * Definition) list
      /// "TypeName.MemberName" -> the member's definition. Member names are
      /// NOT globally unique, so a use site is bound by the receiver's
      /// inferred type (see Infer.MemberSites), not by name alone.
      Members : (string * Definition) list }

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

let resolve (path : string) (imports : Dict<string, Definition>) (root : GreenNode) : BindResult =
    let defs = vecNew<Definition> ()
    let uses = vecNew<Resolution> ()
    let exports = vecNew<string * Definition> ()
    let ownExports = dictNew<string, Definition> ()
    let opens = vecNew<string> ()
    // "TypeName.MemberName" -> def, and bare name -> every def with that
    // name (a use is disambiguated by the receiver type during inference)
    let memberDefs = dictNew<string, Definition> ()
    let membersByName = dictNew<string, Definition list> ()
    let mutable modulePath = ""

    let define (kind : DefKind) (t : Token) : Definition =
        let d = { Name = t.Text; Kind = kind; Path = path; Offset = t.Offset; Length = strLen t.Text }
        vecAdd defs d
        d

    let record (t : Token) (d : Definition) : unit =
        vecAdd uses { UseOffset = t.Offset; UseLength = strLen t.Text; Def = d }

    let exportDef (d : Definition) : unit =
        let full = if modulePath = "" then d.Name else modulePath + "." + d.Name
        vecAdd exports (full, d)
        dictSet ownExports full d

    /// Bases to try when qualifying a name. F# shadowing: the LAST `open`
    /// wins among competing candidates, so opens are consulted in reverse
    /// declaration order, before the enclosing module path and its prefixes.
    let bases () : string list =
        let rec prefixes (p : string) : string list =
            if p = "" then [ "" ]
            else
                let i = p.LastIndexOf '.'
                if i < 0 then [ p; "" ] else p :: prefixes (substr p 0 i)
        List.rev (vecToList opens) @ prefixes modulePath @ [ "" ]

    let findQualified (dotted : string) : Definition option =
        bases ()
        |> List.tryPick (fun b ->
            let full = if b = "" then dotted else b + "." + dotted
            match dictTryFind ownExports full with
            | Some d -> Some d
            | None -> dictTryFind imports full)

    /// Local environment first, then opened/imported modules.
    let lookupValue (env : Env) (name : string) : Definition option =
        match Map.tryFind name env with
        | Some d -> Some d
        | None -> findQualified name

    let tryRecord (env : Env) (t : Token) : unit =
        match lookupValue env t.Text with
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
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat

    let isTypeKind (k : NodeKind) =
        k = NamedType || k = VarType || k = AnonType || k = TupleType
        || k = FunType || k = AppType || k = PostfixType || k = ParenType

    /// Marks the boundary between top-level walking (defs are exported) and
    /// walking inside binding bodies (defs are local).
    let mutable atExportLevel = true

    /// Run f with export-level off, restoring afterwards.
    let inline local (f : unit -> 'a) : 'a =
        let saved = atExportLevel
        atExportLevel <- false
        let r = f ()
        atExportLevel <- saved
        r

    // ---- types ------------------------------------------------------------

    let rec walkType (env : Env) (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            match n.NodeKind with
            | NamedType ->
                let idents =
                    n.Children |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
                (match idents with
                 | [ t ] ->
                     (match lookupValue env t.Text with
                      | Some d when d.Kind = DefType -> record t d
                      | _ -> ())
                 | many when not (List.isEmpty many) ->
                     let dotted = many |> List.map (fun t -> t.Text) |> String.concat "."
                     (match findQualified dotted with
                      | Some d when d.Kind = DefType -> record (List.last many) d
                      | _ -> ())
                 | _ -> ())
            | VarType | AnonType -> ()
            | _ -> List.iter (walkType env) n.Children

    // ---- patterns ---------------------------------------------------------

    let rec bindPat (kind : DefKind) (env : Env) (g : Green) : Env =
        match g with
        | GToken _ -> env
        | GNode n ->
            match n.NodeKind with
            | IdentPat ->
                (match n.Children with
                 | GToken t :: rest when t.Kind = Ident ->
                     if not (List.isEmpty rest) then
                         tryRecord env t
                         env
                     else
                         match lookupValue env t.Text with
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

    /// Flatten a pure identifier spine `a.b.c`; None if any segment is not a
    /// plain identifier.
    let rec flattenSpine (g : Green) : Token list option =
        match g with
        | GNode n when n.NodeKind = IdentExpr ->
            (match n.Children with
             | [ GToken t ] when t.Kind = Ident -> Some [ t ]
             | _ -> None)
        | GNode n when n.NodeKind = DotExpr ->
            (match n.Children with
             | [ lhs; GToken _; GToken r ] when r.Kind = Ident ->
                 flattenSpine lhs |> Option.map (fun sp -> sp @ [ r ])
             | _ -> None)
        | _ -> None

    let rec walkExpr (env : Env) (g : Green) : Env =
        match g with
        | GToken _ -> env
        | GNode n ->
            match n.NodeKind with
            | IdentExpr ->
                (match n.Children with
                 | [ GToken t ] when t.Kind = Ident -> tryRecord env t
                 | _ -> ())
                env
            | ObjExpr ->
                // an anonymous class: its members are keyed by a synthetic
                // name derived from the expression's position
                let synth =
                    match Green.tokens g |> List.tryHead with
                    | Some t -> "obj@" + string t.Offset
                    | None -> "obj@?"
                let iface =
                    n.Children
                    |> List.tryPick (fun c ->
                        match c with
                        | GNode ty when isTypeKind ty.NodeKind ->
                            (walkType env c
                             Green.tokens c |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast)
                        | _ -> None)
                    |> Option.map (fun t -> t.Text)
                let owner = match iface with Some i -> synth + "." + i | None -> synth
                for c in n.Children do
                    match c with
                    | GNode m when m.NodeKind = MemberDecl -> walkMember owner env m
                    | _ -> ()
                env
            | DotExpr ->
                (match flattenSpine g with
                 | Some (head :: _ as spine) when (Map.tryFind head.Text env |> Option.forall (fun d -> d.Kind = DefModule)) ->
                     // qualified module access: resolve the full spine
                     let dotted = spine |> List.map (fun t -> t.Text) |> String.concat "."
                     (match findQualified dotted with
                      | Some d ->
                          record (List.last spine) d
                          tryRecord env head
                      | None -> tryRecord env head)
                 | _ when (match n.Children |> List.rev |> List.tryPick (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None) with
                           | Some t -> (dictTryFind membersByName t.Text).IsSome
                           | None -> false) ->
                     // member access: the name alone only tells us *a* member
                     // exists. Record the first candidate so hover has
                     // something; inference rebinds it by receiver type.
                     let t = (n.Children |> List.rev |> List.pick (fun c -> match c with GToken x when x.Kind = Ident -> Some x | _ -> None))
                     record t (dictTryFind membersByName t.Text).Value.Head
                     (match n.Children with
                      | first :: _ -> walkExpr env first |> ignore
                      | [] -> ())
                 | _ ->
                     // member access on a value: resolve the lhs, and walk
                     // any index expression (a.[i])
                     (match n.Children with
                      | first :: rest ->
                          walkExpr env first |> ignore
                          for c in rest do
                              match c with
                              | GNode m when m.NodeKind = ListExpr -> walkExpr env c |> ignore
                              | _ -> ()
                      | [] -> ()))
                env
            | LetDecl -> local (fun () -> walkLet env n)
            | LambdaExpr ->
                let pats = n.Children |> List.filter (fun c -> match c with GNode p -> isPatKind p.NodeKind | _ -> false)
                let inner = List.fold (bindPat DefParam) env pats
                for c in n.Children do
                    match c with
                    | GNode p when isPatKind p.NodeKind -> ()
                    | GToken _ -> ()
                    | body -> walkExpr inner body |> ignore
                env
            | MatchExpr | TryExpr ->
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
            | BraceExpr -> env
            | BlockExpr ->
                let mutable e = env
                for c in n.Children do e <- walkExpr e c
                env
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
        let exportHere = atExportLevel
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
        for c in vecToList before do
            match c with
            | GNode p when isTypeKind p.NodeKind -> walkType env c
            | _ -> ()
        let isDestructure =
            vecToList before |> List.exists (fun c -> match c with GToken t -> t.Kind = Comma | _ -> false)
        let defsBefore = vecLen defs
        let result =
            if isDestructure then
                let envAll = List.fold (bindPat DefLet) env pats
                local (fun () ->
                    for c in vecToList after do
                        walkExpr env c |> ignore)
                envAll
            else
                match pats with
                | [] -> env
                | namePat :: paramPats ->
                    let envWithName = bindPat DefLet env namePat
                    let bodyBase = if isRec then envWithName else env
                    local (fun () ->
                        let bodyEnv = List.fold (bindPat DefParam) bodyBase paramPats
                        for c in vecToList after do
                            walkExpr bodyEnv c |> ignore)
                    envWithName
        if exportHere then
            for i in defsBefore .. vecLen defs - 1 do
                let d = vecGet defs i
                if d.Kind = DefLet then exportDef d
        result

    and walkMember (owner : string) (env : Env) (n : GreenNode) : unit =
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
        let declareMember (name : Token) =
            let d = define DefMember name
            dictSet memberDefs (owner + "." + name.Text) d
            let prior = match dictTryFind membersByName name.Text with Some l -> l | None -> []
            dictSet membersByName name.Text (prior @ [ d ])
        match vecToList idents with
        | [ self; name ] ->
            if self.Text <> "_" then
                let d = define DefSelf self
                inner <- Map.add self.Text d inner
            declareMember name
        | [ name ] -> declareMember name
        | _ -> ()
        local (fun () ->
            for p in vecToList pats do inner <- bindPat DefParam inner p
            for c in vecToList body do walkExpr inner c |> ignore)

    and walkTypeDecl (env : Env) (n : GreenNode) : Env =
        let nameTok = firstIdentToken n.Children
        let typeName = match nameTok with Some t -> t.Text | None -> "?"
        let exportHere = atExportLevel
        let mutable outer = env
        match nameTok with
        | Some t ->
            let d = define DefType t
            outer <- Map.add t.Text d outer
            if exportHere then exportDef d
        | None -> ()
        for c in n.Children do
            match c with
            | GNode u when u.NodeKind = UnionCase ->
                (match firstIdentToken u.Children with
                 | Some t ->
                     let d = define DefCase t
                     outer <- Map.add t.Text d outer
                     if exportHere then exportDef d
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
        let mutable inner = outer
        for c in n.Children do
            match c with
            | GNode p when isPatKind p.NodeKind ->
                local (fun () -> inner <- bindPat DefParam inner c)
            | GNode m when m.NodeKind = MemberDecl -> walkMember typeName inner m
            | GNode i when i.NodeKind = InterfaceImpl ->
                // an explicit implementation is not part of the class' own
                // member namespace: it is reached only through the interface
                let ifaceName =
                    i.Children
                    |> List.tryPick (fun x ->
                        match x with
                        | GNode ty when isTypeKind ty.NodeKind ->
                            Green.tokens x |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                        | _ -> None)
                    |> Option.map (fun t -> t.Text)
                let implOwner =
                    match ifaceName with
                    | Some inm -> typeName + "." + inm
                    | None -> typeName
                for x in i.Children do
                    match x with
                    | GNode m when m.NodeKind = MemberDecl -> walkMember implOwner inner m
                    | GNode ty when isTypeKind ty.NodeKind -> walkType inner x
                    | _ -> ()
            | GNode inh when inh.NodeKind = InheritDecl ->
                // `inherit Base(args)`: bind the base name, resolve the args
                // the arguments are constructor-parameter expressions, so
                // they see the primary constructor's parameters
                for x in inh.Children do
                    match x with
                    | GNode ty when isTypeKind ty.NodeKind -> walkType outer x
                    | GNode _ -> local (fun () -> walkExpr inner x |> ignore)
                    | GToken _ -> ()
            | GNode l when l.NodeKind = LetDecl -> local (fun () -> inner <- walkLet inner l)
            | GNode b when b.NodeKind = BlockExpr -> local (fun () -> walkExpr inner c |> ignore)
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
                let nameToks =
                    n.Children |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
                let segment = nameToks |> List.map (fun t -> t.Text) |> String.concat "."
                (match nameToks with
                 | t :: _ ->
                     let d = define DefModule t
                     outer <- Map.add t.Text d outer
                     if atExportLevel then exportDef d
                 | [] -> ())
                let saved = modulePath
                modulePath <- (if modulePath = "" then segment else modulePath + "." + segment)
                let mutable inner = outer
                for c in n.Children do
                    match c with
                    | GNode _ -> inner <- walkDecl inner c
                    | GToken _ -> ()
                modulePath <- saved
                outer
            | ModuleHeader ->
                let nameToks =
                    n.Children |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
                (match nameToks with
                 | t :: _ -> define DefModule t |> ignore
                 | [] -> ())
                modulePath <- nameToks |> List.map (fun t -> t.Text) |> String.concat "."
                env
            | OpenDecl ->
                let dotted =
                    n.Children
                    |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t.Text | _ -> None)
                    |> String.concat "."
                if dotted = "" then env
                else
                    vecAdd opens dotted
                    // F# temporal shadowing: an `open` injects the module's
                    // direct exports into the environment AT THIS POINT —
                    // shadowing earlier lets and earlier opens; later lets
                    // shadow these in turn.
                    let prefix = dotted + "."
                    let inject (e : Env) (tbl : Dict<string, Definition>) : Env =
                        let mutable acc = e
                        for full, d in dictPairs tbl do
                            if full.StartsWith prefix then
                                let rest = substr full (strLen prefix) (strLen full - strLen prefix)
                                if not (rest.Contains ".") then
                                    acc <- Map.add rest d acc
                        acc
                    inject (inject env imports) ownExports
            | AttributeList | TyParams -> env
            | _ -> local (fun () -> walkExpr env g) |> ignore; env

    let mutable env : Env = Map.empty
    for c in root.Children do
        env <- walkDecl env c

    { Definitions = vecToList defs
      Resolutions = vecToList uses
      Exports = vecToList exports
      Members = dictPairs memberDefs }

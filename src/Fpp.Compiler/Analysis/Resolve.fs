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
    /// set by an `[<AutoOpen>]` attribute, consumed by the module it precedes
    let mutable pendingAutoOpen = false
    // "TypeName.MemberName" -> def, and bare name -> every def with that
    // name (a use is disambiguated by the receiver type during inference)
    let memberDefs = dictNew<string, Definition> ()
    let membersByName = dictNew<string, Definition list> ()
    let mutable modulePath = ""

    let define (kind : DefKind) (t : Token) : Definition =
        let d = { Name = t.Text; Kind = kind; Path = path; Offset = t.Offset; Length = strLen t.Text }
        vecAdd defs d
        d

    /// Define under a name other than the token's text (property accessors:
    /// the `set` token declares a member called `set_Prop`).
    let defineAs (kind : DefKind) (nm : string) (t : Token) : Definition =
        let d = { Name = nm; Kind = kind; Path = path; Offset = t.Offset; Length = strLen t.Text }
        vecAdd defs d
        d

    let record (t : Token) (d : Definition) : unit =
        vecAdd uses { UseOffset = t.Offset; UseLength = strLen t.Text; Def = d }

    let exportUnder (name : string) (d : Definition) : unit =
        let full = if modulePath = "" then name else modulePath + "." + name
        vecAdd exports (full, d)
        dictSet ownExports full d
        // a type and a module may share a full name (`type MapLinked` and
        // `module MapLinked`); the plain key holds whichever came last, so
        // the type ALSO lives under its own namespace key
        if d.Kind = DefType then
            vecAdd exports ("type " + full, d)
            dictSet ownExports ("type " + full) d

    let exportDef (d : Definition) : unit = exportUnder d.Name d

    /// Bases to try when qualifying a name. F# shadowing: the LAST `open`
    /// wins among competing candidates, so opens are consulted in reverse
    /// declaration order, before the enclosing module path and its prefixes.
    let bases () : string list =
        let rec prefixes (p : string) : string list =
            if p = "" then [ "" ]
            else
                let i = p.LastIndexOf '.'
                if i < 0 then [ p; "" ] else p :: prefixes (substr p 0 i)
        // An `open M` names a module RELATIVE to where it appears, so it has
        // to be composed with the enclosing module path — otherwise opening
        // a module fails to bring its nested modules into scope.
        let opened =
            List.rev (vecToList opens)
            |> List.collect (fun o ->
                (prefixes modulePath |> List.map (fun p -> if p = "" then o else p + "." + o)))
        opened @ prefixes modulePath @ [ "" ]

    // "TypeName.CaseName" -> the case's definition, so `NodeKind.Inner`
    // still means the CASE when an unrelated type also answers to `Inner`
    let typeCases = dictNew<string, Definition> ()

    let findQualified (dotted : string) : Definition option =
        bases ()
        |> List.tryPick (fun b ->
            let full = if b = "" then dotted else b + "." + dotted
            match dictTryFind ownExports full with
            | Some d -> Some d
            | None -> dictTryFind imports full)

    /// As findQualified, but for a name in a position where a TYPE is meant
    /// (a dotted type annotation, or a constructor call): the type namespace
    /// is consulted first, so a module sharing the name cannot shadow it.
    let findQualifiedType (dotted : string) : Definition option =
        bases ()
        |> List.tryPick (fun b ->
            let full = if b = "" then dotted else b + "." + dotted
            match dictTryFind ownExports ("type " + full) with
            | Some d -> Some d
            | None ->
                match dictTryFind imports ("type " + full) with
                | Some d -> Some d
                | None ->
                    match dictTryFind ownExports full with
                    | Some d -> Some d
                    | None -> dictTryFind imports full)

    /// Local environment first, then opened/imported modules.
    let lookupValue (env : Env) (name : string) : Definition option =
        match Map.tryFind name env with
        | Some d -> Some d
        | None -> findQualified name

    /// Types live in their own namespace: F# lets a module and a type share
    /// a name, and `MapLinked.exists` then means the module while
    /// `MapLinked<'K,'V>` means the type.
    let typeKey (name : string) = "type " + name

    let lookupType (env : Env) (name : string) : Definition option =
        match Map.tryFind (typeKey name) env with
        | Some d -> Some d
        | None ->
            match Map.tryFind name env with
            | Some d when d.Kind = DefType -> Some d
            | _ -> findQualifiedType name

    /// Record a use under a name that is not the token's own text — an
    /// operator's definition is written `(+++)` and used as `+++`.
    let tryRecordAs (env : Env) (name : string) (t : Token) : unit =
        match Map.tryFind name env with
        | Some d -> record t d
        | None -> ()

    let tryRecord (env : Env) (t : Token) : unit =
        // A bare name in expression position is a value or a constructor,
        // never a module: if a module shadows a type of the same name, the
        // type is what was meant here.
        let picked =
            match Map.tryFind t.Text env with
            | Some d when d.Kind = DefModule ->
                (match Map.tryFind (typeKey t.Text) env with
                 | Some ty -> Some ty
                 | None -> Some d)
            | Some d -> Some d
            | None -> findQualified t.Text
        match picked with
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

    /// `type A ... and B ...`: the members of an `and` group see EACH OTHER,
    /// so every sibling's name is bound before any body in the group is
    /// walked. Keyed by the index of the group's first declaration; the
    /// bindings are value-equal to what walkTypeDecl registers later.
    /// The name a SIMPLE `let` binding introduces — the first `IdentPat`
    /// child, which is the binding's own name (its parameters follow it).
    /// None for a destructuring binding, which never forms an `and` group.
    let letNameToken (children : Green list) : Token option =
        children
        |> List.tryPick (fun c ->
            match c with
            | GNode p when p.NodeKind = IdentPat ->
                (match p.Children with
                 | [ GToken t ] when t.Kind = Ident -> Some t
                 | _ -> None)
            | _ -> None)

    /// Names an `and` group must have in scope BEFORE any of its members is
    /// walked, keyed by the index of the member that opens the group. Both
    /// `type A ... and B ...` and `let rec f ... and g ...`: a member's body
    /// is walked when that member is reached, so a forward reference to a
    /// sibling has nothing to resolve against otherwise — and an unresolved
    /// name is not a diagnostic, so it fails silently and only surfaces as an
    /// `EUnknown` at emission.
    let andGroupBindings (children : Green list) : Dict<int, (string * Definition) list> =
        let m = dictNew<int, (string * Definition) list> ()
        let arr = Array.ofList children
        let groupKind (g : Green) =
            match g with
            | GNode n when n.NodeKind = TypeDecl -> "type"
            | GNode n when n.NodeKind = LetDecl -> "let"
            | _ -> ""
        let startsWithAnd (g : Green) =
            match Green.tokens g |> List.tryHead with
            | Some t -> t.Kind = Keyword && t.Text = "and"
            | None -> false
        let mutable i = 0
        while i < arr.Length do
            let kind = groupKind arr.[i]
            if kind <> "" && not (startsWithAnd arr.[i]) then
                let mutable j = i + 1
                while j < arr.Length && groupKind arr.[j] = kind && startsWithAnd arr.[j] do j <- j + 1
                if j - i > 1 then
                    let defKind = if kind = "type" then DefType else DefLet
                    let binds =
                        [ i .. j - 1 ]
                        |> List.choose (fun k ->
                            match arr.[k] with
                            | GNode n ->
                                let tok =
                                    if kind = "type" then firstIdentToken n.Children
                                    else letNameToken n.Children
                                (match tok with
                                 | Some t ->
                                     Some (t.Text, { Name = t.Text; Kind = defKind; Path = path
                                                     Offset = t.Offset; Length = strLen t.Text })
                                 | None -> None)
                            | GToken _ -> None)
                    dictSet m i binds
                i <- j
            else i <- i + 1
        m

    /// LetDecl offset -> the names of the `and` group it belongs to. A local
    /// group is registered by the block that contains it and applied by
    /// `walkLet` when it reaches each member, which is what puts a sibling in
    /// scope for a body walked BEFORE that sibling is bound.
    let groupBinds = dictNew<int, Definition list> ()

    /// The env a sibling at `idx` is walked in: if an `and` group opens here,
    /// every member's name goes in scope first. Only the env is touched —
    /// each definition is still recorded when its own member is walked, and
    /// the entry made here is the value `define` builds there, so they agree.
    let openAndGroup (groups : Dict<int, (string * Definition) list>) (idx : int) (env : Env) : Env =
        let mutable e = env
        (match dictTryFind groups idx with
         | Some binds ->
             for nm, d in binds do
                 // a type also answers to its type-namespace key; a value never does
                 let withValue = Map.add nm d e
                 if d.Kind = DefType then e <- Map.add (typeKey nm) d withValue
                 else e <- withValue
         | None -> ())
        e

    /// Record every `and` group among `children` against each of its members
    /// (a group's bindings carry their own name-token offsets, which is the
    /// key `walkLet` looks itself up by). Returns nothing: a block only
    /// reports what it saw, and `walkLet` does the scoping.
    let noteAndGroups (children : Green list) : unit =
        for _, binds in dictPairs (andGroupBindings children) do
            let ds = List.map snd binds
            for d in ds do
                dictSet groupBinds d.Offset ds

    let isPatKind (k : NodeKind) =
        k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat || k = StructTuplePat
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat || k = TypeTestPat

    let isTypeKind (k : NodeKind) =
        k = NamedType || k = VarType || k = AnonType || k = TupleType || k = StructTupleType
        || k = FunType || k = AppType || k = PostfixType || k = ParenType
        || k = SpliceType

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
            // `%t` in type position: the spliced NAME is an ordinary value use,
            // so it resolves like one rather than as a type name
            | SpliceType ->
                n.Children
                |> List.iter (fun c ->
                    match c with
                    | GNode inner when inner.NodeKind = IdentExpr ->
                        (match inner.Children |> List.choose (fun x -> match x with GToken t when t.Kind = Ident -> Some t | _ -> None) with
                         | [ t ] ->
                             (match lookupValue env t.Text with
                              | Some d -> record t d
                              | None -> ())
                         | _ -> ())
                    | _ -> ())
            | NamedType ->
                let idents =
                    n.Children |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
                (match idents with
                 | [ t ] ->
                     (match lookupType env t.Text with
                      | Some d when d.Kind = DefType -> record t d
                      | _ -> ())
                 | many when not (List.isEmpty many) ->
                     let dotted = many |> List.map (fun t -> t.Text) |> String.concat "."
                     (match findQualifiedType dotted with
                      | Some d when d.Kind = DefType -> record (List.last many) d
                      | _ -> ())
                 | _ -> ())
            | VarType | AnonType -> ()
            | _ -> List.iter (walkType env) n.Children

    // ---- patterns ---------------------------------------------------------

    /// A QUALIFIED case in pattern position (`Classes.Improve inst`). The
    /// case is the LAST segment — the leading spine is its module — and the
    /// use has to land on that segment, because that is where inference
    /// looks for the constructor to instantiate. Without it the payload
    /// binder never gets a type, and everything read out of it stays
    /// unknown: the loop over `inst.Context` could not even tell it was
    /// walking a list.
    let recordQualifiedCase (env : Env) (children : Green list) : unit =
        let idents =
            children
            |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
        match idents with
        | [] -> ()
        | first :: _ ->
            // the prefix still records as before, so go-to-def on a module
            // segment keeps working
            tryRecord env first
            if idents.Length > 1 then
                let full = idents |> List.map (fun t -> t.Text) |> String.concat "."
                let last = List.last idents
                match lookupValue env full with
                | Some d -> record last d
                | None ->
                    // `Inner.Colour.Green` in PATTERN position: the case is
                    // named through its TYPE as well as its module, and no
                    // value carries that whole path. The type is the
                    // second-to-last segment, and `typeCases` is keyed by the
                    // type's own name whatever holds it.
                    if idents.Length > 2 then
                        let ty = idents |> List.item (idents.Length - 2)
                        (match dictTryFind typeCases (ty.Text + "." + last.Text) with
                         | Some cd -> record last cd
                         | None -> ())

    /// `inCase` marks a pattern in MATCH position, where a bare uppercase
    /// identifier is a union case and never a binder. A parameter or a `let`
    /// pattern is a binding position, where such a name is an ordinary (if
    /// unconventional) binder — so the rule cannot simply apply everywhere.
    let rec bindPatIn (inCase : bool) (kind : DefKind) (env : Env) (g : Green) : Env =
        match g with
        | GToken _ -> env
        | GNode n ->
            match n.NodeKind with
            | IdentPat ->
                (match n.Children with
                 | GToken t :: rest when t.Kind = Ident ->
                     if not (List.isEmpty rest) then
                         recordQualifiedCase env n.Children
                         env
                     else
                         match lookupValue env t.Text with
                         | Some d when d.Kind = DefCase ->
                             record t d
                             env
                         | _ ->
                             if t.Text = "_" then env
                             // F# reads a pattern identifier that starts with
                             // an UPPERCASE letter as a union case, never as
                             // a new binding. Binding it shadowed the case for
                             // the rest of the clause, so in `| None -> None`
                             // the body's `None` was the pattern's binder and
                             // took its type from the scrutinee — a false
                             // mismatch, and only where the case could not be
                             // resolved, which is the dogfooding gate exactly.
                             elif inCase && strLen t.Text > 0
                                  && charAt t.Text 0 >= 'A' && charAt t.Text 0 <= 'Z' then
                                 env
                             else
                                 let d = define kind t
                                 Map.add t.Text d env
                 | _ -> env)
            | StructTuplePat ->
                n.Children |> List.fold (fun e c -> bindPatIn inCase kind e c) env
            | WildcardPat | LiteralPat -> env
            | AppPat ->
                (match n.Children with
                 | head :: args ->
                     (match head with
                      | GNode hn when hn.NodeKind = IdentPat ->
                          (match hn.Children with
                           | GToken t :: _ when t.Kind = Ident -> recordQualifiedCase env hn.Children
                           | _ -> ())
                      | _ -> ())
                     List.fold (bindPatIn inCase kind) env args
                 | [] -> env)
            | SplicePat ->
                // `%p` binds nothing here: the NAME is an ordinary value use
                n.Children
                |> List.iter (fun c ->
                    match c with
                    | GNode inner when inner.NodeKind = IdentExpr ->
                        (match inner.Children |> List.choose (fun x -> match x with GToken t when t.Kind = Ident -> Some t | _ -> None) with
                         | [ t ] -> (match lookupValue env t.Text with Some d -> record t d | None -> ())
                         | _ -> ())
                    | _ -> ())
                env
            | k when isTypeKind k ->
                walkType env g
                env
            | _ -> List.fold (bindPatIn inCase kind) env n.Children

    // ---- expressions ------------------------------------------------------

    /// Flatten a pure identifier spine `a.b.c`; None if any segment is not a
    /// plain identifier.

    /// binding position: a `let`, a parameter, a `for`
    let bindPat (kind : DefKind) (env : Env) (g : Green) : Env = bindPatIn false kind env g
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
            | BinaryExpr ->
                // `a +++ b` where `+++` is a binding rather than a builtin.
                // The name is the FUSED one a definition writes, `(+++)`, so
                // an operator that resolves is recorded like any other use
                // and the later passes see a call instead of a primitive.
                (match n.Children |> List.choose (fun c -> match c with GToken t -> Some t | _ -> None) with
                 | [ op ] when op.Kind = Operator ->
                     // ONLY a let-bound one. A CLASS declares its operators
                     // too (`static (/) : 'a -> 'a -> 'a`), and those are
                     // dispatched through the instance the operand type
                     // selects — binding a use to the declaration would call
                     // a member that has no body.
                     (match Map.tryFind ("(" + op.Text + ")") env with
                      | Some d when d.Kind = DefLet -> tryRecordAs env ("(" + op.Text + ")") op
                      | _ -> ())
                 | _ -> ())
                let mutable e = env
                for c in n.Children do e <- walkExpr e c
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
                // the spine may start with NAMESPACE segments this language
                // does not have (`System.Threading.Interlocked.Exchange`):
                // drop unbound heads until the remaining path names
                // something real
                let qualifiedSuffix (spine : Token list) : Token list option =
                    let rec go (sp : Token list) =
                        match sp with
                        | [] | [ _ ] -> None
                        | h :: rest ->
                            let dotted = sp |> List.map (fun t -> t.Text) |> String.concat "."
                            if (findQualified dotted).IsSome then Some sp
                            elif (Map.tryFind h.Text env).IsNone then go rest
                            else None
                    go spine
                (match flattenSpine g with
                 | Some (head0 :: _ as spine0) when
                        (qualifiedSuffix spine0).IsSome
                        && (Map.tryFind head0.Text env |> Option.forall (fun d -> d.Kind <> DefLet && d.Kind <> DefParam)) ->
                     // qualified access: the spine (with any namespace heads
                     // dropped) names something real, and the head is not a
                     // local shadowing it
                     let spine = (qualifiedSuffix spine0).Value
                     let head = List.head spine
                     let dotted = spine |> List.map (fun t -> t.Text) |> String.concat "."
                     let picked =
                         match findQualified dotted with
                         // a module is never a value: if a type shares the
                         // full name, the spine means its constructor
                         | Some d when d.Kind = DefModule ->
                             (match findQualifiedType dotted with
                              | Some ty when ty.Kind = DefType -> Some ty
                              | _ -> Some d)
                         | other -> other
                     (match picked with
                      | Some d ->
                          record (List.last spine) d
                          tryRecord env head
                      | None -> tryRecord env head)
                 | Some spine0 when
                        List.length spine0 >= 3
                        && (spine0 |> List.take (List.length spine0 - 2)
                            |> List.forall (fun t -> (Map.tryFind t.Text env).IsNone && (findQualified t.Text).IsNone))
                        && (let tyTok = spine0 |> List.item (List.length spine0 - 2)
                            match Map.tryFind tyTok.Text env with
                            | Some d -> d.Kind = DefType
                            | None ->
                                (match findQualifiedType tyTok.Text with
                                 | Some d -> d.Kind = DefType
                                 | None -> false)) ->
                     // NAMESPACE-QUALIFIED static access, e.g.
                     // `System.Threading.Interlocked.Exchange`: every
                     // segment before the TYPE names a namespace this
                     // language does not have. Recording the type is enough
                     // — inference rebinds the member by receiver type.
                     let tyTok = spine0 |> List.item (List.length spine0 - 2)
                     (match Map.tryFind tyTok.Text env with
                      | Some d -> record tyTok d
                      | None ->
                          (match findQualifiedType tyTok.Text with
                           | Some d -> record tyTok d
                           | None -> ()))
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
                 | Some (head :: rest) when
                        (match Map.tryFind head.Text env with
                         | Some d when d.Kind = DefType ->
                             (match rest |> List.tryLast with
                              | Some last ->
                                  // the case is looked up in the TYPE's own
                                  // cases first: an unrelated type sharing
                                  // the case's name must not shadow it
                                  (dictTryFind typeCases (d.Name + "." + last.Text)).IsSome
                                  || (Map.tryFind last.Text env |> Option.map (fun c -> c.Kind = DefCase)) = Some true
                              | None -> false)
                         | _ -> false) ->
                     // `NodeKind.Leaf`: a case named through its own type
                     let spine = head :: rest
                     let last = List.last spine
                     let headDef = Map.find head.Text env
                     record head headDef
                     (match dictTryFind typeCases (headDef.Name + "." + last.Text) with
                      | Some cd -> record last cd
                      | None -> record last (Map.find last.Text env))
                 // `Inner.Colour.Green`: a case named through its type AND
                 // the module that holds it. The TYPE is the second-to-last
                 // segment and the case the last; `typeCases` is keyed by the
                 // type's own name, so the module spine in front of it does
                 // not change the lookup.
                 | Some spine when
                        List.length spine >= 3
                        && (let last = List.last spine
                            let ty = spine |> List.item (List.length spine - 2)
                            (dictTryFind typeCases (ty.Text + "." + last.Text)).IsSome) ->
                     let last = List.last spine
                     let ty = spine |> List.item (List.length spine - 2)
                     (match Map.tryFind (List.head spine).Text env with
                      | Some hd -> record (List.head spine) hd
                      | None -> ())
                     (match Map.tryFind ty.Text env with
                      | Some td -> record ty td
                      | None -> ())
                     (match dictTryFind typeCases (ty.Text + "." + last.Text) with
                      | Some cd -> record last cd
                      | None -> ())
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
                        let inner = List.fold (bindPatIn true DefParam) env pats
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
            | CompExpr ->
                // Only the PROBE sees one of these: by the time the rewrite
                // has run there is no CompExpr left. Binding its body anyway
                // is what lets the probe TYPE the body, which is how the
                // implicit-yield question — is the trailing expression a
                // value or a statement? — gets a real answer.
                for c in n.Children do
                    match c with
                    | GNode br when br.NodeKind = BraceExpr ->
                        let mutable e = env
                        for x in br.Children do e <- walkExpr e x
                    | other -> walkExpr env other |> ignore
                env
            | BraceExpr -> env
            | BlockExpr ->
                // a local `let rec f ... and g ...`: register the group's
                // names against each member, so `walkLet` has them in scope
                // for every body. Recording is all that happens here — see
                // `groupBinds`
                noteAndGroups n.Children
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
        // `and g ...` continues a `let rec` group: the `rec` keyword sits on
        // the group's FIRST member, but every member of it is recursive — and
        // sees the whole group, not just itself
        let isRec = hasKwChild "rec" n.Children || hasKwChild "and" n.Children
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
            // declared constraints: `let f x : 'a when Num<'a> = ...`
            | GNode p when p.NodeKind = WhenDecl -> walkType env c
            | _ -> ()
        let isDestructure =
            (vecToList before |> List.exists (fun c -> match c with GToken t -> t.Kind = Comma | _ -> false))
            // `let (k, v) = e` — the parens hide the comma from the token
            // scan, and treating it as a SIMPLE binding bound only k
            || (match pats with
                | [ GNode p ] when p.NodeKind = ParenPat ->
                    p.Children
                    |> List.exists (fun c ->
                        match c with
                        // the parens hold a FLAT comma-separated pattern
                        | GToken t -> t.Kind = Comma
                        | GNode inner -> inner.NodeKind = ConsPat || inner.NodeKind = ListPat)
                | [ GNode p ] -> p.NodeKind = StructTuplePat
                | _ -> false)
        let defsBefore = vecLen defs
        // Only what the BINDING ITSELF introduces is exported — the snapshot
        // is taken after binding the patterns and before walking the body.
        // Sweeping to the end of the body instead exported every nested
        // local: a `let struct(exists, _) = ...` deep inside a function in
        // module SetNode overwrote the module's own `exists` under the very
        // same dotted name.
        let mutable defsBound = defsBefore
        let result =
            if isDestructure then
                let envAll = List.fold (bindPat DefLet) env pats
                defsBound <- vecLen defs
                local (fun () ->
                    let mutable here = env
                    for c in vecToList after do
                        match c with
                        | GToken t when t.Kind = Keyword && t.Text = "in" -> here <- envAll
                        | c -> walkExpr here c |> ignore)
                envAll
            else
                match pats with
                | [] -> env
                | namePat :: paramPats ->
                    let envWithName = bindPat DefLet env namePat
                    defsBound <- vecLen defs
                    // a member of a local `let rec f ... and g ...`: the whole
                    // group is in scope for this body, siblings included, and
                    // a sibling defined LATER is exactly what `and` is for
                    // a member of a local `let rec f ... and g ...`: the whole
                    // group is in scope for this body, and a sibling defined
                    // LATER is exactly what `and` is for
                    let groupNames =
                        match letNameToken (vecToList before) with
                        | Some nt ->
                            (match dictTryFind groupBinds nt.Offset with
                             | Some binds -> binds
                             | None -> [])
                        | None -> []
                    let envGroup =
                        List.fold (fun (acc : Env) (d : Definition) -> Map.add d.Name d acc)
                            envWithName groupNames
                    let bodyBase = if isRec then envGroup else env
                    local (fun () ->
                        let mutable here = List.fold (bindPat DefParam) bodyBase paramPats
                        for c in vecToList after do
                            match c with
                            | GToken t when t.Kind = Keyword && t.Text = "in" -> here <- envWithName
                            | c -> walkExpr here c |> ignore)
                    envWithName
        if exportHere then
            for i in defsBefore .. defsBound - 1 do
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
        // `new(args) = ...` has no member name; its parameters and body are
        // walked like any other member's
        if n.Children |> List.exists (fun c -> match c with GToken t -> t.Kind = Keyword && t.Text = "new" | _ -> false) then
            // an explicit constructor is its own definition, so a type may
            // have several and a call site can pick between them
            (match n.Children |> List.tryPick (fun c -> match c with GToken t when t.Kind = Keyword && t.Text = "new" -> Some t | _ -> None) with
             | Some nt -> dictSet memberDefs (owner + ".new@" + string nt.Offset) (defineAs DefMember "new" nt)
             | None -> ())
            local (fun () ->
                let mutable ctorEnv = env
                for p in vecToList pats do ctorEnv <- bindPat DefParam ctorEnv p
                for c in vecToList body do walkExpr ctorEnv c |> ignore)
        // `val mutable X : T` declares a FIELD, so it must not enter the
        // member namespace — `x.X` is a field read, not a call
        let isValDecl =
            n.Children |> List.exists (fun c -> match c with GToken t -> t.Kind = Keyword && t.Text = "val" | _ -> false)
        let declareMember (name : Token) =
            if isValDecl then define DefField name |> ignore else
            let d = define DefMember name
            // an OVERLOAD keeps its own entry under an ordinal suffix; the
            // plain key stays with the first declaration, so everything that
            // knows nothing of overloading keeps working
            let key = owner + "." + name.Text
            if (dictTryFind memberDefs key).IsNone then dictSet memberDefs key d
            else
                let mutable k = 2
                while (dictTryFind memberDefs (key + "#" + string k)).IsSome do k <- k + 1
                dictSet memberDefs (key + "#" + string k) d
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
        // property accessors carry their own parameters and bodies
        let accessors =
            n.Children |> List.choose (fun c -> match c with GNode a when a.NodeKind = AccessorDecl -> Some a | _ -> None)
        match vecToList idents |> List.tryLast with
        | Some propName when not (List.isEmpty accessors) ->
            for acc in accessors do
                let kindTok = acc.Children |> List.tryPick (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
                (match kindTok with
                 | Some kt when kt.Text = "set" ->
                     let d = defineAs DefMember ("set_" + propName.Text) kt
                     dictSet memberDefs (owner + ".set_" + propName.Text) d
                 | _ -> ())
                local (fun () ->
                    let mutable accEnv = inner
                    for c in acc.Children do
                        match c with
                        | GNode p when isPatKind p.NodeKind -> accEnv <- bindPat DefParam accEnv c
                        | _ -> ()
                    let mutable seenAccEq = false
                    for c in acc.Children do
                        match c with
                        | GToken t when t.Kind = Operator && t.Text = "=" -> seenAccEq <- true
                        | _ when seenAccEq -> walkExpr accEnv c |> ignore
                        | _ -> ())
        | _ -> ()
        local (fun () ->
            for p in vecToList pats do inner <- bindPat DefParam inner p
            for c in vecToList body do walkExpr inner c |> ignore)

    and walkTypeDecl (env : Env) (n : GreenNode) : Env =
        let nameTok = firstIdentToken n.Children
        let typeName = match nameTok with Some t -> t.Text | None -> "?"
        let exportHere = atExportLevel
        // `type X with member ...` names a type declared ELSEWHERE. Defining
        // the name again would shadow the real declaration — and with it the
        // constructor, so `X(...)` at a later call site resolved to the
        // extension and found nothing to call.
        let isExtension =
            (n.Children |> List.exists (fun c ->
                match c with GToken t -> t.Kind = Keyword && t.Text = "with" | _ -> false))
            && not (n.Children |> List.exists (fun c ->
                match c with GToken t -> t.Kind = Operator && t.Text = "=" | _ -> false))
        let mutable outer = env
        match nameTok with
        | Some t when not isExtension ->
            let d = define DefType t
            outer <- Map.add t.Text d outer
            outer <- Map.add (typeKey t.Text) d outer
            if exportHere then exportDef d
        | _ -> ()
        for c in n.Children do
            match c with
            | GNode u when u.NodeKind = UnionCase ->
                (match firstIdentToken u.Children with
                 | Some t ->
                     // an ENUM member (`| None = 0`) is only in scope
                     // QUALIFIED, as in F# — binding it bare would shadow
                     // union cases of the same name (Option's None). Its
                     // definition carries the qualified name so every later
                     // pass distinguishes it from a union case.
                     let isEnumMember =
                         u.Children |> List.exists (fun c ->
                             match c with
                             | GToken et -> et.Kind = Operator && et.Text = "="
                             | _ -> false)
                     let d =
                         if isEnumMember then defineAs DefCase (typeName + "." + t.Text) t
                         else define DefCase t
                     if not isEnumMember then
                         outer <- Map.add t.Text d outer
                     dictSet typeCases (typeName + "." + t.Text) d
                     if exportHere then
                         if isEnumMember then exportUnder (typeName + "." + t.Text) d
                         else exportDef d
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
                // the interface is the HEAD of the type application, and the
                // last identifier of that head (the rest are module names)
                let rec ifaceOf (ty : GreenNode) : string option =
                    let sub = ty.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)
                    match sub |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
                    | Some hd when ty.NodeKind = AppType -> ifaceOf hd
                    | _ ->
                        Green.tokens (GNode ty) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                        |> Option.map (fun t -> t.Text)
                let ifaceName =
                    i.Children
                    |> List.tryPick (fun x ->
                        match x with
                        | GNode ty when isTypeKind ty.NodeKind -> ifaceOf ty
                        | _ -> None)
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

    /// `class C<'a>` — the class name lives in the type namespace, and its
    /// members become ordinary values in scope. `Zero` and `(+)` are looked
    /// up exactly like any other binding; what makes them special is only
    /// that their schemes carry a constraint.
    and walkClassDecl (env : Env) (n : GreenNode) : Env =
        let exportHere = atExportLevel
        let mutable outer = env
        // the name sits inside the head type (`class Num<'a>` parses the head
        // as an application), not as a direct token child
        let nameTok =
            n.Children
            |> List.tryPick (fun c ->
                match c with
                | GNode ty when isTypeKind ty.NodeKind ->
                    Green.tokens c |> List.tryFind (fun t -> t.Kind = Ident)
                | _ -> None)
        let className = match nameTok with Some t -> t.Text | None -> "?"
        (match nameTok with
         | Some t ->
             let d = define DefType t
             outer <- Map.add t.Text d outer
             outer <- Map.add (typeKey t.Text) d outer
             if exportHere then exportDef d
         | None -> ())
        for c in n.Children do
            match c with
            | GNode m when m.NodeKind = MemberDecl ->
                // `type Result` declares an associated type, not a value
                if not (hasKwChild "type" m.Children) then
                    match firstIdentToken m.Children with
                    | Some t ->
                        let d = define DefLet t
                        outer <- Map.add t.Text d outer
                        if exportHere then
                            exportDef d
                            // also under `Class.Member`, so every member has
                            // a spelling that cannot be shadowed or confused
                            // with another class' member of the same name
                            exportUnder (className + "." + t.Text) d
                    | None -> ()
                for x in m.Children do
                    match x with
                    | GNode ty when isTypeKind ty.NodeKind -> walkType outer x
                    | _ -> ()
            | GNode w when w.NodeKind = WhenDecl -> walkType outer c
            | GNode ty when isTypeKind ty.NodeKind -> walkType outer c
            | _ -> ()
        outer

    /// `instance C<int, int>` — free-standing, so it introduces no names of
    /// its own. Its members are reached only by resolving the class.
    and walkInstanceDecl (env : Env) (n : GreenNode) : Env =
        let owner =
            match Green.tokens (GNode n) |> List.tryHead with
            | Some t -> "instance@" + string t.Offset
            | None -> "instance@?"
        for c in n.Children do
            match c with
            | GNode m when m.NodeKind = MemberDecl ->
                if hasKwChild "type" m.Children then
                    for x in m.Children do
                        match x with
                        | GNode ty when isTypeKind ty.NodeKind -> walkType env x
                        | _ -> ()
                else walkMember owner env m
            | GNode w when w.NodeKind = WhenDecl -> walkType env c
            | GNode ty when isTypeKind ty.NodeKind -> walkType env c
            | _ -> ()
        env

    and walkDecl (env : Env) (g : Green) : Env =
        match g with
        | GToken _ -> env
        | GNode n ->
            match n.NodeKind with
            | LetDecl -> walkLet env n
            | TypeDecl -> walkTypeDecl env n
            | ClassDecl -> walkClassDecl env n
            | InstanceDecl -> walkInstanceDecl env n
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
                let auto = pendingAutoOpen
                pendingAutoOpen <- false
                modulePath <- (if modulePath = "" then segment else modulePath + "." + segment)
                let full = modulePath
                let mutable inner = outer
                let groups = andGroupBindings n.Children
                let mutable idx = 0
                for c in n.Children do
                    inner <- openAndGroup groups idx inner
                    (match c with
                     | GNode _ -> inner <- walkDecl inner c
                     | GToken _ -> ())
                    idx <- idx + 1
                modulePath <- saved
                if auto then
                    vecAdd opens full
                    // and into scope unqualified, the way `open` does
                    let prefix = full + "."
                    let injectAuto (e : Env) (tbl : Dict<string, Definition>) : Env =
                        let mutable acc = e
                        for k, d in dictPairs tbl do
                            if k.StartsWith prefix then
                                let rest = substr k (strLen prefix) (strLen k - strLen prefix)
                                if not (rest.Contains ".") then acc <- Map.add rest d acc
                        acc
                    injectAuto (injectAuto outer imports) ownExports
                else outer
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
            | AttributeList ->
                // `[<AutoOpen>] module M` puts M's contents in scope for
                // everything after it, without an `open`. The adaptive library
                // leans on it — `HashSet.computeDelta` lives in an auto-opened
                // `DifferentiationExtensions.HashSet`, and without this the
                // name falls through to whatever else answers to it.
                if Green.tokens g |> List.exists (fun t -> t.Kind = Ident && t.Text = "AutoOpen") then
                    pendingAutoOpen <- true
                env
            | TyParams -> env
            | _ -> local (fun () -> walkExpr env g) |> ignore; env

    let mutable env : Env = Map.empty
    let rootGroups = andGroupBindings root.Children
    let mutable rootIdx = 0
    for c in root.Children do
        env <- openAndGroup rootGroups rootIdx env
        env <- walkDecl env c
        rootIdx <- rootIdx + 1

    { Definitions = vecToList defs
      Resolutions = vecToList uses
      Exports = vecToList exports
      Members = dictPairs memberDefs }

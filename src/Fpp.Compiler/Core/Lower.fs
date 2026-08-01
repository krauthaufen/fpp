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
    /// `let struct(a, b) = e`: bind the struct once, then read its fields.
    /// One slot per ELEMENT, empty where the element is a wildcard — a
    /// binder list alone would renumber `struct(_, n)` as Item1.
    | StructLet of (VarId * Scheme) option list * string * Expr * Expr option

let lower (path : string) (root : GreenNode) (binder : Resolve.BindResult)
          (schemes : Dict<string, Scheme>) (opKinds : Dict<int, string>)
          (arrKinds : Dict<int, string>) (instSites : Dict<int, string list>)
          (memberSites : Dict<int, string>) (fieldOwners : Dict<int, string>)
          (ctorSites : Dict<int, int>)
          (projectMembers : Dict<string, Resolve.Definition>)
          (ifaces : Dict<string, (string * int) list>)
          (classUses : Dict<int, Fpp.Analysis.Classes.InstMember>)
          (classPending : Dict<int, string>)
          (opTypes : Dict<int, string>) : LowerResult =

    let notes = vecNew<int * string> ()
    let decls = vecNew<Decl> ()

    /// A reference to the instance member a class use resolved to. A GENERIC
    /// instance is a template, so the reference carries the instantiation and
    /// monomorphization stamps one body per element type — which is what
    /// makes the instance's own `when` context resolve per use rather than
    /// once for the whole program.
    let classRef (im : Fpp.Analysis.Classes.InstMember) : Expr =
        let v = { Path = im.MPath; Offset = im.MOffset; Name = im.MName }
        let sch = mono (TCon ("?", []))
        if List.isEmpty im.MInst then EVar (v, sch) else EVarI (v, sch, im.MInst)

    let mutable pendingStruct = false
    let mutable pendingExport = false
    // Set while lowering the loop of a list comprehension: the loop's BODY
    // is the yielded element, so it accumulates instead of being evaluated
    // for effect. Consumed on entry to the body, so a nested loop inside it
    // is an ordinary loop again.
    let mutable yieldInto : VarId option = None
    // Set while lowering the STATEMENT form of a comprehension. Unlike the
    // arrow form the yields are explicit and can sit anywhere — inside an
    // `if`, a `match` arm, a nested loop — so the sink is dynamic and the
    // interception happens at `yield` itself, wherever the ordinary lowering
    // reaches it.
    let mutable compAcc : VarId option = None
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
                        (match m.Children |> List.choose (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None) with
                         | [ _; nm ] | [ nm ] -> dictSet topLevelDefs nm.Offset true
                         | _ -> ())
                        // `member x.P with get … and set …` declares the
                        // writer as a SEPARATE function, named by the `set`
                        // keyword. Without it here, a use site could not
                        // carry a specialization demand, and a setter whose
                        // body depends on the layout (`items.[i] <- v`) was
                        // called through the template the stamper had already
                        // removed — "unbound variable set_Item".
                        for c in m.Children do
                            match c with
                            | GNode a when a.NodeKind = AccessorDecl ->
                                (match Green.tokens (GNode a) |> List.tryFind (fun t -> t.Kind = Ident) with
                                 | Some t -> dictSet topLevelDefs t.Offset true
                                 | None -> ())
                            | _ -> ()
                    elif m.NodeKind = InterfaceImpl then
                        m.Children |> List.iter (fun c -> match c with GNode x -> collectMembers x | _ -> ())
                    elif m.NodeKind = LetDecl
                         && (Green.tokens (GNode m) |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")) then
                        // a `static let` lifts to a top-level binding, so its
                        // uses may carry specialization demands too
                        match m.Children
                              |> List.tryPick (fun c ->
                                   match c with
                                   | GNode p when p.NodeKind = IdentPat ->
                                       Green.tokens (GNode p) |> List.tryFind (fun t -> t.Kind = Ident)
                                   | _ -> None) with
                        | Some t -> dictSet topLevelDefs t.Offset true
                        | None -> ()
                n.Children |> List.iter (fun c -> match c with GNode m -> collectMembers m | _ -> ())
            | InstanceDecl ->
                // an instance member is a top-level function like any other
                for c in n.Children do
                    match c with
                    | GNode m when m.NodeKind = MemberDecl ->
                        (match m.Children |> List.choose (fun x -> match x with GToken t when t.Kind = Ident -> Some t | _ -> None) with
                         | [ nm ] -> dictSet topLevelDefs nm.Offset true
                         | _ -> ())
                    | _ -> ()
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
    for k, d in dictPairs projectMembers do dictSet memberIndex k d
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
            Green.tokens (GNode tn) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
            |> Option.map (fun t -> t.Text)

    /// `C.Foo` where C names a type: a static member, so no receiver.
    /// `C(args).Foo` is NOT static — the call built an instance, and seeing
    /// through it here silently dropped the receiver. Only a pure type
    /// application (`Comparer<int>.Instance`) is looked through.
    let isStaticUse (n : GreenNode) : bool =
        let rec headIdent (h : GreenNode) =
            if h.NodeKind = IdentExpr then
                h.Children |> List.tryPick (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
            elif h.NodeKind = AppExpr
                 && (h.Children
                     |> List.forall (fun c ->
                         match c with
                         | GNode m -> m.NodeKind = IdentExpr || m.NodeKind = TyParams
                         | GToken _ -> true)) then
                match h.Children |> List.tryPick (fun c -> match c with GNode m -> Some m | _ -> None) with
                | Some inner -> headIdent inner
                | None -> None
            else None
        match n.Children |> List.tryPick (fun c -> match c with GNode m -> Some m | _ -> None) with
        | Some head ->
            (match headIdent head with
             | Some t -> (dictTryFind useDefs t.Offset |> Option.map (fun d -> d.Kind = Resolve.DefType)) = Some true
             | None -> false)
        | None -> false

    /// The member a dot-access binds to, if inference typed its receiver.
    let memberAt (t : Token) : (string * Resolve.Definition) option =
        match dictTryFind memberSites t.Offset with
        | Some owner ->
            // "HashMap#2" names the second OVERLOAD of the member on
            // HashMap; the ordinal composes into the index key
            let hash = owner.IndexOf "#"
            let key =
                if hash < 0 then owner + "." + t.Text
                else owner.Substring (0, hash) + "." + t.Text + owner.Substring hash
            let plainOwner = if hash < 0 then owner else owner.Substring (0, hash)
            (match dictTryFind memberIndex key with
             | Some d -> Some (plainOwner, d)
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
    /// The label of a record-literal field. It may be qualified with the
    /// owning type or module (`{ Classes.MPath = p; ... }`), in which case
    /// the label is the LAST identifier before the '=', not the first.
    let recordFieldLabel (f : GreenNode) =
        let mutable found = None
        let mutable stop = false
        for t in tokensOf f do
            if not stop then
                if t.Kind = Operator && t.Text = "=" then stop <- true
                elif t.Kind = Ident then found <- Some t
        found
    let offsetOf (n : GreenNode) =
        match Green.tokens (GNode n) |> List.tryHead with
        | Some t -> t.Offset
        | None -> 0

    let isPatKind (k : NodeKind) =
        k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat || k = StructTuplePat
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat || k = TypeTestPat
        || k = SplicePat
    let isTypeKind (k : NodeKind) =
        k = NamedType || k = VarType || k = AnonType || k = TupleType || k = StructTupleType
        || k = FunType || k = AppType || k = PostfixType || k = ParenType
        // `%t` in type position is a type node like any other
        || k = SpliceType
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

    /// The callee for a member bound at `t`: a member of a generic class is a
    /// generic function, so the instantiation recorded at the use site has to
    /// travel with it for the linker to stamp.
    let memberFn (t : Token) (d : Resolve.Definition) : Expr =
        match dictTryFind instSites t.Offset with
        | Some inst when
             not (List.isEmpty inst)
             && (if d.Path = path then (dictTryFind topLevelDefs d.Offset).IsSome else true) ->
            EVarI (varIdOf d, schemeOf d, inst)
        | _ -> EVar (varIdOf d, schemeOf d)

    /// `recv.[i]` on a type that declares `Item`. Inference bound the access
    /// at a synthetic offset off the bracket token — there is no `Item` token
    /// to key on — the way the for-in protocol binds its three members.
    let indexerTok (base_ : int) (name : string) (br : Token) : Token =
        { Kind = Ident; Text = name; Leading = []; Trailing = []; Offset = base_ + br.Offset }

    // ---- patterns ---------------------------------------------------------

    /// The identifier a pattern is NAMED by. A qualified case
    /// (`Classes.Improve inst`) is named by its LAST segment — the leading
    /// spine is a module, and that is also where resolution recorded it.
    let patHeadToken (n : GreenNode) : Token option =
        let idents = tokensOf n |> List.filter (fun t -> t.Kind = Ident)
        if tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = ".") then
            List.tryLast idents
        else List.tryHead idents

    let anonScheme = mono (TCon ("?", []))

    /// Every alternative of an or-pattern binds the SAME variables (F#
    /// requires the same names in each), but each writes its own binder, so
    /// each got its own VarId — and the body, which resolves to the FIRST,
    /// then read a local that the matching alternative never wrote. Aliasing
    /// the later alternatives onto the first's identities by NAME is what
    /// makes `| A n | B n -> n` bind one `n`. By name, not position: in
    /// `| TVar v, other | other, TVar v ->` the binders swap sides.
    let alignOrBinders (alts : Pat list) : Pat list =
        let rec binders (p : Pat) : (string * (VarId * Scheme)) list =
            match p with
            | PVar (v, sch) -> [ v.Name, (v, sch) ]
            | PAs (inner, v, sch) -> (v.Name, (v, sch)) :: binders inner
            | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.collect binders ps
            | PCons (h, t) -> binders h @ binders t
            | PWild | PLit _ | PTypeTest _ -> []
        match alts with
        | [] | [ _ ] -> alts
        | _ ->
            // canonical identity comes from the LAST alternative: the
            // resolver walks the alternatives in order and each shadows the
            // previous, so that is the one the body's uses resolve to
            let canon = dictNew<string, VarId * Scheme> ()
            for name, b in binders (List.last alts) do
                if (dictTryFind canon name).IsNone then dictSet canon name b
            let rec rename (p : Pat) : Pat =
                match p with
                | PVar (v, sch) ->
                    (match dictTryFind canon v.Name with
                     | Some (cv, csch) -> PVar (cv, csch)
                     | None -> PVar (v, sch))
                | PAs (inner, v, sch) ->
                    (match dictTryFind canon v.Name with
                     | Some (cv, csch) -> PAs (rename inner, cv, csch)
                     | None -> PAs (rename inner, v, sch))
                | PCtor (n, sch, ps) -> PCtor (n, sch, List.map rename ps)
                | PTuple ps -> PTuple (List.map rename ps)
                | PListLit ps -> PListLit (List.map rename ps)
                | POr ps -> POr (List.map rename ps)
                | PCons (h, t) -> PCons (rename h, rename t)
                | other -> other
            List.map rename alts

    let rec lowerPat (n : GreenNode) : Pat =
        match n.NodeKind with
        | WildcardPat -> PWild
        | LiteralPat ->
            (match tokensOf n |> List.tryLast |> Option.bind litOf with
             | Some l -> PLit l
             | None -> PWild)
        | IdentPat ->
            (match patHeadToken n with
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
                     match patHeadToken head |> Option.bind (fun t -> dictTryFind useDefs t.Offset) with
                     | Some d -> d.Name, schemeOf d
                     | None -> "?", mono (TCon ("?", []))
                 PCtor (ctorName, ctorSch, args |> List.filter (fun m -> isPatKind m.NodeKind) |> List.map lowerPat)
             | [] -> PWild)
        | TypeTestPat ->
            (match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) |> Option.bind ifaceNameOf with
             | Some tn -> PTypeTest tn
             | None -> PWild)
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
             | many when hasBar -> POr (alignOrBinders (List.map lowerPat many))
             | many -> PTuple (List.map lowerPat many))
        | AsPat ->
            (match nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) with
             | [ inner; namePat ] ->
                 (match tokensOf namePat |> List.tryFind (fun t -> t.Kind = Ident) |> Option.bind (fun t -> dictTryFind defsAt t.Offset) with
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

    /// Curried parameter lowering: every parameter keeps its own binder, and a
    /// structured one destructures a synthetic argument inside the body. Unlike
    /// `paramBinds` this never collapses `fun i (a, b) -> ..` into a single
    /// tupled argument, so the arity survives into the core term.
    let paramBindsCurried (pats : GreenNode list) (body : Expr) : (VarId * Scheme) list * Expr =
        let mutable bodyW = body
        let binds =
            pats
            |> List.map (fun p ->
                match lowerPat p with
                | PVar (v, s) -> v, s
                | PLit LUnit -> { Path = path; Offset = offsetOf p; Name = "_unit" }, mono tUnit
                | other ->
                    let arg = { Path = path; Offset = offsetOf p + 660000; Name = "_arg" }
                    let sch = mono (TCon ("?", []))
                    bodyW <- EMatch (EVar (arg, sch), [ other, None, bodyW ])
                    arg, sch)
        binds, bodyW

    /// One slot per element of a `struct(...)` pattern, in source order:
    /// `Some binder` for a named element, `None` for a wildcard or literal.
    /// The POSITION is what names the field, so a dropped element still
    /// takes its slot.
    let structSlots (p : GreenNode) : (VarId * Scheme) option list =
        let rec unwrap (m : GreenNode) =
            if m.NodeKind = ParenPat || m.NodeKind = TuplePat then
                nodesOf m |> List.filter (fun x -> isPatKind x.NodeKind) |> List.collect unwrap
            else [ m ]
        nodesOf p
        |> List.filter (fun m -> isPatKind m.NodeKind)
        |> List.collect unwrap
        |> List.map (fun m ->
            Green.tokens (GNode m)
            |> List.filter (fun t -> t.Kind = Ident)
            |> List.tryHead
            |> Option.bind (fun t -> dictTryFind defsAt t.Offset)
            |> Option.map (fun d -> varIdOf d, schemeOf d))

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
                     (match dictTryFind classUses t.Offset with
                      // a class member (`Zero`) is a name for whatever the
                      // selected instance provides
                      | Some im ->
                          let r = classRef im
                          if im.MTakesUnit then EApp (r, [ ELit LUnit ]) else r
                      | None ->
                     match dictTryFind classPending t.Offset with
                      // not resolved yet: the operand type is a variable of
                      // the enclosing binding, which stamping will fix
                      | Some payload -> EUnknown ("$class:" + payload)
                      | None ->
                     match dictTryFind useDefs t.Offset with
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
                                // another file's top-level binding is just as
                                // stampable — Link sees the whole program, so
                                // the demand is meaningful across files
                                && (if d.Path = path then (dictTryFind topLevelDefs d.Offset).IsSome else true) ->
                               EVarI (varIdOf d, schemeOf d, inst)
                           | _ -> EVar (varIdOf d, schemeOf d))
                      | None -> EUnknown t.Text)
                 | None -> note (offsetOf n) "type-variable expression")
            // a numeric conversion carries the source kind inference found
            | AppExpr when
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | head :: [ _ ] when head.NodeKind = IdentExpr ->
                     (match tokensOf head |> List.tryHead with
                      | Some t ->
                          List.contains t.Text [ "int"; "int64"; "uint32"; "float"; "float32"; "float16"; "string"; "char"; "byte"; "sbyte" ]
                          && (dictTryFind useDefs t.Offset).IsNone
                      | None -> false)
                 | _ -> false) ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | [ head; a ] ->
                     let t = (tokensOf head |> List.head)
                     // no entry means the source is int, which is the kind
                     // OpKinds leaves out
                     let k = match dictTryFind opKinds t.Offset with Some x -> x | None -> ""
                     EApp (EUnknown (t.Text + "#" + k), [ lowerExpr (GNode a) ])
                 | _ -> note (offsetOf n) "conversion shape")
            | AppExpr when
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | head :: [ _ ] when head.NodeKind = IdentExpr ->
                     (match tokensOf head |> List.tryHead with
                      | Some t ->
                          t.Text = "print"
                          && (match dictTryFind opKinds t.Offset with
                              | Some "w" | Some "h" | Some "b" | Some "c" -> true
                              | _ -> false)
                      | None -> false)
                 | _ -> false) ->
                // an unsigned value prints unsigned
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | [ head; a ] ->
                     let t = (tokensOf head |> List.head)
                     let fn =
                         match dictTryFind opKinds t.Offset with
                         | Some "h" -> "printh"
                         | Some "b" -> "printb"
                         | Some "c" -> "printc"
                         | _ -> "printu"
                     EApp (EUnknown fn, [ lowerExpr (GNode a) ])
                 | _ -> note (offsetOf n) "print shape")
            | AppExpr when
                // the printf family, fully applied: flatten the curried
                // spine down to the ident and expand at COMPILE TIME
                (let rec spineHead (m : GreenNode) =
                    match nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) with
                    | h :: _ when h.NodeKind = AppExpr -> spineHead h
                    | h :: _ when h.NodeKind = IdentExpr -> Some h
                    | _ -> None
                 match spineHead n with
                 | Some h ->
                     (match tokensOf h |> List.tryHead with
                      | Some t ->
                          List.contains t.Text [ "sprintf"; "printf"; "printfn"; "failwithf" ]
                          && (dictTryFind useDefs t.Offset).IsNone
                      | None -> false)
                 | None -> false) ->
                // collect the argument spine innermost-first
                let rec collect (m : GreenNode) (acc : GreenNode list) : GreenNode list =
                    match nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) with
                    | h :: rest when h.NodeKind = AppExpr -> collect h (rest @ acc)
                    | _ :: rest -> rest @ acc
                    | [] -> acc
                let allArgs = collect n []
                let headIdent =
                    let rec sh (m : GreenNode) =
                        match nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) with
                        | h :: _ when h.NodeKind = AppExpr -> sh h
                        | h :: _ -> h
                        | [] -> m
                    sh n
                let fn = (tokensOf headIdent |> List.head).Text
                (match allArgs with
                 | fmtArg :: holeArgs ->
                     (match Green.tokens (GNode fmtArg) |> List.tryHead with
                      | Some ft when ft.Kind = StringLit ->
                          let raw = ft.Text.Substring (1, ft.Text.Length - 2)
                          (match Fpp.Analysis.Format.parse raw with
                           | Ok segs ->
                               let holes = Fpp.Analysis.Format.holes segs
                               if List.length holes < List.length holeArgs then
                                   note (offsetOf n) "more arguments than the format has holes"
                               else
                               // PARTIAL application expands to a lambda:
                               // `Seq.map (sprintf "%A")` is ordinary F#
                               let missing = List.length holes - List.length holeArgs
                               let lamBinds =
                                   List.init missing (fun i ->
                                       { Path = path; Offset = offsetOf n + 7000000 + i; Name = "_fmt" + string i },
                                       mono (TCon ("?", [])))
                               let kindAt (i : int) =
                                   match dictTryFind opKinds (ft.Offset + 1 + i) with
                                   | Some k -> k
                                   | None -> ""
                               // the one-character string holding a double
                               // quote: its literal token is "\""
                               let dquote = ELit (LString "\"\\\"\"")
                               let quoted (e : Expr) =
                                   EPrim ("+t", [ EPrim ("+t", [ dquote; e ]); dquote ])
                               let boolWords lower =
                                   if lower then "\"true\"", "\"false\"" else "\"True\"", "\"False\""
                               let render (i : int) (c : char) (e : Expr) : Expr =
                                   let k = kindAt i
                                   match c with
                                   | 's' -> e
                                   | 'c' -> EApp (EUnknown "string#c", [ e ])
                                   | 'b' ->
                                       let tw, fw = boolWords true
                                       EIf (e, ELit (LString tw), ELit (LString fw))
                                   | 'x' | 'X' | 'o' ->
                                       let fn =
                                           (if c = 'x' then "hexlower" elif c = 'X' then "hexupper" else "octal")
                                           + (if k = "l" then "64" else "")
                                       EApp (EUnknown fn, [ e ])
                                   | 'f' -> EApp (EUnknown "fixed6", [ e ])
                                   | 'u' ->
                                       (match k with
                                        | "l" -> EApp (EUnknown "string#l", [ e ])
                                        | _ -> EApp (EUnknown "string#w", [ e ]))
                                   | 'A' ->
                                       (match k with
                                        | "t" -> quoted e
                                        | "b" ->
                                            let tw, fw = boolWords true
                                            EIf (e, ELit (LString tw), ELit (LString fw))
                                        | "c" ->
                                            EPrim ("+t", [ EPrim ("+t", [ ELit (LString "\"'\""); EApp (EUnknown "string#c", [ e ]) ])
                                                           ELit (LString "\"'\"") ])
                                        | "f" | "s" | "l" | "w" | "h" -> EApp (EUnknown ("string#" + k), [ e ])
                                        // int and statically-unknown share "":
                                        // the runtime dispatch answers both
                                        | _ -> EApp (EUnknown "showv", [ e ]))
                                   | _ ->   // d, i
                                       EApp (EUnknown ("string#" + k), [ e ])
                               let mutable hi = 0
                               let pieces =
                                   segs |> List.map (fun seg ->
                                       match seg with
                                       | Fpp.Analysis.Format.Text t2 -> ELit (LString ("\"" + t2 + "\""))
                                       | Fpp.Analysis.Format.Hole (c, width, zero, left) ->
                                           let e =
                                               if hi < List.length holeArgs then
                                                   lowerExpr (GNode (List.item hi holeArgs))
                                               else
                                                   let v, sch = List.item (hi - List.length holeArgs) lamBinds
                                                   EVar (v, sch)
                                           let r = render hi c e
                                           hi <- hi + 1
                                           if width = 0 then r
                                           else
                                               // pad to the minimum width;
                                               // zeros only make sense on the
                                               // right-justified numeric side
                                               let mode =
                                                   if left then "padl"
                                                   elif zero then "pad0"
                                                   else "padr"
                                               EApp (EUnknown (mode + "#" + string width), [ r ]))
                               let total =
                                   match pieces with
                                   | [] -> ELit (LString "\"\"")
                                   | first :: rest -> List.fold (fun acc p -> EPrim ("+t", [ acc; p ])) first rest
                               let whole =
                                   match fn with
                                   | "sprintf" -> total
                                   | "printf" -> EApp (EUnknown "prints", [ total ])
                                   | "printfn" -> EApp (EUnknown "prints", [ EPrim ("+t", [ total; ELit (LString "\"\\n\"") ]) ])
                                   | _ -> EApp (EUnknown "failwith", [ total ])
                               if missing = 0 then whole else ELam (lamBinds, whole)
                           | Error msg -> note ft.Offset msg)
                      | _ -> note (offsetOf n) "a format string must be a literal")
                 | [] -> note (offsetOf n) "format application shape")
            | AppExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | head :: args ->
                     // `f<T> x` nests as `(f<T>) x`; the type application is
                     // inference's business and already spent, so the HEAD for
                     // lowering is the plain callee — otherwise the builtin
                     // and member special cases below never see their shape
                     let head =
                         if head.NodeKind = AppExpr
                            && (nodesOf head |> List.exists (fun x -> x.NodeKind = TyParams))
                            && (nodesOf head |> List.filter (fun x -> isExprish x.NodeKind) |> List.length) = 1 then
                             (nodesOf head |> List.filter (fun x -> isExprish x.NodeKind)).Head
                         else head
                     let f = lowerExpr (GNode head)
                     let loweredArgs = args |> List.map (fun a -> lowerExpr (GNode a))
                     // a type with several constructors: inference chose one
                     let overloaded =
                         let ctorHead =
                             if head.NodeKind = IdentExpr then Some head
                             elif head.NodeKind = AppExpr
                                  && (nodesOf head |> List.exists (fun x -> x.NodeKind = TyParams)) then
                                 nodesOf head |> List.tryFind (fun x -> x.NodeKind = IdentExpr)
                             else None
                         match ctorHead with
                         | None -> None
                         | Some head ->
                             match tokensOf head |> List.tryFind (fun t -> t.Kind = Ident) with
                             | Some ht ->
                                 (match dictTryFind ctorSites ht.Offset with
                                  | Some coff -> dictTryFind defsAt coff
                                  | None -> None)
                             | None -> None
                     // a BUILTIN member on `string`: no definition to call,
                     // it emits as a $str primitive. The member site names
                     // the owner ("string", or "string#2" for the second
                     // overload), and the ordinal picks the primitive.
                     let stringBuiltin =
                         if head.NodeKind <> DotExpr then None
                         else
                             match Green.tokens (GNode head) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                             | Some t ->
                                 (match dictTryFind memberSites t.Offset with
                                  | Some owner when owner = "string" || owner.StartsWith "string#" ->
                                      let ord = if owner = "string" then "" else owner.Substring (owner.IndexOf "#")
                                      (match nodesOf head |> List.tryHead with
                                       | Some recv -> Some ("$str." + t.Text + ord, lowerExpr (GNode recv))
                                       | None -> None)
                                  | _ -> None)
                             | None -> None
                     match stringBuiltin with
                     | Some (prim, recv) ->
                         // a 2-argument .NET call passes a TUPLE; flatten it
                         // so the primitive sees plain operands
                         let flat =
                             loweredArgs
                             |> List.collect (fun a -> match a with ETuple xs -> xs | ELit LUnit -> [] | x -> [ x ])
                         EApp (EUnknown prim, recv :: flat)
                     | None ->
                     match overloaded with
                     | Some cd -> EApp (EVar (varIdOf cd, schemeOf cd), loweredArgs)
                     | None ->
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
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ pa ] when bv.Name = "pin" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          EArrayPin (nm, pa)
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ pa ] when bv.Name = "unpin" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          EArrayUnpin (nm, pa)
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ pa ] when bv.Name = "byteSize" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          EArrayBytes (nm, pa)
                      // box/unbox are type-level: every value is already a
                      // reference, so both are the identity at runtime
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ bx ] when
                            (bv.Name = "box" || bv.Name = "unbox" || bv.Name = "float16Bits")
                            && bv.Path = "(builtin)" -> bx
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ bx ] when
                            (bv.Name = "doubleBits" || bv.Name = "singleBits")
                            && bv.Path = "(builtin)" ->
                          // NOT identity: the float is boxed, the bits are an
                          // integer — the emitters reinterpret
                          EApp (EUnknown bv.Name, [ bx ])
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ sx ] when
                            (bv.Name = "stackDepth" || bv.Name = "stackFrame")
                            && bv.Path = "(builtin)" ->
                          // the shadow stack: a global read, not an import
                          EApp (EUnknown bv.Name, [ sx ])
                      // raw linear memory: single instructions, not imports.
                      // Every one of these is `mem`-prefixed in the prelude
                      // precisely so this rule can claim them as a family.
                      | (EVar (bv, _) | EVarI (bv, _, _)), margs when
                            bv.Path = "(builtin)" && bv.Name.StartsWith "mem"
                            && (bv.Name = "memAlloc" || bv.Name = "memSize" || bv.Name = "memCopy"
                                || bv.Name.StartsWith "memLoad" || bv.Name.StartsWith "memStore") ->
                          EApp (EUnknown bv.Name, margs)
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ ss; sst; sln ] when bv.Name = "strsub" && bv.Path = "(builtin)" ->
                          // the string slice: a primitive, not an FFI import
                          EApp (EUnknown "strsub", [ ss; sst; sln ])
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ cn ] when bv.Name = "zeroCreate" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          // the zero value is per-representation, so the
                          // marker survives to the emitter, which knows it
                          EArrayCreate (nm, cn, EUnknown "$zero")
                      | (EVar (bv, _) | EVarI (bv, _, _)), [ cn; cv ] when bv.Name = "create" && bv.Path = "(builtin)" ->
                          let nm =
                              match dictTryFind arrKinds (offsetOf n) with
                              | Some x -> x
                              | None -> ""
                          EArrayCreate (nm, cn, cv)
                      // System.Object.ReferenceEquals(a, b): the identity
                      // primitive, however the namespace is spelled
                      | EField (EField (EUnknown "System", "Object", _), "ReferenceEquals", _), [ ETuple [ ra; rb ] ]
                      | EField (EUnknown "Object", "ReferenceEquals", _), [ ETuple [ ra; rb ] ] ->
                          EApp (EUnknown "refEq", [ ra; rb ])
                      // `obj.Equals (a, b)` is .NET's STRUCTURAL comparison,
                      // which is what `=` already means here — including on
                      // arrays, where both compare by reference
                      | EField (EField (EUnknown "System", "Object", _), "Equals", _), [ ETuple [ ra; rb ] ]
                      | EField (EUnknown "Object", "Equals", _), [ ETuple [ ra; rb ] ]
                      | EField (EUnknown "obj", "Equals", _), [ ETuple [ ra; rb ] ] ->
                          EPrim ("=", [ ra; rb ])
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
                          // `recv.[i] <- v` calls the indexer's setter, bound
                          // at the bracket's synthetic offset. Decided FIRST:
                          // the property path keys on the last identifier in
                          // the target, which for an index target is part of
                          // the index expression
                          let indexSetter =
                              match nodesOf l with
                              | [ recv; ix ] when l.NodeKind = DotExpr && ix.NodeKind = ListExpr ->
                                  (match Green.tokens (GNode ix) |> List.tryHead with
                                   | Some br ->
                                       let t = indexerTok 70000000 "set_Item" br
                                       (match memberAt t, nodesOf ix |> List.filter (fun m -> isExprish m.NodeKind) with
                                        | Some (_, d), [ i ] ->
                                            Some (memberFn t d, lowerExpr (GNode recv), lowerExpr (GNode i))
                                        | _ -> None)
                                   | None -> None)
                              | _ -> None
                          // `recv.P <- v` calls the property's setter
                          let propSetter =
                              if l.NodeKind <> DotExpr || indexSetter.IsSome then None
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
                          (match indexSetter with
                           | Some (fn, recv, i) -> EApp (fn, [ recv; i; lowerExpr (GNode r) ])
                           | None ->
                          match propSetter with
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
                      // f >> g  ==  fun x -> g (f x)   (and << the other way)
                      | ">>" | "<<" ->
                          let first, second =
                              if op.Text = ">>" then lowerExpr (GNode l), lowerExpr (GNode r)
                              else lowerExpr (GNode r), lowerExpr (GNode l)
                          let arg = { Path = path; Offset = offsetOf n + 660000; Name = "_cx" }
                          let sch = mono (TCon ("?", []))
                          ELam ([ arg, sch ], EApp (second, [ EApp (first, [ EVar (arg, sch) ]) ]))
                      | _ ->
                          // typed prims: inference resolved the operand kind
                          // (equality stays unsuffixed — structural $equal)
                          let suffixable =
                              List.contains op.Text
                                  [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="
                                    // unsigned shifts/division differ from signed
                                    ">>>"; "&&&"; "|||"; "^^^"; "<<<" ]
                          let suffix =
                              if not suffixable then
                                  // EQUALITY types too, where the operand kind
                                  // resolved: a scalar or string `=` compiles
                                  // to the machine instruction (or a byte
                                  // compare) instead of structural $equal.
                                  // Halves must not fall through either:
                                  // comparing the i31 BIT PATTERN makes
                                  // -0.0h <> 0.0h and nan_h = nan_h
                                  if op.Text = "=" || op.Text = "<>" then
                                      match dictTryFind opKinds op.Offset with
                                      | Some "h" -> "h"
                                      | Some "t" -> "t"
                                      | Some "l" -> "l"
                                      | Some "f" -> "f"
                                      | Some "s" -> "s"
                                      | Some "w" | Some "b" | Some "c" -> "i"
                                      | _ ->
                                          match dictTryFind opTypes op.Offset with
                                          | Some "int" | Some "bool" | Some "char" -> "i"
                                          // a type variable or user type:
                                          // resolved after stamping, exactly
                                          // like the arithmetic suffixes —
                                          // this is what specializes the
                                          // GENERIC dict probe's key compare
                                          | Some t when t <> "" -> "@" + t
                                          | _ -> ""
                                  else ""
                              else
                                  match dictTryFind opKinds op.Offset with
                                  // bool and char exist for conversions and
                                  // print only; as operands they are ints
                                  | Some "b" | Some "c" -> ""
                                  | Some k -> k
                                  | None ->
                                      // no primitive kind: either a type
                                      // variable of the enclosing binding, or
                                      // a type whose instance carries a body.
                                      // Both are named, and resolved after
                                      // monomorphization has made them
                                      // concrete.
                                      match dictTryFind opTypes op.Offset with
                                      | Some t when t <> "" && t <> "int" && t <> "char" && t <> "bool" ->
                                          "@" + t
                                      | _ -> ""
                          // an operator whose instance has a body is an
                          // ordinary call to that body
                          match dictTryFind classUses op.Offset with
                          | Some im ->
                              let call =
                                  EApp (classRef im, [ lowerExpr (GNode l); lowerExpr (GNode r) ])
                              // ordering has ONE operation: the predicates are
                              // notation for a test on its result
                              if im.MName = "compare" then EPrim (op.Text, [ call; ELit (LInt "0") ])
                              else call
                          | None ->
                              EPrim (op.Text + suffix, [ lowerExpr (GNode l); lowerExpr (GNode r) ]))
                 | _ -> note (offsetOf n) "operator shape")
            | PrefixExpr when (match tokensOf n |> List.tryHead with
                               | Some t -> t.Kind = Keyword && t.Text = "yield"
                               | None -> false) && compAcc.IsSome ->
                let acc = compAcc.Value
                let bang = tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = "!")
                let value =
                    match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                    | [ e ] -> lowerExpr (GNode e)
                    | _ -> ELit LUnit
                if not bang then
                    // the accumulator is built REVERSED and turned around once
                    EAssign (acc, EPrim ("::", [ value; EVar (acc, anonScheme) ]))
                else
                    // `yield!` splices a list: walk it and push each element,
                    // which keeps the single reversal at the end correct
                    let off = offsetOf n
                    let rv = { Path = path; Offset = off + 16000000; Name = "_yrest" }
                    let hv = { Path = path; Offset = off + 17000000; Name = "_yh" }
                    let tv = { Path = path; Offset = off + 18000000; Name = "_yt" }
                    let notNull (e : Expr) =
                        EIf (EApp (EUnknown "isNull", [ e ]), ELit (LBool false), ELit (LBool true))
                    ELet (false, rv, anonScheme, value,
                      EWhile (notNull (EVar (rv, anonScheme)),
                        EMatch (EVar (rv, anonScheme),
                          [ PCons (PVar (hv, anonScheme), PVar (tv, anonScheme)), None,
                              ESeq [ EAssign (acc, EPrim ("::", [ EVar (hv, anonScheme); EVar (acc, anonScheme) ]))
                                     EAssign (rv, EVar (tv, anonScheme)) ]
                            PWild, None, ELit LUnit ])))
            | PrefixExpr ->
                (match tokensOf n |> List.tryHead, nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | Some op, [ a ] when op.Text = "-" || op.Text = "not" || op.Text = "~~~" ->
                     let suffix =
                         match dictTryFind opKinds op.Offset with
                         | Some "b" | Some "c" -> ""
                         | Some k -> k
                         | None ->
                             // as for a binary operator: a type variable or a
                             // user instance, both resolved after stamping
                             match dictTryFind opTypes op.Offset with
                             | Some t when t <> "" && t <> "int" && t <> "char" && t <> "bool" -> "@" + t
                             | _ -> ""
                     match dictTryFind classUses op.Offset with
                     | Some im ->
                         EApp (classRef im, [ lowerExpr (GNode a) ])
                     | None -> EPrim ("u" + op.Text + suffix, [ lowerExpr (GNode a) ])
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
            | QuoteExpr ->
                // The body was type checked in place; what survives to run time
                // is the code AS A TREE. A splice contributes the Code value it
                // denotes — a subtree, not text — so nothing is re-parsed and
                // composition cannot be reinterpreted by precedence.
                let str (t : string) = ELit (LString ("\"" + t.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""))
                // a case with several payload fields takes them as ONE tuple
                let ctor (name : string) (args : Expr list) =
                    match args with
                    | [] | [ _ ] -> ECtor (name, mono (TCon ("CodeTree", [])), args)
                    | many -> ECtor (name, mono (TCon ("CodeTree", [])), [ ETuple many ])
                // HYGIENE: every binder inside a quotation is renamed to a name
                // unique to this quotation site, and references to it inside
                // the same quotation follow the rename. A spliced tree brings
                // its own free names, which therefore cannot be captured by a
                // binder that happens to share their spelling.
                let renames = dictNew<string, string> ()
                let fresh (nm : string) (off : int) =
                    // `_q` and not `#`: a renamed binder has to stay a legal
                    // identifier, or rendered code would not parse back
                    let unique = nm + "_q" + string off
                    dictSet renames nm unique
                    unique
                let seen (nm : string) =
                    match dictTryFind renames nm with
                    | Some u -> u
                    | None -> nm
                let rec quote (m : GreenNode) : Expr =
                    let kids = nodesOf m |> List.filter (fun x -> isExprish x.NodeKind)
                    match m.NodeKind with
                    | SpliceExpr ->
                        // the spliced value is a typed handle; its TREE goes in
                        (match kids with
                         | inner :: _ -> EField (lowerExpr (GNode inner), "Raw", "Code")
                         | [] -> note (offsetOf m) "empty splice")
                    | ParenExpr ->
                        (match kids with
                         | inner :: _ -> quote inner
                         | [] -> note (offsetOf m) "empty parentheses in a quotation")
                    | LiteralExpr ->
                        (match tokensOf m |> List.tryHead with
                         | Some t when t.Kind = IntLit -> ctor "CInt" [ ELit (LInt t.Text) ]
                         | Some t when t.Kind = StringLit -> ctor "CStr" [ ELit (LString t.Text) ]
                         | Some t when t.Text = "true" -> ctor "CBool" [ ELit (LBool true) ]
                         | Some t when t.Text = "false" -> ctor "CBool" [ ELit (LBool false) ]
                         | _ -> note (offsetOf m) "literal not quotable")
                    | IdentExpr ->
                        (match tokensOf m |> List.tryHead with
                         | Some t -> ctor "CName" [ str (seen t.Text) ]
                         | None -> note (offsetOf m) "name not quotable")
                    | BinaryExpr ->
                        let op = tokensOf m |> List.tryFind (fun t -> t.Kind = Operator)
                        (match op, kids with
                         | Some o, [ l; r ] -> ctor "CBin" [ str o.Text; quote l; quote r ]
                         | _ -> note (offsetOf m) "operator not quotable")
                    | AppExpr ->
                        (match kids with
                         | f :: args -> ctor "CApp" [ quote f; EListLit (List.map quote args) ]
                         | [] -> note (offsetOf m) "empty application")
                    | IfExpr ->
                        (match kids with
                         | [ c; t; e ] -> ctor "CIf" [ quote c; quote t; quote e ]
                         | _ -> note (offsetOf m) "an `if` in a quotation needs an `else`")
                    | MemberDecl ->
                        // `<@ member x.Bla (a : %t) : %r = ... @>`
                        let idents = Green.tokens (GNode m) |> List.filter (fun t -> t.Kind = Ident)
                        let pats =
                            nodesOf m |> List.filter (fun x -> x.NodeKind = IdentPat || x.NodeKind = ParenPat)
                        let value = nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) |> List.tryLast
                        let retTy = nodesOf m |> List.filter (fun x -> isTypeKind x.NodeKind) |> List.tryHead
                        let nameOf (x : GreenNode) =
                            match Green.tokens (GNode x) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead with
                            | Some t -> t.Text
                            | None -> "_"
                        // `member x.Bla` — the receiver, then the member name
                        (match idents, value with
                         | selfTok :: nameTok :: _, Some v ->
                             let ps =
                                 pats
                                 |> List.map (fun x ->
                                     let ty = nodesOf x |> List.filter (fun y -> isTypeKind y.NodeKind) |> List.tryHead
                                     ETuple [ str (fresh (nameOf x) (offsetOf x)); quoteTy ty ])
                             ctor "CDMember"
                                 [ str selfTok.Text; str nameTok.Text; EListLit ps; quoteTy retTy; quote v ]
                         | _ -> note (offsetOf m) "member quotation needs a receiver, a name and a body")
                    | TypeDecl ->
                        // `<@ type R = { X : %t } @>`
                        let nameTok = Green.tokens (GNode m) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead
                        let fields =
                            nodesOf m
                            |> List.filter (fun x -> x.NodeKind = RecordRepr)
                            |> List.collect nodesOf
                            |> List.filter (fun x -> x.NodeKind = RecordField)
                            |> List.map (fun f ->
                                let fn =
                                    match tokensOf f |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead with
                                    | Some t -> t.Text
                                    | None -> "_"
                                let ft = nodesOf f |> List.filter (fun y -> isTypeKind y.NodeKind) |> List.tryHead
                                ETuple [ str fn; quoteTy ft ])
                        (match nameTok with
                         | Some nt when not (List.isEmpty fields) ->
                             ctor "CDRecord" [ str nt.Text; EListLit fields ]
                         | _ -> note (offsetOf m) "only a record type can be quoted so far")
                    | LetDecl ->
                        // a quotation whose whole body is a `let` is a
                        // DECLARATION quote: `<@ let f (x : %t) : %r = ... @>`
                        let pats =
                            nodesOf m
                            |> List.filter (fun x -> x.NodeKind = IdentPat || x.NodeKind = ParenPat)
                        let value = nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) |> List.tryLast
                        // a bare type child is the RETURN annotation
                        let retTy =
                            nodesOf m |> List.filter (fun x -> isTypeKind x.NodeKind) |> List.tryHead
                        (match pats, value with
                         | nameNode :: paramNodes, Some v ->
                             let nameOf (x : GreenNode) =
                                 match Green.tokens (GNode x) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead with
                                 | Some t -> t.Text
                                 | None -> "_"
                             let ps =
                                 paramNodes
                                 |> List.map (fun x ->
                                     let ty =
                                         nodesOf x |> List.filter (fun y -> isTypeKind y.NodeKind) |> List.tryHead
                                     ETuple [ str (fresh (nameOf x) (offsetOf x)); quoteTy ty ])
                             ctor "CDLet" [ str (nameOf nameNode); EListLit ps; quoteTy retTy; quote v ]
                         | _ -> note (offsetOf m) "declaration quotation must bind a name")
                    | BlockExpr ->
                        // `let n = v` then the rest
                        (match nodesOf m with
                         | d :: rest when d.NodeKind = LetDecl && (rest |> List.exists (fun x -> isExprish x.NodeKind)) ->
                             let nameTok =
                                 nodesOf d
                                 |> List.tryFind (fun x -> x.NodeKind = IdentPat)
                                 |> Option.bind (fun x -> tokensOf x |> List.tryHead)
                             let value = nodesOf d |> List.filter (fun x -> isExprish x.NodeKind) |> List.tryLast
                             let body = rest |> List.filter (fun x -> isExprish x.NodeKind) |> List.tryHead
                             (match nameTok, value, body with
                              | Some nt, Some v, Some b ->
                                  // the value cannot see the binder; the body can
                                  let qv = quote v
                                  let unique = fresh nt.Text nt.Offset
                                  ctor "CLet" [ str unique; qv; quote b ]
                              | _ -> note (offsetOf m) "let in a quotation must bind a name to a value")
                         | [ only ] when only.NodeKind = LetDecl -> quote only
                         | inner :: _ when isExprish inner.NodeKind -> quote inner
                         | _ -> note (offsetOf m) "block not quotable")
                    | TupleExpr -> ctor "CTuple" [ EListLit (List.map quote kids) ]
                    | ListExpr ->
                        // items arrive wrapped in a BlockExpr when separated
                        let items =
                            match kids with
                            | [ single ] when single.NodeKind = BlockExpr ->
                                nodesOf single |> List.filter (fun x -> isExprish x.NodeKind)
                            | other -> other
                        ctor "CList" [ EListLit (List.map quote items) ]
                    | LambdaExpr ->
                        let ps =
                            nodesOf m
                            |> List.filter (fun x -> x.NodeKind = IdentPat)
                            |> List.map (fun x ->
                                match tokensOf x |> List.tryHead with
                                | Some t -> str (fresh t.Text t.Offset)
                                | None -> str "_")
                        (match List.tryLast kids with
                         | Some body -> ctor "CLam" [ EListLit ps; quote body ]
                         | None -> note (offsetOf m) "lambda without a body")
                    | DotExpr ->
                        let fieldTok = tokensOf m |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                        (match kids, fieldTok with
                         | recv :: _, Some ft -> ctor "CField" [ quote recv; str ft.Text ]
                         | _ -> note (offsetOf m) "field access not quotable")
                    | MatchExpr ->
                        let clauses = nodesOf m |> List.filter (fun x -> x.NodeKind = MatchClause)
                        (match kids with
                         | scrut :: _ ->
                             let arms =
                                 clauses
                                 |> List.map (fun cl ->
                                     let pat = nodesOf cl |> List.tryFind (fun x -> isPatKind x.NodeKind)
                                     let body = nodesOf cl |> List.filter (fun x -> isExprish x.NodeKind) |> List.tryLast
                                     match pat, body with
                                     | Some p, Some b -> ETuple [ quotePat p; quote b ]
                                     | _ -> note (offsetOf cl) "match clause not quotable")
                             ctor "CMatch" [ quote scrut; EListLit arms ]
                         | [] -> note (offsetOf m) "match without a scrutinee")
                    | k -> note (offsetOf m) ("not quotable in <@ @>: " + string k)
                and quoteTy (t : GreenNode option) : Expr =
                    let tctor (name : string) (args : Expr list) =
                        match args with
                        | [] | [ _ ] -> ECtor (name, mono (TCon ("QTy", [])), args)
                        | many -> ECtor (name, mono (TCon ("QTy", [])), [ ETuple many ])
                    match t with
                    | None -> tctor "QTyName" [ str "" ]
                    | Some m ->
                        match m.NodeKind with
                        // `%t` — the spliced value IS the type
                        | SpliceType ->
                            (match nodesOf m |> List.tryFind (fun x -> x.NodeKind = IdentExpr) with
                             | Some idn -> lowerExpr (GNode idn)
                             | None -> note (offsetOf m) "empty type splice")
                        | AppType ->
                            let head =
                                nodesOf m
                                |> List.tryHead
                                |> Option.bind (fun h -> Green.tokens (GNode h) |> List.filter (fun tk -> tk.Kind = Ident) |> List.tryLast)
                            let args = nodesOf m |> List.skip (min 1 (List.length (nodesOf m)))
                            (match head with
                             | Some h ->
                                 tctor "QTyApp" [ str h.Text; EListLit (args |> List.map (fun a -> quoteTy (Some a))) ]
                             | None -> note (offsetOf m) "type not quotable")
                        | _ ->
                            (match Green.tokens (GNode m) |> List.filter (fun tk -> tk.Kind = Ident) |> List.tryLast with
                             | Some tk -> tctor "QTyName" [ str tk.Text ]
                             | None -> note (offsetOf m) "type not quotable")

                and quotePat (m : GreenNode) : Expr =
                    let pctor (name : string) (args : Expr list) =
                        match args with
                        | [] | [ _ ] -> ECtor (name, mono (TCon ("QPat", [])), args)
                        | many -> ECtor (name, mono (TCon ("QPat", [])), [ ETuple many ])
                    match m.NodeKind with
                    // `%p` — the spliced value IS the pattern
                    | SplicePat ->
                        (match nodesOf m |> List.tryFind (fun x -> x.NodeKind = IdentExpr) with
                         | Some idn -> lowerExpr (GNode idn)
                         | None -> note (offsetOf m) "empty pattern splice")
                    | WildcardPat -> pctor "QWild" []
                    | ParenPat ->
                        (match nodesOf m |> List.filter (fun x -> isPatKind x.NodeKind) with
                         | inner :: _ -> quotePat inner
                         | [] -> note (offsetOf m) "empty pattern")
                    | LiteralPat ->
                        (match tokensOf m |> List.tryHead with
                         | Some t when t.Kind = IntLit -> pctor "QInt" [ ELit (LInt t.Text) ]
                         | _ -> note (offsetOf m) "literal pattern not quotable")
                    | IdentPat ->
                        (match tokensOf m |> List.tryHead with
                         // upper case names a case, lower case binds
                         | Some t when t.Text.Length > 0 && System.Char.IsUpper t.Text.[0] ->
                             pctor "QCase" [ str t.Text; EListLit [] ]
                         | Some t -> pctor "QVar" [ str (fresh t.Text t.Offset) ]
                         | None -> note (offsetOf m) "pattern not quotable")
                    | AppPat ->
                        (match nodesOf m |> List.filter (fun x -> isPatKind x.NodeKind) with
                         | head :: args ->
                             let name =
                                 match tokensOf head |> List.tryHead with
                                 | Some t -> t.Text
                                 | None -> "?"
                             pctor "QCase" [ str name; EListLit (List.map quotePat args) ]
                         | [] -> note (offsetOf m) "empty constructor pattern")
                    | k -> note (offsetOf m) ("pattern not quotable in <@ @>: " + string k)
                // the quotation itself is the typed handle over that tree
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | body :: _ -> ERecord ("Code", [ "Raw", quote body ])
                 | [] -> note (offsetOf n) "empty quotation")
            | ParenExpr ->
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | [] when (Green.tokens (GNode n) |> List.exists (fun t -> t.Kind = Operator && t.Text <> ":")) ->
                     // operator section `(+)`: a lambda over the infix use,
                     // with the same suffix/class resolution an infix
                     // occurrence would get at this offset
                     let op = Green.tokens (GNode n) |> List.find (fun t -> t.Kind = Operator && t.Text <> ":")
                     let va = { Path = path; Offset = offsetOf n + 610000; Name = "_opl" }
                     let vb = { Path = path; Offset = offsetOf n + 610001; Name = "_opr" }
                     let sch = mono (TCon ("?", []))
                     let la = EVar (va, sch)
                     let lb = EVar (vb, sch)
                     let suffixable =
                         List.contains op.Text
                             [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="
                               ">>>"; "&&&"; "|||"; "^^^"; "<<<" ]
                     let suffix =
                         if not suffixable then ""
                         else
                             match dictTryFind opKinds op.Offset with
                             | Some "b" | Some "c" -> ""
                             | Some k -> k
                             | None ->
                                 match dictTryFind opTypes op.Offset with
                                 | Some t when t <> "" && t <> "int" && t <> "char" && t <> "bool" -> "@" + t
                                 | _ -> ""
                     let body =
                         match dictTryFind classUses op.Offset with
                         | Some im ->
                             let call = EApp (classRef im, [ la; lb ])
                             if im.MName = "compare" then EPrim (op.Text, [ call; ELit (LInt "0") ])
                             else call
                         | None -> EPrim (op.Text + suffix, [ la; lb ])
                     ELam ([ va, sch; vb, sch ], body)
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
                // `[ for x in src -> e ]`: the loop's body is the element.
                // The loop itself lowers by the ordinary rules — range, cons
                // walk, indexed array or enumerator — with the body consing
                // onto an accumulator, which is then reversed.
                let arrowFor =
                    match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                    | [ f ] when f.NodeKind = ForExpr
                                 && (tokensOf f |> List.exists (fun t -> t.Kind = Operator && t.Text = "->")) -> Some f
                    | _ -> None
                // the STATEMENT form: `[ for ... do ... yield e ... ]`, with
                // the yields explicit and anywhere inside. Refused when the
                // body has no yield at all, because an IMPLICIT yield would
                // otherwise lower to a statement and silently produce []
                let hasYield =
                    let rec go (m : GreenNode) =
                        (m.NodeKind = PrefixExpr
                         && (match tokensOf m |> List.tryHead with
                             | Some t -> t.Kind = Keyword && t.Text = "yield"
                             | None -> false))
                        // a nested comprehension owns its own yields
                        || (m.NodeKind <> ListExpr && (nodesOf m |> List.exists go))
                    nodesOf n |> List.exists go
                let stmtFor =
                    match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                    | [ f ] when (f.NodeKind = ForExpr || f.NodeKind = WhileExpr) && hasYield -> Some f
                    | _ -> None
                // `[ a .. b ]` — a range as a VALUE, not a loop source. Built
                // DOWNWARDS so the conses come out in order and nothing has to
                // be reversed; both ends are bound first, so each is evaluated
                // once.
                let rangeItems =
                    match vecToList items with
                    | [ EPrim ("..", [ lo; hi ]) ] -> Some (lo, hi)
                    | _ -> None
                match rangeItems with
                | Some (lo, hi) ->
                    let off = offsetOf n
                    let ish = mono (TCon ("int", []))
                    let anon = anonScheme
                    let loV = { Path = path; Offset = off + 16000000; Name = "_rlo" }
                    let iV = { Path = path; Offset = off + 17000000; Name = "_ri" }
                    let outV = { Path = path; Offset = off + 18000000; Name = "_rout" }
                    ELet (false, loV, ish, lo,
                      ELet (false, iV, ish, hi,
                        ELet (false, outV, anon, EListLit [],
                          ESeq [ EWhile (EPrim (">=", [ EVar (iV, ish); EVar (loV, ish) ]),
                                   ESeq [ EAssign (outV, EPrim ("::", [ EVar (iV, ish); EVar (outV, anon) ]))
                                          EAssign (iV, EPrim ("-", [ EVar (iV, ish); ELit (LInt "1") ])) ])
                                 EVar (outV, anon) ])))
                | None ->
                match arrowFor with
                | Some f ->
                    let off = offsetOf n
                    let acc = { Path = path; Offset = off + 11000000; Name = "_acc" }
                    let restV = { Path = path; Offset = off + 12000000; Name = "_crest" }
                    let outV = { Path = path; Offset = off + 13000000; Name = "_cout" }
                    let hV = { Path = path; Offset = off + 14000000; Name = "_ch" }
                    let tV = { Path = path; Offset = off + 15000000; Name = "_ct" }
                    let anon = anonScheme
                    let saved = yieldInto
                    yieldInto <- Some acc
                    let loop = lowerExpr (GNode f)
                    yieldInto <- saved
                    let notNull (e : Expr) =
                        EIf (EApp (EUnknown "isNull", [ e ]), ELit (LBool false), ELit (LBool true))
                    // built by prepending, so the result is reversed once
                    let reverse =
                        ELet (false, restV, anon, EVar (acc, anon),
                          ELet (false, outV, anon, EListLit [],
                            ESeq [ EWhile (notNull (EVar (restV, anon)),
                                     EMatch (EVar (restV, anon),
                                       [ PCons (PVar (hV, anon), PVar (tV, anon)), None,
                                           ESeq [ EAssign (outV, EPrim ("::", [ EVar (hV, anon); EVar (outV, anon) ]))
                                                  EAssign (restV, EVar (tV, anon)) ]
                                         PWild, None, ELit LUnit ]))
                                   EVar (outV, anon) ]))
                    ELet (false, acc, anon, EListLit [], ESeq [ loop; reverse ])
                | None ->
                match stmtFor with
                | Some f ->
                    let off = offsetOf n
                    let acc = { Path = path; Offset = off + 11000000; Name = "_acc" }
                    let restV = { Path = path; Offset = off + 12000000; Name = "_crest" }
                    let outV = { Path = path; Offset = off + 13000000; Name = "_cout" }
                    let hV = { Path = path; Offset = off + 14000000; Name = "_ch" }
                    let tV = { Path = path; Offset = off + 15000000; Name = "_ct" }
                    let anon = anonScheme
                    let savedAcc = compAcc
                    let savedYield = yieldInto
                    compAcc <- Some acc
                    // the loop body is a STATEMENT sequence here, not the
                    // element: the arrow-form sink must not also fire
                    yieldInto <- None
                    let loop = lowerExpr (GNode f)
                    compAcc <- savedAcc
                    yieldInto <- savedYield
                    let notNull (e : Expr) =
                        EIf (EApp (EUnknown "isNull", [ e ]), ELit (LBool false), ELit (LBool true))
                    let reverse =
                        ELet (false, restV, anon, EVar (acc, anon),
                          ELet (false, outV, anon, EListLit [],
                            ESeq [ EWhile (notNull (EVar (restV, anon)),
                                     EMatch (EVar (restV, anon),
                                       [ PCons (PVar (hV, anon), PVar (tV, anon)), None,
                                           ESeq [ EAssign (outV, EPrim ("::", [ EVar (hV, anon); EVar (outV, anon) ]))
                                                  EAssign (restV, EVar (tV, anon)) ]
                                         PWild, None, ELit LUnit ]))
                                   EVar (outV, anon) ]))
                    ELet (false, acc, anon, EListLit [], ESeq [ loop; reverse ])
                | None ->
                    if comprehension then note (offsetOf n) "list comprehension"
                    else EListLit (vecToList items)
            | LambdaExpr ->
                let pats = nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind)
                let body =
                    nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                    |> List.map (fun m -> lowerExpr (GNode m))
                let bodyE = match List.tryLast body with Some b -> b | None -> ELit LUnit
                if pats |> List.exists (fun p -> p.NodeKind = StructTuplePat) then
                    // `fun struct(k, v) -> ...`: each struct-tuple parameter
                    // becomes a synthetic argument destructured in the body
                    let mutable bodyW = bodyE
                    let binds =
                        pats |> List.map (fun p ->
                            if p.NodeKind = StructTuplePat then
                                let binders = structSlots p
                                let tn =
                                    match dictTryFind fieldOwners (offsetOf p) with
                                    | Some o -> o
                                    | None -> "StructTuple" + string binders.Length
                                let arg = { Path = path; Offset = offsetOf p + 650000; Name = "_sarg" }
                                let sch = mono (TCon (tn, []))
                                bodyW <- structLetExpr binders tn (EVar (arg, sch)) bodyW
                                arg, sch
                            else
                                match lowerPat p with
                                | PVar (v, s) -> v, s
                                | PLit LUnit -> { Path = path; Offset = offsetOf p; Name = "_unit" }, mono tUnit
                                | _ ->
                                    // a structured sibling: bind and match
                                    let arg = { Path = path; Offset = offsetOf p + 650000; Name = "_arg" }
                                    let sch = mono (TCon ("?", []))
                                    bodyW <- EMatch (EVar (arg, sch), [ lowerPat p, None, bodyW ])
                                    arg, sch)
                    ELam (binds, bodyW)
                else
                let binds, bodyW = paramBindsCurried pats bodyE
                ELam (binds, bodyW)
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
                        let pat, body =
                            match pats with
                            | [ p ] when p.NodeKind = StructTuplePat ->
                                // `| struct(a, b) ->`: bind the whole value,
                                // then read its fields into the binders
                                let binders = structSlots p
                                let tn =
                                    match dictTryFind fieldOwners (offsetOf p) with
                                    | Some o -> o
                                    | None -> "StructTuple" + string binders.Length
                                let tmp = { Path = path; Offset = offsetOf p + 4100000; Name = "_sm" }
                                let sch = mono (TCon (tn, []))
                                PVar (tmp, sch), structLetExpr binders tn (EVar (tmp, sch)) body
                            | [ p ] -> lowerPat p, body
                            | [] -> PWild, body
                            | ps -> POr (alignOrBinders (List.map lowerPat ps)), body   // bar-separated alternatives
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
                        let name = recordFieldLabel f
                        let value = nodesOf f |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast
                        match name, value with
                        | Some t, Some v -> Some (t.Text, lowerExpr (GNode v))
                        | _ -> None)
                let owner =
                    match dictTryFind fieldOwners (offsetOf n) with
                    | Some o -> o
                    | None -> "?"
                // `{ base with f = v }`: the BASE is the first expression
                // child that is not a field. Lowering it as a plain record
                // silently dropped every field the literal did not mention
                let baseExpr =
                    if not (tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "with")) then None
                    else
                        nodesOf n
                        |> List.filter (fun m -> m.NodeKind <> RecordExprField && isExprish m.NodeKind)
                        |> List.tryHead
                (match baseExpr with
                 | Some b -> ERecordExt (owner, lowerExpr (GNode b), fields)
                 | None -> ERecord (owner, fields))
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
                         // this index's own bracket group is the key, but a
                         // LATE dot-resolution may have recorded the resolved
                         // element type under the node itself. Prefer a name
                         // that is not still a type variable.
                         let br = Green.tokens (GNode ix) |> List.tryHead
                         let atBracket = br |> Option.bind (fun t -> dictTryFind arrKinds t.Offset)
                         let atNode = dictTryFind arrKinds (offsetOf n)
                         let resolved (x : string option) =
                             match x with
                             | Some v when v <> "" && not (v.StartsWith "#") -> Some v
                             | _ -> None
                         match resolved atBracket with
                         | Some v -> v
                         | None ->
                             match resolved atNode with
                             | Some v -> v
                             | None ->
                                 match atBracket with
                                 | Some v -> v
                                 | None -> (match atNode with Some v -> v | None -> "")
                     // a user-defined indexer takes precedence over the array
                     // read: inference only binds one when the receiver is
                     // NOT an array
                     let indexer =
                         match Green.tokens (GNode ix) |> List.tryHead with
                         | Some br ->
                             let t = indexerTok 60000000 "Item" br
                             (match memberAt t with
                              | Some (_, d) -> Some (memberFn t d)
                              | None -> None)
                         | None -> None
                     (match indexer, idx with
                      | Some fn, [ i ] -> EApp (fn, [ lowerExpr (GNode lhs); i ])
                      | _, [ i ] -> EIndex (nm, lowerExpr (GNode lhs), i)
                      | _ -> note (offsetOf n) "index shape")
                 | _ -> note (offsetOf n) "index shape")
            | DotExpr when
                (match Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some t -> t.Text = "Length" && (dictTryFind arrKinds t.Offset).IsSome
                 | None -> false) ->
                let mt = Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.last
                (match nodesOf n |> List.tryHead with
                 | Some lhs -> EArrayLen ((dictTryFind arrKinds mt.Offset).Value, lowerExpr (GNode lhs))
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
                // a var may be a capture of SEVERAL nested object
                // expressions at once — the enclosing mapping is restored
                // before the construction site is built
                let savedMaps =
                    caps |> List.map (fun (v, _) ->
                        (v.Path, v.Offset), dictTryFind fieldOfVar (v.Path, v.Offset))
                for v, _ in caps do dictSet fieldOfVar (v.Path, v.Offset) (synth, v.Name)
                vecAdd decls (DRecord (synth, [], caps |> List.map (fun (v, _) -> v.Name, "?"), false))
                let savedClass = currentClass
                currentClass <- synth
                let bound =
                    nodesOf n
                    |> List.filter (fun m -> m.NodeKind = MemberDecl)
                    |> List.choose (liftMemberIn synth)
                currentClass <- savedClass
                for k, prior in savedMaps do
                    match prior with
                    | Some p -> dictSet fieldOfVar k p
                    | None -> dictRemove fieldOfVar k
                vecAdd decls
                    (DClass (synth, None, [],
                             match iface with Some i -> [ i, bound ] | None -> []))
                // the CONSTRUCTION reads each captured var in the enclosing
                // scope — where it may itself be a field of the class being
                // lowered (a nested object expression, or a ctor parameter
                // that became instance state)
                let capInit (v : VarId, sch : Scheme) : Expr =
                    match currentSelf, dictTryFind fieldOfVar (v.Path, v.Offset) with
                    | Some (sv, ssch), Some (owner, fname) when owner = currentClass ->
                        EField (EVar (sv, ssch), fname, currentClass)
                    | _ -> EVar (v, sch)
                ERecord (synth, caps |> List.map (fun (v, sch) -> v.Name, capInit (v, sch)))
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
                    nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) |> Option.bind ifaceNameOf
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
                         // cross-file members are exports, hence top-level;
                         // their stamps matter just as much as local ones
                         && (if d.Path = path then (dictTryFind topLevelDefs d.Offset).IsSome else true) ->
                        EVarI (varIdOf d, schemeOf d, inst)
                    | _ -> EVar (varIdOf d, schemeOf d)
                if isStaticUse n then
                    // a static property is a function of unit; read it
                    (match (schemeOf d).Body with
                     | TFun (u, _) when u = tUnit -> EApp (fn, [ ELit LUnit ])
                     | _ -> fn)
                else
                    (match nodesOf n |> List.tryHead with
                     | Some lhs -> EApp (fn, [ lowerExpr (GNode lhs) ])
                     | None -> note (offsetOf n) "member access without a receiver")
            | DotExpr ->
                (match nodesOf n |> List.tryHead, Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                 | Some lhs, Some name ->
                     // qualified value (resolver linked it) or field access
                     (match dictTryFind classUses name.Offset with
                      // `Num.Zero` — the class says which member, the
                      // instance says which body
                      | Some im ->
                          let r = classRef im
                          if im.MTakesUnit then EApp (r, [ ELit LUnit ]) else r
                      | None ->
                     match dictTryFind classPending name.Offset with
                      | Some payload -> EUnknown ("$class:" + payload)
                      | None ->
                     match dictTryFind useDefs name.Offset |> Option.filter (fun d -> d.Kind <> Resolve.DefMember) with
                      | Some d when d.Kind = Resolve.DefCase -> ECtor (d.Name, schemeOf d, [])
                      | Some d ->
                          (match dictTryFind instSites name.Offset with
                           | Some inst when
                                not (List.isEmpty inst)
                                // a qualified use of another file's binding
                                // (Module.f) records a demand like any other
                                && (if d.Path = path then (dictTryFind topLevelDefs d.Offset).IsSome else true) ->
                               EVarI (varIdOf d, schemeOf d, inst)
                           | _ -> EVar (varIdOf d, schemeOf d))
                      | None ->
                          let owner =
                              match dictTryFind fieldOwners name.Offset with
                              | Some o -> o
                              | None -> (match dictTryFind memberSites name.Offset with Some o -> o | None -> "")
                          // a BUILTIN member on `option`: a property of the
                          // tag, so it lowers to the match it means rather
                          // than to a stamped member (see Infer)
                          let anon = anonScheme
                          let optTag (whenSome : Expr) (whenNone : Expr) =
                              EMatch (lowerExpr (GNode lhs),
                                      [ PCtor ("Some", anon, [ PWild ]), None, whenSome
                                        PWild, None, whenNone ])
                          if owner = "Option" && name.Text = "IsSome" then
                              optTag (ELit (LBool true)) (ELit (LBool false))
                          elif owner = "Option" && name.Text = "IsNone" then
                              optTag (ELit (LBool false)) (ELit (LBool true))
                          elif owner = "Option" && name.Text = "Value" then
                              let tmp = { Path = path; Offset = offsetOf n + 21000000; Name = "_optv" }
                              EMatch (lowerExpr (GNode lhs),
                                      [ PCtor ("Some", anon, [ PVar (tmp, anon) ]), None, EVar (tmp, anon)
                                        PWild, None,
                                          EApp (EUnknown "failwith",
                                                [ ELit (LString "\"the option value was None\"") ]) ])
                          // list: cons-cell properties, lowered to the shape
                          // they mean rather than to a stamped member
                          elif owner = "list" && name.Text = "IsEmpty" then
                              EMatch (lowerExpr (GNode lhs),
                                      [ PCons (PWild, PWild), None, ELit (LBool false)
                                        PWild, None, ELit (LBool true) ])
                          elif owner = "list" && name.Text = "Head" then
                              let h = { Path = path; Offset = offsetOf n + 22000000; Name = "_lh" }
                              EMatch (lowerExpr (GNode lhs),
                                      [ PCons (PVar (h, anon), PWild), None, EVar (h, anon)
                                        PWild, None,
                                          EApp (EUnknown "failwith",
                                                [ ELit (LString "\"the list is empty\"") ]) ])
                          elif owner = "list" && name.Text = "Tail" then
                              let t = { Path = path; Offset = offsetOf n + 23000000; Name = "_lt" }
                              EMatch (lowerExpr (GNode lhs),
                                      [ PCons (PWild, PVar (t, anon)), None, EVar (t, anon)
                                        PWild, None,
                                          EApp (EUnknown "failwith",
                                                [ ELit (LString "\"the list is empty\"") ]) ])
                          elif owner = "list" && name.Text = "Length" then
                              EApp (EUnknown "$listLength", [ lowerExpr (GNode lhs) ])
                          else EField (lowerExpr (GNode lhs), name.Text, owner))
                 | _ -> note (offsetOf n) "dot shape")
            | ForExpr ->
                // range-for: `for i in a .. b do body` — desugars to a while
                let pats = nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind)
                let exprs = nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                (match pats, exprs with
                 | [ ip ], [ range; body ] ->
                     (match lowerPat ip, lowerExpr (GNode range) with
                      // `for _ in 1 .. n do` counts without naming the
                      // counter; the loop still needs one, so a wildcard
                      // binder gets a synthetic variable
                      | (PVar _ | PWild), EPrim ("..", [ lo; hi ]) ->
                          let iv, isch =
                              match lowerPat ip with
                              | PVar (v, sch) -> v, sch
                              | _ ->
                                  { Path = path; Offset = offsetOf n + 19000000; Name = "_i" },
                                  mono (TCon ("int", []))
                          let hiV = { Path = iv.Path; Offset = iv.Offset + 1000000; Name = "_hi" }
                          ELet (false, iv, isch, lo,
                            ELet (false, hiV, isch, hi,
                              EWhile (EPrim ("<=", [ EVar (iv, isch); EVar (hiV, isch) ]),
                                ESeq [ loopBody body
                                       EAssign (iv, EPrim ("+", [ EVar (iv, isch); ELit (LInt "1") ])) ])))
                      | pat, coll when (dictTryFind arrKinds (offsetOf range)) = Some "list" ->
                          // for x in xs (a LIST): a cons walk. The binder may
                          // destructure, so the element binds through the
                          // cons pattern itself.
                          let anon = mono (TCon ("?", []))
                          let restV = { Path = path; Offset = offsetOf n + 5000000; Name = "_rest" }
                          let tailV = { Path = path; Offset = offsetOf n + 6000000; Name = "_tail" }
                          let notNull (e : Expr) =
                              EIf (EApp (EUnknown "isNull", [ e ]), ELit (LBool false), ELit (LBool true))
                          ELet (false, restV, anon, coll,
                            EWhile (notNull (EVar (restV, anon)),
                              EMatch (EVar (restV, anon),
                                [ PCons (pat, PVar (tailV, anon)), None,
                                    ESeq [ loopBody body
                                           EAssign (restV, EVar (tailV, anon)) ]
                                  PWild, None, ELit LUnit ])))
                      | pat, coll when
                            (dictTryFind arrKinds (offsetOf range)).IsSome
                            // arrKinds also holds plain application results,
                            // so the ARRAY path only applies when inference
                            // did NOT bind the protocol's synthetic access
                            && (dictTryFind memberSites (30000000 + offsetOf n)).IsNone ->
                          // for x in arr do body  ==>  indexed while loop;
                          // a destructuring binder matches the element
                          let nm = (dictTryFind arrKinds (offsetOf range)).Value
                          let anon = mono (TCon ("?", []))
                          let av = { Path = path; Offset = offsetOf n + 2000000; Name = "_arr" }
                          let ix = { Path = path; Offset = offsetOf n + 3000000; Name = "_ix" }
                          let ish = mono (TCon ("int", []))
                          let elem = EIndex (nm, EVar (av, anon), EVar (ix, ish))
                          let inner =
                              match pat with
                              | PVar (iv, isch) -> ELet (false, iv, isch, elem, loopBody body)
                              | p -> EMatch (elem, [ p, None, loopBody body ])
                          ELet (false, av, anon, coll,
                            ELet (false, ix, ish, ELit (LInt "0"),
                              EWhile (EPrim ("<", [ EVar (ix, ish); EArrayLen (nm, EVar (av, anon)) ]),
                                ESeq [ inner
                                       EAssign (ix, EPrim ("+", [ EVar (ix, ish); ELit (LInt "1") ])) ])))
                      | pat, coll ->
                          // the enumerator protocol. Inference bound three
                          // member accesses at synthetic offsets derived from
                          // the loop's first token; each is either an
                          // interface method (vtable dispatch) or a concrete
                          // member (a lifted function).
                          let fo = offsetOf n
                          let synth (txt : string) (base_ : int) : Token =
                              { Kind = Ident; Text = txt; Leading = []; Trailing = []; Offset = base_ + fo }
                          let call (t : Token) (recv : Expr) (withUnit : bool) : Expr option =
                              if (memberAt t).IsNone then None
                              else
                                  let owner, d = (memberAt t).Value
                                  let args = if withUnit then [ ELit LUnit ] else []
                                  match dictTryFind ifaces owner with
                                  | Some ms when ms |> List.exists (fun (m, _) -> m = t.Text) ->
                                      Some (EIfaceCall (owner, t.Text, recv, args))
                                  // a concrete member of a GENERIC class is
                                  // stamped per instantiation like any other
                                  // generic function; the protocol's call has
                                  // to name the stamp
                                  | _ -> Some (EApp (memberFn t d, recv :: args))
                          let anon = mono (TCon ("?", []))
                          let enV = { Path = path; Offset = fo + 4000000; Name = "_en" }
                          (match call (synth "GetEnumerator" 30000000) (lowerExpr (GNode range)) true,
                                 call (synth "MoveNext" 40000000) (EVar (enV, anon)) true,
                                 call (synth "Current" 50000000) (EVar (enV, anon)) false with
                           | Some g, Some m, Some c ->
                               let inner =
                                   match pat with
                                   | PVar (iv, isch) ->
                                       ELet (false, iv, isch, c, loopBody body)
                                   | p ->
                                       // tuple and struct-tuple binders
                                       // destructure the current element
                                       EMatch (c, [ p, None, loopBody body ])
                               ELet (false, enV, anon, g, EWhile (m, inner))
                           | _ -> note (offsetOf n) "for-in (no GetEnumerator on the source)"))
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
                            | ps -> POr (alignOrBinders (List.map lowerPat ps))
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
                    let savedSelf = currentSelf
                    currentSelf <- Some selfBind
                    let mutable seenEq = false
                    let bodies = vecNew<GreenNode> ()
                    for c in acc.Children do
                        match c with
                        | GToken t when t.Kind = Operator && t.Text = "=" -> seenEq <- true
                        | GNode b when seenEq && isExprish b.NodeKind -> vecAdd bodies b
                        | _ -> ()
                    let body = lowerBlock (vecToList bodies)
                    currentSelf <- savedSelf
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
            // save, don't clear: a nested object expression's members lift
            // from INSIDE this body, and clearing killed the enclosing self
            // for everything after them
            let savedSelf = currentSelf
            if not isStaticM then currentSelf <- Some selfBind
            let body = lowerBlock (vecToList bodies |> List.choose (fun c -> match c with GNode x -> Some x | _ -> None))
            currentSelf <- savedSelf
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
            let allBinds =
                if not isStaticM then selfBind :: binds
                elif List.isEmpty binds then
                    // a static property is re-evaluated per access, so it
                    // lifts to a function of unit rather than a value
                    // initializer that every program would have to run
                    [ { Path = path; Offset = d.Offset + 500000; Name = "_unit" }, mono tUnit ]
                else binds
            vecAdd decls (DLet (false, varIdOf d, sch, ELam (allBinds, mbody)))
            Some (d.Name, varIdOf d)
        | None -> None

    /// Expand `let struct(a, b) = rhs in body` into a struct binding plus
    /// one field read per binder — the struct itself is an ordinary value.
    /// A loop body. Inside a list comprehension the body IS the yielded
    /// element, so it is consed onto the accumulator instead of being run
    /// for its effect; the sink is consumed here, so a loop NESTED in the
    /// body is an ordinary loop again.
    and loopBody (body : GreenNode) : Expr =
        match yieldInto with
        | None -> lowerExpr (GNode body)
        | Some acc ->
            yieldInto <- None
            let e = lowerExpr (GNode body)
            yieldInto <- Some acc
            EAssign (acc, EPrim ("::", [ e; EVar (acc, anonScheme) ]))

    and structLetExpr (slots : (VarId * Scheme) option list) (tn : string) (rhs : Expr) (body : Expr) : Expr =
        match slots |> List.choose id with
        | [] -> body
        | (first, _) :: _ ->
            let tmp = { Path = first.Path; Offset = first.Offset + 4000000; Name = "_st" }
            let tsch = mono (TCon (tn, []))
            let inner =
                List.foldBack
                    (fun (i, slot) acc ->
                        match slot with
                        | Some (v, vsch) ->
                            ELet (false, v, vsch, EField (EVar (tmp, tsch), "Item" + string (i + 1), tn), acc)
                        | None -> acc)
                    (slots |> List.mapi (fun i b -> i, b))
                    body
            ELet (false, tmp, tsch, rhs, inner)

    /// Classify and lower a LetDecl node.
    and lowerLetParts (n : GreenNode) : LetShape option =
        // `and g ...` continues a `let rec` group: the `rec` sits on the
        // group's FIRST member, but every member of it is recursive
        let isRec =
            tokensOf n
            |> List.exists (fun t -> t.Kind = Keyword && (t.Text = "rec" || t.Text = "and"))
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
            (vecToList before |> List.exists (fun c -> match c with GToken t -> t.Kind = Comma | _ -> false))
            // `let (k, v) = e` — the parens hide the comma from the token
            // scan, and treating it as a SIMPLE binding bound only k
            || (match pats with
                | [ p ] when p.NodeKind = ParenPat ->
                    p.Children
                    |> List.exists (fun c ->
                        match c with
                        // the parens hold a FLAT comma-separated pattern
                        | GToken t -> t.Kind = Comma
                        | GNode inner -> inner.NodeKind = ConsPat || inner.NodeKind = ListPat)
                | [ p ] -> p.NodeKind = StructTuplePat
                | _ -> false)
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
            let binders = structSlots sp
            if binders |> List.forall Option.isNone then None
            else
                let tn =
                    match dictTryFind fieldOwners (offsetOf sp) with
                    | Some o -> o
                    | None -> "StructTuple" + string binders.Length
                Some (StructLet (binders, tn, lowerBlock rhsExprs, cont))
        | _ ->
        if isDestructure then
            // `let (k, v) = e` carries ONE flat ParenPat; the tuple pattern
            // is its comma-separated inner pats
            let flat =
                match pats with
                | [ p ] when p.NodeKind = ParenPat ->
                    p.Children |> List.choose (fun c -> match c with GNode m when isPatKind m.NodeKind -> Some m | _ -> None)
                | ps -> ps
            match flat with
            | [] -> None
            | [ one ] -> Some (DestructureLet (lowerPat one, lowerBlock rhsExprs, cont))
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
        let newCtorNodes = allMemberNodes |> List.filter isNewCtor
        let newCtorNode = List.tryHead newCtorNodes
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
        let isStaticLet (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")
        let staticLets = nodesOf n |> List.filter (fun m -> m.NodeKind = LetDecl && isStaticLet m)
        let classLets = nodesOf n |> List.filter (fun m -> m.NodeKind = LetDecl && not (isStaticLet m))
        for sl in staticLets do
            match lowerLetParts sl with
            | Some (SimpleLet (isRec, v, sch, rhs, _)) -> vecAdd decls (DLet (isRec, v, sch, rhs))
            | _ -> vecAdd notes (offsetOf sl, "static let shape")
        let doNodes = nodesOf n |> List.filter (fun m -> m.NodeKind = BlockExpr)
        let isAbstract (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "abstract")
        let isStaticM (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")
        // a type whose members are all abstract declares an interface: no
        // storage, no constructor — dispatch is a separate concern
        // `type X with member ...` — an intrinsic type EXTENSION. It carries
        // no representation (that is the marker: `with` where `=` would be),
        // so it declares no record, no constructor and no vtable slot. Its
        // members are ordinary functions of the receiver, attached to a type
        // declared elsewhere — which is what an extension member IS, in F#
        // as here: static dispatch, resolved by the receiver's type.
        let isExtension =
            tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "with")
            && not (tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = "="))
        let isInterface =
            not isExtension
            && not (List.isEmpty memberNodes) && memberNodes |> List.forall isAbstract
        // a class is anything with instance storage or a constructor
        let isClass =
            not isExtension
            && not isInterface
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

        // Mirrors inference: with no primary constructor the FIRST `new` is
        // what the type name denotes; the rest live at their own keyword.
        let ctorDefOf (isFirst : bool) (nc : GreenNode) =
            if isFirst && ctorPat.IsNone then
                tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) |> Option.bind (fun t -> dictTryFind defsAt t.Offset)
            else
                tokensOf nc |> List.tryFind (fun t -> t.Kind = Keyword && t.Text = "new")
                |> Option.bind (fun t -> dictTryFind defsAt t.Offset)
        // `new(...)` constructors: a type may declare several, and each is
        // its own function so a call site can pick between them
        let emitExplicitCtors () =
            newCtorNodes
            |> List.iteri (fun i nc ->
                match ctorDefOf (i = 0) nc with
                | Some cd ->
                    let ps = nodesOf nc |> List.filter (fun m -> isPatKind m.NodeKind)
                    let bodies = nodesOf nc |> List.filter (fun m -> isExprish m.NodeKind)
                    let body =
                        match lowerBlock bodies with
                        | ERecord (rn, fs) when rn = "?" -> ERecord (name, fs)
                        | other -> other
                    let rhs =
                        match paramBinds ps with
                        | binds, [] -> ELam (binds, body)
                        | _, structured ->
                            let arg = { Path = path; Offset = cd.Offset + 600000; Name = "_arg" }
                            let asch = mono (TCon ("?", []))
                            (match structured with
                             | [ p ] -> ELam ([ arg, asch ], EMatch (EVar (arg, asch), [ p, None, body ]))
                             | pps -> ELam ([ arg, asch ], EMatch (EVar (arg, asch), [ PTuple pps, None, body ])))
                    vecAdd decls (DLet (false, varIdOf cd, schemeOf cd, rhs))
                | None -> ())

        if not (List.isEmpty valFields) then
            // declared storage: the type IS these fields
            if pendingStruct then vecAdd structNames name
            vecAdd decls (DRecord (name, tyParams, valFields, pendingStruct))
            emitExplicitCtors ()
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
            emitExplicitCtors ()

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
            // records and DUs are not classes but may still declare members,
            // and an Equals/GetHashCode among them overrides the generated one
            if not (List.isEmpty (vecToList ownMembers)) then
                vecAdd decls (DMembers (name, vecToList ownMembers))

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
                 | Some (SimpleLet (isRec, v, sch, rhs, _)) ->
                     vecAdd decls (DLet (isRec, v, sch, rhs))
                     if pendingExport then vecAdd decls (DExport (v, v.Name))
                 | _ -> vecAdd notes (offsetOf n, "top-level let shape"))
                pendingExport <- false
            | TypeDecl ->
                lowerTypeDecl n
                pendingStruct <- false
            // a class declares signatures only; an instance's members are
            // ordinary top-level functions, reached through the class
            | ClassDecl -> ()
            | InstanceDecl ->
                for c in nodesOf n do
                    if c.NodeKind = MemberDecl
                       && not (tokensOf c |> List.exists (fun t -> t.Kind = Keyword && t.Text = "type")) then
                        liftPlainMember "instance" c |> ignore
            | ModuleDef -> nodesOf n |> List.iter (fun m -> lowerDecl (GNode m))
            | AttributeList ->
                if Green.tokens g |> List.exists (fun t -> t.Kind = Ident && t.Text = "Struct") then
                    pendingStruct <- true
                if Green.tokens g |> List.exists (fun t -> t.Kind = Ident && t.Text = "Export") then
                    pendingExport <- true
            | ModuleHeader | OpenDecl -> ()
            | k when isExprish k ->
                vecAdd decls (DLet (false, { Path = path; Offset = offsetOf n; Name = "_it" }, mono tUnit, lowerExpr g))
            | _ -> vecAdd notes (offsetOf n, "declaration " + string n.NodeKind)

    for c in root.Children do lowerDecl c

    { Decls = vecToList decls
      Notes = vecToList notes }

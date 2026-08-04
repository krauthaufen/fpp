module Fpp.Analysis.Infer

open Fpp.Prelude
open Fpp.Syntax
open Fpp.Analysis
open Fpp.Analysis.Types

// Type inference for the HM core, v0. The key trick: name resolution has
// already solved all scoping, so schemes are keyed by *definition offset* —
// a use looks up its definition through the resolver's use->def table and
// instantiates that definition's scheme. No environment threading at all.
//
// Anything unresolved (BCL, other files, member access, brace-soup) gets a
// fresh unconstrained variable — inference degrades to "unknown", never to a
// false error. Mismatch diagnostics therefore only fire where both sides are
// genuinely known.

type InferResult =
    { Diagnostics : (int * string) list
      /// definition offset, length, pretty-printed type
      DefTypes : (int * int * string) list
      /// operator token offset -> resolved kind: "f"=float "s"=float32
      /// "h"=float16
      /// "l"=int64 "t"=string ""=int/other — drives typed prim emission
      OpKinds : (int * string) list
      /// array-site offset -> element type name (for flat struct arrays)
      ArrKinds : (int * string) list
      /// use offset -> concrete type per quantified var of the callee's
      /// scheme (tier-1 specialization demands; "" when not concrete)
      InstSites : (int * string list) list
      /// member/field name-token offset -> the receiver's type name. Member
      /// names are not unique, so this — not the name — binds a dot-access
      /// to the member it calls.
      MemberSites : (int * string) list
      /// application-head offset -> the definition offset of the chosen
      /// constructor, when a type offers more than one
      CtorSites : (int * int) list
      /// use offset of a class member -> the (path, offset) of the instance
      /// member it resolved to. Absent when the instance is builtin, which
      /// is exactly when the backend emits the operation itself.
      ClassUses : (int * Classes.InstMember) list
      /// a class-member use that did NOT resolve, because the type is still
      /// a variable of the enclosing binding: "Class:member:typeName". The
      /// binding is stamped, and the member resolves in each copy.
      ClassPending : (int * string) list
      /// arithmetic-operator offset -> the operand type's name, or "#id"
      /// when it is a type variable of the enclosing binding. The suffix
      /// letters in OpKinds only cover the primitive types; this covers the
      /// rest, and survives into monomorphization.
      OpTypes : (int * string) list
      /// EVERY expression node, keyed by its SPAN (start, end) -> its inferred
      /// type, pretty-printed once unification settles. The span and not the
      /// offset: a node and its leftmost descendant share a first token, so
      /// offsets alone cannot tell `p.X` from `p`.
      ExprTypes : (int * int * string) list
      /// offset -> the OWNER type at its instantiation (`Pair$int$int`), for
      /// record construction and field access. Distinct from MemberSites,
      /// which names the declaring type for member dispatch.
      FieldOwners : (int * string) list
      /// computation-expression offset -> the BUILDER's type name. F# picks
      /// a computation expression's shape from what the builder declares —
      /// `Run` and `Delay` appear only if it has them — so the rewrite needs
      /// this before it can run, which is why it runs after a probe pass.
      CompBuilders : (int * string) list
      /// offsets of computation-expression body items that have no value:
      /// statements, where anything else in the same position would be an
      /// implicit `yield`
      CompStatements : int list }

type FieldInfo =
    { TypeName : string
      /// the owner type's parameters — substituted by the receiver's args
      Params : Var list
      /// the member's own generic variables — freshened per access
      Quantified : Var list
      FieldType : Type
      /// for a member: the (path, offset) of the function it lifts to, so a
      /// use site can instantiate THAT scheme and record the specialization
      /// demand. None for plain record fields.
      DefKey : (string * int) option
      IsStatic : bool
      /// how many TRAILING parameters were declared `?x` — a caller may
      /// leave that many off the end, and each one it leaves off is None
      Optionals : int
      /// the parameters' names in declaration order, "" where the parameter
      /// is not a plain identifier. What lets a CALL name its arguments.
      ParamNames : string list }

/// `shared` carries generalized schemes of earlier files keyed
/// "path:offset" (and receives this file's); `aliases` carries type
/// abbreviations keyed by short name across the project.
/// `fields` is shared across the project under two keyings per field:
/// bare "fieldName" (last declaration wins, F# shadowing) and
/// "TypeName.fieldName" (for dot-access on a known record type).
let infer (path : string) (root : GreenNode) (binder : Resolve.BindResult)
          (shared : Dict<string, Scheme>) (aliases : Dict<string, Var list * Type>)
          (fields : Dict<string, FieldInfo>) (ifaces : Dict<string, (string * int) list>)
          (bases : Dict<string, Var list * Type>)
          (impls : Dict<string, string list>)
          (implTys : Dict<string, (Var list * Type) list>)
          (structTypes : Dict<string, bool>)
          (ctors : Dict<string, (int * Scheme) list>)
          (classes : Classes.Tables) : InferResult =
    let st = TypeState()
    let diags = vecNew<int * string> ()
    let opKindsRaw = vecNew<int * Type> ()
    let arrKindsRaw = vecNew<int * Type> ()
    // `for x in e` whose source type was still UNKNOWN when the loop was
    // typed — a parked dot resolves after the walk. Promoted to a real
    // marker at the end, but only if it turned out to be a list or an
    // array: the enumerator protocol needs member accesses parked DURING
    // the walk, so promoting one here would emit an array walk over a class
    /// (loop offset, collection-token offset, collection type, binder type)
    let lateLoopSources = vecNew<int * int * Type * Type> ()
    let instRaw = vecNew<int * Type list> ()
    // index expressions whose RECEIVER is an array: `a.[i] <- v` may tie the
    // value to the element type, which a member setter's shape may not
    let arrIndexTargets = dictNew<int, bool> ()
    // index sites that bound a user-defined `Item` member instead: the store
    // goes through `set_Item`, whose value parameter has the getter's type,
    // so the same tie is sound there
    let indexerTargets = dictNew<int, bool> ()
    /// Types this compilation has actually SEEN the members of. "T has no
    /// indexer" is only sayable about those: the dogfooding gate types each
    /// source with nothing resolved, where every .NET type is a bare name.
    let knownTypes = dictNew<string, bool> ()
    let defSchemes = dictNew<int, Scheme> ()
    let defTypes = vecNew<int * int * Type> ()

    let useDefs = dictNew<int, Resolve.Definition> ()
    for u in binder.Resolutions do dictSet useDefs u.UseOffset u.Def
    let defsAt = dictNew<int, Resolve.Definition> ()
    for d in binder.Definitions do dictSet defsAt d.Offset d

    let setScheme (offset : int) (sch : Scheme) : unit =
        dictSet defSchemes offset sch
        dictSet shared (path + ":" + string offset) sch

    /// Instantiate the scheme of a definition. Imported schemes are deep-
    /// freshened over ALL their variables (not just quantified ones), so
    /// residual free variables — value restriction, inference gaps — can
    /// never let one file's unifications contaminate another file.
    /// Instantiate, reporting the fresh var used for each quantified var so
    /// the call site becomes a specialization demand once solving finishes.
    let instantiateTracked (sch : Scheme) : Type * Type list * Constraint list =
        if List.isEmpty sch.Quantified then sch.Body, [], sch.Constraints
        else
            let subst = dictNew<int, Type> ()
            let fresh = sch.Quantified |> List.map (fun v ->
                let f = st.Fresh ()
                // keyed by the var's CURRENT representative: unification may
                // have re-pointed the recorded var since generalization
                dictSet subst (prunedId v) f
                f)
            let rec go (t : Type) : Type =
                match prune t with
                | TVar v -> (match dictTryFind subst v.Id with Some f -> f | None -> TVar v)
                | TCon (n, args) -> TCon (n, List.map go args)
                | TFun (a, b) -> TFun (go a, go b)
                | TTuple ts -> TTuple (List.map go ts)
            go sch.Body, fresh, List.map (mapConstraint go) sch.Constraints

    /// Instantiate an IMPORTED scheme. Every variable is freshened, not just
    /// the quantified ones, so a residual free variable in another file's
    /// scheme can never be unified here — but the fresh counterparts of the
    /// quantified vars are still reported, because a call across a file
    /// boundary is a specialization demand exactly like a local one.
    let instantiateImported (sch : Scheme) : Type * Type list * Constraint list =
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
            | TCon (c, xs) -> TCon (c, List.map go xs)
            | TFun (a, b) -> TFun (go a, go b)
            | TTuple ts -> TTuple (List.map go ts)
        let body = go sch.Body
        let cs = List.map (mapConstraint go) sch.Constraints
        let fresh =
            sch.Quantified
            |> List.map (fun v -> match dictTryFind subst v.Id with Some f -> f | None -> st.Fresh ())
        body, fresh, cs

    let schemeOfDef (d : Resolve.Definition) : Scheme option =
        if d.Path = path then dictTryFind defSchemes d.Offset
        else dictTryFind shared (d.Path + ":" + string d.Offset)

    let instantiateFor (d : Resolve.Definition) : (Type * Constraint list) option =
        if d.Path = path then
            dictTryFind defSchemes d.Offset |> Option.map st.InstantiateC
        else
            dictTryFind shared (d.Path + ":" + string d.Offset)
            |> Option.map (fun sch ->
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
                    | TCon (c, xs) -> TCon (c, List.map go xs)
                    | TFun (a, b) -> TFun (go a, go b)
                    | TTuple ts -> TTuple (List.map go ts)
                go sch.Body, List.map (mapConstraint go) sch.Constraints)

    /// Substitute specific vars (by id) with given types, freshening nothing else.
    /// Memoized on node identity so a shared sub-DAG is copied ONCE.
    let substVars (subst : Dict<int, Type>) (t : Type) : Type =
        let memo = refMapNew<Type, Type> shallowHash
        let rec go (t : Type) : Type =
            let p = prune t
            match refMapTryFind memo p with
            | Some r -> r
            | None ->
                let r =
                    match p with
                    | TVar v -> (match dictTryFind subst v.Id with Some a -> a | None -> TVar v)
                    | TCon (c, xs) -> TCon (c, List.map go xs)
                    | TFun (a, b) -> TFun (go a, go b)
                    | TTuple ts -> TTuple (List.map go ts)
                refMapSet memo p r
                r
        go t

    let unifyAt (offset : int) (t1 : Type) (t2 : Type) : unit =
        match unify t1 t2 with
        | Some msg -> vecAdd diags (offset, msg)
        | None -> ()

    /// Nominal subtyping: is `sup` `sub` itself, an ancestor of it, or an
    /// interface it implements? Inheritance and interfaces both count.
    // `seq<'a>` IS `IEnumerable<'a>`, and arrays, lists and any type
    // implementing it genuinely are sequences
    let isSeqName (n : string) = n = "seq" || n = "IEnumerable"
    let rec isSupertypeOf (sup : string) (sub : string) : bool =
        // obj is the top type: everything widens to it
        sup = "obj" || sup = sub
        || (isSeqName sup
            && (isSeqName sub || sub = "array" || sub = "list" || sub = "List"
                || (match dictTryFind impls sub with
                    | Some is -> is |> List.exists isSeqName
                    | None -> false)))
        || (match dictTryFind impls sub with
            | Some is -> List.contains sup is
            | None -> false)
        || (match dictTryFind bases sub with
            | Some (_, bt) ->
                (match prune bt with
                 | TCon (b, _) -> isSupertypeOf sup b
                 | _ -> false)
            | None -> false)

    // (iface-side, class-side) -> the DECLARED interface instantiation to
    // unify against, or the identity pair when only the NAME relation is
    // known (the arguments then stay open and later uses pin them)
    do Types.subsumeHook <-
        Some (fun ifaceTy clsTy ->
            match prune ifaceTy, prune clsTy with
            | TCon (iname, iargs), TCon (cname, cargs) when iname <> "obj" ->
                let rec resolve (cname : string) (cargs : Type list) : (Type * Type) option =
                    // an entry whose parameter count differs is ANOTHER
                    // class sharing the bare name (two AbstractReaders):
                    // substituting nothing and unifying its RAW parameter
                    // variables bound them globally and corrupted every
                    // later use of that class
                    let viaDecl =
                        match dictTryFind implTys cname with
                        | Some entries ->
                            entries |> List.tryPick (fun (ps, ity) ->
                                match prune ity with
                                // the ARITY must match too: IOpReader<'d>
                                // and IOpReader<'s, 'd> share the bare name
                                | TCon (inm, ia) when inm = iname
                                                      && ia.Length = iargs.Length
                                                      && ps.Length = cargs.Length ->
                                    let subst = dictNew<int, Type> ()
                                    List.zip ps cargs
                                    |> List.iter (fun (pv, ca) -> dictSet subst (prunedId pv) ca)
                                    for fv in freeVars ity do
                                        if (dictTryFind subst (prunedId fv)).IsNone then
                                            dictSet subst (prunedId fv) (st.Fresh ())
                                    Some (substVars subst ity, ifaceTy)
                                | _ -> None)
                        | None -> None
                    match viaDecl with
                    | Some r -> Some r
                    | None ->
                        match dictTryFind bases cname with
                        | Some (ps, bt) when ps.Length = cargs.Length ->
                            let subst = dictNew<int, Type> ()
                            List.zip ps cargs
                            |> List.iter (fun (pv, ca) -> dictSet subst (prunedId pv) ca)
                            for fv in freeVars bt do
                                if (dictTryFind subst (prunedId fv)).IsNone then
                                    dictSet subst (prunedId fv) (st.Fresh ())
                            (match prune (substVars subst bt) with
                             | TCon (bn, bargs) -> resolve bn bargs
                             | _ -> None)
                        | _ -> None
                (match resolve cname cargs with
                 | Some r -> Some r
                 | None ->
                     // name-only knowledge: the value widens, the arguments
                     // stay the interface's own business
                     if isSupertypeOf iname cname then Some (ifaceTy, ifaceTy)
                     else None)
            | _ -> None)

    /// Unify an argument against a parameter, allowing the argument to be a
    /// subtype — F# inserts the upcast, and the representation is identical.
    let rec unifyArg (offset : int) (paramTy : Type) (argTy : Type) : unit =
        match prune paramTy, prune argTy with
        | TCon (p, pa), TCon (a, aa) when p <> a && isSupertypeOf p a ->
            // widening: the positional pairing is right whenever the
            // subtype passes its parameters straight through (list -> seq),
            // and it is TRIED first so those keep their exact old path. A
            // reader's own parameter is the ELEMENT while IOpReader's is
            // the DELTA — there the pairs cannot unify, and the class's
            // DECLARED instantiation of the supertype carries the real
            // argument mapping instead.
            let resolved =
                match Types.subsumeHook with
                | Some hook -> hook (TCon (p, pa)) (TCon (a, aa))
                | None -> None
            (match resolved with
             | Some (da, db) -> unifyAt offset da db
             | None -> ())
            // the positional pairing still applies wherever it fits — it is
            // what a subtype passing its parameters straight through relies
            // on; after the declared-instantiation unify it is a no-op there
            if pa.Length = aa.Length
               && List.forall2 (fun x y -> (Types.unifyTrial false x y).IsNone) pa aa then
                List.iter2 (unifyAt offset) pa aa
        // a multi-argument member packs its arguments into a tuple, and each
        // POSITION widens independently — `M(cmp, leaf)` against
        // `(IEqualityComparer * SetNode)` must accept a MapLeaf second
        | TTuple ps, TTuple has when ps.Length = has.Length ->
            List.iter2 (unifyArg offset) ps has
        // a function RESULT is read-only, so it widens covariantly — which
        // is also all that `#IOpReader<...>` in a declared callback result
        // needs, since the flexible marker itself is dropped at parse
        | TFun (p1, r1), TFun (p2, r2) ->
            unifyAt offset p1 p2
            unifyArg offset r1 r2
        | _ -> unifyAt offset paramTy argTy

    /// Unify a MEMBER's type against the type its use demands, letting each
    /// argument position widen: `Outputs.Remove x` passes the class where the
    /// declaration says the interface, exactly as F# inserts the upcast.
    let rec unifyMemberAt (offset : int) (demanded : Type) (memT : Type) : unit =
        match prune demanded, prune memT with
        | TFun (dArg, dRes), TFun (mArg, mRes) ->
            unifyArg offset mArg dArg
            unifyMemberAt offset dRes mRes
        | _ -> unifyAt offset demanded memT

    /// The name of a type at its instantiation. A name still mentioning a
    /// type variable (`Pair$<#7.int>`) marks code that is itself generic:
    /// stamping that code substitutes the variable and fixes the layout.
    /// Only a STRUCT type is named per instantiation. A reference type's
    /// fields are uniform whatever it is instantiated at, so stamping it
    /// would buy nothing and only split the type.
    let instName (t : Type) : string =
        match prune t with
        | TCon (n, args) when not (List.isEmpty args) && (dictTryFind structTypes n) = Some true ->
            typeConName t
        | TCon (n, _) -> n
        | other -> typeConName other

    let recordDef (t : Token) (ty : Type) : unit =
        vecAdd defTypes (t.Offset, strLen t.Text, ty)

    // ---- deferred dot-access resolution -----------------------------------
    // `x.M` is meaningless until x's type is known, and that can happen long
    // after the access is first seen (a later call fixes the parameter, say).
    // Every access therefore returns a fresh variable immediately and parks
    // here; the parked set is retried to fixpoint once the file is inferred.
    let mutable pendingStructAttr = false
    let memberSitesRaw = vecNew<int * string> ()
    let fieldOwnersRaw = vecNew<int * string> ()
    let pendingOwners = vecNew<int * Type> ()
    /// dot accesses that bound to a plain DATA field (a record or DU field,
    /// never a member with a body). Assigning to one is as safe to unify
    /// through as assigning to a variable — see the `assign` case.
    let recordFieldTargets = dictNew<int, bool> ()
    let ctorSitesRaw = vecNew<int * int> ()
    /// record literals, resolved after solving so the instantiation is known
    let pendingRecords = vecNew<int * Type> ()
    let pendingDots = vecNew<int * Type * Type * string> ()
    /// `when 'B :> IFace` — the subtype bound, by the variable's id: member
    /// access on the bounded variable resolves through the interface
    let subtypeBounds = dictNew<int, string> ()
    /// computation-expression offset -> the builder expression's type. Only
    /// the PROBE pass fills this: by the time the rewrite has run there is
    /// no CompExpr left to see.
    let compBuildersRaw = vecNew<int * Type> ()
    /// offsets of bare body expressions that turned out to have NO value —
    /// statements, not implicit yields
    let compStmtsRaw = vecNew<int> ()

    /// A body item with no computation keyword of its own: the only kind
    /// whose reading depends on its type.
    let isBareCompItem (m : GreenNode) : bool =
        let kws =
            m.Children
            |> List.choose (fun c -> match c with GToken t when t.Kind = Keyword -> Some t.Text | _ -> None)
        not (List.contains "let" kws) && not (List.contains "use" kws)
        && not (List.contains "do" kws) && not (List.contains "and" kws)
        && not (List.contains "yield" kws) && not (List.contains "return" kws)
        && m.NodeKind <> ForExpr && m.NodeKind <> WhileExpr
        && m.NodeKind <> IfExpr && m.NodeKind <> MatchExpr && m.NodeKind <> TryExpr
    /// `downcast`/`upcast` sites: the target type is only known once the
    /// surrounding expression has been solved
    let pendingCasts = vecNew<int * Type> ()
    let pendingBaseInsts = vecNew<int * Type> ()
    /// `a.[i]` whose receiver was still a variable when the walk reached it —
    /// which is every index into the result of a PARKED dot access, e.g.
    /// `(s.Split ':').[0]`. Retried once the dot fixpoint has run.
    // head offset, receiver, result, bracket offset, index type — the last two
    // are what a user-defined `Item` needs to bind once the receiver settles
    let pendingIndex = vecNew<int * Type * Type * int * Type> ()

    /// Register a member's FieldInfo. A second declaration under the same
    /// name is an OVERLOAD: it keeps its own entry under an ordinal suffix
    /// ("HashMap.CopyTo#2"), assigned in declaration order — the same order
    /// the resolver assigns, so the two suffixes name the same definition.
    /// use-site offset -> how many trailing arguments that use may omit
    let optionalsAt = dictNew<int, int> ()

    let registerField (key : string) (fi : FieldInfo) : unit =
        dictSet knownTypes fi.TypeName true
        // A second entry keyed by the DEFINITION, so a use site that resolved
        // to the definition (a static member through its type, say) can ask
        // how many arguments it may leave off without knowing the receiver.
        // `fields` is the project-wide table, so this crosses files.
        (match fi.DefKey with
         | Some (dp, doff) when fi.Optionals > 0 || not (List.isEmpty fi.ParamNames) ->
             dictSet fields ("$sig:" + dp + ":" + string doff) fi
         | _ -> ())
        if (dictTryFind fields key).IsNone then dictSet fields key fi
        else
            let mutable k = 2
            while (dictTryFind fields (key + "#" + string k)).IsSome do k <- k + 1
            dictSet fields (key + "#" + string k) fi

    // ---- builtin members on `string` --------------------------------------
    // F# code says `name.StartsWith "$<"`, so F++ has to mean it. A string is
    // a primitive with no class to hang members on, so the surface is
    // registered here and emitted through the $str primitives. It is a
    // BOUNDED set, derived from what the compiler's own sources actually
    // call — not the beginning of general extension members on builtins
    // (see DIVERGENCES.md).
    //
    // Overloads use the ordinal mechanism: the second Substring is
    // "string.Substring#2", chosen by the shape the use site was
    // constrained to, exactly like a user-declared overload set.
    let registerStringMembers () =
        if (dictTryFind fields "string.Substring").IsNone then
            let m (ty : Type) =
                { TypeName = "string"; Params = []; Quantified = []
                  FieldType = ty; DefKey = None; IsStatic = false; Optionals = 0; ParamNames = [] }
            let strArr = TCon ("array", [ tString ])
            let charArr = TCon ("array", [ tChar ])
            // the 1-arg form first: ordinal order IS declaration order
            registerField "string.Substring" (m (TFun (tInt, tString)))
            registerField "string.Substring" (m (TFun (TTuple [ tInt; tInt ], tString)))
            registerField "string.StartsWith" (m (TFun (tString, tBool)))
            registerField "string.EndsWith" (m (TFun (tString, tBool)))
            registerField "string.Contains" (m (TFun (tString, tBool)))
            registerField "string.IndexOf" (m (TFun (tString, tInt)))
            registerField "string.IndexOf" (m (TFun (tChar, tInt)))
            registerField "string.IndexOf" (m (TFun (TTuple [ tString; tInt ], tInt)))
            registerField "string.LastIndexOf" (m (TFun (tChar, tInt)))
            registerField "string.Split" (m (TFun (tChar, strArr)))
            registerField "string.Replace" (m (TFun (TTuple [ tString; tString ], tString)))
            registerField "string.Trim" (m (TFun (tUnit, tString)))
            registerField "string.TrimEnd" (m (TFun (charArr, tString)))
            registerField "string.TrimStart" (m (TFun (charArr, tString)))
            // .NET has both; the runtime normalises a single char into a set
            registerField "string.TrimStart" (m (TFun (tChar, tString)))
            registerField "string.TrimEnd" (m (TFun (tChar, tString)))
            registerField "string.ToUpper" (m (TFun (tUnit, tString)))
            registerField "string.ToLower" (m (TFun (tUnit, tString)))
            registerField "string.PadLeft" (m (TFun (tInt, tString)))
            registerField "string.PadRight" (m (TFun (tInt, tString)))
            registerField "string.ToCharArray" (m (TFun (tUnit, charArr)))
            registerField "string.Insert" (m (TFun (TTuple [ tInt; tString ], tString)))
            registerField "string.Remove" (m (TFun (tInt, tString)))
            registerField "string.Remove" (m (TFun (TTuple [ tInt; tInt ], tString)))
            registerField "string.StartsWith" (m (TFun (tChar, tBool)))
            registerField "string.EndsWith" (m (TFun (tChar, tBool)))
            registerField "string.Contains" (m (TFun (tChar, tBool)))
    registerStringMembers ()

    // ---- builtin members on `option` --------------------------------------
    // F# code says `d.IsSome`, so F++ has to mean it. These COULD be written
    // as ordinary members on the prelude's `Option` DU — that compiles — but
    // a member on a generic DU is stamped per instantiation, and `option` is
    // instantiated at nearly every type in the compiler: doing it that way
    // took the 20-file self-emit from 115s/0.6GB to over 30min/30GB. They are
    // properties of the TAG, identical at every element type, so they belong
    // here and lower to a match instead (see DIVERGENCES.md).
    let registerOptionMembers () =
        if (dictTryFind fields "Option.IsSome").IsNone then
            // `Value` reads the payload, so its type IS the receiver's type
            // argument: one parameter, substituted per use site
            let elem = match st.Fresh () with TVar v -> v | _ -> failwith "fresh"
            let m (ty : Type) =
                { TypeName = "Option"; Params = [ elem ]; Quantified = []
                  FieldType = ty; DefKey = None; IsStatic = false; Optionals = 0; ParamNames = [] }
            registerField "Option.IsSome" (m tBool)
            registerField "Option.IsNone" (m tBool)
            registerField "Option.Value" (m (TVar elem))
    registerOptionMembers ()

    // ---- builtin members on `list` ----------------------------------------
    // Same argument as `option`: F# code says `xs.IsEmpty`, and these are
    // properties of the cons CELL, identical at every element type. A member
    // on the generic list would be stamped per element type for nothing.
    let registerListMembers () =
        if (dictTryFind fields "list.IsEmpty").IsNone then
            let elem = match st.Fresh () with TVar v -> v | _ -> failwith "fresh"
            let m (ty : Type) =
                { TypeName = "list"; Params = [ elem ]; Quantified = []
                  FieldType = ty; DefKey = None; IsStatic = false; Optionals = 0; ParamNames = [] }
            registerField "list.IsEmpty" (m tBool)
            registerField "list.Length" (m tInt)
            registerField "list.Head" (m (TVar elem))
            registerField "list.Tail" (m (tList (TVar elem)))
    registerListMembers ()

    /// A member's overload set, with the ordinal that reaches each entry
    /// (0 = the plain key).
    let fieldCandidates (key : string) : (int * FieldInfo) list =
        match dictTryFind fields key with
        | None -> []
        | Some first ->
            let rest =
                List.unfold
                    (fun k ->
                        match dictTryFind fields (key + "#" + string k) with
                        | Some fi -> Some ((k, fi), k + 1)
                        | None -> None)
                    2
            (0, first) :: rest

    /// Could a member of this type serve a use already constrained to that
    /// shape? Purely structural and non-committing — this picks among
    /// OVERLOADS, and a trial unification would corrupt the losers. Any
    /// variable is a wildcard; only concrete structure discriminates, which
    /// is exactly what overloads differ by (a struct tuple against a ref
    /// tuple, one arity against another).
    /// `strict` refuses the supertype allowance: `Equals : obj -> bool`
    /// fits EVERY call once obj widens, so exact fits must outrank widened
    /// ones or the most general overload always wins.
    let rec shapeFits (strict : bool) (cand : Type) (actual : Type) : bool =
        match prune cand, prune actual with
        | TVar _, _ | _, TVar _ -> true
        | TCon (c, ca), TCon (a, aa) ->
            (c = a || (not strict && isSupertypeOf c a))
            && (ca.Length <> aa.Length || List.forall2 (shapeFits strict) ca aa)
        | TFun (a1, b1), TFun (a2, b2) -> shapeFits strict a1 a2 && shapeFits strict b1 b2
        | TTuple xs, TTuple ys -> xs.Length = ys.Length && List.forall2 (shapeFits strict) xs ys
        | _ -> false

    /// The type an overloaded member access is being asked for, keyed by its
    /// name token. Set by the application that surrounds it, for the length
    /// of typing that head and no longer.
    ///
    /// It informs the CHOICE and nothing else. The chosen member is still
    /// unified with the access's own result the way it always was, because
    /// that unification widens arguments — `hs.UnionWith [ 5; 6 ]` passes a
    /// list where a seq is declared — and a demand unified directly would
    /// refuse it.
    /// (offset, demanded type, SYNTACTIC argument count). The count is what
    /// separates `d.TryGetValue v` from `d.TryGetValue (k, &v)` when v's
    /// type is still a variable: one written element means the out-parameter
    /// VIEW, the full count means the .NET signature — exactly F#'s rule.
    let mutable dotDemand : (int * Type * int) option = None

    /// The TUPLE VIEW of a member whose last parameter is an out. F#
    /// synthesizes one for every such method — `d.TryGetValue k` returns
    /// `(found, value)` — so a library writes the .NET signature and calls it
    /// either way. Returns the view and the out parameter's type name, which
    /// is what lowering needs to make the cell.
    let outView (t : Type) : (Type * string) option =
        let nameOf (o : Type) =
            match prune o with
            | TCon (n, _) -> n
            | _ -> "?"
        match prune t with
        | TFun (dom, res) ->
            (match prune dom with
             | TTuple ps when List.length ps >= 2 ->
                 (match prune (List.item (List.length ps - 1) ps) with
                  | TCon ("ByRefCell", [ o ]) ->
                      let rest = ps |> List.take (List.length ps - 1)
                      let d2 = match rest with [ one ] -> one | many -> TTuple many
                      Some (TFun (d2, TTuple [ res; o ]), nameOf o)
                  | _ -> None)
             | TCon ("ByRefCell", [ o ]) -> Some (TFun (tUnit, TTuple [ res; o ]), nameOf o)
             | _ -> None)
        | _ -> None

    /// Try to bind one dot-access. Returns false only when the receiver type
    /// is still unknown — i.e. when retrying later could learn something.
    let rec tryResolveDot (force : bool) (offset : int) (recvTy : Type) (result : Type) (name : string) : bool =
        // members are inherited: walk up the base chain to the type that
        // actually declares this one, and bind to THAT declaration
        // Walk to the type that declares this member, carrying the receiver's
        // type arguments up through each `inherit` so a generic base is
        // instantiated the way the derived class instantiated it.
        // Types are keyed by BARE NAME, so `IAdaptiveValue` and
        // `IAdaptiveValue<'T>` share one entry and the generic one's
        // `inherit IAdaptiveValue` can make a type its own base. The record
        // below refuses the self-edge; this refuses every longer cycle, and
        // costs one set on a walk that is a handful of links deep.
        let seenOwners = dictNew<string, bool> ()
        let rec declaringOwner (tn : string) (args : Type list) : ((int * FieldInfo) list * string * Type list) option =
            if (dictTryFind seenOwners tn).IsSome then None else
            dictSet seenOwners tn true
            match fieldCandidates (tn + "." + name) with
            | (_ :: _) as cs -> Some (cs, tn, args)
            | [] ->
                match dictTryFind bases tn with
                | Some (ps, baseTy) ->
                    let subst = dictNew<int, Type> ()
                    if ps.Length = args.Length then
                        List.zip ps args |> List.iter (fun (pv, a) -> dictSet subst (prunedId pv) a)
                    (match prune (substVars subst baseTy) with
                     | TCon (bn, bargs) -> declaringOwner bn bargs
                     | _ -> None)
                | None ->
                    // an EXTENSION member on an interface the receiver
                    // implements (`type IAdaptiveObject with member
                    // x.MarkOutdated ...`) declares through the interface;
                    // without this hop the access fell to the by-name field
                    // lookup, which types fine and records nothing — and
                    // emission then read an unknown FIELD
                    // NOT for the enumerator protocol: the for-in lowering
                    // has its own resolution for those, and binding them here
                    // broke `for e in x` over a class enumerated another way
                    if name = "GetEnumerator" || name = "MoveNext" || name = "Current" || name = "Dispose" then None else
                    match dictTryFind impls tn with
                    | Some ifs ->
                        ifs |> List.tryPick (fun i ->
                            match fieldCandidates (i + "." + name) with
                            | (_ :: _) as cs -> Some (cs, i, [])
                            | [] -> None)
                    | None -> None
        // Instantiating the member's own scheme (rather than substituting
        // into its type) is what turns the use into a specialization demand:
        // a generic class' members must be stamped per element type just
        // like a generic function's.
        // Only when the member is declared on the receiver's OWN type: for an
        // inherited member the declared self is the base, and unifying it
        // with the receiver would demand a subtyping the unifier has no
        // notion of. Type arguments are unified, never the nominal head.
        let tracked (ownerTag : string) (tn : string) (args : Type list) (fi : FieldInfo) : bool =
            match fi.DefKey with
            | Some (dp, doff) when not fi.IsStatic && fi.TypeName = tn ->
                // ANOTHER FILE's member is a specialization demand just like
                // this file's — the prelude's own generic classes are reached
                // that way, and without the demand the linker dropped their
                // layout-dependent templates and the call named nothing
                // ("unbound variable Add" on a ResizeArray<int>)
                (match (if dp = path then dictTryFind defSchemes doff
                        else dictTryFind shared (dp + ":" + string doff)) with
                 | Some sch ->
                     (match (if dp = path then instantiateTracked sch else instantiateImported sch) with
                      | TFun (selfT, memT), fresh, _ ->
                          (match prune selfT with
                           | TCon (sn, sargs) when sn = tn && sargs.Length = args.Length ->
                               List.iter2 (unifyAt offset) sargs args
                               // the same out-parameter view the general path
                               // takes; a member of THIS file arrives here
                               let demanded, argc =
                                   match dotDemand with
                                   | Some (off, want, c) when off = offset -> want, Some c
                                   | _ -> result, None
                               // the WRITTEN element count decides between the
                               // .NET byref signature and its tuple view — a
                               // still-variable argument fits both, and the
                               // full signature then swallowed the variable
                               let viewFits () =
                                   match outView memT with
                                   | Some (v, outName) when (Types.unifyTrial false v demanded).IsNone ->
                                       Some (v, outName)
                                   | _ -> None
                               let fullParams =
                                   match prune memT with
                                   | TFun (d, _) ->
                                       (match prune d with TTuple ps -> List.length ps | _ -> 1)
                                   | _ -> 0
                               let preferView =
                                   match argc with
                                   | Some c -> c = fullParams - 1
                                   | None -> false
                               let memT =
                                   if preferView then
                                       match viewFits () with
                                       | Some (v, outName) ->
                                           vecAdd fieldOwnersRaw (offset, "$out:" + outName)
                                           v
                                       | None -> memT
                                   elif (Types.unifyTrial false memT demanded).IsNone then memT
                                   else
                                       match viewFits () with
                                       | Some (v, outName) ->
                                           vecAdd fieldOwnersRaw (offset, "$out:" + outName)
                                           v
                                       | _ -> memT
                               unifyMemberAt offset result memT
                               if not (List.isEmpty fresh) then vecAdd instRaw (offset, fresh)
                               vecAdd memberSitesRaw (offset, ownerTag)
                               true
                           | _ -> false)
                      | _ -> false)
                 | None -> false)
            | _ -> false
        match prune recvTy, name with
        // a variable BOUNDED by `when 'B :> IFace` dispatches its members
        // through the bound, exactly as F# types it
        | TVar v, _ when (dictTryFind subtypeBounds v.Id).IsSome ->
            tryResolveDot force offset (TCon ((dictTryFind subtypeBounds v.Id).Value, [])) result name
        // `.Length` on an array or a string is a BUILTIN: there is no
        // "array.Length" in the fields table, so without this the parked
        // path fell through to a by-name field lookup and bound the access
        // to some unrelated record that happens to declare a `Length` —
        // silently, since a field WAS found. The eager path (where the
        // receiver type is already known) has always answered here; a
        // receiver that only takes shape through another parked dot
        // (`(s.Substring 1).Split ':'`) reaches this one and must agree.
        | TCon ("array", [ e ]), "Length" ->
            unifyAt offset result tInt
            vecAdd arrKindsRaw (offset, TCon ("array", [ e ]))
            true
        | TCon ("string", []), "Length" ->
            // sentinel: string RECEIVER, not string elements
            unifyAt offset result tInt
            vecAdd arrKindsRaw (offset, TCon ("$str", []))
            true
        | _ ->
        match prune recvTy with
        | TCon (tn, args) ->
            let universal () =
                // .NET's UNIVERSAL object members: every class answers
                // GetHashCode and Equals even without declaring them. The
                // defaults are reference semantics (a constant hash is
                // legal — all-equal — and Equals is identity), marked for
                // lowering by a sentinel owner.
                if (name = "GetHashCode" || name = "Equals") && (dictTryFind knownTypes tn).IsSome then
                    (match name with
                     | "GetHashCode" -> unifyMemberAt offset result (TFun (tUnit, tInt))
                     | _ -> unifyMemberAt offset result (TFun (TCon ("obj", []), tBool)))
                    vecAdd memberSitesRaw (offset, "$object")
                    true
                else false
            (match declaringOwner tn args with
             | Some (cands, own, ownArgs) ->
                 // one candidate is today's path; several are an overload
                 // set, filtered by the shape the use site has ALREADY been
                 // constrained to (the retry runs after the whole file is
                 // typed, so a call's arguments are visible through `result`)
                 // With several candidates, the use site has to have taken
                 // SHAPE before choosing means anything — an access resolves
                 // eagerly, before its application has constrained `result`,
                 // and everything fits an unconstrained variable. So an
                 // uninformative overload set stays parked; the retry runs
                 // after the whole file is typed, and a final FORCED pass
                 // breaks genuine ties in declaration order.
                 let demanded =
                     match dotDemand with
                     | Some (off, want, _) when off = offset -> want
                     | _ -> result
                 let informative =
                     match prune demanded with
                     | TVar _ -> false
                     | _ -> true
                 if List.length cands > 1 && not informative && not force then false else
                 // Selection is a real unification, tried and then undone.
                 // What this replaced was a structural stand-in that called
                 // every unresolved type a wildcard — so a three-parameter
                 // member "fit" a one-argument call, and the overload
                 // declared FIRST won. `MapExt.TryRemove(key)` reached
                 // `TryRemove(key, &result, &removed)` that way, and the
                 // mismatch surfaced a line off from the call.
                 //
                 // Under `unifyTrial true` the caller's own type parameters
                 // are RIGID: the body has to work for every instantiation,
                 // so a candidate may not choose them to make itself fit.
                 // That is the question F# asks, and asking it properly is
                 // what makes arity fall out rather than be special-cased.
                 let ord, fi =
                     match cands with
                     | [ one ] -> one
                     | many ->
                         // Fit first, exactness second. Exactness is measured
                         // on the PARAMETER positions only: `IndexOf(Index)`
                         // takes an Index argument with zero bindings where
                         // `IndexOf('T)` must bind one — and picking the
                         // generic member bound the receiver's own class
                         // parameter, corrupting every later use of the type.
                         // Result positions stay out of the count (they bind
                         // the use's fresh result either way), and a still
                         // unconstrained argument scores every candidate the
                         // same, which leaves the tie to declaration order.
                         let score (c : FieldInfo) : int option =
                             let subst = dictNew<int, Type> ()
                             for pv in c.Params do dictSet subst (prunedId pv) (st.Fresh ())
                             for qv in c.Quantified do dictSet subst (prunedId qv) (st.Fresh ())
                             for fv in freeVars c.FieldType do
                                 if (dictTryFind subst (prunedId fv)).IsNone then
                                     dictSet subst (prunedId fv) (st.Fresh ())
                             let ft = substVars subst c.FieldType
                             match Types.unifyTrialScore true ft demanded with
                             | None -> None
                             | Some _ ->
                                 match prune ft, prune demanded with
                                 | TFun (p1, _), TFun (p2, _) ->
                                     (match Types.unifyTrialScore true p1 p2 with
                                      | Some n -> Some n
                                      | None -> Some 1000000)
                                 | _ -> Some 0
                         let scored =
                             many |> List.choose (fun (o, c) -> score c |> Option.map (fun n -> n, (o, c)))
                         (match scored with
                          | _ :: _ ->
                              // an EXACT fit (zero parameter bindings)
                              // outranks declaration order; anything less
                              // exact keeps the old first-fit rule, which
                              // matters when arguments are still variables
                              (match scored |> List.tryPick (fun (n, pc) -> if n = 0 then Some pc else None) with
                               | Some pc -> pc
                               | None -> snd (List.head scored))
                          | [] ->
                              // Nothing fits EXACTLY. Widening is the one
                              // rule plain unification does not model —
                              // `Equals : obj -> bool` takes anything once
                              // obj widens — so the structural test gets the
                              // second word, and only then declaration order.
                              match many |> List.filter (fun (_, c) -> shapeFits false c.FieldType demanded) with
                              | picked :: _ -> picked
                              // none at all: the use is wrong, and binding
                              // the first puts the mismatch at THIS use with
                              // both types named
                              | [] -> List.head many)
                 let ownerTag =
                     if ord = 0 then fi.TypeName else fi.TypeName + "#" + string ord
                 if own = tn && tracked ownerTag tn args fi then true
                 elif fi.Params.Length = ownArgs.Length || (fi.IsStatic && List.isEmpty ownArgs) then
                     // a STATIC access parked before its declaration carries
                     // no receiver arguments; freshen the class parameters
                     let ownArgs =
                         if fi.Params.Length = ownArgs.Length then ownArgs
                         else fi.Params |> List.map (fun _ -> st.Fresh ())
                     let subst = dictNew<int, Type> ()
                     List.zip fi.Params ownArgs |> List.iter (fun (pv, a) -> dictSet subst (prunedId pv) a)
                     for qv in fi.Quantified do dictSet subst (prunedId qv) (st.Fresh ())
                     // EVERY remaining free variable freshens too: the stored
                     // type is shared project-wide, and unifying a var that
                     // leaked into it from another declaration bound that
                     // declaration's parameter FOR EVERYONE (MapExt's 'Key
                     // went to int through one such use)
                     for fv in freeVars fi.FieldType do
                         if (dictTryFind subst (prunedId fv)).IsNone then
                             dictSet subst (prunedId fv) (st.Fresh ())
                     // F# synthesizes a TUPLE VIEW for a trailing out
                     // parameter: `d.TryGetValue k` is `(found, value)` where
                     // the declaration says `TryGetValue(k, value : byref<_>)`.
                     // The declaration stays .NET's; the view is the
                     // compiler's, as it is in F#.
                     let declared = substVars subst fi.FieldType
                     let chosen =
                         if (Types.unifyTrial false declared demanded).IsNone then declared
                         else
                             match outView declared with
                             | Some (v, outName) when (Types.unifyTrial false v demanded).IsNone ->
                                 vecAdd fieldOwnersRaw (offset, "$out:" + outName)
                                 v
                             | _ -> declared
                     unifyMemberAt offset result chosen
                     vecAdd memberSitesRaw (offset, ownerTag)
                     if fi.DefKey.IsNone then
                         // named AFTER solving, like a record literal: at
                         // this moment the receiver's arguments may still be
                         // variables, and naming it now produced the BARE
                         // template name while the write named the
                         // instantiation — two representations for one value
                         vecAdd pendingOwners (offset, recvTy)
                         dictSet recordFieldTargets offset true
                     // a SAME-FILE member is a generic function once lifted:
                     // this use is a specialization demand like any other,
                     // recorded in the definition scheme's own variable
                     // order so the stamper's zip lines up. Without it a
                     // layout-dependent static resolved through the PARKED
                     // path emitted a bare EVar — and the template it named
                     // had been removed by stamping
                     (match fi.DefKey with
                      | Some (dp, doff) when dp = path ->
                          (match dictTryFind defSchemes doff with
                           | Some sch when not (List.isEmpty sch.Quantified) ->
                               let inst =
                                   sch.Quantified
                                   |> List.map (fun qv ->
                                       match dictTryFind subst qv.Id with
                                       | Some t -> t
                                       | None -> st.Fresh ())
                               vecAdd instRaw (offset, inst)
                           | _ -> ())
                      | _ -> ())
                     true
                 else true
             | None ->
                 // "no such member" is only meaningful once the FIELDS table
                 // is complete — during the main pass a member declared later
                 // in the same class has not registered yet, and giving up
                 // here silently unbound `for e in x` over self. Stay parked;
                 // the forced pass concedes — to the UNIVERSAL object
                 // members, when the name is one of theirs.
                 if force then (universal () || true) else false)
        | _ -> false

    /// `recv.[i]` where the receiver declares `member x.Item` — a .NET
    /// indexer. There is no `Item` TOKEN in the source to key the binding on,
    /// so the access is bound at a synthetic offset derived from the bracket,
    /// exactly the way the `for … in` protocol binds GetEnumerator. The
    /// setter is bound too whenever the type declares one; `b.[i] <- v` needs
    /// it, and a get-only indexer simply leaves it unbound.
    let tryResolveIndexer (recvTy : Type) (br : int) (idxTy : Type) (result : Type) : bool =
        match prune recvTy with
        | TCon (tn, _) when tn <> "array" && tn <> "string" ->
            if tryResolveDot false (60000000 + br) recvTy (TFun (idxTy, result)) "Item" then
                tryResolveDot false (70000000 + br) recvTy (TFun (idxTy, TFun (result, tUnit))) "set_Item"
                |> ignore
                true
            else false
        | _ -> false

    let nodesOf (n : GreenNode) : GreenNode list =
        n.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)

    /// how many of this member's parameters were written `?x`. F# requires
    /// them last, so the count IS how many a caller may leave off.
    let optionalArity (m : GreenNode) : int =
        nodesOf m
        |> List.filter (fun p -> p.NodeKind = ParenPat)
        |> List.sumBy (fun p ->
            p.Children
            |> List.sumBy (fun c ->
                match c with
                | GToken q when q.Kind = Operator && q.Text = "?" -> 1
                | _ -> 0))

    let tokensOf (n : GreenNode) : Token list =
        n.Children |> List.choose (fun c -> match c with GToken t -> Some t | _ -> None)

    /// the member's parameter names, in order. "" for a parameter that is
    /// not a plain identifier — it can never be named at a call.
    let paramNames (m : GreenNode) : string list =
        match nodesOf m |> List.filter (fun p -> p.NodeKind = ParenPat) with
        | pp :: _ ->
            nodesOf pp
            // the OTHER children are the ascriptions' type nodes
            |> List.filter (fun p ->
                match p.NodeKind with
                | IdentPat | WildcardPat | LiteralPat | TuplePat | StructTuplePat
                | ConsPat | AppPat | ParenPat | ListPat | AsPat | TypeTestPat -> true
                | _ -> false)
            |> List.map (fun p ->
                // the match comes LAST: a `match` with an `else` after it
                // swallows the else, and this has to compile under itself
                let ids = tokensOf p |> List.filter (fun t -> t.Kind = Ident)
                if p.NodeKind <> IdentPat then ""
                else
                    match ids with
                    | [ nt ] -> nt.Text
                    | _ -> "")
        | [] -> []


    /// The label of a record-literal field. It may be qualified with the
    /// owning type or module (`{ Classes.MPath = p; ... }`), in which case
    /// the label is the LAST identifier before the '=', not the first.
    let recordFieldLabel (f : GreenNode) : Token option =
        let mutable found = None
        let mutable stop = false
        for t in tokensOf f do
            if not stop then
                if t.Kind = Operator && t.Text = "=" then stop <- true
                elif t.Kind = Ident then found <- Some t
        found

    let hasOpToken (text : string) (n : GreenNode) : bool =
        tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = text)

    let isPatKind (k : NodeKind) =
        k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat || k = StructTuplePat
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat || k = TypeTestPat

    let isTypeKind (k : NodeKind) =
        k = NamedType || k = VarType || k = AnonType || k = TupleType || k = StructTupleType
        || k = FunType || k = AppType || k = PostfixType || k = ParenType

    let isExprish (k : NodeKind) = not (isPatKind k) && not (isTypeKind k) && k <> TyParams

    // ---- syntax types -> Type ---------------------------------------------

    /// Convert a type node. `vars` maps type-variable names to Types and is
    /// per-declaration so repeated 'a in one signature mean the same thing.
    // ---- multi-arity type names -------------------------------------------
    // .NET keys a type as Name`N — the arity is part of the name, which is
    // how `IOpReader<'D>` and `IOpReader<'S,'D>` coexist in one namespace.
    // Types here were keyed by BARE name, so the two merged: they shared a
    // layout, and a five-line repro died with `missing field`. The same
    // decoration is adopted: the FIRST arity seen keeps the plain name (so
    // nothing that does not collide is renamed, and the deliberate merge
    // with a same-named prelude type still happens), each further arity is
    // `Name`N`. The table rides in `aliases`, which is already project-wide.
    let arityDeclared (name : string) (n : int) : unit =
        match dictTryFind aliases ("$arity:" + name) with
        | None ->
            let vs =
                List.init n (fun _ -> st.Fresh ())
                |> List.choose (fun t -> match prune t with TVar v -> Some v | _ -> None)
            dictSet aliases ("$arity:" + name) (vs, TCon (name, []))
        | Some (ps, _) ->
            if ps.Length <> n then
                dictSet aliases ("$arity:" + name + ":" + string n) ([], TCon (name, []))
    /// the KEY for this name at this arity — plain unless a colliding
    /// variant was declared at exactly this arity
    let arityName (name : string) (n : int) : string =
        if (dictTryFind aliases ("$arity:" + name + ":" + string n)).IsSome
        then name + "`" + string n
        else name
    /// the variant a resolved DEFINITION means — for a bare use, where no
    /// written arguments say which type of this name is intended
    let arityNameOfDef (d : Resolve.Definition) : string =
        match dictTryFind aliases ("$adecl:" + d.Path + ":" + string d.Offset) with
        | Some (ps, _) -> arityName d.Name ps.Length
        | None -> d.Name

    /// every declared variant of a name, for a use that does not write its
    /// type arguments (a bare constructor call chooses by ARGUMENT fit)
    let arityVariants (name : string) : string list =
        name
        :: (List.init 9 (fun i -> i)
            |> List.filter (fun i -> (dictTryFind aliases ("$arity:" + name + ":" + string i)).IsSome)
            |> List.map (fun i -> name + "`" + string i))

    /// A constructor's quantified variables, DECLARED parameters first.
    /// `H<'S, 'D>(x : voption<W<'D>>, ...)` writes 'D before 'S in its
    /// parameters, so free-variable encounter order is ['D; 'S] — and the
    /// explicit type application `H<'S, 'D>(...)` pins POSITIONALLY against
    /// scheme order. Crossed pins unified 'S into 'D and every History
    /// constructor collapsed to Traceable<'a, 'a>.
    let ctorQuantified (declared : Type list) (ctorTy : Type) : Var list =
        let declVars = declared |> List.choose (fun t -> match prune t with TVar v -> Some v | _ -> None)
        let declIds = declVars |> List.map (fun v -> v.Id) |> Set.ofList
        declVars
        @ (freeVars ctorTy
           |> List.distinctBy (fun v -> v.Id)
           |> List.filter (fun v -> not (Set.contains v.Id declIds)))

    let rec typeFromNode (vars : Dict<string, Type>) (n : GreenNode) : Type =
        let namedVar (name : string) : Type =
            match dictTryFind vars name with
            | Some t -> t
            | None ->
                let t = st.Fresh ()
                dictSet vars name t
                t
        let expandAlias (name : string) (args : Type list) : Type option =
            match dictTryFind aliases name with
            | Some (ps, body) when ps.Length = args.Length ->
                let subst = dictNew<int, Type> ()
                List.zip ps args |> List.iter (fun (p, a) -> dictSet subst p.Id a)
                let rec go (t : Type) : Type =
                    match prune t with
                    | TVar v -> (match dictTryFind subst v.Id with Some a -> a | None -> TVar v)
                    | TCon (c, xs) -> TCon (c, List.map go xs)
                    | TFun (a, b) -> TFun (go a, go b)
                    | TTuple ts -> TTuple (List.map go ts)
                Some (go body)
            | _ -> None
        match n.NodeKind with
        | VarType ->
            (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
             | Some t -> namedVar t.Text
             | None -> st.Fresh ())
        | AnonType -> st.Fresh ()
        | NamedType ->
            let name =
                match tokensOf n |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                | Some t -> t.Text
                | None -> "?"
            (match expandAlias name [] with
             | Some t -> t
             | None -> TCon (name, []))
        | AppType ->
            (match nodesOf n with
             | head :: _ ->
                 let args =
                     nodesOf n |> List.tail |> List.filter (fun m -> isTypeKind m.NodeKind)
                     |> List.map (typeFromNode vars)
                 (match nodesOf n |> List.tryHead with
                  | Some h when h.NodeKind = NamedType ->
                      let name =
                          match tokensOf h |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                          | Some t -> t.Text
                          | None -> "?"
                      (match expandAlias name args with
                       | Some t -> t
                       | None -> TCon (arityName name args.Length, args))
                  | _ ->
                      match typeFromNode vars head with
                      | TCon (name, []) -> TCon (name, args)
                      | TVar _ when args.Length > 0 ->
                          // HKT application 'm<'a> — beyond the HM core for now
                          st.Fresh ()
                      | other -> other)
             | [] -> st.Fresh ())
        | PostfixType ->
            (match nodesOf n, tokensOf n with
             | [ inner ], [ t ] when t.Kind = Ident ->
                 let arg = typeFromNode vars inner
                 (match expandAlias t.Text [ arg ] with
                  | Some ty -> ty
                  | None -> TCon (arityName t.Text 1, [ arg ]))
             | [ inner ], _ -> TCon ("array", [ typeFromNode vars inner ])   // int[]
             | _ -> st.Fresh ())
        | FunType ->
            (match nodesOf n with
             | [ a; b ] -> TFun (typeFromNode vars a, typeFromNode vars b)
             | _ -> st.Fresh ())
        | TupleType ->
            TTuple (nodesOf n |> List.filter (fun m -> isTypeKind m.NodeKind) |> List.map (typeFromNode vars))
        | StructTupleType ->
            // the same generic struct the expression and pattern forms use
            let rec elems (m : GreenNode) =
                if m.NodeKind = ParenType || m.NodeKind = TupleType then
                    nodesOf m |> List.filter (fun x -> isTypeKind x.NodeKind) |> List.collect elems
                else [ m ]
            let ts =
                nodesOf n |> List.filter (fun m -> isTypeKind m.NodeKind) |> List.collect elems
            TCon ("StructTuple" + string ts.Length, ts |> List.map (typeFromNode vars))
        | ParenType ->
            (match nodesOf n with
             | [ inner ] -> typeFromNode vars inner
             | _ -> st.Fresh ())
        | _ -> st.Fresh ()

    // ---- literals ---------------------------------------------------------

    // ---- the class layer ---------------------------------------------------
    // Wanted constraints accumulate as inference proceeds and are solved to
    // fixpoint. Anything still unsolved when a binding generalizes becomes
    // part of its scheme — the caller inherits the obligation.

    let mutable wanted : (int * Constraint) list = []
    /// constraints the enclosing binding DECLARED (`when Num<'a>`); a wanted
    /// entailed by one of these is already discharged
    let mutable givens : Constraint list = []
    /// class-member use offset -> the instance member it resolved to
    let classUsesRaw = vecNew<int * Classes.InstMember> ()
    /// class-member uses parked until solving finishes: the instance is
    /// often only pinned down by a later unification
    /// (offset, member, constraint, byName). A use written as a NAME
    /// (`Add.(+)`) must denote a function even at a primitive instance; one
    /// written as an operator (`a + b`) emits the instruction instead.
    let pendingClassUses = vecNew<int * string * Constraint * bool> ()
    /// operator offset -> the left operand's type, for the backend
    let opTypesRaw = vecNew<int * Type> ()
    let exprTypesRaw = vecNew<int * int * Type> ()

    let addWanted (offset : int) (c : Constraint) : unit = wanted <- wanted @ [ offset, c ]

    let isGround (c : Constraint) : bool = List.isEmpty (List.collect freeVars c.Args)

    /// Discharge a wanted against the declared context, if the context
    /// entails it. Returns the associated-type bindings the given fixes.
    let byGiven (c : Constraint) : (string * Type) list option =
        givens
        |> List.collect (Classes.entailed classes)
        |> List.tryPick (fun g -> if Classes.sameHead g c then Some g.Assoc else None)

    /// One solving pass. Returns whether anything changed, and the wanteds
    /// that survive.
    let solveOnce () : bool =
        let mutable progress = false
        let survivors = vecNew<int * Constraint> ()
        let queue = vecNew<int * Constraint> ()
        for w in wanted do vecAdd queue w
        let mutable i = 0
        // an instance context that re-demands its own class would grow the
        // queue forever INSIDE this pass — dedupe repeats, bound the work
        let seenKey = dictNew<string, bool> ()
        let keyOf (c : Constraint) =
            c.Class + "|" + String.concat "," (List.map typeString c.Args)
        let budget = vecLen queue * 4 + 256
        while i < vecLen queue && i < budget do
            let offset, c = vecGet queue i
            i <- i + 1
            let k = keyOf c
            if (dictTryFind seenKey k).IsSome then vecAdd survivors (offset, c)
            else
            dictSet seenKey k true
            match byGiven c with
            | Some assoc ->
                progress <- true
                for n, ty in c.Assoc do
                    match assoc |> List.tryFind (fun (an, _) -> an = n) with
                    | Some (_, gt) -> unifyAt offset ty gt
                    | None -> ()
            | None ->
                // ordering on TUPLES is structural, as in F#: the builtin
                // instance demands orderedness of every component instead
                match c.Class, c.Args |> List.map prune with
                | "Ordered", [ TTuple ts ] ->
                    progress <- true
                    for t in ts do
                        vecAdd queue (offset, { Class = "Ordered"; Args = [ t ]; Assoc = [] })
                | _ ->
                match Classes.select classes c.Class c.Args c.Assoc with
                | Classes.Solved (inst, sub) ->
                    progress <- true
                    for n, ty in c.Assoc do
                        match inst.Assoc |> List.tryFind (fun (an, _) -> an = n) with
                        | Some (_, it) -> unifyAt offset ty (Classes.substInst sub it)
                        | None ->
                            vecAdd diags (offset, "instance " + inst.Class + " does not define the associated type " + n)
                    for ctx in inst.Context do
                        vecAdd queue (offset, mapConstraint (Classes.substInst sub) ctx)
                | Classes.Improve inst ->
                    // exactly one instance could still apply, so its head is
                    // forced: committing to it is improvement, not a guess
                    progress <- true
                    let sub = dictNew<int, Type> ()
                    for v in inst.Params do dictSet sub v.Id (st.Fresh ())
                    let mutable failed = false
                    List.iter2
                        (fun h a ->
                            match unify (Classes.substInst sub h) a with
                            | Some err ->
                                failed <- true
                                vecAdd diags (offset, err)
                            | None -> ())
                        inst.Head c.Args
                    // a FAILED improvement is terminal: re-queueing the
                    // unchanged constraint would improve it again, forever,
                    // inside this very pass — the fuel counter never fires
                    if not failed then vecAdd queue (offset, c)
                | Classes.Deferred -> vecAdd survivors (offset, c)
                | Classes.Ambiguous insts ->
                    // overlapping instances that order neither way. More
                    // information cannot break the tie, so say so here
                    // rather than letting the use fall through unresolved.
                    if isGround c then
                        progress <- true
                        vecAdd diags
                            (offset,
                             "overlapping instances for " + c.Class + "<"
                             + String.concat ", " (List.map typeString c.Args)
                             + ">: " + String.concat " and " (insts |> List.map (fun i ->
                                 i.Class + "<" + String.concat ", " (List.map typeString i.Head) + ">"))
                             + " — neither is more specific")
                    else vecAdd survivors (offset, c)
                | Classes.NoInstance ->
                    if isGround c then
                        progress <- true
                        vecAdd diags
                            (offset,
                             "no instance " + c.Class + "<"
                             + String.concat ", " (List.map typeString c.Args) + ">")
                    else vecAdd survivors (offset, c)
        // whatever the budget cut off survives untouched for the next pass
        while i < vecLen queue do
            vecAdd survivors (vecGet queue i)
            i <- i + 1
        wanted <- vecToList survivors
        progress

    /// Solve to fixpoint. Cheap: each pass either discharges a constraint or
    /// stops, and the store is small.
    let solveWanted () : unit =
        let mutable go = true
        let mutable fuel = 100
        while go && fuel > 0 do
            fuel <- fuel - 1
            go <- solveOnce ()

    /// The instance a resolved constraint selected, if it has a body for
    /// `member`. A builtin instance has none: the backend emits it directly.
    /// Close a binding over its type AND its context. Whatever the body left
    /// unsolved becomes the caller's obligation; anything the binding itself
    /// declared with `when` is kept whether or not the body needed it.
    /// > 0 while typing a nested let — those must neither solve nor move
    /// the wanted pool, which belongs to the enclosing top-level binding
    /// The type `base` denotes inside the type declaration being inferred.
    /// Set for the whole declaration, so members and `do` bindings alike see
    /// it.
    let mutable currentBase : Type option = None
    /// Mark (or unmark) every type parameter a signature wrote. Rigidity is
    /// a property of the BODY being typed, not of the variable forever.
    let setRigid (vars : Dict<string, Type>) (on : bool) : Var list =
        let touched = vecNew<Var> ()
        for _, t in dictPairs vars do
            match prune t with
            | TVar v ->
                // only ones this call actually changes come back, so an
                // enclosing binding's rigidity survives a nested one
                if v.Rigid <> on then
                    v.Rigid <- on
                    vecAdd touched v
            | _ -> ()
        vecToList touched

    /// The member-name token of a head that IS a member access, and nothing
    /// else — a qualified value or a constructor is somebody else's job.
    let memberDemandTok (head : GreenNode) : Token option =
        if head.NodeKind <> DotExpr then None
        else Green.tokens (GNode head) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast

    /// What the pattern about to be typed must BE. Consumed by whoever
    /// reads it, so a nested pattern never inherits its parent's answer by
    /// accident — the parent passes it down deliberately or not at all.
    ///
    /// Only one question needs it: whether a parenthesised comma pattern
    /// destructures a REFERENCE tuple or a STRUCT one. Nothing in the
    /// pattern says, and F# reads it from the scrutinee — allowing
    /// `ValueSome (a, b)` over a struct-tuple payload while rejecting the
    /// same pattern in a `let`.
    /// Uses of parameters DECLARED `byref`/`outref`. F# dereferences a byref
    /// on read — but only a byref: a `ref` CELL is the same representation
    /// here and must not be touched, or `r.Contents` reads through the cell
    /// twice. So the declaration decides, not the type.
    let byrefParams = dictNew<int, bool> ()

    /// Suppresses the automatic dereference of a byref. A byref READ in F#
    /// means the value — `let x = location` copies what the cell holds — but
    /// two positions want the CELL: the operand of `&`, which forwards it,
    /// and the left of an assignment, which writes through it.
    let mutable noDeref = false

    let mutable patExpect : Type option = None

    /// What the expression about to be typed is expected to BE. Consumed by
    /// whoever reads it, so nothing inherits it by accident.
    ///
    /// One question needs it, and it is the mirror of the pattern one:
    /// `(a, b)` builds a REFERENCE tuple unless a struct tuple is what the
    /// context asks for. F# reads it the same way, and the library relies on
    /// it — `PairwiseCyclicV` stores `struct(v0, v1)` in its loop and
    /// `(v0, initial)` after it, into the same map.
    let mutable exprExpect : Type option = None


    let mutable letDepth = 0

    /// The enclosing binding's named type variables ('K of the member or
    /// class being typed). Written type arguments in EXPRESSION position
    /// (`HashMap<'K, 'V>(...)`) must resolve here — a fresh scope would
    /// disconnect them from the signature they name
    let mutable tyScope : Dict<string, Type> = dictNew<string, Type> ()

    let generalizeBinding (declared : Constraint list) (ty : Type) : Scheme =
        if letDepth > 0 then
            // a LOCAL binding: solving here is premature — `let acc = mempty`
            // has not met the annotation that ties its variable down yet, and
            // a lone instance would let improvement ground it. The wanteds
            // stay pooled for the enclosing top-level binding.
            st.Generalize ty
        else
        // solve UNDER the binding's declared context: without it, a lone
        // instance lets improvement GROUND the annotated variable — a
        // `when Monoid<'a>` function silently became int-only
        let saved = givens
        givens <- givens @ declared
        solveWanted ()
        givens <- saved
        let sch = st.GeneralizeWith (declared @ List.map snd wanted) ty
        let moved (c : Constraint) =
            sch.Constraints |> List.exists (fun k -> System.Object.ReferenceEquals (k, c))
        wanted <- wanted |> List.filter (fun (_, c) -> not (moved c))
        sch

    /// Which function an operator or a named member resolves to.
    ///
    /// The rule is PER MEMBER, not per instance: a member the instance gives
    /// a body to is called; one it leaves out is a machine instruction. That
    /// is what lets `instance Floating<float>` write `exp` in source while
    /// `sqrt` stays an `f64.sqrt`, and what stops `compare`'s own body from
    /// calling itself through the `<` it is written with.
    ///
    /// A NAMED use additionally falls back to a generated wrapper, because a
    /// name has to denote something callable even where the operator is an
    /// instruction.
    let instanceMember (byName : bool) (c : Constraint) (memberName : string) : Classes.InstMember option =
        match Classes.select classes c.Class c.Args c.Assoc with
        | Classes.Solved (inst, sub) ->
            // What the instance's own variables were matched to HERE. A
            // generic instance body is a template like any other generic
            // binding, and this is the instantiation that stamps it.
            let instArgs =
                inst.Params |> List.map (fun v ->
                    match (match dictTryFind sub v.Id with
                           | Some t -> Some t
                           | None -> dictTryFind sub (prunedId v)) with
                    | Some t ->
                        (match prune t with
                         // named like any other instantiation, ARGUMENTS and
                         // all — an instance over `'a[]` reached at float[][]
                         // must stamp at float[], not at a bare "array"
                         | TCon (_, targs) when not (List.isEmpty targs) -> typeConName t
                         | TCon (n, _) -> n
                         | TVar tv -> "#" + string tv.Id
                         | TTuple _ | TFun _ -> "$ref"
                         | _ -> "")
                    | None -> "")
            let attach (k : Classes.InstMember) = { k with Classes.MInst = instArgs }
            match inst.Members |> List.tryPick (fun (m, k) -> if m = memberName then Some k else None) with
            | Some k -> Some (attach k)
            | None when byName ->
                (match dictTryFind classes.Classes c.Class with
                 | Some cd ->
                     (match cd.Members |> List.tryFindIndex (fun (m, _) -> m = memberName) with
                      | Some index -> Some (attach (Classes.wrapperMember inst index memberName))
                      | None -> None)
                 | None -> None)
            | None -> None
        | _ -> None

    /// The head of `class C<'a,'b>` / `instance C<int,int>`: the class name
    /// and its arguments, typed in `vars`.
    let classHead (vars : Dict<string, Type>) (n : GreenNode) : (string * Type list) option =
        match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
        | Some hd when hd.NodeKind = AppType ->
            (match nodesOf hd with
             | h :: _ ->
                 let name =
                     tokensOf h |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                     |> Option.map (fun t -> t.Text)
                 let args =
                     nodesOf hd |> List.tail |> List.filter (fun m -> isTypeKind m.NodeKind)
                     |> List.map (typeFromNode vars)
                 name |> Option.map (fun nm -> nm, args)
             | [] -> None)
        | Some hd ->
            tokensOf hd |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
            |> Option.map (fun t -> t.Text, [])
        | None -> None

    /// `when C<'a> with Result = 'a` (and the `= 'a` shorthand, which names
    /// the class' only associated type).
    /// F#'s own constraint spellings, as the classes that mean the same
    /// thing. `equality` and the rest are not omissions: structural `=` is
    /// builtin, so an equality constraint asks for nothing, and `struct` /
    /// `not struct` / `null` / `new` say things about a CLR representation
    /// that has no counterpart here.
    let fsharpConstraintClass (name : string) : string option =
        match name with
        | "comparison" -> Some "Ordered"
        | "unmanaged" -> Some "Unmanaged"
        | _ -> None

    /// `when 'a : comparison` — F#'s INLINE form, which spells the same
    /// thing as `when Ordered<'a>` and reads through the same function.
    let fsharpInlineConstraint (vars : Dict<string, Type>) (n : GreenNode) : Constraint option =
        let idents = tokensOf n |> List.filter (fun t -> t.Kind = Ident)
        let hasColon = tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = ":")
        if not hasColon then None
        else
            match idents |> List.tryLast with
            | Some last ->
                (match fsharpConstraintClass last.Text with
                 | Some cls ->
                     // the constrained variable, read from the TOKENS: the
                     // inline form is absorbed verbatim (that is what keeps
                     // the parse lossless), so there is no type node to read
                     let rec varAfterTick (ts : Token list) =
                         match ts with
                         | a :: b :: rest ->
                             if a.Kind = Operator && a.Text = "'" && b.Kind = Ident then Some b.Text
                             else varAfterTick (b :: rest)
                         | _ -> None
                     (match varAfterTick (tokensOf n) |> Option.bind (dictTryFind vars) with
                      | Some argTy -> Some { Class = cls; Args = [ argTy ]; Assoc = [] }
                      | None ->
                          match n.Children |> List.tryPick (fun c ->
                                    match c with
                                    | GNode ty when isTypeKind ty.NodeKind -> Some (typeFromNode vars ty)
                                    | _ -> None) with
                          | Some argTy -> Some { Class = cls; Args = [ argTy ]; Assoc = [] }
                          | None -> None)
                 | None -> None)
            | None -> None

    let constraintOf (vars : Dict<string, Type>) (n : GreenNode) : Constraint option =
        // `when 'B :> IFace` is not a class constraint, but the BOUND is
        // what resolves member access on 'B — recorded as a side effect,
        // since every when-clause reader comes through here
        (let rec scanBound (ts : Token list) =
            match ts with
            | a :: b :: c :: rest when
                    a.Kind = Operator && a.Text = "'" && b.Kind = Ident
                    && c.Kind = Operator && c.Text = ":>" ->
                let rec ifaceOf (ts2 : Token list) (last : Token option) =
                    match ts2 with
                    | t :: more when t.Kind = Ident -> ifaceOf more (Some t)
                    | t :: more when t.Kind = Operator && t.Text = "." -> ifaceOf more last
                    | _ -> last
                (match ifaceOf rest None, dictTryFind vars b.Text with
                 | Some it, Some tv ->
                     (match prune tv with
                      | TVar v -> dictSet subtypeBounds v.Id it.Text
                      | _ -> ())
                 | _ -> ())
                scanBound rest
            | _ :: rest -> scanBound rest
            | [] -> ()
         scanBound (tokensOf n))
        match fsharpInlineConstraint vars n with
        | Some c -> Some c
        | None ->
        classHead vars n
        |> Option.map (fun (cls, args) ->
            let assocName =
                    match tokensOf n |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                    | Some t when tokensOf n |> List.exists (fun t2 -> t2.Kind = Keyword && t2.Text = "with") -> Some t.Text
                    | _ ->
                        match dictTryFind classes.Classes cls with
                        | Some cd -> (match cd.Assoc with [ only ] -> Some only | _ -> None)
                        | None -> None
            let rhs =
                    // the type after `=`, if any
                    let rec afterEq (cs : Green list) =
                        match cs with
                        | GToken t :: GNode ty :: _ when t.Kind = Operator && t.Text = "=" && isTypeKind ty.NodeKind ->
                            Some (typeFromNode vars ty)
                        | _ :: rest -> afterEq rest
                        | [] -> None
                    afterEq n.Children
            let assoc =
                match assocName, rhs with
                | Some a, Some r -> [ a, r ]
                | _ -> []
            { Class = cls; Args = args; Assoc = assoc })

    let memberNameOf (m : GreenNode) : Token option =
        tokensOf m |> List.tryFind (fun t -> t.Kind = Ident)

    let isAssocDecl (m : GreenNode) : bool =
        tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "type")

    let hasBody (m : GreenNode) : bool =
        m.Children |> List.exists (fun c -> match c with GNode b -> isExprish b.NodeKind | _ -> false)

    /// Replace a bare `Result` (an associated-type name) with the variable
    /// standing for it. Associated types never enter `Type` as a projection;
    /// they are variables tied down by the member's own constraint.
    let bindAssoc (assocVars : Dict<string, Type>) (t : Type) : Type =
        let rec go (t : Type) : Type =
            match prune t with
            | TCon (n, []) ->
                (match dictTryFind assocVars n with Some v -> v | None -> TCon (n, []))
            | TCon (n, args) -> TCon (n, List.map go args)
            | TFun (a, b) -> TFun (go a, go b)
            | TTuple ts -> TTuple (List.map go ts)
            | other -> other
        go t

    let literalType (t : Token) : Type =
        match t.Kind with
        | IntLit ->
            // integer literal suffixes, F#'s: 5y sbyte, 5uy byte, 5s int16,
            // 5us uint16, 5u/5ul uint32, 5L int64, 5UL uint64. The longer
            // ones are tested FIRST — `5UL` ends with `L` too.
            if t.Text.EndsWith "UL" || t.Text.EndsWith "uL"
               || t.Text.EndsWith "Ul" || t.Text.EndsWith "uLL" then TCon ("uint64", [])
            elif t.Text.EndsWith "L" then TCon ("int64", [])
            elif t.Text.EndsWith "uy" || t.Text.EndsWith "UY" then TCon ("byte", [])
            elif t.Text.EndsWith "y" || t.Text.EndsWith "Y" then TCon ("sbyte", [])
            elif t.Text.EndsWith "us" || t.Text.EndsWith "US" then TCon ("uint16", [])
            elif t.Text.EndsWith "s" || t.Text.EndsWith "S" then TCon ("int16", [])
            elif t.Text.EndsWith "u" || t.Text.EndsWith "U" then tUInt
            else tInt
        | FloatLit ->
            // `1.5h` is a half — F# has no such literal, so the spelling is
            // ours; `f` keeps its F# meaning
            if t.Text.EndsWith "h" || t.Text.EndsWith "H" then TCon ("float16", [])
            elif t.Text.EndsWith "f" || t.Text.EndsWith "F" then TCon ("float32", [])
            else tFloat
        | StringLit -> tString
        | CharLit -> tChar
        | Keyword when t.Text = "true" || t.Text = "false" -> tBool
        | _ -> st.Fresh ()

    // ---- patterns ---------------------------------------------------------

    /// Type of a pattern; assigns fresh monomorphic schemes to the names the
    /// pattern binds (identified as definitions by the resolver). `pvars`
    /// scopes type variables of ascriptions to the enclosing binding, so
    /// `(v : Vec<'a>) (x : 'a)` share one 'a.
    let rec patType (pvars : Dict<string, Type>) (n : GreenNode) : Type =
        match n.NodeKind with
        | WildcardPat -> st.Fresh ()
        | LiteralPat ->
            (match tokensOf n |> List.tryLast with
             | Some t -> literalType t
             | None -> st.Fresh ())
        | IdentPat ->
            // A QUALIFIED case pattern (`Classes.Improve inst`) names its
            // case in the LAST identifier — the leading spine is a module.
            // Taking the first typed the pattern off the MODULE name, so the
            // constructor was never instantiated and the payload binder
            // stayed unknown, along with everything read out of it.
            let identToks = tokensOf n |> List.filter (fun t -> t.Kind = Ident)
            let headTok =
                if tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = ".") then
                    List.tryLast identToks
                else List.tryHead identToks
            (match headTok with
             | Some t ->
                 match dictTryFind defsAt t.Offset with
                 | Some _ ->
                     // a binding introduced here
                     let ty = st.Fresh ()
                     setScheme t.Offset (mono ty)
                     recordDef t ty
                     ty
                 | None ->
                     // a constructor use
                     (match dictTryFind useDefs t.Offset with
                      | Some d ->
                          (match instantiateFor d with
                           | Some (t, _) -> t
                           | None -> st.Fresh ())
                      | None -> st.Fresh ())
             | None -> st.Fresh ())
        | AppPat ->
            (match nodesOf n with
             | head :: args ->
                 let want = patExpect
                 patExpect <- None
                 let ctorTy = patType pvars head
                 // Tie the case's RESULT to what this pattern must be FIRST:
                 // that is what makes the payload's type known, and the
                 // payload pattern is about to be typed against it.
                 (match want, prune ctorTy with
                  | Some w, TFun (_, res) -> unify res w |> ignore
                  | _ -> ())
                 let payloadWant =
                     match prune ctorTy with
                     | TFun (dom, _) -> Some dom
                     | _ -> None
                 let argTys =
                     args
                     |> List.filter (fun m -> isPatKind m.NodeKind)
                     |> List.map (fun m ->
                         patExpect <- payloadWant
                         let t = patType pvars m
                         patExpect <- None
                         t)
                 (match argTys with
                  | [] -> ctorTy
                  | [ argTy ] ->
                      let res = st.Fresh ()
                      (match tokensOf head |> List.tryHead with
                       | Some t -> unifyAt t.Offset ctorTy (TFun (argTy, res))
                       | None -> unify ctorTy (TFun (argTy, res)) |> ignore)
                      res
                  | _ -> st.Fresh ())
             | [] -> st.Fresh ())
        | TypeTestPat ->
            // `:? T` narrows to T; the scrutinee itself stays a supertype.
            // The resolved target is recorded in the owner channel: written
            // against a GENERIC parameter the name alone is meaningless, and
            // lowering needs the symbolic form stamping can substitute.
            (match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
             | Some tn ->
                 let ty = typeFromNode pvars tn
                 (match Green.tokens (GNode tn) |> List.tryHead with
                  | Some t -> vecAdd pendingOwners (t.Offset, ty)
                  | None -> ())
                 ty
             | None -> st.Fresh ())
        | TuplePat ->
            let want = patExpect
            patExpect <- None
            let elems = nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind)
            let asStruct =
                match want with
                | Some w ->
                    (match prune w with
                     | TCon (sn, args) when
                            sn.StartsWith "StructTuple" && List.length args = List.length elems ->
                         Some (sn, args)
                     | _ -> None)
                | None -> None
            (match asStruct with
             | Some (sn, args) ->
                 // A struct tuple destructured by a plain comma pattern.
                 // Marked at the pattern's offset, because lowering reads
                 // the node KIND and this node lies about it.
                 let tys = elems |> List.map (patType pvars)
                 List.iter2 (fun t a -> unify t a |> ignore) tys args
                 // recorded in the OWNER channel, which is where lowering
                 // already looks for a struct pattern's instantiated name
                 (match Green.tokens (GNode n) |> List.tryHead with
                  | Some t -> vecAdd pendingOwners (t.Offset, TCon (sn, args))
                  | None -> ())
                 TCon (sn, args)
             | None ->
                 // a tuple matched against a TUPLE passes each element's
                 // expected type down: `| ValueSome(_, l), ValueNone ->`
                 // needs the left element to know its payload is a struct
                 let elemWant =
                     match want with
                     | Some w ->
                         (match prune w with
                          | TTuple ts when List.length ts = List.length elems -> ts
                          | _ -> [])
                     | None -> []
                 if List.isEmpty elemWant then
                     TTuple (elems |> List.map (patType pvars))
                 else
                     TTuple (List.map2
                                 (fun (e : GreenNode) (w : Type) ->
                                     patExpect <- Some w
                                     let t = patType pvars e
                                     patExpect <- None
                                     t)
                                 elems elemWant))
        | StructTuplePat ->
            // the same generic struct the `struct(a, b)` expression builds
            let rec unwrap (m : GreenNode) =
                if m.NodeKind = ParenPat || m.NodeKind = TuplePat then
                    nodesOf m |> List.filter (fun x -> isPatKind x.NodeKind) |> List.collect unwrap
                else [ m ]
            let ps =
                nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) |> List.collect unwrap
            let ty = TCon ("StructTuple" + string ps.Length, ps |> List.map (patType pvars))
            // the element types are fixed by the right-hand side, so the
            // instantiated name is only known after solving
            (match Green.tokens (GNode n) |> List.tryHead with
             | Some t -> vecAdd pendingRecords (t.Offset, ty)
             | None -> ())
            ty
        | ConsPat ->
            (match nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) with
             | [ h; t ] ->
                 let hd = patType pvars h
                 let tl = patType pvars t
                 (match tokensOf n |> List.tryHead with
                  | Some tok -> unifyAt tok.Offset tl (tList hd)
                  | None -> unify tl (tList hd) |> ignore)
                 tl
             | items -> (items |> List.iter (patType pvars >> ignore)); st.Fresh ())
        | ListPat ->
            let elem = st.Fresh ()
            for m in nodesOf n do
                if isPatKind m.NodeKind then unify (patType pvars m) elem |> ignore
            tList elem
        | AsPat ->
            // `pat as name` — the name gets the pattern's type
            (match nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) with
             | [ inner; name ] ->
                 let t = patType pvars inner
                 unify (patType pvars name) t |> ignore
                 t
             | [ inner ] -> patType pvars inner
             | _ -> st.Fresh ())
        | ParenPat ->
            // sequence of patterns, each optionally ascribed, comma-separated
            let want = patExpect
            patExpect <- None
            let items = vecNew<Type> ()
            let kids = n.Children
            // a tuple matched against a TUPLE passes each element's expected
            // type down: `| ValueSome(_, l), ValueNone ->` needs the left
            // element to know its payload is a struct tuple
            let elemWant =
                match want with
                | Some w ->
                    (match prune w with
                     | TTuple ts -> ts
                     | _ -> [])
                | None -> []
            let mutable elemIx = 0
            // `?retries : int` declares an `int option`. The `?` is its own
            // token in the tree, so it is seen just before the pattern it
            // belongs to.
            let mutable optNext = false
            let rec walk (ks : Green list) =
                match ks with
                | GToken q :: rest when q.Kind = Operator && q.Text = "?" ->
                    optNext <- true
                    walk rest
                | GNode p :: rest when isPatKind p.NodeKind ->
                    let isOpt = optNext
                    optNext <- false
                    (if elemIx < List.length elemWant then
                        patExpect <- Some (List.item elemIx elemWant))
                    elemIx <- elemIx + 1
                    let ty = patType pvars p
                    patExpect <- None
                    (match rest with
                     | GToken c :: GNode a :: rest2 when c.Text = ":" && isTypeKind a.NodeKind ->
                         // `(location : byref<int>)` — the DECLARATION is
                         // what makes a read dereference, not the type: a
                         // `ref` cell is the same representation and must be
                         // read as itself
                         (match Green.tokens (GNode a) |> List.filter (fun x -> x.Kind = Ident) |> List.tryHead with
                          | Some ht when ht.Text = "byref" || ht.Text = "outref" ->
                              (match Green.tokens (GNode p) |> List.tryFind (fun x -> x.Kind = Ident) with
                               | Some bt -> dictSet byrefParams bt.Offset true
                               | None -> ())
                          | _ -> ())
                         let declared = typeFromNode pvars a
                         unify ty (if isOpt then TCon ("Option", [ declared ]) else declared) |> ignore
                         vecAdd items ty
                         walk rest2
                     | GToken b :: _ when b.Kind = Operator && b.Text = "|" ->
                         // or-alternatives: all unify, one item
                         let rec ors (ks2 : Green list) =
                             match ks2 with
                             | GToken b2 :: GNode alt :: rest3 when b2.Kind = Operator && b2.Text = "|" && isPatKind alt.NodeKind ->
                                 unify (patType pvars alt) ty |> ignore
                                 ors rest3
                             | _ -> ks2
                         let rest2 = ors rest
                         vecAdd items ty
                         walk rest2
                     | _ ->
                         vecAdd items ty
                         walk rest)
                | _ :: rest -> walk rest
                | [] -> ()
            walk kids
            match vecToList items with
            | [] -> tUnit
            | [ one ] -> one
            | many ->
                // A comma pattern says nothing about which KIND of tuple it
                // takes apart, and F# reads that from what it is matched
                // against: `ValueSome (a, b)` over a struct-tuple payload is
                // allowed, the same pattern in a `let` is not. Marked at the
                // pattern's offset in the owner channel, which is where
                // lowering already looks for a struct pattern's name.
                match want with
                | Some w ->
                    (match prune w with
                     | TCon (sn, args) when
                            sn.StartsWith "StructTuple" && List.length args = List.length many ->
                         List.iter2 (fun t a -> unify t a |> ignore) many args
                         (match Green.tokens (GNode n) |> List.tryHead with
                          | Some t -> vecAdd pendingOwners (t.Offset, TCon (sn, args))
                          | None -> ())
                         TCon (sn, args)
                     | _ -> TTuple many)
                | None -> TTuple many
        | _ -> st.Fresh ()

    // ---- expressions ------------------------------------------------------

    let opClass (text : string) : string =
        if text = "&&" || text = "||" then "logic"
        elif text = "::" then "cons"
        elif text = "|>" then "pipe"
        elif text = "<|" then "pipeBack"
        elif text = ">>" then "compose"
        elif text = "<<" then "composeBack"
        elif text = "=" || text = "<>" || text = "<" || text = ">" || text = "<=" || text = ">=" then "cmp"
        elif text = "+" || text = "-" || text = "*" || text = "/" || text = "%" || text = "**" then "arith"
        elif text = "&&&" || text = "|||" || text = "^^^" || text = "<<<" || text = ">>>" then "bits"
        elif text = "@" then "append"
        elif text = "<-" || text = ":=" then "assign"
        else "unknown"

    let rec exprType (g : Green) : Type =
        let t = exprTypeOf g
        // remember what every node came out as; pruning happens at the end,
        // once unification has settled
        (match g with
         | GNode n ->
             (match Green.tokens (GNode n) |> List.filter (fun tk -> tk.Kind <> Eof) with
              | [] -> ()
              | tks ->
                  let first = List.head tks
                  let last = List.last tks
                  vecAdd exprTypesRaw (first.Offset, last.Offset + last.Text.Length, t))
         | GToken _ -> ())
        t

    and exprTypeOf (g : Green) : Type =
        // Consumed HERE, once, by whichever node is about to be typed. An
        // expectation left standing leaks into a NESTED expression — it
        // reached a constructor inside `ValueSome struct(v, HashMap(...))`
        // and tied its result to the tuple. Only the nodes that deliberately
        // pass it on set it again.
        let expected = exprExpect
        exprExpect <- None
        ignore expected
        match g with
        | GToken _ -> st.Fresh ()
        | GNode n ->
            match n.NodeKind with
            | LiteralExpr ->
                (match tokensOf n |> List.tryHead with
                 | Some t -> literalType t
                 | None -> st.Fresh ())
            | IdentExpr when
                    tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "base") ->
                (match currentBase with
                 | Some t -> t
                 | None -> st.Fresh ())
            | IdentExpr ->
                (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
                 | Some t when (tokensOf n |> List.head).Kind = Ident ->
                     (match dictTryFind useDefs t.Offset with
                      | Some d ->
                          // a use OWES the scheme's context: instantiating it
                          // at int is what turns `Zero` into zero-at-int
                          let owe (cs : Constraint list) : unit =
                              for c in cs do addWanted t.Offset c
                              match dictTryFind classes.MemberOwner t.Text with
                              | Some cls ->
                                  (match cs |> List.tryFind (fun c -> c.Class = cls) with
                                   | Some c -> vecAdd pendingClassUses (t.Offset, t.Text, c, true)
                                   | None -> ())
                              | None -> ()
                          (match schemeOfDef d with
                           | Some sc when not (List.isEmpty sc.Quantified) && d.Path = path ->
                               let ty, fresh, cs = instantiateTracked sc
                               owe cs
                               vecAdd instRaw (t.Offset, fresh)
                               ty
                           | Some sc when not (List.isEmpty sc.Quantified) ->
                               // another file's generic binding: still a
                               // specialization demand, so record it
                               let ty, fresh, cs = instantiateImported sc
                               owe cs
                               vecAdd instRaw (t.Offset, fresh)
                               ty
                           | _ ->
                               match instantiateFor d with
                               | Some (ty, cs) ->
                                   owe cs
                                   // A byref READ means the value. F#
                                   // dereferences it silently and the
                                   // library writes `let mutable initial =
                                   // location`; without this the CELL came
                                   // out, and `f initial` asked `'T` to
                                   // become `ByRefCell<'T>`. Two positions
                                   // want the cell and say so — `&x` and the
                                   // left of an assignment.
                                   (match prune ty with
                                    | TCon ("ByRefCell", [ inner ]) when
                                           not noDeref && (dictTryFind byrefParams d.Offset).IsSome ->
                                        vecAdd fieldOwnersRaw (t.Offset, "$deref")
                                        inner
                                    | _ -> ty)
                               | None -> st.Fresh ())
                      | None -> st.Fresh ())
                 | _ -> st.Fresh ())   // quote-ident type variable
            | AppExpr ->
                (match nodesOf n with
                 | head :: args ->
                     // a numeric conversion needs the SOURCE type, which the
                     // backend's kind analysis cannot see through a global
                     (match head.NodeKind, args with
                      | IdentExpr, [ onlyArg ] when
                            (match tokensOf head |> List.tryHead with
                             | Some t -> List.contains t.Text [ "int"; "int64"; "uint32"; "uint64"; "int16"; "uint16"; "float"; "float32"; "float16"; "string"; "char"; "byte"; "sbyte" ]
                             | None -> false) ->
                          (match tokensOf head |> List.tryHead with
                           | Some ct -> vecAdd opKindsRaw (ct.Offset, exprType (GNode onlyArg))
                           | None -> ())
                      | _ -> ())
                     (match head.NodeKind, args with
                      | IdentExpr, [ onlyArg ] when
                            (tokensOf head |> List.tryHead |> Option.map (fun t -> t.Text)) = Some "print" ->
                          (match tokensOf head |> List.tryHead with
                           | Some pt -> vecAdd opKindsRaw (pt.Offset, exprType (GNode onlyArg))
                           | None -> ())
                      | _ -> ())
                     // the printf family: the format literal IS the type —
                     // each hole a curried parameter, its resolved kind
                     // recorded at a synthetic offset inside the literal for
                     // the expansion to read. The application may be flat
                     // (`sprintf fmt a b` in one AppExpr), so the remaining
                     // arguments unify here.
                     let formatFamily =
                         match head.NodeKind, args with
                         | IdentExpr, fmtArg :: rest ->
                             (match tokensOf head |> List.tryHead with
                              | Some t when List.contains t.Text [ "sprintf"; "printf"; "printfn"; "failwithf" ]
                                            && (dictTryFind useDefs t.Offset).IsNone ->
                                  (match Green.tokens (GNode fmtArg) |> List.tryHead with
                                   | Some ft when ft.Kind = StringLit ->
                                       let raw = ft.Text.Substring (1, ft.Text.Length - 2)
                                       (match Format.parse raw with
                                        | Ok segs ->
                                            let holeTys =
                                                Format.holes segs
                                                |> List.mapi (fun i (c, _, _, _) ->
                                                    let ty =
                                                        match c with
                                                        // any integer width, decided by
                                                        // the recorded kind at expansion
                                                        | 'd' | 'i' | 'x' | 'X' | 'o' | 'u' -> st.Fresh ()
                                                        | 's' -> tString
                                                        | 'c' -> tChar
                                                        | 'b' -> tBool
                                                        | 'f' -> tFloat
                                                        | _ -> st.Fresh ()   // %A takes anything
                                                    vecAdd opKindsRaw (ft.Offset + 1 + i, ty)
                                                    ty)
                                            let ret =
                                                match t.Text with
                                                | "sprintf" -> tString
                                                | "failwithf" -> st.Fresh ()
                                                | _ -> tUnit
                                            let restExprs = rest |> List.filter (fun m -> isExprish m.NodeKind)
                                            let restTys = restExprs |> List.map (fun a -> exprType (GNode a))
                                            let applied = List.truncate restTys.Length holeTys
                                            if restTys.Length <= holeTys.Length then
                                                List.iter2 (unifyAt t.Offset) applied restTys
                                            let remaining = List.skip (min restTys.Length holeTys.Length) holeTys
                                            Some (List.foldBack (fun h acc -> TFun (h, acc)) remaining ret)
                                        | Error msg ->
                                            vecAdd diags (ft.Offset, msg)
                                            Some (st.Fresh ()))
                                   | _ ->
                                       vecAdd diags (t.Offset, "a format string must be a literal")
                                       Some (st.Fresh ()))
                              | _ -> None)
                         | _ -> None
                     match formatFamily with
                     | Some t -> t
                     | None ->
                     // `sizeof<'T>` — the compiler KNOWS every layout, so
                     // this is a real constant, resolved per instantiation
                     // at monomorphization. Typed int; the written
                     // argument's INSTANTIATION NAME rides to lowering.
                     let sizeofMark =
                         match head.NodeKind with
                         | IdentExpr when
                               (tokensOf head |> List.tryHead |> Option.map (fun t -> t.Text)) = Some "sizeof"
                               && (tokensOf head |> List.tryHead |> Option.map (fun t -> (dictTryFind useDefs t.Offset).IsNone)) = Some true ->
                             (match tokensOf head |> List.tryHead,
                                    args |> List.tryFind (fun m -> m.NodeKind = TyParams) with
                              | Some ht, Some tp ->
                                  (match nodesOf tp |> List.filter (fun x -> isTypeKind x.NodeKind) with
                                   | [ ta ] ->
                                       let ty = typeFromNode tyScope ta
                                       vecAdd fieldOwnersRaw (ht.Offset, "$sizeof:" + instName ty)
                                       true
                                   | _ -> false)
                              | _ -> false)
                         | _ -> false
                     if sizeofMark then tInt else
                     // numeric conversions are primitives, not functions
                     let conversion =
                         match head.NodeKind, args with
                         | IdentExpr, [ onlyArg ] ->
                             (match tokensOf head |> List.tryHead with
                              | Some t when t.Text = "int64" && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some (TCon ("int64", []))
                              | Some t when (t.Text = "int" || t.Text = "uint32" || t.Text = "int16" || t.Text = "uint16")
                                            && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some (if t.Text = "int" then tInt else tUInt)
                              // widening and narrowing between float widths
                              | Some t when List.contains t.Text [ "float"; "float32"; "float16" ]
                                            && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some (TCon (t.Text, []))
                              | Some t when t.Text = "int64" && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some (TCon ("int64", []))
                              | Some t when t.Text = "string" && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some tString
                              // a char IS its code point, so this only
                              // changes how the value reads
                              | Some t when t.Text = "char" && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some tChar
                              // byte and sbyte are int-shaped like char: the
                              // conversion changes how the value READS, and
                              // the emitter masks to the width
                              | Some t when (t.Text = "byte" || t.Text = "sbyte")
                                            && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some (TCon (t.Text, []))

                              | Some t when t.Text = "isNull" && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some tBool
                              | _ -> None)
                         | _ -> None
                     match conversion with
                     | Some t -> t
                     | None ->
                     // A type may offer several constructors. Type the
                     // arguments first, then take the one whose parameter
                     // actually accepts them — F#'s overload resolution,
                     // restricted to constructors.
                     let ctorChoice =
                         // the WRITTEN type-argument count, taken from the
                         // outer head before ctorHead narrows to the bare
                         // identifier — `Reader<int, string>(1)` says 2
                         let writtenCount =
                             match nodesOf head |> List.tryFind (fun m -> m.NodeKind = TyParams) with
                             | Some tp ->
                                 Some (nodesOf tp |> List.filter (fun x -> isTypeKind x.NodeKind) |> List.length)
                             | None -> None
                         // the head may carry explicit type arguments:
                         // `HashSet<'K>(comparer, root)`
                         let ctorHead =
                             if head.NodeKind = IdentExpr then Some head
                             // QUALIFIED: `Impl.Node(k, v)` names the type by
                             // its path, and the overload set belongs to the
                             // last segment. Without this the qualified call
                             // never reached selection and took the primary
                             // constructor whatever its arity.
                             elif head.NodeKind = DotExpr then Some head
                             elif head.NodeKind = AppExpr
                                  && (nodesOf head |> List.exists (fun x -> x.NodeKind = TyParams)) then
                                 (match nodesOf head |> List.tryFind (fun x -> x.NodeKind = IdentExpr) with
                                  | Some h -> Some h
                                  | None -> nodesOf head |> List.tryFind (fun x -> x.NodeKind = DotExpr))
                             else None
                         match ctorHead with
                         | None -> None
                         | Some head ->
                             match tokensOf head |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                             | Some ht ->
                                 (match dictTryFind useDefs ht.Offset with
                                  | Some d when d.Kind = Resolve.DefType ->
                                      // an ABBREVIATION constructs the type
                                      // it names: `cval 1` builds a
                                      // ChangeableValue, so the constructor
                                      // set is the TARGET's
                                      let ctorName =
                                          match dictTryFind aliases d.Name with
                                          | Some (_, body) ->
                                              (match prune body with
                                               | TCon (t, _) -> t
                                               | _ -> d.Name)
                                          | None -> d.Name
                                      // the written type arguments pick the
                                      // VARIANT; without them, every variant's
                                      // constructors compete and the argument
                                      // fit decides — the same trial that
                                      // separates ordinary overloads
                                      let written = writtenCount
                                      let cands =
                                          match written with
                                          | Some k ->
                                              (match dictTryFind ctors (arityName ctorName k) with
                                               | Some cs -> cs
                                               | None -> [])
                                          | None ->
                                              arityVariants ctorName
                                              |> List.collect (fun v ->
                                                  match dictTryFind ctors v with
                                                  | Some cs -> cs
                                                  | None -> [])
                                      // ONE candidate is still the answer
                                      // when the name has variants: the
                                      // ordinary path resolves the name to
                                      // its LAST declaration, which may be
                                      // the wrong variant entirely
                                      let hasVariants = (arityVariants ctorName).Length > 1
                                      // the hop through an ABBREVIATION is
                                      // tentative: commit only when a target
                                      // constructor matches the written
                                      // argument count — the compiler's own
                                      // BCL-shaped aliases (Vec, RefMap)
                                      // construct with arguments the
                                      // prelude's classes never declared,
                                      // and those keep the lenient path
                                      let hopOk () =
                                          if ctorName = d.Name then true
                                          else
                                              // a bare `Vec<'a>` head carries NO
                                              // argument node at all — that is a
                                              // type-applied VALUE, not a
                                              // construction; `Vec<'a>()` still
                                              // counts as zero via its empty parens
                                              let writtenArgs =
                                                  match args |> List.filter (fun a -> isExprish a.NodeKind) with
                                                  | [] -> -1
                                                  | [ one ] when one.NodeKind = ParenExpr
                                                                 && (nodesOf one |> List.filter (fun m -> isExprish m.NodeKind) |> List.isEmpty) -> 0
                                                  | xs -> List.length xs
                                              cands |> List.exists (fun (_, csch) ->
                                                  match prune csch.Body with
                                                  | TFun (dom, _) ->
                                                      let n =
                                                          match prune dom with
                                                          | TCon ("unit", []) -> 0
                                                          | TTuple ts -> List.length ts
                                                          | _ -> 1
                                                      n = writtenArgs
                                                  | _ -> false)
                                      (match cands with
                                       | cs when cs.Length > 1 && hopOk () -> Some (ht, cs)
                                       // ONE candidate is still the answer
                                       // when the ordinary path has nothing:
                                       // a struct-block type's scheme lives
                                       // on its `new` members, and the TYPE
                                       // definition itself carries none
                                       | [ _ ] when (hasVariants || (schemeOfDef d).IsNone) && hopOk () -> Some (ht, cands)
                                       | _ -> None)
                                  | _ -> None)
                             | None -> None
                     // `new T(Prop = v, ...)` — an object INITIALIZER. The
                     // constructor takes nothing and the named pairs set
                     // fields on what it made; read as an application, each
                     // pair is an equality test and the call comes out as a
                     // tuple of bools.
                     // the head must name a TYPE. `LBool (b = "1")` applies a
                     // union CASE to a comparison and looks identical
                     let headIsType =
                         // `new T<_>(...)` writes its type arguments, so the
                         // head is an application and its LAST identifier is
                         // a type ARGUMENT — the name is the first one
                         let headTok =
                             if head.NodeKind = AppExpr then
                                 nodesOf head
                                 |> List.tryFind (fun x -> x.NodeKind = IdentExpr)
                                 |> Option.bind (fun x -> Green.tokens (GNode x) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast)
                             else Green.tokens (GNode head) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                         match headTok with
                         | Some ht ->
                             (match dictTryFind useDefs ht.Offset with
                              | Some d -> d.Kind = Resolve.DefType
                              | None -> false)
                         | None -> false
                     let initPairs =
                         match args |> List.filter (fun a -> isExprish a.NodeKind) with
                         | [ one ] when headIsType && one.NodeKind = ParenExpr ->
                             let items =
                                 match nodesOf one |> List.filter (fun m -> isExprish m.NodeKind) with
                                 | [ t ] when t.NodeKind = TupleExpr ->
                                     nodesOf t |> List.filter (fun m -> isExprish m.NodeKind)
                                 | ms -> ms
                             let asPair (m : GreenNode) =
                                 if m.NodeKind <> BinaryExpr then None
                                 else
                                     match nodesOf m, tokensOf m with
                                     | [ l; r ], [ op ] when op.Text = "=" && l.NodeKind = IdentExpr ->
                                         (match tokensOf l |> List.tryHead with
                                          | Some nt when nt.Kind = Ident -> Some (nt, r)
                                          | _ -> None)
                                     | _ -> None
                             let pairs = items |> List.map asPair
                             if not (List.isEmpty pairs) && pairs |> List.forall (fun p -> p.IsSome)
                             then Some (pairs |> List.map (fun p -> p.Value))
                             else None
                         | _ -> None
                     match initPairs with
                     | Some pairs ->
                         let selfTy =
                             match prune (exprType (GNode head)) with
                             | TFun (_, res) -> res
                             | other -> other
                         (match prune selfTy with
                          | TCon (tn, _) ->
                              for nameTok, valueNode in pairs do
                                  let vt = exprType (GNode valueNode)
                                  (match dictTryFind fields (tn + "." + nameTok.Text) with
                                   | Some fi ->
                                       let subst = dictNew<int, Type> ()
                                       for pv in fi.Params do dictSet subst (prunedId pv) (st.Fresh ())
                                       for qv in fi.Quantified do dictSet subst (prunedId qv) (st.Fresh ())
                                       for fv in freeVars fi.FieldType do
                                           if (dictTryFind subst (prunedId fv)).IsNone then
                                               dictSet subst (prunedId fv) (st.Fresh ())
                                       unifyAt nameTok.Offset (substVars subst fi.FieldType) vt
                                       vecAdd memberSitesRaw (nameTok.Offset, tn)
                                   | None ->
                                       vecAdd diags (nameTok.Offset, tn + " has no field " + nameTok.Text))
                              (match Green.tokens (GNode n) |> List.tryHead with
                               | Some t -> vecAdd fieldOwnersRaw (t.Offset, "$init:" + tn)
                               | None -> ())
                          | _ ->
                              for _, valueNode in pairs do exprType (GNode valueNode) |> ignore)
                         selfTy
                     | None ->
                     match ctorChoice with
                     | Some (ht, cs) ->
                         let argTys =
                             args |> List.filter (fun a -> isExprish a.NodeKind)
                                  |> List.map (fun a -> exprType (GNode a))
                         let argTy =
                             match argTys with
                             | [] -> tUnit
                             | [ one ] -> one
                             | many -> TTuple many
                         // A trial unifies for REAL and is then undone, so
                         // one candidate's attempt cannot corrupt the next —
                         // which is what a structural stand-in was there to
                         // avoid, at the cost of calling every unresolved
                         // type a wildcard. That cost was the bug: two
                         // constructors of the same arity both "fit" a call
                         // whose arguments are the caller's own type
                         // parameters, and the first declared won.
                         //
                         // Under `unifyTrial true` those parameters are
                         // RIGID — the body has to work for every
                         // instantiation, so a candidate may not choose them
                         // — and `MapExt(comparer, root)` fails against
                         // `(key, value)` for the same reason F# fails it.
                         //
                         // Subtyping is the one thing unification does not
                         // know: F# widens a constructor argument like any
                         // other, so a parameter declaring a BASE gets a
                         // second chance against the argument's own type
                         // arguments under that base's name.
                         let rec couldAccept (dom : Type) (arg : Type) : bool =
                             (Types.unifyTrial true dom arg).IsNone
                             || (match prune dom, prune arg with
                                 | TCon (d, da), TCon (a, aa) when
                                        d <> a && isSupertypeOf d a && List.length da = List.length aa ->
                                     (Types.unifyTrial true (TCon (d, da)) (TCon (d, aa))).IsNone
                                 | TTuple xs, TTuple ys when List.length xs = List.length ys ->
                                     List.forall2 couldAccept xs ys
                                 // a callback's RESULT widens, as at the call
                                 | TFun (p1, r1), TFun (p2, r2) ->
                                     (Types.unifyTrial true p1 p2).IsNone && couldAccept r1 r2
                                 | _ -> false)
                         // `LazyOrValue<'T> create` WRITES its type argument,
                         // and that is what tells the two constructors apart:
                         // against `new(value : 'T)` the argument would have
                         // to make 'T contain itself. Ignoring the written
                         // arguments left both candidates fitting, and the
                         // first declared won — F# picks the other.
                         let writtenArgs =
                             match nodesOf head |> List.tryFind (fun m -> m.NodeKind = TyParams) with
                             | Some tp ->
                                 nodesOf tp
                                 |> List.filter (fun x -> isTypeKind x.NodeKind)
                                 |> List.map (typeFromNode tyScope)
                             | None -> []
                         // pins a FRESH instantiation, so there is nothing to undo
                         let pin (res : Type) =
                             match writtenArgs, prune res with
                             | (_ :: _), TCon (_, ras) when writtenArgs.Length = ras.Length ->
                                 List.iter2 (fun w r -> Types.unify w r |> ignore) writtenArgs ras
                             | _ -> ()
                         let fits (sch : Scheme) =
                             match prune (st.Instantiate sch) with
                             | TFun (dom, res) ->
                                 pin res
                                 couldAccept dom argTy
                             | _ -> false
                         let chosen =
                             // one fit is the answer; several is an ambiguity
                             // F# breaks in declaration order, and so do we
                             match cs |> List.filter (fun (_, sch) -> fits sch) with
                             | picked :: _ -> Some picked
                             | [] -> None
                         (match chosen with
                          | Some (o, sch) ->
                              vecAdd ctorSitesRaw (ht.Offset, o)
                              (match prune (st.Instantiate sch) with
                               | TFun (dom, res) ->
                                   pin res
                                   // the SPECIALIZATION DEMAND: this arm
                                   // returns without typing the head, so
                                   // nothing else records the instantiation
                                   // — and an undemanded generic class is a
                                   // template the stamper drops, leaving the
                                   // call to name nothing
                                   (match prune res with
                                    | TCon (_, ras) when not (List.isEmpty ras) && false ->
                                        vecAdd instRaw (ht.Offset, ras)
                                    | _ -> ())
                                   // widen per argument, not on the tuple
                                   (match prune dom, prune argTy with
                                    | TTuple ds, TTuple has when ds.Length = has.Length ->
                                        List.iter2 (unifyArg ht.Offset) ds has
                                    | d, a -> unifyArg ht.Offset d a)
                                   res
                               | other -> other)
                          | None ->
                              vecAdd diags (ht.Offset, "no constructor of " + ht.Text + " accepts these arguments")
                              st.Fresh ())
                     | None ->
                     // An overloaded MEMBER is chosen the same way a
                     // constructor is: by what the call passes. So when the
                     // head is a member access, the arguments are typed
                     // FIRST and the demand handed down, which is the only
                     // moment the caller's type parameters are still rigid.
                     // Waiting for the application to constrain the result
                     // after the fact is too late — the binding has been
                     // generalized by then, and the member's result comes out
                     // quantified and empty.
                     // Its result is KEPT. Typing the argument here and again
                     // in the loop below doubles the work per nesting level,
                     // and a computation expression nests once per `yield`:
                     // eight yields took 8 s, thirty-two now take 0.2 s.
                     // The demand is still taken for EVERY member — it is not
                     // only about choosing an overload, the out-parameter view
                     // is built from it too.
                     let mutable demandArg : (int * Type) option = None
                     (match memberDemandTok head, args |> List.filter (fun a -> isExprish a.NodeKind) with
                      | Some mt, ([ only ] as argNodes) ->
                          let argTys = argNodes |> List.map (fun a -> exprType (GNode a))
                          let argTy = match argTys with [ one ] -> one | many -> TTuple many
                          (match Green.tokens (GNode only) |> List.tryHead with
                           | Some t -> demandArg <- Some (t.Offset, argTy)
                           | None -> ())
                          // how many elements the call WROTE
                          let argc =
                              let counted (m : GreenNode) =
                                  if m.NodeKind = TupleExpr
                                  then nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) |> List.length
                                  else 1
                              if only.NodeKind = ParenExpr then
                                  match nodesOf only |> List.filter (fun m -> isExprish m.NodeKind) with
                                  | [ t ] -> counted t
                                  | xs -> List.length xs
                              else counted only
                          dotDemand <- Some (mt.Offset, TFun (argTy, st.Fresh ()), argc)
                      | _ -> ())
                     let want = expected
                     let mutable funTy = exprType (GNode head)
                     dotDemand <- None
                     // Tie the application's RESULT to what it must be before
                     // the arguments are typed. Otherwise a parameter whose
                     // type only a LATER argument settles is still a variable
                     // when an earlier one is checked against it — which is
                     // how `add i0 (v0, initial) res` typed its tuple as a
                     // reference tuple and only then learned the map wanted a
                     // struct.
                     // ONLY when an argument is a tuple LITERAL, and only if
                     // the tie cannot itself fail. Tying the result of every
                     // application to its context is a much bigger change
                     // than this question needs — it takes the result away
                     // from the widening the argument path does — and the
                     // only thing that cannot be settled later is whether a
                     // written `(a, b)` is a struct.
                     let hasTupleLiteral =
                         let rec tupleish (m : GreenNode) =
                             if m.NodeKind = TupleExpr then true
                             elif m.NodeKind = ParenExpr then nodesOf m |> List.exists tupleish
                             else false
                         args |> List.exists (fun a -> isExprish a.NodeKind && tupleish a)
                     (match want with
                      | Some w when hasTupleLiteral ->
                          let argCount = args |> List.filter (fun a -> isExprish a.NodeKind) |> List.length
                          let rec tail (k : int) (t : Type) =
                              if k = 0 then Some t
                              else
                                  match prune t with
                                  | TFun (_, r) -> tail (k - 1) r
                                  | _ -> None
                          (match tail argCount funTy with
                           | Some r ->
                               if (Types.unifyTrial false r w).IsNone then unify r w |> ignore
                           | None -> ())
                      | _ -> ())
                     let off =
                         match Green.tokens (GNode head) |> List.tryHead with
                         | Some t -> t.Offset
                         | None -> 0
                     // explicit type application `zeroCreate<struct(int*int)>`:
                     // typing the head recorded its freshened quantified vars
                     // under the name token, in scheme order — the written
                     // arguments pin exactly those
                     (match args |> List.tryFind (fun m -> m.NodeKind = TyParams) with
                      | Some tp ->
                          let written =
                              // resolved in the ENCLOSING binding's type-var
                              // scope: `HashMap<'K, 'V>(...)` inside a member
                              // means the member's 'K, not a fresh one
                              nodesOf tp |> List.filter (fun x -> isTypeKind x.NodeKind)
                              |> List.map (typeFromNode tyScope)
                          (match Green.tokens (GNode head) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                           | Some ht ->
                               let fresh =
                                   vecToList instRaw |> List.rev
                                   |> List.tryPick (fun (o, fs) -> if o = ht.Offset then Some fs else None)
                               (match fresh with
                                | Some fs when fs.Length = written.Length ->
                                    List.iter2 (unifyAt ht.Offset) fs written
                                | _ -> ())
                           | None -> ())
                      | None -> ())
                     // how many trailing arguments this callee lets the call
                     // leave off — each one it leaves off is None
                     let calleeSig =
                         match Green.tokens (GNode head) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                         | Some ht ->
                             (match dictTryFind useDefs ht.Offset with
                              | Some d -> dictTryFind fields ("$sig:" + d.Path + ":" + string d.Offset)
                              | None -> None)
                         | None -> None
                     let omittable = match calleeSig with Some fi -> fi.Optionals | None -> 0
                     // The elements a call actually wrote, whether or not
                     // they came wrapped in a paren and a tuple.
                     let suppliedNodes =
                         match args |> List.filter (fun a -> isExprish a.NodeKind) with
                         | [ one ] when one.NodeKind = ParenExpr ->
                             (match nodesOf one |> List.filter (fun m -> isExprish m.NodeKind) with
                              | [ t ] when t.NodeKind = TupleExpr ->
                                  nodesOf t |> List.filter (fun m -> isExprish m.NodeKind)
                              | xs -> xs)
                         | xs -> xs
                     /// `name = value`, but ONLY for a name the callee declares
                     /// — anywhere else `x = v` is an equality test and stays one
                     let namedArg (known : string list) (a : GreenNode) =
                         let parts = nodesOf a |> List.filter (fun m -> isExprish m.NodeKind)
                         let ops = tokensOf a
                         if a.NodeKind <> BinaryExpr then None
                         else
                             // the match comes LAST, so nothing follows it
                             match parts, ops with
                             | [ l; r ], [ op ] when op.Text = "=" && l.NodeKind = IdentExpr ->
                                 let ids = tokensOf l |> List.filter (fun t -> t.Kind = Ident)
                                 // `?x = e` passes the OPTION; `x = e` a value
                                 let through =
                                     tokensOf l |> List.exists (fun t -> t.Kind = Operator && t.Text = "?")
                                 (match ids with
                                  | [ nt ] when List.contains nt.Text known -> Some (nt.Text, r, through)
                                  | _ -> None)
                             | _ -> None
                     let names =
                         match calleeSig with Some fi -> fi.ParamNames | None -> []
                     let anyNamed =
                         not (List.isEmpty names)
                         && suppliedNodes |> List.exists (fun a -> (namedArg names a).IsSome)
                     let mutable handled = false
                     (if anyNamed then
                        match prune funTy with
                        | TFun (pt, rt) ->
                            (match prune pt with
                             | TTuple ps when List.length ps = List.length names ->
                                 // each written element takes the slot its name
                                 // gives it; the rest fill the slots left over,
                                 // in order, as F# reads them
                                 let slotOf = dictNew<int, GreenNode> ()
                                 let fromSlot = dictNew<int, int> ()
                                 let namedSlot = dictNew<int, bool> ()
                                 let passThrough = dictNew<int, bool> ()
                                 suppliedNodes |> List.iteri (fun k a ->
                                     match namedArg names a with
                                     | Some (nm, v, through) ->
                                         let i = List.findIndex (fun x -> x = nm) names
                                         dictSet slotOf i v
                                         dictSet fromSlot i k
                                         dictSet namedSlot i true
                                         if through then dictSet passThrough i true
                                     | None -> ())
                                 let mutable pos = 0
                                 suppliedNodes |> List.iteri (fun k a ->
                                     match namedArg names a with
                                     | Some _ -> ()
                                     | None ->
                                         while (dictTryFind slotOf pos).IsSome do pos <- pos + 1
                                         dictSet slotOf pos a
                                         dictSet fromSlot pos k
                                         pos <- pos + 1)
                                 let firstOpt = List.length ps - (match calleeSig with Some fi -> fi.Optionals | None -> 0)
                                 let spec = vecNew<string> ()
                                 let built = vecNew<Type> ()
                                 let mutable ok = true
                                 ps |> List.iteri (fun i pty ->
                                     match dictTryFind slotOf i with
                                     | Some v ->
                                         exprExpect <-
                                             (match prune pty with
                                              | TCon ("Option", [ inner ]) when
                                                     i >= firstOpt && (dictTryFind passThrough i) <> Some true -> Some inner
                                              | other -> Some other)
                                         let vt = exprType (GNode v)
                                         exprExpect <- None
                                         let k = match dictTryFind fromSlot i with Some k -> k | None -> 0
                                         let isNamed = (dictTryFind namedSlot i) = Some true
                                         // an optional parameter given its VALUE
                                         // is wrapped, the way F# wraps it
                                         let wrap =
                                             i >= firstOpt
                                             && (dictTryFind passThrough i) <> Some true
                                             && (match prune pty with
                                                 | TCon ("Option", [ inner ]) ->
                                                     (Types.unifyTrial false pty vt).IsSome
                                                     && (Types.unifyTrial false inner vt).IsNone
                                                 | _ -> false)
                                         (if wrap then
                                            (match prune pty with
                                             | TCon ("Option", [ inner ]) -> unifyArg off inner vt
                                             | _ -> ())
                                            vecAdd built pty
                                          else
                                            vecAdd built vt)
                                         vecAdd spec
                                             ((if wrap then (if isNamed then "S" else "s")
                                               else (if isNamed then "P" else "p")) + string k)
                                     | None ->
                                         if i >= firstOpt then
                                             vecAdd built pty
                                             vecAdd spec "n"
                                         else ok <- false)
                                 if ok then
                                     unifyArg off pt (TTuple (vecToList built))
                                     vecAdd fieldOwnersRaw
                                         (off, "$call:" + String.concat "," (vecToList spec))
                                     funTy <- rt
                                     handled <- true
                             | _ -> ())
                        | _ -> ())
                     let mutable firstArg = true
                     let mutable firstArgTy = None
                     for a in (if handled then [] else args) do
                         if isExprish a.NodeKind then
                             (match prune funTy with
                              | TFun (pt, _) -> exprExpect <- Some pt
                              | _ -> exprExpect <- None)
                             let already =
                                 match demandArg, Green.tokens (GNode a) |> List.tryHead with
                                 | Some (o, t), Some at when o = at.Offset -> Some t
                                 | _ -> None
                             let argTy =
                                 match already with
                                 | Some t -> t
                                 | None -> exprType (GNode a)
                             exprExpect <- None
                             if firstArg then
                                 firstArgTy <- Some argTy
                                 firstArg <- false
                             let res = st.Fresh ()
                             // decompose first so a subclass argument can widen
                             (match prune funTy with
                              | TFun (pt, rt) ->
                                  // `File.ReadAllTextSafe file` against
                                  // `(string * int option)`: the parameters
                                  // the call left off take their declared
                                  // types, and Lower passes None for each
                                  let supplied =
                                      match prune argTy with
                                      | TTuple ys -> ys
                                      | one -> [ one ]
                                  (match prune pt with
                                   | TTuple ps when
                                          omittable > 0
                                          && List.length supplied <= List.length ps
                                          && List.length ps - List.length supplied <= omittable ->
                                       let have = List.length supplied
                                       let need = List.length ps
                                       let firstOpt = need - omittable
                                       // an optional parameter may be given
                                       // its VALUE rather than an option, and
                                       // F# wraps it — but `?x = e` passes the
                                       // option straight through, so only wrap
                                       // where the option itself does not fit
                                       let wraps =
                                           supplied
                                           |> List.mapi (fun i x -> i, x)
                                           |> List.filter (fun (i, x) ->
                                               i >= firstOpt
                                               && (match prune (List.item i ps) with
                                                   | TCon ("Option", [ inner ]) ->
                                                       (Types.unifyTrial false (List.item i ps) x).IsSome
                                                       && (Types.unifyTrial false inner x).IsNone
                                                   | _ -> false))
                                           |> List.map fst
                                       let filled =
                                           supplied
                                           |> List.mapi (fun i x ->
                                               if List.contains i wraps then List.item i ps else x)
                                       vecAdd fieldOwnersRaw
                                           (off, "$optargs:" + string (need - have) + ":"
                                                 + String.concat "," (List.map (fun i -> string i) wraps))
                                       unifyArg off pt (TTuple (filled @ List.skip have ps))
                                       for i in wraps do
                                           (match prune (List.item i ps) with
                                            | TCon ("Option", [ inner ]) ->
                                                unifyArg off inner (List.item i supplied)
                                            | _ -> ())
                                   | _ -> unifyArg off pt argTy)
                                  unifyAt off res rt
                              | _ -> unifyAt off funTy (TFun (argTy, res)))
                             funTy <- res
                     // prefer an array-typed result (Array.create), else an
                     // array-typed first argument (Array.pin/unpin)
                     (match prune funTy, firstArgTy |> Option.map prune with
                      | TCon ("array", _), _ -> vecAdd arrKindsRaw (off, funTy)
                      | _, Some (TCon ("array", _) as at) -> vecAdd arrKindsRaw (off, at)
                      | _ -> vecAdd arrKindsRaw (off, funTy))
                     funTy
                 | [] -> st.Fresh ())
            | BinaryExpr ->
                (match nodesOf n, tokensOf n with
                 // `a +++ b` where `+++` is a BINDING: resolution recorded
                 // the operator like any other use, so it is an application
                 // and not a primitive
                 | [ l; r ], [ op ] when
                        (dictTryFind useDefs op.Offset).IsSome
                        // a symbol the CLASS layer owns keeps its dispatch:
                        // `/` is `Div.(/)`, chosen by the operand type, and a
                        // class declares it exactly as a binding would
                        && (Classes.operatorClass op.Text).IsNone ->
                     let fnTy =
                         match dictTryFind useDefs op.Offset with
                         | Some d -> (match instantiateFor d with Some (t, _) -> t | None -> st.Fresh ())
                         | None -> st.Fresh ()
                     let lt = exprType (GNode l)
                     let rt = exprType (GNode r)
                     let res = st.Fresh ()
                     unifyAt op.Offset fnTy (TFun (lt, TFun (rt, res)))
                     res
                 | [ l; r ], [ op ] ->
                     // the target of an assignment is the CELL, not what it
                     // holds: `location <- v` writes through the byref
                     if opClass op.Text = "assign" then noDeref <- true
                     let lt = exprType (GNode l)
                     noDeref <- false
                     // an assignment says what its right-hand side must be,
                     // and a call on that side needs to hear it BEFORE its
                     // arguments are typed
                     if opClass op.Text = "assign" then exprExpect <- Some lt
                     let rt = exprType (GNode r)
                     exprExpect <- None
                     (match opClass op.Text with
                      | "arith" | "cmp" | "bits" -> vecAdd opKindsRaw (op.Offset, lt)
                      | _ -> ())
                     (match opClass op.Text with
                      | "logic" ->
                          unifyAt op.Offset lt tBool
                          unifyAt op.Offset rt tBool
                          tBool
                      | "cmp" ->
                          // comparison stays homogeneous; what the class adds
                          // is that a body generic in the operand type gets
                          // stamped, instead of silently running the integer
                          // comparison at every type
                          unifyAt op.Offset lt rt
                          // EQUALITY has no class (it is structural), so the
                          // class branch below never records its operand
                          // type — and without a type name the backend has
                          // to fall back to the structural walk even where
                          // the operand is an enum-like union or a scalar.
                          // Record it here: homogeneous by the unify above.
                          // ONLY an argument-free type constructor: a
                          // generic one (SetLinked<'K>, StructTuple2<..>)
                          // would put a new instantiation name into the
                          // operator, and stamping reads those — which
                          // renamed stamped records out from under their
                          // callers. Arg-free names (NodeKind, TokenKind)
                          // are exactly what the backend can exploit.
                          if op.Text = "=" || op.Text = "<>" then
                              (match prune lt with
                               | TCon (_, []) -> vecAdd opTypesRaw (op.Offset, lt)
                               | _ -> ())
                          (match Classes.operatorClass op.Text with
                           | Some cls when (dictTryFind classes.Classes cls).IsSome ->
                               let c = { Class = cls; Args = [ lt ]; Assoc = [] }
                               addWanted op.Offset c
                               vecAdd pendingClassUses (op.Offset, Classes.operatorMemberName op.Text, c, false)
                               vecAdd opTypesRaw (op.Offset, lt)
                               solveWanted ()
                           | _ -> ())
                          tBool
                      | "arith" ->
                          // an operator is a class member: the operand pair
                          // selects the instance, and the result is whatever
                          // that instance says it is
                          (match Classes.operatorClass op.Text with
                           | Some cls when (dictTryFind classes.Classes cls).IsSome ->
                               let cd = (dictTryFind classes.Classes cls).Value
                               // a two-parameter class (Add) takes the operand
                               // PAIR and yields its associated Result; a
                               // one-parameter one (`**` through Floating) is
                               // homogeneous and closed
                               let res = st.Fresh ()
                               let c =
                                   if cd.Params.Length = 1 then
                                       unifyAt op.Offset lt rt
                                       unifyAt op.Offset res lt
                                       { Class = cls; Args = [ lt ]; Assoc = [] }
                                   else { Class = cls; Args = [ lt; rt ]; Assoc = [ "Result", res ] }
                               addWanted op.Offset c
                               // if this resolves to an instance with a body,
                               // the operator IS a call to it
                               vecAdd pendingClassUses (op.Offset, Classes.operatorMemberName op.Text, c, false)
                               // solve eagerly: with one operand known the
                               // choice is often already forced, and fixing
                               // it here keeps later inference honest
                               solveWanted ()
                               vecAdd opTypesRaw (op.Offset, lt)
                               res
                           | _ ->
                               unifyAt op.Offset lt rt
                               lt)
                      | "bits" ->
                          // F#: `&&&`/`|||`/`^^^` are same-type; the shift
                          // operators take an int distance and keep the type
                          if op.Text = "<<<" || op.Text = ">>>" then
                              unifyAt op.Offset rt tInt
                              lt
                          else
                              unifyAt op.Offset lt rt
                              lt
                      | "cons" ->
                          unifyAt op.Offset rt (tList lt)
                          rt
                      | "append" ->
                          unifyAt op.Offset lt rt
                          lt
                      | "pipe" ->
                          // decompose first, so the piped value may WIDEN to
                          // the parameter (a list into a seq)
                          let res = st.Fresh ()
                          (match prune rt with
                           | TFun (pt, rt2) ->
                               unifyArg op.Offset pt lt
                               unifyAt op.Offset res rt2
                           | _ -> unifyAt op.Offset rt (TFun (lt, res)))
                          res
                      | "pipeBack" ->
                          let res = st.Fresh ()
                          (match prune lt with
                           | TFun (pt, lt2) ->
                               unifyArg op.Offset pt rt
                               unifyAt op.Offset res lt2
                           | _ -> unifyAt op.Offset lt (TFun (rt, res)))
                          res
                      | "compose" | "composeBack" ->
                          // f >> g : the output of one feeds the other. Same
                          // decomposition as a pipe, so an argument may widen
                          let a = st.Fresh ()
                          let b = st.Fresh ()
                          let c = st.Fresh ()
                          let first, second = (if opClass op.Text = "compose" then lt, rt else rt, lt)
                          unifyAt op.Offset first (TFun (a, b))
                          unifyAt op.Offset second (TFun (b, c))
                          TFun (a, c)
                      | "assign" ->
                          // the RHS must fit the target — like an argument,
                          // so a list may still widen into a seq-typed cell.
                          // Without this, `inner <- Some e` constrained
                          // NOTHING and the payload stayed unknown forever
                          // the tie is what lets an option CELL learn its
                          // payload (`inner <- Some e`) — but ONLY for a
                          // plain variable target. A dot target can resolve
                          // to a SETTER shape the dot machinery still
                          // mistypes, and unifying through that poisons the
                          // value's type far from the assignment
                          // an ARRAY index target is safe for the same reason
                          // a variable is: the target type IS the element
                          // type, so `a.[i] <- x` is what tells a generic
                          // element what it holds
                          let isArrayIndex =
                              l.NodeKind = DotExpr
                              && (nodesOf l |> List.exists (fun m -> m.NodeKind = ListExpr))
                              && (match Green.tokens (GNode l) |> List.tryHead with
                                  | Some t -> (dictTryFind arrIndexTargets t.Offset).IsSome
                                  | None -> false)
                          // a RECORD FIELD target is safe for the same reason
                          // again: its type is the declared field type, and
                          // the store has to fit it. Leaving it out is how
                          // `r.Slots <- Array.zeroCreate n` (Slots : int[])
                          // built a UNIFORM array — nothing pinned the
                          // element type, so the write and every later read
                          // disagreed about the representation
                          let isRecordField =
                              l.NodeKind = DotExpr
                              && not isArrayIndex
                              && (match Green.tokens (GNode l) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast with
                                  | Some t -> (dictTryFind recordFieldTargets t.Offset).IsSome
                                  | None -> false)
                          // `p <- v` where p is a BYREF: the write goes
                          // through the cell, and what it must fit is the
                          // cell's CONTENT. Recorded under the target's own
                          // offset as a field owner, which is what lowering
                          // reads to emit the store.
                          let byrefTarget =
                              if l.NodeKind <> IdentExpr then None
                              else
                                  match prune lt with
                                  | TCon ("ByRefCell", [ inner ]) ->
                                      (match Green.tokens (GNode l) |> List.tryFind (fun t -> t.Kind = Ident) with
                                       | Some t -> Some (t.Offset, inner)
                                       | None -> None)
                                  | _ -> None
                          (match byrefTarget with
                           | Some (off, inner) ->
                               vecAdd fieldOwnersRaw (off, "ByRefCell")
                               unifyArg op.Offset inner rt
                           | None -> ())
                          // an INDEXER target ties the same way: `set_Item`'s
                          // value parameter is the getter's result type
                          let isIndexer =
                              l.NodeKind = DotExpr
                              && (nodesOf l |> List.exists (fun m -> m.NodeKind = ListExpr))
                              && (match Green.tokens (GNode l) |> List.tryHead with
                                  | Some t -> (dictTryFind indexerTargets t.Offset).IsSome
                                  | None -> false)
                          if op.Text = "<-" && byrefTarget.IsNone
                             && (l.NodeKind = IdentExpr || isArrayIndex || isIndexer || isRecordField) then
                              unifyArg op.Offset lt rt
                          tUnit
                      | _ -> st.Fresh ())
                 | _ ->
                     for m in nodesOf n do exprType (GNode m) |> ignore
                     st.Fresh ())
            | PrefixExpr ->
                // `&x` forwards the CELL; everything else reads through it
                let isAddr =
                    match tokensOf n |> List.tryHead with
                    | Some t -> t.Text = "&"
                    | None -> false
                let inner =
                    nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                    |> List.map (fun m ->
                        if isAddr then noDeref <- true
                        let t = exprType (GNode m)
                        noDeref <- false
                        t)
                (match tokensOf n |> List.tryHead with
                 | Some t when t.Text = "not" ->
                     (match inner with
                      | [ i ] ->
                          unifyAt t.Offset i tBool
                          tBool
                      // `not` with nothing to negate is the FUNCTION
                      | _ -> TFun (tBool, tBool))
                 | Some t when t.Text = "assert" ->
                     (match inner with
                      | [ i ] -> unifyAt t.Offset i tBool
                      | _ -> ())
                     tUnit
                 | Some t when t.Text = "&" ->
                     // record which kind this is: forwarding an existing
                     // cell, or taking the address of a LOCATION, which the
                     // call site has to copy in and out around the call
                     (match inner with
                      | [ i ] ->
                          (match prune i with
                           | TCon ("ByRefCell", _) -> vecAdd fieldOwnersRaw (t.Offset, "ByRefCell")
                           | _ -> vecAdd fieldOwnersRaw (t.Offset, "ByRefCopy"))
                      | _ -> ())
                     // `&x` for a byref argument. Forwarding a byref
                     // parameter (`f (key, &value)` where value is already
                     // one) hands the SAME cell on; anything else is a
                     // location whose cell the call site makes.
                     (match inner with
                      | [ i ] ->
                          (match prune i with
                           | TCon ("ByRefCell", _) -> i
                           | other -> TCon ("ByRefCell", [ other ]))
                      | _ -> st.Fresh ())
                 | Some t when t.Text = "~~~" ->
                     // bitwise complement keeps its operand's integer type
                     (match inner with
                      | [ i ] -> i
                      | _ -> tInt)
                 | Some t when t.Text = "new" ->
                     // `new X(args)` IS `X(args)`; the inner application was
                     // typed above, and dropping it for a fresh var left every
                     // `new`-built enumerator with an unknown type
                     (match inner with
                      | [ i ] -> i
                      | _ -> st.Fresh ())
                 | Some t when t.Text = "-" || t.Text = "+" ->
                     (match inner with
                      | [ i ] ->
                          vecAdd opKindsRaw (t.Offset, i)
                          if t.Text = "-" && (dictTryFind classes.Classes "Neg").IsSome then
                              let c = { Class = "Neg"; Args = [ i ]; Assoc = [] }
                              addWanted t.Offset c
                              vecAdd pendingClassUses (t.Offset, Classes.operatorMemberName "~-", c, false)
                              vecAdd opTypesRaw (t.Offset, i)
                              solveWanted ()
                          i
                      | _ -> st.Fresh ())
                 | _ -> st.Fresh ())
            | QuoteExpr ->
                // Type the BODY like any other expression — that is what makes
                // the quoted code resolve, report its own errors and hover. The
                // quotation itself denotes code, not the value the body would
                // produce.
                // the quotation is Code<'t> where 't is what the body produces
                let bodyTy =
                    n.Children
                    |> List.choose (fun c ->
                        match c with
                        | GNode m when isExprish m.NodeKind -> Some (exprType (GNode m))
                        | _ -> None)
                    |> List.tryHead
                TCon ("Code", [ (match bodyTy with Some t -> t | None -> st.Fresh ()) ])
            | SpliceExpr ->
                let hole = st.Fresh ()
                // `%x` splices code in, so `x` must denote code; what the
                // spliced fragment evaluates to is not known here, so the hole
                // takes a fresh variable and the surrounding quote still checks
                n.Children
                |> List.iter (fun c ->
                    match c with
                    | GNode m when isExprish m.NodeKind ->
                        let t = exprType (GNode m)
                        let off = match tokensOf n |> List.tryHead with Some tk -> tk.Offset | None -> 0
                        // `%x` fills a hole of type 'a, and x must be Code<'a>
                        unifyAt off t (TCon ("Code", [ hole ]))
                    | _ -> ())
                hole
            | ParenExpr ->
                let vars = dictNew<string, Type> ()
                let inner =
                    n.Children
                    |> List.filter (fun c -> match c with GNode m -> isExprish m.NodeKind | _ -> false)
                    // parentheses pass the expectation through: `(a, b)` as
                    // an argument is a ParenExpr wrapping the tuple
                    |> List.map (fun m ->
                        exprExpect <- expected
                        let t = exprType m
                        exprExpect <- None
                        t)
                let ascribed =
                    nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind)
                    |> Option.map (typeFromNode vars)
                match inner, ascribed with
                | [], _ when (tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text <> ":")) ->
                    // an operator SECTION `(+)`: the operator as a function.
                    // Typed exactly as its infix use would be, against two
                    // fresh operands — same class wanted, same markers, so
                    // lowering and stamping treat the body like any infix use
                    let op = tokensOf n |> List.find (fun t -> t.Kind = Operator && t.Text <> ":")
                    let lt = st.Fresh ()
                    let rt = st.Fresh ()
                    (match opClass op.Text with
                     | "arith" | "cmp" | "bits" -> vecAdd opKindsRaw (op.Offset, lt)
                     | _ -> ())
                    (match opClass op.Text with
                     | "logic" ->
                         unifyAt op.Offset lt tBool
                         unifyAt op.Offset rt tBool
                         TFun (tBool, TFun (tBool, tBool))
                     | "cmp" ->
                         unifyAt op.Offset lt rt
                         (match Classes.operatorClass op.Text with
                          | Some cls when (dictTryFind classes.Classes cls).IsSome ->
                              let c = { Class = cls; Args = [ lt ]; Assoc = [] }
                              addWanted op.Offset c
                              vecAdd pendingClassUses (op.Offset, Classes.operatorMemberName op.Text, c, false)
                              vecAdd opTypesRaw (op.Offset, lt)
                          | _ -> ())
                         TFun (lt, TFun (rt, tBool))
                     | "arith" ->
                         (match Classes.operatorClass op.Text with
                          | Some cls when (dictTryFind classes.Classes cls).IsSome ->
                              let cd = (dictTryFind classes.Classes cls).Value
                              let res = st.Fresh ()
                              let c =
                                  if cd.Params.Length = 1 then
                                      unifyAt op.Offset lt rt
                                      unifyAt op.Offset res lt
                                      { Class = cls; Args = [ lt ]; Assoc = [] }
                                  else { Class = cls; Args = [ lt; rt ]; Assoc = [ "Result", res ] }
                              addWanted op.Offset c
                              vecAdd pendingClassUses (op.Offset, Classes.operatorMemberName op.Text, c, false)
                              vecAdd opTypesRaw (op.Offset, lt)
                              TFun (lt, TFun (rt, res))
                          | _ ->
                              unifyAt op.Offset lt rt
                              TFun (lt, TFun (rt, lt)))
                     | "bits" ->
                         if op.Text = "<<<" || op.Text = ">>>" then
                             unifyAt op.Offset rt tInt
                         else unifyAt op.Offset lt rt
                         TFun (lt, TFun (rt, lt))
                     | "cons" ->
                         unifyAt op.Offset rt (tList lt)
                         TFun (lt, TFun (rt, rt))
                     | "append" ->
                         unifyAt op.Offset lt rt
                         TFun (lt, TFun (rt, lt))
                     | _ -> st.Fresh ())
                | [], _ -> tUnit
                | [ t ], Some a -> unify t a |> ignore; t
                | [ t ], None -> t
                | many, _ -> List.last many
            | TupleExpr ->
                let want = expected
                let elems =
                    n.Children
                    |> List.filter (fun c -> match c with GNode m -> isExprish m.NodeKind | _ -> false)
                    |> List.map exprType
                (match want with
                 | Some w ->
                     (match prune w with
                      | TCon (sn, args) when
                             sn.StartsWith "StructTuple" && List.length args = List.length elems ->
                          // marked in the owner channel, where lowering reads
                          // a struct tuple's instantiated name
                          List.iter2 (fun a e -> unify a e |> ignore) args elems
                          (match Green.tokens (GNode n) |> List.tryHead with
                           | Some t -> vecAdd pendingOwners (t.Offset, TCon (sn, args))
                           | None -> ())
                          TCon (sn, args)
                      | _ -> TTuple elems)
                 | None -> TTuple elems)
            | ListExpr ->
                let elem = st.Fresh ()
                let rec addItems (m : GreenNode) =
                    if m.NodeKind = BlockExpr then
                        for c in nodesOf m do addItems c
                    elif m.NodeKind = LetDecl || m.NodeKind = ForExpr || m.NodeKind = WhileExpr then
                        exprType (GNode m) |> ignore
                    elif isExprish m.NodeKind then
                        let off = match Green.tokens (GNode m) |> List.tryHead with Some t -> t.Offset | None -> 0
                        unifyAt off (exprType (GNode m)) elem
                for m in nodesOf n do addItems m
                tList elem
            | LambdaExpr ->
                let pats = nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind)
                let lvars = dictNew<string, Type> ()
                let paramTys = pats |> List.map (patType lvars)
                // Tie the parameters to what the context asks for BEFORE the
                // body is typed. Otherwise they are still variables while it
                // runs, and a pattern inside it cannot tell a struct tuple
                // from a reference one — which is what `(fun left self right
                // -> match left, right with | ValueSome(_, l), ...)` needs.
                (match expected with
                 | Some w ->
                     let rec tie (ps : Type list) (t : Type) =
                         match ps, prune t with
                         | p :: rest, TFun (dom, res) ->
                             unify p dom |> ignore
                             tie rest res
                         | _ -> ()
                     tie paramTys w
                 | None -> ())
                let body =
                    nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                    |> List.map (fun m -> exprType (GNode m))
                let resT = match List.tryLast body with Some t -> t | None -> tUnit
                List.foldBack (fun p acc -> TFun (p, acc)) paramTys resT
            | IfExpr ->
                let exprs = nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                (match exprs with
                 | cond :: rest ->
                     let condOff =
                         match Green.tokens (GNode cond) |> List.tryHead with
                         | Some t -> t.Offset | None -> 0
                     unifyAt condOff (exprType (GNode cond)) tBool
                     // an elif continuation nests as a child IfExpr and
                     // completes the chain just like `else` does
                     let hasElse =
                         (tokensOf n |> List.exists (fun t -> t.Text = "else"))
                         || (rest |> List.exists (fun m -> m.NodeKind = IfExpr))
                     let branchTys = rest |> List.map (fun m -> exprType (GNode m))
                     (match branchTys with
                      | [] -> tUnit
                      | [ one ] -> if hasElse then one else tUnit
                      | first :: others ->
                          if hasElse then
                              for o in others do
                                  let off = match Green.tokens (GNode n) |> List.tryHead with Some t -> t.Offset | None -> 0
                                  unifyAt off first o
                              first
                          else tUnit)
                 | [] -> st.Fresh ())
            | TryExpr when
                    n.Children
                    |> List.exists (fun c ->
                        match c with
                        | GToken t -> t.Kind = Keyword && t.Text = "finally"
                        | _ -> false) ->
                // `try B finally F`: the value is B's and F is run for its
                // effect only, so it must NOT unify with the result
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | [ b; f ] ->
                     let r = exprType (GNode b)
                     exprType (GNode f) |> ignore
                     r
                 | [ b ] -> exprType (GNode b)
                 | ms ->
                     for m in ms do exprType (GNode m) |> ignore
                     st.Fresh ())
            | TryExpr ->
                let result = st.Fresh ()
                let exnTy = TCon ("exn", [])
                for c in nodesOf n do
                    if c.NodeKind = MatchClause then
                        let cvars = dictNew<string, Type> ()
                        for m in nodesOf c do
                            if isPatKind m.NodeKind then
                                unify (patType cvars m) exnTy |> ignore
                        let bodies = nodesOf c |> List.filter (fun m -> isExprish m.NodeKind)
                        (match List.tryLast bodies with
                         | Some b -> unify (exprType (GNode b)) result |> ignore
                         | None -> ())
                    elif isExprish c.NodeKind then
                        unify (exprType (GNode c)) result |> ignore
                result
            | MatchExpr ->
                let scrutTy =
                    nodesOf n
                    |> List.tryFind (fun m -> m.NodeKind <> MatchClause && isExprish m.NodeKind)
                    |> Option.map (fun m -> exprType (GNode m))
                let scrut = match scrutTy with Some t -> t | None -> st.Fresh ()
                let result = st.Fresh ()
                // `function` has no scrutinee written: it IS the function
                let isFunctionForm = scrutTy.IsNone
                for cl in nodesOf n do
                    if cl.NodeKind = MatchClause then
                        let barOff = match tokensOf cl |> List.tryHead with Some t -> t.Offset | None -> 0
                        // pattern nodes (before ->) unify with the scrutinee
                        let cvars = dictNew<string, Type> ()
                        let rec isTypeTest (m : GreenNode) =
                            m.NodeKind = TypeTestPat
                            || (m.NodeKind = AsPat
                                && (nodesOf m |> List.exists isTypeTest))
                        for m in nodesOf cl do
                            if isPatKind m.NodeKind then
                                // A `:?` clause states a runtime test, not an
                                // equation: the tested type need not even be
                                // one we have a declaration for. Typing its
                                // binder is enough.
                                if isTypeTest m then patType cvars m |> ignore
                                else
                                    // the scrutinee is what this pattern must
                                    // be, and a comma pattern needs to know
                                    patExpect <- Some scrut
                                    let pt = patType cvars m
                                    patExpect <- None
                                    unifyArg barOff scrut pt
                        // body: expr children; when-guard is bool but we keep it loose
                        let bodies = nodesOf cl |> List.filter (fun m -> isExprish m.NodeKind)
                        (match List.tryLast bodies with
                         | Some b ->
                             for extra in bodies do
                                 if not (System.Object.ReferenceEquals (extra, b)) then
                                     exprType (GNode extra) |> ignore
                             unifyAt barOff (exprType (GNode b)) result
                         | None -> ())
                if isFunctionForm then TFun (scrut, result) else result
            | BlockExpr ->
                let mutable last = tUnit
                for m in nodesOf n do
                    last <- exprType (GNode m)
                last
            | LetDecl ->
                letDepth <- letDepth + 1
                let r = inferLet n
                letDepth <- letDepth - 1
                r
            | ObjExpr ->
                // an anonymous class implementing one interface: type its
                // members against a synthetic receiver, yield the interface
                let synth =
                    match Green.tokens (GNode n) |> List.tryHead with
                    | Some t -> "obj@" + string t.Offset
                    | None -> "obj@?"
                let ivars = dictNew<string, Type> ()
                let ifaceTy =
                    match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
                    | Some tn -> typeFromNode ivars tn
                    | None -> st.Fresh ()
                let ifaceName =
                    match prune ifaceTy with
                    | TCon (nm, _) -> nm
                    | _ -> "?"
                let selfTy = TCon (synth, [])
                // members share the INTERFACE's type-variable scope: a
                // `'a` in a member annotation is the interface's `'a`, which
                // the context's unification links to the enclosing binding's
                // — a fresh dict left it dangling, so `compare a b` in an
                // object expression defaulted instead of going class-pending
                for m in nodesOf n do
                    if m.NodeKind = MemberDecl then
                        inferMember (synth + "." + ifaceName) ivars [] selfTy m
                    // a CLASS base's constructor arguments:
                    // `{ new AbstractReader<'d>(empty) with ... }` — typed
                    // like any expression, so their member accesses resolve
                    elif isExprish m.NodeKind then
                        exprType (GNode m) |> ignore
                ifaceTy
            // `downcast e` / `upcast e`: the target is whatever the context
            // demands, so park the result and read it back once solved
            | StructTupleExpr ->
                // `struct(a, b)` IS the generic struct StructTuple2<'a,'b> —
                // no separate concept, just different syntax
                let rec unwrap (m : GreenNode) =
                    if m.NodeKind = ParenExpr || m.NodeKind = TupleExpr then
                        nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) |> List.collect unwrap
                    else [ m ]
                let elems =
                    nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) |> List.collect unwrap
                let ts = elems |> List.map (fun m -> exprType (GNode m))
                let ty = TCon ("StructTuple" + string ts.Length, ts)
                // like the pattern form: the element types are only settled
                // once the whole file is solved, so naming the instantiation
                // here would freeze a variable that later unification links
                // away — and the stamper's substitution would then miss it
                (match Green.tokens (GNode n) |> List.tryHead with
                 | Some t -> vecAdd pendingRecords (t.Offset, ty)
                 | None -> ())
                ty
            | CastExpr when tokensOf n |> List.exists (fun t -> t.Kind = Keyword && (t.Text = "downcast" || t.Text = "upcast")) ->
                (match nodesOf n |> List.tryFind (fun m -> isExprish m.NodeKind) with
                 | Some operand -> exprType (GNode operand) |> ignore
                 | None -> ())
                let result = st.Fresh ()
                (match tokensOf n |> List.tryHead with
                 | Some t -> vecAdd pendingCasts (t.Offset, result)
                 | None -> ())
                result
            | CastExpr ->
                // `e :> T` / `e :?> T`: the operand is typed for its own
                // sake, the result is the target type
                let cvars = dictNew<string, Type> ()
                (match nodesOf n |> List.tryFind (fun m -> isExprish m.NodeKind) with
                 | Some operand -> exprType (GNode operand) |> ignore
                 | None -> ())
                if hasOpToken ":?" n then
                    (match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
                     | Some tn ->
                         let ty = typeFromNode cvars tn
                         (match Green.tokens (GNode tn) |> List.tryHead with
                          | Some t -> vecAdd pendingOwners (t.Offset, ty)
                          | None -> ())
                     | None -> ())
                    tBool
                else
                    match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
                    | Some tn -> typeFromNode cvars tn
                    | None -> st.Fresh ()
            | DotExpr when (nodesOf n |> List.exists (fun m -> m.NodeKind = ListExpr)) ->
                // index access a.[i]: element type when the receiver is known
                let lhsTy =
                    nodesOf n
                    |> List.tryFind (fun m -> m.NodeKind <> ListExpr && isExprish m.NodeKind)
                    |> Option.map (fun m -> exprType (GNode m))
                // the bracket group parses as a LIST, so the index's own type
                // is that list's element — taken from the same typing the
                // array path already ran, because typing the index expression
                // a second time would duplicate its effects
                let mutable idxTy = st.Fresh ()
                for m in nodesOf n do
                    if m.NodeKind = ListExpr then
                        match prune (exprType (GNode m)) with
                        | TCon ("list", [ e ]) -> idxTy <- e
                        | _ -> ()
                // `a.[lo..hi]` is a SLICE: the bracket holds a range and the
                // result is an array, not an element
                let isSlice =
                    nodesOf n
                    |> List.filter (fun m -> m.NodeKind = ListExpr)
                    |> List.exists (fun ix ->
                        match nodesOf ix |> List.filter (fun m -> isExprish m.NodeKind) with
                        | [ one ] ->
                            one.NodeKind = BinaryExpr
                            && (one.Children |> List.exists (fun c ->
                                    match c with
                                    | GToken t -> t.Kind = Operator && t.Text = ".."
                                    | _ -> false))
                        | _ -> false)
                (match lhsTy |> Option.map prune with
                 | Some (TCon ("array", [ e ])) when isSlice ->
                     (match nodesOf n |> List.tryFind (fun m -> m.NodeKind = ListExpr)
                            |> Option.bind (fun ix -> Green.tokens (GNode ix) |> List.tryHead) with
                      | Some br ->
                          vecAdd arrKindsRaw (br.Offset, TCon ("array", [ e ]))
                          dictSet arrIndexTargets br.Offset true
                          vecAdd fieldOwnersRaw (br.Offset, "$slice")
                      | None -> ())
                     (match Green.tokens (GNode n) |> List.tryHead with
                      | Some t ->
                          vecAdd arrKindsRaw (t.Offset, TCon ("array", [ e ]))
                          dictSet arrIndexTargets t.Offset true
                      | None -> ())
                     TCon ("array", [ e ])
                 | Some (TCon ("array", [ e ])) ->
                     // keyed by THIS index's bracket: `a.[i].[j]` has two
                     // index sites whose expressions start at the same token,
                     // and the inner one silently overwrote the outer's
                     // element kind (the outer read used the inner's layout)
                     // keyed by THIS index's own bracket — the first token of
                     // the ListExpr child. Not "the last bracket in the node":
                     // the index expression may contain brackets of its own
                     // (`a.[i.[0]]`), and not the head token either — chained
                     // indexes share it and overwrote each other's layout
                     (match nodesOf n |> List.tryFind (fun m -> m.NodeKind = ListExpr)
                            |> Option.bind (fun ix -> Green.tokens (GNode ix) |> List.tryHead) with
                      | Some br ->
                          vecAdd arrKindsRaw (br.Offset, TCon ("array", [ e ]))
                          dictSet arrIndexTargets br.Offset true
                      | None -> ())
                     // ALSO under the head token, which is where a later
                     // dot-resolution records the RESOLVED element type; the
                     // bracket key disambiguates chained indexes, the head key
                     // carries the resolution, and lowering prefers whichever
                     // is not still a type variable
                     (match Green.tokens (GNode n) |> List.tryHead with
                      | Some t ->
                          vecAdd arrKindsRaw (t.Offset, TCon ("array", [ e ]))
                          dictSet arrIndexTargets t.Offset true
                      | None -> ())
                     e
                 | Some (TCon ("string", [])) ->
                     // the marker means "the RECEIVER is a string", which is
                     // not the same thing as an array whose ELEMENTS are
                     // strings — a sentinel keeps the two apart
                     (match Green.tokens (GNode n) |> List.tryHead with
                      | Some t -> vecAdd arrKindsRaw (t.Offset, TCon ("$str", []))
                      | None -> ())
                     tChar
                 | _ ->
                     // the receiver is still a variable: park the site rather
                     // than leaving it nameless, which reaches emission as
                     // "array read needs a statically known element type"
                     let result = st.Fresh ()
                     let br =
                         nodesOf n |> List.tryFind (fun m -> m.NodeKind = ListExpr)
                         |> Option.bind (fun ix -> Green.tokens (GNode ix) |> List.tryHead)
                         |> Option.map (fun t -> t.Offset)
                     let head = Green.tokens (GNode n) |> List.tryHead
                     let bound =
                         match lhsTy, br with
                         | Some recv, Some b -> tryResolveIndexer recv b idxTy result
                         | _ -> false
                     if bound then
                         (match head with
                          | Some t -> dictSet indexerTargets t.Offset true
                          | None -> ())
                     else
                         (match lhsTy, head, br with
                          | Some recv, Some t, Some b -> vecAdd pendingIndex (t.Offset, recv, result, b, idxTy)
                          | Some recv, Some t, None -> vecAdd pendingIndex (t.Offset, recv, result, 0, idxTy)
                          | _ -> ())
                     result)
            | DotExpr ->
                let lastIdent =
                    Green.tokens (GNode n)
                    |> List.filter (fun t -> t.Kind = Ident)
                    |> List.tryLast
                // a member name binds through the receiver's type, never
                // through the resolver's by-name candidate
                let qualified =
                    lastIdent
                    |> Option.bind (fun t -> dictTryFind useDefs t.Offset)
                    |> Option.filter (fun d -> d.Kind <> Resolve.DefMember)
                // `Unchecked.defaultof<_>`: the context decides the type, and
                // the zero value depends on it
                let isDefaultOf =
                    match lastIdent with
                    | Some t -> t.Text = "defaultof" && (dictTryFind useDefs t.Offset).IsNone
                    | None -> false
                if isDefaultOf then
                    let result = st.Fresh ()
                    (match lastIdent with
                     | Some t ->
                         vecAdd pendingCasts (t.Offset, result)
                         // `defaultof<VolatileSetData>` WRITES its type: the
                         // enclosing application's written-argument pinning
                         // reads instRaw at the head token, so registering
                         // the result there is all it takes
                         vecAdd instRaw (t.Offset, [ result ])
                     | None -> ())
                    result
                else
                // `C.M` where C names a type: a static member, so the owner
                // is the type itself and there is no receiver to type
                let staticOwner =
                    // the head may be a bare type name or a generic
                    // application: `Comparer.Instance` or `Comparer<int>.Instance`
                    let rec headIdent (h : GreenNode) =
                        if h.NodeKind = IdentExpr then tokensOf h |> List.tryFind (fun t -> t.Kind = Ident)
                        // QUALIFIED: `Inner.Box.Make` names the type by its
                        // path, and the type is the LAST segment of the head
                        elif h.NodeKind = DotExpr then
                            Green.tokens (GNode h) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                        elif h.NodeKind = AppExpr
                             && (nodesOf h |> List.forall (fun m -> m.NodeKind = IdentExpr || m.NodeKind = TyParams || m.NodeKind = DotExpr)) then
                            // only a PURE type application: `C(args).M` is an
                            // instance access, and seeing through the call
                            // typed it as a static
                            match nodesOf h |> List.tryHead with
                            | Some inner when inner.NodeKind = IdentExpr || inner.NodeKind = DotExpr ->
                                headIdent inner
                            | _ -> None
                        else None
                    match nodesOf n |> List.tryHead |> Option.bind headIdent with
                    | Some t ->
                        (match dictTryFind useDefs t.Offset with
                         | Some d when d.Kind = Resolve.DefType -> Some (arityNameOfDef d)
                         | _ -> None)
                    | None -> None
                match staticOwner, lastIdent with
                | Some tn, Some name when (dictTryFind fields (tn + "." + name.Text)).IsSome ->
                    (match fieldCandidates (tn + "." + name.Text) with
                     | [ (_, fi) ] ->
                         let subst = dictNew<int, Type> ()
                         for pv in fi.Params do dictSet subst (prunedId pv) (st.Fresh ())
                         for qv in fi.Quantified do dictSet subst (prunedId qv) (st.Fresh ())
                         vecAdd memberSitesRaw (name.Offset, tn)
                         // a same-file static member of a generic type is a
                         // generic function once lifted, so this use is a
                         // specialization demand — recorded in the definition
                         // scheme's own variable order so the stamper's zip
                         // lines up. Without it a layout-dependent static
                         // emitted a bare EVar naming a template that
                         // stamping had already removed.
                         (match fi.DefKey with
                          | Some (dp, doff) when dp = path ->
                              (match dictTryFind defSchemes doff with
                               | Some sch when not (List.isEmpty sch.Quantified) ->
                                   let inst =
                                       sch.Quantified
                                       |> List.map (fun qv ->
                                           match dictTryFind subst qv.Id with
                                           | Some t -> t
                                           | None -> st.Fresh ())
                                   vecAdd instRaw (name.Offset, inst)
                               | _ -> ())
                          | _ -> ())
                         substVars subst fi.FieldType
                     | (_, first) :: _ ->
                         // STATIC overloads park like instance ones: at this
                         // moment the application has not been typed, so
                         // nothing distinguishes the candidates yet. A
                         // synthetic receiver carries the owner to the retry.
                         let result = st.Fresh ()
                         let recv = TCon (tn, first.Params |> List.map (fun _ -> st.Fresh ()))
                         vecAdd pendingDots (name.Offset, recv, result, name.Text)
                         result
                     | [] -> st.Fresh ())
                | _ ->
                (match qualified with
                 | Some d ->
                     // qualified use (Module.fn): record its instantiation too
                     let oweAt (tk : Token) (cs : Constraint list) : unit =
                         for c in cs do addWanted tk.Offset c
                         // `Num.Zero` binds to an instance member exactly as
                         // the bare `Zero` does — the qualification only says
                         // which class, never which instance
                         match dictTryFind classes.MemberOwner d.Name with
                         | Some cls ->
                             (match cs |> List.tryFind (fun c -> c.Class = cls) with
                              | Some c -> vecAdd pendingClassUses (tk.Offset, d.Name, c, true)
                              | None -> ())
                         | None -> ()
                     (match schemeOfDef d, lastIdent with
                      | Some sc, Some tk when not (List.isEmpty sc.Quantified) && d.Path = path ->
                          let ty, fresh, cs = instantiateTracked sc
                          oweAt tk cs
                          vecAdd instRaw (tk.Offset, fresh)
                          ty
                      | Some sc, Some tk when not (List.isEmpty sc.Quantified) ->
                          let ty, fresh, cs = instantiateImported sc
                          oweAt tk cs
                          vecAdd instRaw (tk.Offset, fresh)
                          ty
                      | _ ->
                          match instantiateFor d, lastIdent with
                          | Some (t, cs), Some tk -> oweAt tk cs; t
                          | _ ->
                          match instantiateFor d with
                          | Some (t, _) -> t
                          | None -> st.Fresh ())
                 | None ->
                     let lhsTy =
                         match nodesOf n |> List.tryHead with
                         | Some lhs -> Some (exprType (GNode lhs))
                         | None -> None
                     (match lhsTy |> Option.map prune, lastIdent with
                      | Some (TCon ("array", [ e ])), Some nm when nm.Text = "Length" ->
                          // keyed by the MEMBER token: `a.[i].Length` has an
                          // index site and a length site whose expressions
                          // start at the SAME token, and one overwrote the
                          // other's element kind
                          vecAdd arrKindsRaw (nm.Offset, TCon ("array", [ e ]))
                          tInt
                      | Some (TCon ("string", [])), Some nm when nm.Text = "Length" ->
                          // sentinel: string RECEIVER, not string elements
                          vecAdd arrKindsRaw (nm.Offset, TCon ("$str", []))
                          tInt
                      | _ ->
                     match lhsTy, lastIdent with
                      | Some lt, Some name ->
                          // when the head names a TYPE, this is a static
                          // member used above its declaration (nothing else
                          // reached here) — park on the OWNER, not on the
                          // meaningless type-in-expression-position value
                          let recv =
                              match staticOwner with
                              | Some tn -> TCon (tn, [])
                              | None -> lt
                          let result = st.Fresh ()
                          if not (tryResolveDot false name.Offset recv result name.Text) then
                              vecAdd pendingDots (name.Offset, recv, result, name.Text)
                          result
                      | _ -> st.Fresh ()))
            | ForExpr | WhileExpr ->
                let fvars = dictNew<string, Type> ()
                // the source and the binder are typed HERE, once — the
                // general loop below must not re-type them, or the binder's
                // freshly re-created scheme orphans the element unification
                // and every constraint on it
                let mutable handled : GreenNode list = []
                // `for x in arr do`: bind x to the element type and record
                // the collection's element name for lowering
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | coll :: _ when n.NodeKind = ForExpr ->
                     handled <- coll :: handled
                     (match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
                      | Some ip -> handled <- ip :: handled
                      | None -> ())
                     let ct = exprType (GNode coll)
                     (match prune ct with
                      | TCon ("array", [ e ]) ->
                          (match Green.tokens (GNode coll) |> List.tryHead with
                           | Some t -> vecAdd arrKindsRaw (t.Offset, ct)
                           | None -> ())
                          (match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
                           | Some ip -> unify (patType fvars ip) e |> ignore
                           | None -> ())
                      | TCon ("list", [ e ]) ->
                          // a cons walk, not the protocol: the marker is the
                          // recorded element type, exactly as for arrays
                          (match Green.tokens (GNode coll) |> List.tryHead with
                           | Some t -> vecAdd arrKindsRaw (t.Offset, ct)
                           | None -> ())
                          (match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
                           | Some ip -> unify (patType fvars ip) e |> ignore
                           | None -> ())
                      | TCon ("string", []) ->
                          // `for c in s`: a string is walked by index, like
                          // an array. The "$str" sentinel is the marker the
                          // emitter already reads for a string receiver, so
                          // the array lowering does the rest
                          (match Green.tokens (GNode coll) |> List.tryHead with
                           | Some t -> vecAdd arrKindsRaw (t.Offset, TCon ("$str", []))
                           | None -> ())
                          (match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
                           | Some ip -> unify (patType fvars ip) tChar |> ignore
                           | None -> ())
                      | TCon (tn, _) when tn <> "string" ->
                          // the enumerator protocol: three member accesses
                          // that have no tokens of their own, parked at
                          // SYNTHETIC offsets derived from the loop's — the
                          // lowering derives the same three and reads what
                          // they bound to
                          ignore tn
                          let fo =
                              match Green.tokens (GNode n) |> List.tryHead with
                              | Some t -> t.Offset
                              | None -> 0
                          let enTy = st.Fresh ()
                          let gTy = st.Fresh ()
                          if not (tryResolveDot false (30000000 + fo) ct gTy "GetEnumerator") then
                              vecAdd pendingDots (30000000 + fo, ct, gTy, "GetEnumerator")
                          unify gTy (TFun (tUnit, enTy)) |> ignore
                          let mTy = st.Fresh ()
                          if not (tryResolveDot false (40000000 + fo) enTy mTy "MoveNext") then
                              vecAdd pendingDots (40000000 + fo, enTy, mTy, "MoveNext")
                          unify mTy (TFun (tUnit, tBool)) |> ignore
                          let cTy = st.Fresh ()
                          if not (tryResolveDot false (50000000 + fo) enTy cTy "Current") then
                              vecAdd pendingDots (50000000 + fo, enTy, cTy, "Current")
                          (match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
                           | Some ip -> unify (patType fvars ip) cTy |> ignore
                           | None -> ())
                      | _ ->
                          // the type is not known YET — a parked dot may
                          // still resolve it. Remember the source so the
                          // finalization can look again
                          // neither array, list nor protocol YET: bind the
                          // pattern so the body sees its names, and remember
                          // BOTH types so the finalization can wire the
                          // protocol once the source's type has resolved
                          let bt =
                              match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
                              | Some ip -> patType fvars ip
                              | None -> st.Fresh ()
                          (match Green.tokens (GNode n) |> List.tryHead,
                                 Green.tokens (GNode coll) |> List.tryHead with
                           | Some t, Some c -> vecAdd lateLoopSources (t.Offset, c.Offset, ct, bt)
                           | _ -> ()))
                 | _ -> ())
                for m in nodesOf n do
                    if List.exists (fun h -> System.Object.ReferenceEquals (h, m)) handled then ()
                    elif isPatKind m.NodeKind then patType fvars m |> ignore
                    elif isExprish m.NodeKind then exprType (GNode m) |> ignore
                tUnit
            | CompExpr ->
                // The PROBE. Type the BUILDER — that is what decides the
                // shape the rewrite emits — and then, separately, type the
                // bare expressions in the body. A bare expression is an
                // implicit `yield` unless it is a STATEMENT, and in F# the
                // only thing that tells those apart is whether it has a
                // value. Nothing else in the body is typed here: it is still
                // written in `let!` and `yield`, which mean nothing until the
                // rewrite has turned them into calls.
                (match nodesOf n |> List.tryHead with
                 | Some b ->
                     let bt = exprType (GNode b)
                     (match Green.tokens (GNode n) |> List.tryHead with
                      | Some t -> vecAdd compBuildersRaw (t.Offset, bt)
                      | None -> ())
                 | None -> ())
                (match nodesOf n |> List.filter (fun m -> m.NodeKind = BraceExpr) |> List.tryHead with
                 | Some brace ->
                     let items =
                         match nodesOf brace with
                         | [ one ] when one.NodeKind = BlockExpr -> nodesOf one
                         | ms -> ms
                     for it in items do
                         if isBareCompItem it then
                             let t = exprType (GNode it)
                             (match Green.tokens (GNode it) |> List.tryHead with
                              | Some tok ->
                                  (match prune t with
                                   | TCon ("unit", []) -> vecAdd compStmtsRaw tok.Offset
                                   | _ -> ())
                              | None -> ())
                 | None -> ())
                st.Fresh ()
            | RecordExpr ->
                let fieldNodes = nodesOf n |> List.filter (fun m -> m.NodeKind = RecordExprField)
                let baseExpr = nodesOf n |> List.tryFind (fun m -> m.NodeKind <> RecordExprField && isExprish m.NodeKind)
                let fieldNames =
                    fieldNodes
                    |> List.choose recordFieldLabel
                    |> List.map (fun t -> t.Text)
                // determine the record type from ALL labels (F# semantics):
                // among candidate owners, the first whose field set covers
                // every written label wins
                let owner =
                    fieldNames
                    |> List.tryPick (fun n ->
                        match dictTryFind fields n with
                        | Some info when fieldNames |> List.forall (fun m -> (dictTryFind fields (info.TypeName + "." + m)).IsSome) ->
                            Some info
                        | _ -> None)
                (match owner with
                 | Some info ->
                     let subst = dictNew<int, Type> ()
                     for pv in info.Params do dictSet subst pv.Id (st.Fresh ())
                     let recTy = TCon (info.TypeName, info.Params |> List.map (fun pv -> substVars subst (TVar pv)))
                     // remember which instantiation this literal builds, so
                     // the stamped record (and its layout) is the one used
                     (match Green.tokens (GNode n) |> List.tryHead with
                      | Some t -> vecAdd pendingRecords (t.Offset, recTy)
                      | None -> ())
                     (match baseExpr with
                      | Some b ->
                          let off = match Green.tokens (GNode b) |> List.tryHead with Some t -> t.Offset | None -> 0
                          unifyAt off (exprType (GNode b)) recTy
                      | None -> ())
                     for f in fieldNodes do
                         let nameTok = recordFieldLabel f
                         let valTy =
                             nodesOf f |> List.filter (fun m -> isExprish m.NodeKind)
                             |> List.map (fun m -> exprType (GNode m))
                         (match nameTok, List.tryLast valTy with
                          | Some t, Some vt ->
                              (match dictTryFind fields (info.TypeName + "." + t.Text) with
                               | Some fi -> unifyAt t.Offset vt (substVars subst fi.FieldType)
                               | None -> ())
                          | _ -> ())
                     recTy
                 | None ->
                     // unknown record type: walk values, stay unconstrained
                     for f in fieldNodes do
                         for m in nodesOf f do
                             if isExprish m.NodeKind then exprType (GNode m) |> ignore
                     (match baseExpr with
                      | Some b -> exprType (GNode b) |> ignore
                      | None -> ())
                     st.Fresh ())
            | ArrayExpr ->
                let elem = st.Fresh ()
                for m in nodesOf n do
                    if isExprish m.NodeKind then
                        let off = match Green.tokens (GNode m) |> List.tryHead with Some t -> t.Offset | None -> 0
                        unifyAt off (exprType (GNode m)) elem
                (match Green.tokens (GNode n) |> List.tryHead with
                 | Some t -> vecAdd arrKindsRaw (t.Offset, TCon ("array", [ elem ]))
                 | None -> ())
                TCon ("array", [ elem ])
            | BraceExpr -> st.Fresh ()
            | ErrorNode -> st.Fresh ()
            | _ ->
                for m in nodesOf n do
                    if isExprish m.NodeKind then exprType (GNode m) |> ignore
                    elif isPatKind m.NodeKind then patType (dictNew ()) m |> ignore
                st.Fresh ()

    // ---- declarations -----------------------------------------------------

    and inferLet (n : GreenNode) : Type =
        let isRec =
            tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "rec")
        // split at `=`
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
        let vars = dictNew<string, Type> ()
        // a TOP-LEVEL binding owns the written-type-variable scope; a nested
        // let keeps its enclosing binding's scope, as F# scoping demands
        if letDepth = 0 then tyScope <- vars
        // NOTE: must be called only after EnterLevel — variables created by
        // the ascription have to live at the binding's level to generalize
        let ascriptionOf () =
            vecToList before
            |> List.tryPick (fun c -> match c with GNode t when isTypeKind t.NodeKind -> Some (typeFromNode vars t) | _ -> None)
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
        match pats with
        | [] ->
            for c in vecToList after do exprType c |> ignore
            tUnit
        | namePat :: paramPats when not isDestructure ->
            let hasIn =
                tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "in")
            st.EnterLevel ()
            let ascription = ascriptionOf ()
            let nameTy = patType vars namePat
            let paramTys = paramPats |> List.map (patType vars)
            // a declared `when C<'a>` is a GIVEN inside the body: a wanted it
            // entails is already discharged, which is how a closed class like
            // Fractional keeps generic math from inferring a chain of
            // unreduced projections
            let declared =
                vecToList before
                |> List.choose (fun c ->
                    match c with
                    | GNode w when w.NodeKind = WhenDecl -> constraintOf vars w
                    | _ -> None)
            let savedGivens = givens
            givens <- givens @ declared
            // The type parameters this binding WROTE are rigid while its body
            // is typed: the body has to work for every instantiation, so an
            // overload may not choose them. Only overload trials consult the
            // flag — ordinary unification is unchanged, and the flag is
            // cleared before generalization.
            let rigidHere = setRigid vars true
            let bodyTys =
                try vecToList after |> List.map exprType
                finally
                    // cleared HERE, not at the end of the branch: a rigid
                    // variable that outlives its binding poisons every later
                    // overload trial, and the branches out of this function
                    // are many
                    for v in rigidHere do v.Rigid <- false
            givens <- savedGivens
            // with `in`, the last after-expr is the continuation, the first
            // is the binding body
            let bodyTy =
                match bodyTys, hasIn with
                | b :: _, true -> b
                | _, _ -> (match List.tryLast bodyTys with Some t -> t | None -> st.Fresh ())
            let resultTy =
                match ascription with
                | Some a ->
                    (match Green.tokens (GNode namePat) |> List.tryHead with
                     | Some t -> unifyAt t.Offset bodyTy a
                     | None -> unify bodyTy a |> ignore)
                    bodyTy
                | None -> bodyTy
            let funTy = List.foldBack (fun p acc -> TFun (p, acc)) paramTys resultTy
            (match Green.tokens (GNode namePat) |> List.tryHead with
             | Some t -> unifyAt t.Offset nameTy funTy
             | None -> unify nameTy funTy |> ignore)
            ignore isRec   // rec already works: the name's tvar was bound before the body
            st.ExitLevel ()
            // `use x = e` disposes at the end of the scope. There is no
            // `Dispose` token to key on, so the access is parked at a
            // synthetic offset off the `use` keyword, exactly as the
            // enumerator protocol parks its three
            if paramPats.IsEmpty
               && (tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "use")) then
                let fo =
                    match tokensOf n |> List.tryHead with
                    | Some t -> t.Offset
                    | None -> 0
                let dTy = st.Fresh ()
                if not (tryResolveDot false (95000000 + fo) resultTy dTy "Dispose") then
                    vecAdd pendingDots (95000000 + fo, resultTy, dTy, "Dispose")
                unify dTy (TFun (tUnit, tUnit)) |> ignore
            // generalize and overwrite the monomorphic scheme. A MUTABLE
            // binding never generalizes (the value restriction): its cell is
            // one location, and quantifying it hands every read a fresh copy
            // of a variable the writes can no longer reach — `let mutable
            // acc = mempty` lost its tie to the annotation this way
            let isMutable =
                tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "mutable")
            // the value restriction, FULL form: a parameterless binding
            // whose right-hand side is expansive (an application, a match —
            // anything that COMPUTES) must stay monomorphic. Generalizing
            // `let a = Array.zeroCreate n` hands every use a fresh variable:
            // the writes and the reads stop agreeing on the element type,
            // and inside a generic body the stamper can no longer tie the
            // array's layout to the enclosing instantiation
            let rec nonExpansive (c : Green) =
                match c with
                | GToken _ -> true
                | GNode m ->
                    match m.NodeKind with
                    | LiteralExpr | IdentExpr | LambdaExpr | ObjExpr -> true
                    | ListExpr | ArrayExpr | TupleExpr | StructTupleExpr | ParenExpr ->
                        m.Children |> List.forall nonExpansive
                    | _ -> false
            // EXPLICIT type parameters exempt a binding from the value
            // restriction. `let empty<'k, 'v> : Mp<'k, 'v> = ...` names what
            // it is generic in, which is exactly the promise the restriction
            // exists to withhold from a binding that made no such promise —
            // F# reads it the same way and calls the result a generic value.
            //
            // Without this every use of `MapExt.empty` shared ONE type, so a
            // map bound empty before a loop was tied to the map the loop read
            // from, and storing a pair into it asked `'T` to become `'T * 'T`.
            // That surfaced as an occurs check on the tuple, a long way from
            // the binding that caused it.
            let declaresTyParams =
                vecToList before
                |> List.exists (fun c ->
                    match c with
                    | GNode t -> t.NodeKind = TyParams
                    | _ -> false)
            let expansiveValue =
                paramPats.IsEmpty
                && not declaresTyParams
                && (let body =
                        match vecToList after, hasIn with
                        | b :: _, true -> Some b
                        | xs, _ -> List.tryLast xs
                    match body with
                    | Some b -> not (nonExpansive b)
                    | None -> false)
            (match Green.tokens (GNode namePat) |> List.tryFind (fun t -> t.Kind = Ident) with
             | Some t when (dictTryFind defsAt t.Offset).IsSome ->
                 if isMutable || expansiveValue then setScheme t.Offset (mono funTy)
                 else setScheme t.Offset (generalizeBinding declared funTy)
             | _ -> ())
            // `let x = e in body` evaluates to the continuation
            if hasIn then (match List.tryLast bodyTys with Some t -> t | None -> tUnit)
            else tUnit
        | _ ->
            // destructuring: bind all pattern names, unify with the body.
            // With `in` the FIRST after-expr is the value and the last is the
            // continuation — unifying the pattern with the continuation
            // instead is how `let (x, y) = pair () in x + y` reported
            // "int * int vs int", and made the whole let type as unit
            let hasIn =
                tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "in")
            st.EnterLevel ()
            let patTys = pats |> List.map (patType vars)
            let bodyTys = vecToList after |> List.map exprType
            st.ExitLevel ()
            let valueTy =
                match bodyTys, hasIn with
                | v :: _, true -> Some v
                | _, _ -> List.tryLast bodyTys
            // REPORTED, not discarded. `let (p, q) = struct(1, "x")` is an
            // error in F# — one tuple is a struct, the other is not — and
            // swallowing it here let the binding compile and then trap,
            // which is the worst of the three outcomes available.
            let at =
                match pats |> List.tryHead |> Option.bind (fun p -> Green.tokens (GNode p) |> List.tryHead) with
                | Some t -> t.Offset
                | None -> 0
            (match patTys, valueTy with
             | [ single ], Some b -> unifyAt at single b
             | many, Some b -> unifyAt at (TTuple many) b
             | _ -> ())
            if hasIn then (match List.tryLast bodyTys with Some t -> t | None -> tUnit)
            else tUnit

    and inferTypeDecl (n : GreenNode) : unit =
        if pendingStructAttr then
            (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
             | Some t -> dictSet structTypes t.Text true
             | None -> ())
        pendingStructAttr <- false
        // declared type parameters
        let vars = dictNew<string, Type> ()
        tyScope <- vars
        let tyParams = vecNew<Type> ()
        for m in nodesOf n do
            if m.NodeKind = TyParams then
                // 'a sits inside VarType nodes — walk all descendant tokens,
                // but NOT those of an inline constraint (`'Key : comparison`),
                // whose identifiers name a class rather than a parameter
                let paramToks =
                    m.Children
                    |> List.collect (fun c ->
                        match c with
                        | GNode w when w.NodeKind = WhenDecl -> []
                        | other -> Green.tokens other)
                for t in paramToks do
                    if t.Kind = Ident && t.Text <> "_" && not (dictTryFind vars t.Text).IsSome then
                        let v = st.Fresh ()
                        dictSet vars t.Text v
                        vecAdd tyParams v
        let written =
            match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
            | Some t -> t.Text
            | None -> "?"
        // An extension on an ALIAS extends what the alias NAMES. `type
        // List<'T> with` adds members to ResizeArray, because that is what
        // `List` is — F# reads it the same way, and attaching them to the
        // alias instead left the members on a type nothing has.
        //
        // But NOT for the abbreviation's OWN declaration. The pre-scan
        // registers abbreviations before this runs, so `type MultiSetMap =
        // HashMap<'k, HashSet<'v>>` found ITSELF here, took the name
        // `HashMap`, and re-registered the alias under it — after which
        // every `HashMap<K, V>` in the project expanded with a HashSet
        // wrapped around its value type.
        let isAbbreviation =
            not (nodesOf n
                 |> List.exists (fun m ->
                     m.NodeKind = UnionCase || m.NodeKind = RecordRepr
                     || m.NodeKind = MemberDecl || m.NodeKind = InterfaceImpl))
            && (nodesOf n |> List.exists (fun m -> isTypeKind m.NodeKind))
        let plain =
            if isAbbreviation then written
            else
                match dictTryFind aliases written with
                | Some (_, body) ->
                    (match prune body with
                     | TCon (target, _) -> target
                     | _ -> written)
                | None -> written
        // a name redeclared at a DIFFERENT arity is a DIFFERENT type — the
        // pre-sweep recorded every arity, so the decoration is known here
        let name = arityName plain (vecToList tyParams |> List.length)
        if name <> plain then
            (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
             | Some t -> vecAdd fieldOwnersRaw (t.Offset, "$tyname:" + name)
             | None -> ())
        let selfTy = TCon (name, vecToList tyParams)
        // `inherit Base(...)`: remember the base so member lookup and layout
        // can walk the chain
        (match nodesOf n |> List.tryFind (fun m -> m.NodeKind = InheritDecl) with
         | Some inh ->
             (match nodesOf inh |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
              | Some tn ->
                  // typed in the class' own scope, so `inherit Node<'K>` on
                  // `Pair<'K,'V>` records Node applied to Pair's first param
                  let ownParams =
                      vecToList tyParams
                      |> List.choose (fun t -> match prune t with TVar v -> Some v | _ -> None)
                  let baseTy = typeFromNode vars tn
                  // the instantiation handed to the base, rendered once
                  // solving settles: stamping a construction substitutes the
                  // class' variables, so an inherited layout-dependent
                  // member can specialize at the BASE's own arguments
                  (match Green.tokens (GNode tn) |> List.tryHead with
                   | Some t -> vecAdd pendingBaseInsts (t.Offset, baseTy)
                   | None -> ())
                  // `and IAdaptiveValue<'T> = inherit IAdaptiveValue` names
                  // the SAME key as the type being declared, because a type
                  // is keyed by its bare name. Recording it would make the
                  // type its own base and the member walk would never end.
                  match prune baseTy with
                  | TCon (b, _) when b = name -> ()
                  | _ -> dictSet bases name (ownParams, baseTy)
              | None -> ())
         | None -> ())
        currentBase <-
            match dictTryFind bases name with
            | Some (_, bt) -> Some bt
            | None -> None
        // Any abstract member declares a dispatch slot — on a pure interface
        // (all members abstract) or on a base class with overridable methods.
        let memberDecls = nodesOf n |> List.filter (fun m -> m.NodeKind = MemberDecl)
        let isAbstractM (m : GreenNode) =
            tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "abstract")
        if memberDecls |> List.exists isAbstractM then
            dictSet ifaces name
                (memberDecls
                 |> List.filter isAbstractM
                 |> List.choose (fun m ->
                     let nameTok =
                         match tokensOf m |> List.filter (fun t -> t.Kind = Ident) with
                         | [ _; nm ] -> Some nm
                         | [ nm ] -> Some nm
                         | _ -> None
                     nameTok |> Option.map (fun t ->
                         // a TYPE-ONLY abstract (`abstract Apply : 'D -> 'D`)
                         // declares its parameters as arrows, not patterns —
                         // the count feeds eta-expansion of member VALUES,
                         // so a method must not look like a getter
                         let patCount = nodesOf m |> List.filter (fun p -> isPatKind p.NodeKind) |> List.length
                         let arity =
                             if patCount > 0 then patCount
                             else
                                 let rec arrows (g : GreenNode) =
                                     if g.NodeKind = FunType then
                                         match nodesOf g |> List.filter (fun x -> isTypeKind x.NodeKind) |> List.rev with
                                         | cod :: _ -> 1 + arrows cod
                                         | [] -> 1
                                     else 0
                                 match nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                                 | Some ty -> arrows ty
                                 | None -> 0
                         t.Text, arity)))
        // type abbreviation: register for same-file expansion
        let hasStructure =
            nodesOf n
            |> List.exists (fun m ->
                m.NodeKind = UnionCase || m.NodeKind = RecordRepr
                || m.NodeKind = MemberDecl || m.NodeKind = InterfaceImpl)
        if not hasStructure then
            match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
            | Some repr ->
                let body = typeFromNode vars repr
                let paramVars =
                    vecToList tyParams
                    |> List.choose (fun t -> match prune t with TVar v -> Some v | _ -> None)
                dictSet aliases name (paramVars, body)
            | None -> ()
        let paramVarList () =
            vecToList tyParams
            |> List.choose (fun t -> match prune t with TVar v -> Some v | _ -> None)
        // `type Box<'a> when Ordered<'a> = ...` — the type's own context. It
        // travels on the CONSTRUCTOR's scheme, so building a Box<Opaque>
        // wants Ordered<Opaque> the way any other call would, and F#'s
        // inline spelling (`<'a when 'a : comparison>`) lands in the same
        // place: `constraintOf` reads both.
        let declaredTypeCons =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = WhenDecl)
            |> List.choose (constraintOf vars)
        let inlineTypeCons =
            nodesOf n
            |> List.filter (fun m -> m.NodeKind = TyParams)
            |> List.collect (fun m ->
                    m.Children
                    |> List.choose (fun c ->
                        match c with
                        | GNode w when w.NodeKind = WhenDecl -> constraintOf vars w
                        | _ -> None))
        let typeCons = declaredTypeCons @ inlineTypeCons
        // union cases become constructor schemes
        for m in nodesOf n do
            match m.NodeKind with
            | RecordRepr ->
                for f in nodesOf m do
                    if f.NodeKind = RecordField then
                        let nameTok = tokensOf f |> List.tryFind (fun t -> t.Kind = Ident)
                        let tyNode = nodesOf f |> List.tryFind (fun x -> isTypeKind x.NodeKind)
                        (match nameTok, tyNode with
                         | Some t, Some tn ->
                             let ft = typeFromNode vars tn
                             recordDef t ft
                             let info =
                                 { TypeName = name; Params = paramVarList (); Quantified = []
                                   FieldType = ft; DefKey = None; IsStatic = false; Optionals = 0; ParamNames = [] }
                             // bare name: last declaration wins (F# shadowing);
                             // qualified key: dot-access on a known record type
                             dictSet fields t.Text info
                             dictSet fields (name + "." + t.Text) info
                         | _ -> ())
            | UnionCase ->
                let caseTok = tokensOf m |> List.tryFind (fun t -> t.Kind = Ident)
                let isGadt = hasOpToken ":" m
                let tyNode = nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind)
                let ctorTy =
                    match tyNode with
                    | Some tn when isGadt ->
                        // per-case signature is the whole constructor type;
                        // per-case variables live in their own scope
                        let caseVars = dictNew<string, Type> ()
                        typeFromNode caseVars tn
                    | Some tn -> TFun (typeFromNode vars tn, selfTy)
                    | None -> selfTy
                (match caseTok with
                 | Some t when (dictTryFind defsAt t.Offset).IsSome ->
                     let sch = { Quantified = ctorQuantified (vecToList tyParams) ctorTy; Constraints = []; Body = ctorTy }
                     setScheme t.Offset sch
                     recordDef t ctorTy
                 | _ -> ())
            | LetDecl -> inferLet m |> ignore
            // a `do` block in a class body is CONSTRUCTOR code and has to be
            // typed like any other: without this its dot-accesses never
            // resolved, so `do db.SetInput ...` reached emission as an
            // unknown field — and only when something made it reachable
            | BlockExpr -> exprType (GNode m) |> ignore
            | MemberDecl when tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "val") ->
                // `val mutable X : T` is a field declaration
                (match tokensOf m |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast,
                       nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                 | Some nameTok, Some tyNode ->
                     let ft = typeFromNode vars tyNode
                     recordDef nameTok ft
                     let info =
                         { TypeName = name; Params = paramVarList (); Quantified = []
                           FieldType = ft; DefKey = None; IsStatic = false; Optionals = 0; ParamNames = [] }
                     dictSet fields nameTok.Text info
                     dictSet fields (name + "." + nameTok.Text) info
                 | _ -> ())
            | MemberDecl when tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "new") ->
                // an explicit constructor determines how the type is built
                let ps = nodesOf m |> List.filter (fun x -> isPatKind x.NodeKind)
                let argTy =
                    match ps |> List.map (patType vars) with
                    | [] -> tUnit
                    | [ one ] -> one
                    | many -> TTuple many
                for b in nodesOf m do
                    if isExprish b.NodeKind then exprType (GNode b) |> ignore
                let ctorTy = TFun (argTy, selfTy)
                let csch = { Quantified = ctorQuantified (vecToList tyParams) ctorTy; Constraints = typeCons; Body = ctorTy }
                // With no primary constructor the FIRST `new` is what the
                // type name denotes; any others live at their own keyword.
                let prior = match dictTryFind ctors name with Some l -> l | None -> []
                let typeTok = tokensOf n |> List.tryFind (fun t -> t.Kind = Ident)
                let siteOffset =
                    match typeTok with
                    | Some tt when List.isEmpty prior && (dictTryFind defsAt tt.Offset).IsSome -> Some tt.Offset
                    | _ ->
                        tokensOf m
                        |> List.tryFind (fun t -> t.Kind = Keyword && t.Text = "new")
                        |> Option.map (fun t -> t.Offset)
                (match siteOffset with
                 | Some off ->
                     setScheme off csch
                     dictSet ctors name (prior @ [ off, csch ])
                 | None -> ())
            | MemberDecl -> inferMember name vars (paramVarList ()) selfTy m
            | InterfaceImpl ->
                // implementations live under "Class.Interface.Method": they
                // are not accessible as members of the class itself
                let rec ifaceOf (ty : GreenNode) : string option =
                    // DECORATED: `interface IAdaptiveValue<'State> with`
                    // implements IAdaptiveValue`1, and recording the bare
                    // name meant nothing ever widened into the generic
                    // interface
                    match nodesOf ty |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                    | Some hd when ty.NodeKind = AppType ->
                        let n = nodesOf ty |> List.tail |> List.filter (fun x -> isTypeKind x.NodeKind) |> List.length
                        ifaceOf hd |> Option.map (fun nm -> arityName nm n)
                    | _ ->
                        Green.tokens (GNode ty) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                        |> Option.map (fun t -> t.Text)
                let ifaceName =
                    nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) |> Option.bind ifaceOf
                let owner = match ifaceName with Some inm -> name + "." + inm | None -> name
                (match ifaceName with
                 | Some inm ->
                     let prior = match dictTryFind impls name with Some l -> l | None -> []
                     dictSet impls name (inm :: prior)
                 | None -> ())
                for x in nodesOf m do
                    if x.NodeKind = MemberDecl then inferMember owner vars (paramVarList ()) selfTy x
            | k when isPatKind k ->
                // primary-ctor params — and the class becomes constructible:
                // `State(src, toks)` gets the scheme ctorArgs -> Self
                let ctorArgTy = patType vars m
                (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
                 | Some nameTok when (dictTryFind defsAt nameTok.Offset).IsSome ->
                     let ctorTy = TFun (ctorArgTy, selfTy)
                     let sch = { Quantified = ctorQuantified (vecToList tyParams) ctorTy; Constraints = typeCons; Body = ctorTy }
                     setScheme nameTok.Offset sch
                     let prior = match dictTryFind ctors name with Some l -> l | None -> []
                     if not (prior |> List.exists (fun (o, _) -> o = nameTok.Offset)) then
                         dictSet ctors name (prior @ [ nameTok.Offset, sch ])
                 | _ -> ())
            | _ -> ()
        // A type that declares `CompareTo` IS ordered, and knows it as soon
        // as the declaration is finished — a body typed later asks for the
        // instance, and asking is the only chance it gets.
        //
        // F#'s `'a : comparison` is satisfied by IComparable, and
        // `Ordered<'a>` is how that constraint is spelled here, so a library
        // implementing comparison the .NET way must not also have to declare
        // an instance it never wrote. The member lifts to a function of the
        // receiver and the argument, which is exactly `compare`'s shape, so
        // the instance points straight at it and no code is synthesized.
        deriveOrdered name

    and deriveOrdered (tn : string) : unit =
        match dictTryFind fields (tn + ".CompareTo") with
        | Some fi when fi.DefKey.IsSome && not fi.IsStatic ->
            let already =
                Classes.instancesOf classes "Ordered"
                |> List.exists (fun i ->
                    match i.Head with
                    | [ h ] -> (match prune h with TCon (n, _) -> n = tn | _ -> false)
                    | _ -> false)
            // one argument of the type itself, answering an int: anything
            // else is some other CompareTo and none of our business
            let shapeOk =
                match prune fi.FieldType with
                | TFun (a, r) ->
                    (match prune r with TCon ("int", []) -> true | _ -> false)
                    && (match prune a with TCon (n, _) -> n = tn | _ -> false)
                | _ -> false
            if not already && shapeOk then
                let path, off = fi.DefKey.Value
                Classes.addInstance classes
                    { Class = "Ordered"
                      Params = fi.Params
                      Head = [ TCon (tn, fi.Params |> List.map TVar) ]
                      Assoc = []
                      Context = []
                      Members =
                        [ "compare",
                          // named for the CLASS member, not the type's: a
                          // VarId is identified by path and offset, and the
                          // name is what tells lowering this is a comparison
                          // — `a < b` becomes `compare a b < 0` only for a
                          // member called `compare`
                          { MPath = path; MOffset = off; MName = "compare"
                            MTakesUnit = false; MInst = [] } ]
                      Builtin = false
                      Path = path
                      Offset = off }
        | _ -> ()

    and inferMember (tyName : string) (tyVars : Dict<string, Type>) (classParams : Var list) (selfTy : Type) (n : GreenNode) : unit =
        // member scope: the class type variables plus the member's own
        let mvars = dictNew<string, Type> ()
        for k, v in dictPairs tyVars do dictSet mvars k v
        tyScope <- mvars
        st.EnterLevel ()
        let mutable seenEq = false
        let idents = vecNew<Token> ()
        let pats = vecNew<GreenNode> ()
        let mutable ascr : Type option = None
        let bodies = vecNew<Green> ()
        for c in n.Children do
            match c with
            | GToken t when t.Kind = Operator && t.Text = "=" && not seenEq -> seenEq <- true
            | GToken t when not seenEq && t.Kind = Ident -> vecAdd idents t
            | GNode p when not seenEq && isPatKind p.NodeKind -> vecAdd pats p
            | GNode ty when not seenEq && isTypeKind ty.NodeKind -> ascr <- Some (typeFromNode mvars ty)
            | GNode b when seenEq && isExprish b.NodeKind -> vecAdd bodies c
            | _ -> ()
        // self identifier gets the enclosing type
        let nameTok =
            match vecToList idents with
            | [ self; name ] ->
                if self.Text <> "_" && (dictTryFind defsAt self.Offset).IsSome then
                    setScheme self.Offset (mono selfTy)
                    recordDef self selfTy
                Some name
            | [ name ] -> Some name
            | _ -> None
        // ---- property accessors -----------------------------------------
        // `member x.P with get() = e and set v = e2` declares TWO members:
        // the property itself and a `set_P` writer.
        let accessors =
            nodesOf n |> List.filter (fun m -> m.NodeKind = AccessorDecl)
        if not (List.isEmpty accessors) then
            let accOf (which : string) =
                accessors
                |> List.tryFind (fun a ->
                    match tokensOf a |> List.tryFind (fun t -> t.Kind = Ident) with
                    | Some t -> t.Text = which
                    | None -> false)
            let accParts (a : GreenNode) =
                // a lone `()` is the getter's no-argument marker, not a param
                let ps =
                    nodesOf a
                    |> List.filter (fun m -> isPatKind m.NodeKind)
                    |> List.filter (fun p -> not (List.isEmpty (Green.tokens (GNode p) |> List.filter (fun t -> t.Kind = Ident))))
                let bodies = nodesOf a |> List.filter (fun m -> isExprish m.NodeKind)
                ps, bodies
            let propTy =
                match accOf "get" with
                | Some g ->
                    let ps, bodies = accParts g
                    let pts = ps |> List.map (patType mvars)
                    let bt = bodies |> List.map (fun b -> exprType (GNode b)) |> List.tryLast
                    let rt = match bt with Some t -> t | None -> st.Fresh ()
                    List.foldBack (fun p acc -> TFun (p, acc)) pts rt
                | None -> st.Fresh ()
            (match accOf "set" with
             | Some sa ->
                 let ps, bodies = accParts sa
                 let pts = ps |> List.map (patType mvars)
                 // the written value has the property's type — tie it BEFORE
                 // typing the body, so the body's own unifications (the
                 // assignment inside the setter) see the settled variable
                 (match pts with
                  | [ only ] -> unifyAt (match tokensOf sa |> List.tryHead with Some t -> t.Offset | None -> 0) only propTy
                  | _ -> ())
                 for b in bodies do exprType (GNode b) |> ignore
                 let setTy = List.foldBack (fun p acc -> TFun (p, acc)) pts tUnit
                 (match tokensOf sa |> List.tryFind (fun t -> t.Kind = Ident) with
                  | Some kt when (dictTryFind defsAt kt.Offset).IsSome ->
                      let defTy = TFun (selfTy, setTy)
                      setScheme kt.Offset { Quantified = freeVars defTy |> List.distinctBy (fun v -> v.Id); Constraints = []; Body = defTy }
                      (match nameTok with
                       | Some pn ->
                           // registerField, not a raw set: an overloaded
                           // indexer (`Item` by Index AND by int) needs the
                           // second entry DECORATED, or it overwrites the
                           // first and the wrong index type always wins
                           registerField (tyName + ".set_" + pn.Text)
                               { TypeName = tyName; Params = classParams
                                 Quantified = []
                                 FieldType = setTy
                                 DefKey = Some (path, kt.Offset); IsStatic = false; Optionals = 0; ParamNames = [] }
                       | None -> ())
                  | _ -> ())
             | None -> ())
            st.ExitLevel ()
            (match nameTok with
             | Some t ->
                 recordDef t propTy
                 let defTy = TFun (selfTy, propTy)
                 if (dictTryFind defsAt t.Offset).IsSome then
                     setScheme t.Offset { Quantified = freeVars defTy |> List.distinctBy (fun v -> v.Id); Constraints = []; Body = defTy }
                 let classIds = classParams |> List.map (fun v -> v.Id) |> Set.ofList
                 registerField (tyName + "." + t.Text)
                     { TypeName = tyName; Params = classParams
                       Quantified =
                           freeVars propTy |> List.distinctBy (fun v -> v.Id)
                           |> List.filter (fun v -> not (Set.contains v.Id classIds))
                       FieldType = propTy
                       DefKey = (if (dictTryFind defsAt t.Offset).IsSome then Some (path, t.Offset) else None)
                       IsStatic = false; Optionals = 0; ParamNames = [] }
             | None -> ())
        else

        let paramTys = vecToList pats |> List.map (patType mvars)
        // an OVERRIDE's parameters take the ABSTRACT's declared types,
        // exactly as F# types them: the body dispatches members on them
        // (`o.Tag` on an IAdaptiveObject), and typing them fresh left the
        // receiver unresolvable — the access fell to a by-name field guess
        let isOverride =
            tokensOf n |> List.exists (fun t -> t.Kind = Keyword && (t.Text = "override" || t.Text = "default"))
        (match nameTok with
         | Some nm when isOverride && not (List.isEmpty paramTys) ->
             // walk the base chain for the declaration, substituting each
             // hop's own parameters by the instantiation the subclass wrote
             let rec findDecl (cls : string) (args : Type list) (fuel : int) : Type option =
                 if fuel <= 0 then None
                 else
                     match dictTryFind bases cls with
                     | Some (bps, bty) when List.length bps = List.length args ->
                         let subst = dictNew<int, Type> ()
                         List.iter2 (fun (pv : Var) a -> dictSet subst (prunedId pv) a) bps args
                         for fv in freeVars bty do
                             if (dictTryFind subst (prunedId fv)).IsNone then
                                 dictSet subst (prunedId fv) (st.Fresh ())
                         (match prune (substVars subst bty) with
                          | TCon (bn, bargs) ->
                              (match dictTryFind fields (bn + "." + nm.Text) with
                               | Some fi when List.length fi.Params = List.length bargs ->
                                   let fs = dictNew<int, Type> ()
                                   List.iter2 (fun (pv : Var) a -> dictSet fs (prunedId pv) a) fi.Params bargs
                                   for qv in fi.Quantified do dictSet fs (prunedId qv) (st.Fresh ())
                                   for fv in freeVars fi.FieldType do
                                       if (dictTryFind fs (prunedId fv)).IsNone then
                                           dictSet fs (prunedId fv) (st.Fresh ())
                                   Some (substVars fs fi.FieldType)
                               | _ -> findDecl bn bargs (fuel - 1))
                          | _ -> None)
                     | _ -> None
             (match findDecl tyName (classParams |> List.map TVar) 8 with
              | Some declared ->
                  let rec pin (ps : Type list) (d : Type) =
                      match ps, prune d with
                      | p :: rest, TFun (dom, cod) ->
                          unifyAt nm.Offset dom p
                          pin rest cod
                      | _ -> ()
                  pin paramTys declared
              | None -> ())
         | _ -> ())
        // body typed only after parameters are bound
        let bodyTys = vecToList bodies |> List.map exprType
        let bodyTy =
            match List.tryLast bodyTys with
            | Some t -> t
            | None -> (match ascr with Some a -> a | None -> st.Fresh ())
        (match ascr, nameTok with
         | Some a, Some t -> unifyAt t.Offset bodyTy a
         | _ -> ())
        let memberTy = List.foldBack (fun p acc -> TFun (p, acc)) paramTys bodyTy
        st.ExitLevel ()
        // an instance member lowers to a function whose first parameter is
        // the receiver, so the *definition's* scheme carries self; the type
        // seen at a use site (`c.M`) is the self-free one, recorded in fields
        let isStatic = tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")
        // a static PROPERTY is re-evaluated per access, so it lifts to a
        // function of unit — never a value initializer, which would run in
        // every program whether or not anything reads it
        let defTy =
            if isStatic then
                (if List.isEmpty paramTys then TFun (tUnit, memberTy) else memberTy)
            else TFun (selfTy, memberTy)
        match nameTok with
        | Some t ->
            recordDef t memberTy
            if (dictTryFind defsAt t.Offset).IsSome then
                // quantify explicitly: the class' own type parameters live at
                // the type-declaration level, which level-based
                // generalization would refuse to close over
                setScheme t.Offset { Quantified = freeVars defTy |> List.distinctBy (fun v -> v.Id); Constraints = []; Body = defTy }
            let classIds = classParams |> List.map (fun v -> v.Id) |> Set.ofList
            let quantified =
                freeVars memberTy
                |> List.distinctBy (fun v -> v.Id)
                |> List.filter (fun v -> not (Set.contains v.Id classIds))
            registerField (tyName + "." + t.Text)
                { TypeName = tyName; Params = classParams; Quantified = quantified
                  FieldType = memberTy
                  DefKey = (if (dictTryFind defsAt t.Offset).IsSome then Some (path, t.Offset) else None)
                  IsStatic = isStatic; Optionals = optionalArity n; ParamNames = paramNames n }
        | None -> ()

    /// An instance member is an ordinary function; the only extra work is
    /// pinning its type to the signature the class declared, at this head.
    and inferInstanceMember (expected : Type option) (t : Token) (m : GreenNode) : unit =
        st.EnterLevel ()
        let mvars = dictNew<string, Type> ()
        tyScope <- mvars
        let pats = nodesOf m |> List.filter (fun x -> isPatKind x.NodeKind)
        let bodies =
            m.Children |> List.filter (fun c -> match c with GNode b -> isExprish b.NodeKind | _ -> false)
        let paramTys = pats |> List.map (patType mvars)
        let bodyTys = bodies |> List.map exprType
        let bodyTy = match List.tryLast bodyTys with Some x -> x | None -> st.Fresh ()
        st.ExitLevel ()
        let valueTy = List.foldBack (fun p acc -> TFun (p, acc)) paramTys bodyTy
        (match expected with Some e -> unifyAt t.Offset valueTy e | None -> ())
        // a member with no parameters (`static Zero = 0`) lifts to a
        // unit-taking function, never a value initializer: an initializer
        // would run in every program whether or not anything reads it
        let defTy = if List.isEmpty paramTys then TFun (tUnit, valueTy) else valueTy
        recordDef t valueTy
        if (dictTryFind defsAt t.Offset).IsSome then
            setScheme t.Offset
                { Quantified = freeVars defTy |> List.distinctBy (fun v -> v.Id)
                  Constraints = []; Body = defTy }

    /// Type an instance's bodies. Separate from registering it, because a
    /// body may mention a type declared further down the file, while the
    /// instance TABLE has to exist before any body anywhere is checked.
    and inferInstanceBodies (n : GreenNode) : unit =
        let vars = dictNew<string, Type> ()
        match classHead vars n with
        | None -> ()
        | Some (name, args) ->
            let members = nodesOf n |> List.filter (fun m -> m.NodeKind = MemberDecl)
            let assoc =
                members |> List.filter isAssocDecl
                |> List.choose (fun m ->
                    match memberNameOf m, nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                    | Some t, Some tn -> Some (t.Text, typeFromNode vars tn)
                    | _ -> None)
            let bodied = members |> List.filter (fun m -> not (isAssocDecl m) && hasBody m)
            // The instance's OWN `when` context is a given while its bodies
            // are checked, exactly as a function's declared context is inside
            // that function. Without it the body's demand on the context
            // class is an ordinary wanted: solving grounds it — or defaulting
            // does — and every instantiation of a generic instance collapses
            // onto whichever instance that picked. `size [1.0]` ran the `int`
            // body for precisely this reason.
            let context =
                nodesOf n |> List.filter (fun m -> m.NodeKind = WhenDecl)
                |> List.choose (constraintOf vars)
            match dictTryFind classes.Classes name with
            | None -> ()
            | Some cd ->
                let savedGivens = givens
                givens <- givens @ context
                for m in bodied do
                    match memberNameOf m with
                    | None -> ()
                    | Some t ->
                        // the member's declared type, at THIS instance's head
                        let expected =
                            match cd.Members |> List.tryFind (fun (mn, _) -> mn = t.Text) with
                            | Some (_, sch) ->
                                let ty, cs = st.InstantiateC sch
                                // pin the class parameters to the head, and
                                // the associated types to what we bound
                                for c in cs do
                                    if c.Class = name && c.Args.Length = args.Length then
                                        List.iter2 (unifyAt t.Offset) c.Args args
                                        for an, av in c.Assoc do
                                            match assoc |> List.tryFind (fun (bn, _) -> bn = an) with
                                            | Some (_, bt) -> unifyAt t.Offset av bt
                                            | None -> ()
                                Some ty
                            | None ->
                                vecAdd diags (t.Offset, "class " + name + " has no member " + t.Text)
                                None
                        inferInstanceMember expected t m
                // Solve WHILE the context is still given. A member body's
                // wanteds are otherwise pooled and solved at file level,
                // where the context is long out of scope — and a wanted the
                // context entails would there be ground out by defaulting.
                solveWanted ()
                givens <- savedGivens

    /// Pre-register the primary-constructor scheme of an `and`-chained type,
    /// so an EARLIER sibling's body can construct it. The real pass
    /// re-registers the same offset with its own variables; both schemes
    /// instantiate by copy, so the two never meet.
    and predeclareCtor (n : GreenNode) : unit =
        let vars = dictNew<string, Type> ()
        let tyParams = vecNew<Type> ()
        for m in nodesOf n do
            if m.NodeKind = TyParams then
                for t in Green.tokens (GNode m) do
                    if t.Kind = Ident && t.Text <> "_" && not (dictTryFind vars t.Text).IsSome then
                        let v = st.Fresh ()
                        dictSet vars t.Text v
                        vecAdd tyParams v
        match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
        | Some nameTok when (dictTryFind defsAt nameTok.Offset).IsSome ->
            // the same Name`N key the declaration itself will take
            let selfTy = TCon (arityName nameTok.Text (vecToList tyParams |> List.length), vecToList tyParams)
            // a struct-block type's only constructors are `new(...)` MEMBERS
            // — predeclare those too, or an earlier member of the and-group
            // calling `new MapExtEnumerator<_,_>(root)` finds nothing and
            // its result stays a variable forever
            for m in nodesOf n do
                if m.NodeKind = MemberDecl then
                    match tokensOf m |> List.tryFind (fun t -> t.Kind = Keyword && t.Text = "new"),
                          nodesOf m |> List.tryFind (fun p -> isPatKind p.NodeKind) with
                    | Some nk, Some p ->
                        let ctorArgTy = patType vars p
                        let ctorTy = TFun (ctorArgTy, selfTy)
                        let sch =
                            { Quantified = ctorQuantified (vecToList tyParams) ctorTy
                              Constraints = []; Body = ctorTy }
                        setScheme nk.Offset sch
                        let key = match prune selfTy with TCon (kn, _) -> kn | _ -> nameTok.Text
                        let prior = match dictTryFind ctors key with Some l -> l | None -> []
                        if not (prior |> List.exists (fun (o, _) -> o = nk.Offset)) then
                            dictSet ctors key (prior @ [ nk.Offset, sch ])
                    | _ -> ()
            (match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
             | Some p ->
                 let ctorArgTy = patType vars p
                 let ctorTy = TFun (ctorArgTy, selfTy)
                 let sch =
                     { Quantified = ctorQuantified (vecToList tyParams) ctorTy
                       Constraints = []; Body = ctorTy }
                 setScheme nameTok.Offset sch
                 // into the overload table NOW: in an `and` group an earlier
                 // member's body calls this constructor before the
                 // declaration itself is inferred, and an empty candidate
                 // set fell back to the resolver — which knows only the LAST
                 // declaration of the name
                 let key =
                     match prune selfTy with
                     | TCon (kn, _) -> kn
                     | _ -> nameTok.Text
                 let prior = match dictTryFind ctors key with Some l -> l | None -> []
                 if not (prior |> List.exists (fun (o, _) -> o = nameTok.Offset)) then
                     dictSet ctors key (prior @ [ nameTok.Offset, sch ])
             | None -> ())
        | _ -> ()

    and predeclareAndGroups (children : Green list) : unit =
        for c in children do
            match c with
            | GNode n when n.NodeKind = TypeDecl ->
                (match Green.tokens c |> List.tryHead with
                 | Some t when t.Kind = Keyword && t.Text = "and" -> predeclareCtor n
                 | _ -> ())
            | _ -> ()

    and inferDecl (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            match n.NodeKind with
            | LetDecl -> inferLet n |> ignore
            | TypeDecl -> inferTypeDecl n
            | ModuleDef ->
                predeclareAndGroups n.Children
                for c in n.Children do inferDecl c
            | AttributeList ->
                if Green.tokens g |> List.exists (fun t -> t.Kind = Ident && t.Text = "Struct") then
                    pendingStructAttr <- true
            | ModuleHeader | OpenDecl -> ()
            // the tables are read before any body; only the bodies are
            // typed here, in declaration order like everything else
            | ClassDecl -> ()
            | InstanceDecl -> inferInstanceBodies n
            | _ -> exprType g |> ignore

    // ---- class and instance declarations -----------------------------------
    // Both are read before any body is inferred: a class member may be used
    // above its declaration, and an instance must be selectable from
    // anywhere in the file.

    let inferClassDecl (n : GreenNode) : unit =
        let vars = dictNew<string, Type> ()
        match classHead vars n with
        | None -> ()
        | Some (name, args) ->
            let ps = args |> List.collect freeVars |> List.distinctBy (fun v -> v.Id)
            let members = nodesOf n |> List.filter (fun m -> m.NodeKind = MemberDecl)
            let assocNames =
                members |> List.filter isAssocDecl |> List.choose memberNameOf |> List.map (fun t -> t.Text)
            let assocVars = dictNew<string, Type> ()
            for a in assocNames do dictSet assocVars a (st.Fresh ())
            let self = { Class = name; Args = args
                         Assoc = assocNames |> List.map (fun a -> a, (dictTryFind assocVars a).Value) }
            let supers =
                nodesOf n |> List.filter (fun m -> m.NodeKind = WhenDecl)
                |> List.choose (constraintOf vars)
            let sigs =
                members
                |> List.filter (fun m -> not (isAssocDecl m))
                |> List.choose (fun m ->
                    match memberNameOf m with
                    | None -> None
                    | Some t ->
                        let ty =
                            match nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                            | Some tn -> bindAssoc assocVars (typeFromNode vars tn)
                            | None -> st.Fresh ()
                        let qs =
                            (freeVars ty @ ps @ List.collect freeVars (List.map snd self.Assoc))
                            |> List.distinctBy (fun v -> v.Id)
                        let sch = { Quantified = qs; Constraints = [ self ]; Body = ty }
                        if (dictTryFind defsAt t.Offset).IsSome then setScheme t.Offset sch
                        recordDef t ty
                        Some (t.Text, sch))
            let cdef : Classes.ClassDef =
                { Name = name
                  Params = ps; Assoc = assocNames; Supers = supers
                  Members = sigs; Path = path
                  Offset = (match tokensOf n |> List.tryHead with Some t -> t.Offset | None -> 0) }
            Classes.addClass classes cdef

    let inferInstanceDecl (n : GreenNode) : unit =
        let vars = dictNew<string, Type> ()
        match classHead vars n with
        | None -> ()
        | Some (name, args) ->
            let ps = args |> List.collect freeVars |> List.distinctBy (fun v -> v.Id)
            let members = nodesOf n |> List.filter (fun m -> m.NodeKind = MemberDecl)
            let assoc =
                members |> List.filter isAssocDecl
                |> List.choose (fun m ->
                    match memberNameOf m, nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                    | Some t, Some tn -> Some (t.Text, typeFromNode vars tn)
                    | _ -> None)
            let context =
                nodesOf n |> List.filter (fun m -> m.NodeKind = WhenDecl)
                |> List.choose (constraintOf vars)
            let bodied = members |> List.filter (fun m -> not (isAssocDecl m) && hasBody m)
            let offset = match tokensOf n |> List.tryHead with Some t -> t.Offset | None -> 0
            // A PRELUDE instance is primitive: the backend supplies whatever
            // it does not write out. That is per member, so
            // `instance Floating<float>` can write `exp` in source and still
            // let `sqrt` be an f64.sqrt.
            let builtin = path = Classes.builtinPath
            let inst : Classes.InstanceDef =
                { Class = name
                  Params = ps; Head = args; Assoc = assoc; Context = context
                  Members =
                    bodied |> List.choose (fun m ->
                        let takesUnit =
                            nodesOf m |> List.filter (fun x -> isPatKind x.NodeKind) |> List.isEmpty
                        memberNameOf m
                        |> Option.map (fun t ->
                            t.Text,
                            { Classes.MPath = path; MOffset = t.Offset
                              MName = t.Text; MTakesUnit = takesUnit; MInst = [] }))
                  Builtin = builtin; Path = path; Offset = offset }
            Classes.addInstance classes inst
            match dictTryFind classes.Classes name with
            | None -> vecAdd diags (offset, "unknown class " + name)
            | Some cd ->
                if cd.Params.Length <> args.Length then
                    vecAdd diags (offset, "class " + name + " takes " + string cd.Params.Length + " type arguments")
                for a in cd.Assoc do
                    if not (assoc |> List.exists (fun (an, _) -> an = a)) then
                        vecAdd diags (offset, "instance " + name + " must define the associated type " + a)
                if not builtin then
                    for m, _ in cd.Members do
                        if not (inst.Members |> List.exists (fun (mn, _) -> mn = m)) then
                            vecAdd diags (offset, "instance " + name + " must implement " + m)

    // Type abbreviations, all of them, before any signature is read. In an
    // `and` group the abbreviation can come AFTER the interface that uses it
    // — `IVisitor` takes an `aval<'T>` three lines above `and aval<'T> =
    // IAdaptiveValue<'T>` — and registering them in declaration order left
    // that parameter as an opaque `aval`, so no argument ever widened into
    // it. The main pass registers them again; this only makes them early.
    let rec preScanAliases (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            if n.NodeKind = TypeDecl then
                let hasStructure =
                    nodesOf n
                    |> List.exists (fun m ->
                        m.NodeKind = UnionCase || m.NodeKind = RecordRepr
                        || m.NodeKind = MemberDecl || m.NodeKind = InterfaceImpl)
                if not hasStructure then
                    match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident),
                          nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
                    | Some nameTok, Some repr ->
                        let vars = dictNew<string, Type> ()
                        let ps = vecNew<Var> ()
                        for m in nodesOf n do
                            if m.NodeKind = TyParams then
                                let paramToks =
                                    m.Children
                                    |> List.collect (fun c ->
                                        match c with
                                        | GNode w when w.NodeKind = WhenDecl -> []
                                        | other -> Green.tokens other)
                                for t in paramToks do
                                    if t.Kind = Ident && t.Text <> "_"
                                       && not (dictTryFind vars t.Text).IsSome then
                                        let v = st.Fresh ()
                                        dictSet vars t.Text v
                                        match prune v with
                                        | TVar vr -> vecAdd ps vr
                                        | _ -> ()
                        dictSet aliases nameTok.Text (vecToList ps, typeFromNode vars repr)
                    | _ -> ()
            elif n.NodeKind = ModuleDef then n.Children |> List.iter preScanAliases
    // every type name's arities, BEFORE anything reads a signature: the
    // decoration has to be known at the first use, not the declaration
    let tyParamCount (n : GreenNode) : int =
        match nodesOf n |> List.tryFind (fun m -> m.NodeKind = TyParams) with
        | Some m ->
            m.Children
            |> List.collect (fun c ->
                match c with
                | GNode w when w.NodeKind = WhenDecl -> []
                | other -> Green.tokens other)
            |> List.filter (fun t -> t.Kind = Ident && t.Text <> "_")
            |> List.distinctBy (fun t -> t.Text)
            |> List.length
        | None -> 0
    let rec aritySweep (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            if n.NodeKind = TypeDecl then
                match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
                | Some t ->
                    arityDeclared t.Text (tyParamCount n)
                    // per-DECLARATION arity, so a BARE use — `Inner.GetCount`
                    // has no written arguments — can still find the variant
                    // its resolved definition means
                    let seat = "$adecl:" + path + ":" + string t.Offset
                    if (dictTryFind aliases seat).IsNone then
                        let vs =
                            List.init (tyParamCount n) (fun _ -> st.Fresh ())
                            |> List.choose (fun x -> match prune x with TVar v -> Some v | _ -> None)
                        dictSet aliases seat (vs, TCon (t.Text, []))
                | None -> ()
            elif n.NodeKind = ModuleDef then n.Children |> List.iter aritySweep
    root.Children |> List.iter aritySweep

    root.Children |> List.iter preScanAliases

    // Which interfaces each type implements has to be known BEFORE any
    // body is checked: a type's own members may narrow to it (`:? HashSet`
    // from a `seq`), and that test needs the subtype relation already.
    let rec preScan (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            if n.NodeKind = TypeDecl then
                match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
                | Some nameTok ->
                    let rec ifaceOf (ty : GreenNode) : string option =
                        // decorated, as in inferTypeDecl's copy above
                        match nodesOf ty |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                        | Some hd when ty.NodeKind = AppType ->
                            let n = nodesOf ty |> List.tail |> List.filter (fun x -> isTypeKind x.NodeKind) |> List.length
                            ifaceOf hd |> Option.map (fun nm -> arityName nm n)
                        | _ ->
                            Green.tokens (GNode ty) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                            |> Option.map (fun t -> t.Text)
                    let names =
                        nodesOf n
                        |> List.filter (fun m -> m.NodeKind = InterfaceImpl)
                        |> List.choose (fun m ->
                            nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) |> Option.bind ifaceOf)
                    // `interface aval<'b> with` implements IAdaptiveValue.
                    // Recorded under the abbreviation's own name, no argument
                    // would ever widen into the interface it stands for.
                    let names =
                        names |> List.map (fun nm ->
                            match dictTryFind aliases nm with
                            | Some (_, body) ->
                                (match prune body with TCon (t, _) -> t | _ -> nm)
                            | None -> nm)
                    if not (List.isEmpty names) then
                        let key = arityName nameTok.Text (tyParamCount n)
                        let prior = match dictTryFind impls key with Some l -> l | None -> []
                        dictSet impls key (prior @ names)
                        // the DECLARED instantiation, typed at the class's
                        // own parameters: what subsumption unifies against
                        let pvars = dictNew<string, Type> ()
                        let pvarList =
                            match nodesOf n |> List.tryFind (fun m -> m.NodeKind = TyParams) with
                            | Some m ->
                                m.Children
                                |> List.collect (fun c ->
                                    match c with
                                    | GNode w when w.NodeKind = WhenDecl -> []
                                    | other -> Green.tokens other)
                                |> List.filter (fun t -> t.Kind = Ident && t.Text <> "_")
                                |> List.distinctBy (fun t -> t.Text)
                                |> List.map (fun t ->
                                    let fv = st.Fresh ()
                                    dictSet pvars t.Text fv
                                    match prune fv with
                                    | TVar v -> v
                                    | _ -> { Id = 0; Level = 0; Link = None; Rigid = false })
                            | None -> []
                        let ityps =
                            nodesOf n
                            |> List.filter (fun m -> m.NodeKind = InterfaceImpl)
                            |> List.choose (fun m -> nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind))
                            |> List.map (typeFromNode pvars)
                        if not (List.isEmpty ityps) then
                            let prior2 = match dictTryFind implTys key with Some l -> l | None -> []
                            dictSet implTys key (prior2 @ (ityps |> List.map (fun t -> pvarList, t)))
                | None -> ()
            elif n.NodeKind = ModuleDef then n.Children |> List.iter preScan
    root.Children |> List.iter preScan

    // classes before instances, both before any body: the `= 'a` shorthand
    // in a superclass constraint names the class' only associated type, so
    // the class it mentions has to be on the table already
    let rec scanKind (kind : NodeKind) (f : GreenNode -> unit) (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            if n.NodeKind = kind then f n
            elif n.NodeKind = ModuleDef then n.Children |> List.iter (scanKind kind f)
    root.Children |> List.iter (scanKind ClassDecl inferClassDecl)
    root.Children |> List.iter (scanKind InstanceDecl inferInstanceDecl)

    predeclareAndGroups root.Children
    for c in root.Children do inferDecl c

    solveWanted ()

    // Numeric defaulting, as F# does it: a constraint nothing in the program
    // ever pins down resolves at int. `Zero + One` has to mean something, and
    // int is the answer every F# programmer already expects.
    let mutable defaulting = true
    while defaulting do
        defaulting <- false
        // never default a DECLARATION-LEVEL variable (level 0): that is some
        // class's or top-level binding's parameter, shared project-wide, and
        // defaulting it bound the parameter for everyone — MapExt's 'Key went
        // to int through one leftover constraint. Such a constraint resolves
        // per instantiation when the use is stamped; drop it here.
        let declLevel (c : Constraint) =
            c.Args |> List.exists (fun a ->
                match prune a with
                | TVar v -> v.Level = 0
                | _ -> false)
        wanted <- wanted |> List.filter (fun (_, c) -> isGround c || not (declLevel c))
        match wanted |> List.tryFind (fun (_, c) -> not (isGround c)) with
        | Some (offset, c) ->
            (match Classes.select classes c.Class (c.Args |> List.map (fun _ -> tInt)) [] with
             | Classes.Solved _ ->
                 // a defaulting unification can FAIL (the arg is a tuple,
                 // int is not): report once and drop the constraint, or
                 // tryFind selects the very same one forever
                 let mutable failed = false
                 for a in c.Args do
                     match unify a tInt with
                     | Some err ->
                         failed <- true
                         vecAdd diags (offset, err)
                     | None -> ()
                 if failed then
                     wanted <- wanted |> List.filter (fun (_, w) -> not (System.Object.ReferenceEquals (w, c)))
                 defaulting <- true
                 solveWanted ()
             | _ -> wanted <- wanted |> List.filter (fun (_, w) -> not (System.Object.ReferenceEquals (w, c))))
        | None -> ()

    // a class-member use binds to an instance member only once solving has
    // settled; a builtin instance has no member to bind to, which is exactly
    // when the backend emits the operation itself
    let classPendingRaw = vecNew<int * string> ()
    for offset, name, c, byName in vecToList pendingClassUses do
        match instanceMember byName c name with
        | Some key -> vecAdd classUsesRaw (offset, key)
        | None ->
            // unresolved because the operand type is still a variable: name
            // the class, the member and the variable, and let stamping
            // finish the job in each specialized copy
            if byName then
                let tn =
                    match c.Args |> List.tryHead |> Option.map prune with
                    | Some (TCon (_, targs) as ct) when not (List.isEmpty targs) -> typeConName ct
                    | Some (TCon (n, _)) -> n
                    | Some (TVar v) -> "#" + string v.Id
                    | _ -> ""
                if tn <> "" then vecAdd classPendingRaw (offset, c.Class + ":" + name + ":" + tn)

    // retry parked dot-accesses until nothing more can be learned: resolving
    // one can fix a variable that unblocks another
    let mutable parked = vecToList pendingDots
    let mutable progress = true
    while progress do
        progress <- false
        let still = vecNew<int * Type * Type * string> ()
        for offset, recvTy, result, name in parked do
            if tryResolveDot false offset recvTy result name then progress <- true
            else vecAdd still (offset, recvTy, result, name)
        parked <- vecToList still
    // `use x = e` on a type that declares no Dispose. Say it HERE, where the
    // type is known: lowering sees only a member that did not bind, and it
    // falls back to a plain `let` — which is right for a receiver whose type
    // nothing pinned down, and wrong to do quietly for one we know.
    for offset, recvTy, _, name in parked do
        if offset >= 95000000 && name = "Dispose" then
            match prune recvTy with
            | TCon (tn, _) when (dictTryFind knownTypes tn).IsSome ->
                vecAdd diags (offset - 95000000, tn + " declares no Dispose member, so `use` has nothing to call")
            | _ -> ()
    // a use that never took shape (the member passed as a VALUE, say) can
    // wait no longer: force the tie, which binds in declaration order
    for offset, recvTy, result, name in parked do
        tryResolveDot true offset recvTy result name |> ignore
    // a loop whose source's type only settled during the fixpoint: wire the
    // enumerator protocol NOW, at the same synthetic offsets the eager
    // branch would have used — the lowering derives them from the loop and
    // reads what they bound to. `for kv in dict` was silently unlowerable
    // because the Dictionary ctor's result resolves late.
    for fo, _, ct, bt in vecToList lateLoopSources do
        match prune ct with
        | TCon ("list", _) | TCon ("array", _) | TCon ("string", []) -> ()
        | TCon (_, _) ->
            let enTy = st.Fresh ()
            let gTy = st.Fresh ()
            if tryResolveDot false (30000000 + fo) ct gTy "GetEnumerator"
               || tryResolveDot true (30000000 + fo) ct gTy "GetEnumerator" then
                unify gTy (TFun (tUnit, enTy)) |> ignore
                let mTy = st.Fresh ()
                (if not (tryResolveDot false (40000000 + fo) enTy mTy "MoveNext") then
                    tryResolveDot true (40000000 + fo) enTy mTy "MoveNext" |> ignore)
                unify mTy (TFun (tUnit, tBool)) |> ignore
                let cTy = st.Fresh ()
                (if not (tryResolveDot false (50000000 + fo) enTy cTy "Current") then
                    tryResolveDot true (50000000 + fo) enTy cTy "Current" |> ignore)
                unify bt cTy |> ignore
        | _ -> ()
    // index sites whose receiver only took shape through a parked dot: the
    // element type is known now, so name the read and tie the result to it
    for offset, recvTy, result, br, idxTy in vecToList pendingIndex do
        match prune recvTy with
        | TCon ("array", [ e ]) ->
            unifyAt offset result e
            vecAdd arrKindsRaw (offset, TCon ("array", [ e ]))
            dictSet arrIndexTargets offset true
        | TCon ("string", []) ->
            unifyAt offset result tChar
            vecAdd arrKindsRaw (offset, TCon ("$str", []))
        | _ ->
            // a receiver that only took shape through a parked dot may still
            // be a type with an indexer
            if br > 0 && tryResolveIndexer recvTy br idxTy result then
                dictSet indexerTargets offset true
            else
                // Nothing can index this. Say so HERE: the read used to reach
                // emission as an unnamed array access, which compiles to a
                // cast that fails at run time — a wrong program with no
                // diagnostic anywhere.
                match prune recvTy with
                | TCon (tn, _) when (dictTryFind knownTypes tn).IsSome ->
                    vecAdd diags (offset, tn + " cannot be indexed: it is not an array and declares no Item member")
                | _ -> ()

    // record literals: name the instantiation once everything is solved
    for offset, ty in vecToList pendingRecords do
        vecAdd fieldOwnersRaw (offset, instName ty)
    // field READS the same way, for the same reason
    for offset, ty in vecToList pendingOwners do
        vecAdd fieldOwnersRaw (offset, instName ty)
    // base instantiations keep their FULL argument names — member stamping
    // maps the base's parameters positionally against them
    for offset, ty in vecToList pendingBaseInsts do
        match prune ty with
        | TCon (_, args) when not (List.isEmpty args) ->
            vecAdd fieldOwnersRaw (offset, "$baseinst:" + String.concat "@" (args |> List.map typeConName))
        | _ -> ()

    // contextual casts: the target is whatever the context settled on.
    // A STRUCT target is flagged: `defaultof` of a struct is a ZEROED value,
    // not a null, and lowering needs to know which to build.
    for offset, ty in vecToList pendingCasts do
        match prune ty with
        | TCon (n, _) ->
            if (dictTryFind structTypes n) = Some true
            then vecAdd memberSitesRaw (offset, "$struct:" + n)
            else vecAdd memberSitesRaw (offset, n)
        | _ -> ()

    // Anything still parked has an indeterminate receiver. We do NOT guess a
    // member from the name alone: the access stays unbound, and emission
    // rejects it with a real error rather than calling the wrong function.

    let kindOf (t : Type) : string =
        match prune t with
        | TCon ("float", []) -> "f"
        | TCon ("float32", []) -> "s"
        | TCon ("float16", []) -> "h"
        | TCon ("int64", []) -> "l"
        | TCon ("uint32", []) -> "w"
        | TCon ("uint64", []) -> "v"
        | TCon ("string", []) -> "t"
        // conversions and print need these; operator suffixes filter them
        | TCon ("bool", []) -> "b"
        | TCon ("char", []) -> "c"
        | _ -> ""

    { Diagnostics = vecToList diags
      DefTypes =
        vecToList defTypes
        |> List.map (fun (off, len, ty) -> off, len, typeString ty)
      OpKinds =
        vecToList opKindsRaw
        |> List.map (fun (off, ty) -> off, kindOf ty)
        |> List.filter (fun (_, k) -> k <> "")
      InstSites =
        vecToList instRaw
        |> List.map (fun (off, fresh) ->
            off,
            fresh |> List.map (fun f ->
                match prune f with
                // The name carries the ARGUMENTS. Dropping them is what left
                // a constraint inside a generic function with nothing to
                // dispatch on: `total` at list<int> and at list<float> were
                // both just "list", so the `when Sized<'a>` of a generic
                // `instance Sized<list<'a>>` had no element type to resolve.
                // (This is only the INSTANTIATION name; a field owner is
                // still named by its constructor alone — see `instName`.)
                | TCon (_, args) when not (List.isEmpty args) -> typeConName f
                | TCon (n, _) -> n
                // still a variable: this use sits inside a generic body and
                // instantiates at the ENCLOSING binding's type variable —
                // name it so stamping can substitute the caller's argument
                | TVar v -> "#" + string v.Id
                // a tuple (or a function) is a uniform reference: it names
                // itself so that every such instantiation SHARES one body,
                // instead of arriving unnamed and looking layout-dependent
                | TTuple _ | TFun _ -> "$ref"
                | _ -> ""))
      MemberSites = vecToList memberSitesRaw
      FieldOwners = vecToList fieldOwnersRaw
      CompStatements = vecToList compStmtsRaw
      CompBuilders =
        vecToList compBuildersRaw
        |> List.map (fun (off, ty) ->
            off,
            match prune ty with
            | TCon (n, _) -> n
            | _ -> "")
        |> List.filter (fun (_, n) -> n <> "")
      CtorSites = vecToList ctorSitesRaw
      ClassUses = vecToList classUsesRaw
      ClassPending = vecToList classPendingRaw
      ExprTypes =
        vecToList exprTypesRaw
        |> List.map (fun (st, en, ty) -> st, en, Types.typeString (prune ty))
      OpTypes =
        vecToList opTypesRaw
        |> List.map (fun (off, ty) ->
            off,
            match prune ty with
            | TCon (n, _) -> n
            // a variable of the enclosing binding: named so that stamping
            // substitutes the caller's argument and the operator resolves
            // in the specialized copy
            | TVar v -> "#" + string v.Id
            | _ -> "")
      ArrKinds =
        // a loop source that only became known after the walk joins the
        // markers — but ONLY as a list or an array, the two shapes lowering
        // can walk without anything having been parked for it
        (vecToList arrKindsRaw
         @ (vecToList lateLoopSources
            |> List.choose (fun (_, off, ty, _) ->
                match prune ty with
                | TCon ("list", [ _ ]) | TCon ("array", [ _ ]) -> Some (off, ty)
                // a string walks by index under the sentinel, and can never
                // have been the enumerator protocol
                | TCon ("string", []) -> Some (off, TCon ("$str", []))
                | _ -> None)))
        |> List.choose (fun (off, ty) ->
            let nameOf (t : Type) =
                match prune t with
                // a NESTED array is a reference like any other object: the
                // outer array holds pointers, so it is a uniform $ref array.
                // Naming it "array" asked the emitter for a packed layout
                // that does not exist and trapped on the cast.
                | TCon ("array", _) -> Some "$ref"
                // the name carries the instantiation, so an array of
                // Pair<int,int> is packed rather than an array of boxes
                | TCon (_, _) -> Some (instName t)
                // element type is the enclosing binding's type variable:
                // name it so stamping substitutes the real element type
                | TVar v -> Some ("#" + string v.Id)
                // tuples and functions are uniform references: the array is
                // a plain anyref array whatever they are
                | _ -> Some "$ref"
            match prune ty with
            // every site records the ARRAY type, so this unwraps exactly
            // once: `int[][]` names its element `$ref` (a nested array is a
            // reference), never the inner element's packed kind
            | TCon ("array", [ e ]) -> nameOf e |> Option.map (fun n -> off, n)
            | TCon (_, _) -> Some (off, instName ty)
            | TVar v -> Some (off, "#" + string v.Id)
            // an index site records the ELEMENT type directly; a tuple or
            // function element is a uniform reference
            | TTuple _ | TFun _ -> Some (off, "$ref")
            | _ -> None) }

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
      /// offset -> the OWNER type at its instantiation (`Pair$int$int`), for
      /// record construction and field access. Distinct from MemberSites,
      /// which names the declaring type for member dispatch.
      FieldOwners : (int * string) list }

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
      IsStatic : bool }

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
          (structTypes : Dict<string, bool>)
          (ctors : Dict<string, (int * Scheme) list>)
          (classes : Classes.Tables) : InferResult =
    let st = TypeState()
    let diags = vecNew<int * string> ()
    let opKindsRaw = vecNew<int * Type> ()
    let arrKindsRaw = vecNew<int * Type> ()
    let instRaw = vecNew<int * Type list> ()
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
                dictSet subst v.Id f
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
    let substVars (subst : Dict<int, Type>) (t : Type) : Type =
        let rec go (t : Type) : Type =
            match prune t with
            | TVar v -> (match dictTryFind subst v.Id with Some a -> a | None -> TVar v)
            | TCon (c, xs) -> TCon (c, List.map go xs)
            | TFun (a, b) -> TFun (go a, go b)
            | TTuple ts -> TTuple (List.map go ts)
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
            && (isSeqName sub || sub = "array" || sub = "list"
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

    /// Unify an argument against a parameter, allowing the argument to be a
    /// subtype — F# inserts the upcast, and the representation is identical.
    let unifyArg (offset : int) (paramTy : Type) (argTy : Type) : unit =
        match prune paramTy, prune argTy with
        | TCon (p, pa), TCon (a, aa) when p <> a && isSupertypeOf p a ->
            // widening: only the type arguments they share need to agree
            if pa.Length = aa.Length then List.iter2 (unifyAt offset) pa aa
        | _ -> unifyAt offset paramTy argTy

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
    let ctorSitesRaw = vecNew<int * int> ()
    /// record literals, resolved after solving so the instantiation is known
    let pendingRecords = vecNew<int * Type> ()
    let pendingDots = vecNew<int * Type * Type * string> ()
    /// `downcast`/`upcast` sites: the target type is only known once the
    /// surrounding expression has been solved
    let pendingCasts = vecNew<int * Type> ()

    /// Try to bind one dot-access. Returns false only when the receiver type
    /// is still unknown — i.e. when retrying later could learn something.
    let tryResolveDot (offset : int) (recvTy : Type) (result : Type) (name : string) : bool =
        // members are inherited: walk up the base chain to the type that
        // actually declares this one, and bind to THAT declaration
        // Walk to the type that declares this member, carrying the receiver's
        // type arguments up through each `inherit` so a generic base is
        // instantiated the way the derived class instantiated it.
        let rec declaringOwner (tn : string) (args : Type list) : (FieldInfo * string * Type list) option =
            match dictTryFind fields (tn + "." + name) with
            | Some fi -> Some (fi, tn, args)
            | None ->
                match dictTryFind bases tn with
                | Some (ps, baseTy) ->
                    let subst = dictNew<int, Type> ()
                    if ps.Length = args.Length then
                        List.zip ps args |> List.iter (fun (pv, a) -> dictSet subst pv.Id a)
                    (match prune (substVars subst baseTy) with
                     | TCon (bn, bargs) -> declaringOwner bn bargs
                     | _ -> None)
                | None -> None
        // Instantiating the member's own scheme (rather than substituting
        // into its type) is what turns the use into a specialization demand:
        // a generic class' members must be stamped per element type just
        // like a generic function's.
        // Only when the member is declared on the receiver's OWN type: for an
        // inherited member the declared self is the base, and unifying it
        // with the receiver would demand a subtyping the unifier has no
        // notion of. Type arguments are unified, never the nominal head.
        let tracked (tn : string) (args : Type list) (fi : FieldInfo) : bool =
            match fi.DefKey with
            | Some (dp, doff) when dp = path && not fi.IsStatic && fi.TypeName = tn ->
                (match dictTryFind defSchemes doff with
                 | Some sch ->
                     (match instantiateTracked sch with
                      | TFun (selfT, memT), fresh, _ ->
                          (match prune selfT with
                           | TCon (sn, sargs) when sn = tn && sargs.Length = args.Length ->
                               List.iter2 (unifyAt offset) sargs args
                               unifyAt offset result memT
                               if not (List.isEmpty fresh) then vecAdd instRaw (offset, fresh)
                               vecAdd memberSitesRaw (offset, fi.TypeName)
                               true
                           | _ -> false)
                      | _ -> false)
                 | None -> false)
            | _ -> false
        match prune recvTy with
        | TCon (tn, args) ->
            (match declaringOwner tn args with
             | Some (fi, own, ownArgs) when own = tn && tracked tn args fi -> true
             | Some (fi, _, ownArgs) when fi.Params.Length = ownArgs.Length ->
                 let subst = dictNew<int, Type> ()
                 List.zip fi.Params ownArgs |> List.iter (fun (pv, a) -> dictSet subst pv.Id a)
                 for qv in fi.Quantified do dictSet subst qv.Id (st.Fresh ())
                 unifyAt offset result (substVars subst fi.FieldType)
                 vecAdd memberSitesRaw (offset, fi.TypeName)
                 if fi.DefKey.IsNone then vecAdd fieldOwnersRaw (offset, instName recvTy)
                 true
             | _ -> true)   // receiver known, no such member: retrying cannot help
        | _ -> false

    let nodesOf (n : GreenNode) : GreenNode list =
        n.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)

    let tokensOf (n : GreenNode) : Token list =
        n.Children |> List.choose (fun c -> match c with GToken t -> Some t | _ -> None)

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
                       | None -> TCon (name, args))
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
                  | None -> TCon (t.Text, [ arg ]))
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
        while i < vecLen queue do
            let offset, c = vecGet queue i
            i <- i + 1
            match byGiven c with
            | Some assoc ->
                progress <- true
                for n, ty in c.Assoc do
                    match assoc |> List.tryFind (fun (an, _) -> an = n) with
                    | Some (_, gt) -> unifyAt offset ty gt
                    | None -> ()
            | None ->
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
                    List.iter2 (fun h a -> unifyAt offset (Classes.substInst sub h) a) inst.Head c.Args
                    vecAdd queue (offset, c)
                | Classes.Deferred -> vecAdd survivors (offset, c)
                | Classes.NoInstance ->
                    if isGround c then
                        progress <- true
                        vecAdd diags
                            (offset,
                             "no instance " + c.Class + "<"
                             + String.concat ", " (List.map typeString c.Args) + ">")
                    else vecAdd survivors (offset, c)
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
    let generalizeBinding (declared : Constraint list) (ty : Type) : Scheme =
        solveWanted ()
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
        | Classes.Solved (inst, _) ->
            match inst.Members |> List.tryPick (fun (m, k) -> if m = memberName then Some k else None) with
            | Some k -> Some k
            | None when byName ->
                (match dictTryFind classes.Classes c.Class with
                 | Some cd ->
                     (match cd.Members |> List.tryFindIndex (fun (m, _) -> m = memberName) with
                      | Some index -> Some (Classes.wrapperMember inst index memberName)
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
    let constraintOf (vars : Dict<string, Type>) (n : GreenNode) : Constraint option =
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
            // integer literal suffixes: 5L is int64, 5u is uint32
            if t.Text.EndsWith "L" then TCon ("int64", [])
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
            (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
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
                 let ctorTy = patType pvars head
                 let argTys = args |> List.filter (fun m -> isPatKind m.NodeKind) |> List.map (patType pvars)
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
            // `:? T` narrows to T; the scrutinee itself stays a supertype
            (match nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind) with
             | Some tn -> typeFromNode pvars tn
             | None -> st.Fresh ())
        | TuplePat ->
            TTuple (nodesOf n |> List.filter (fun m -> isPatKind m.NodeKind) |> List.map (patType pvars))
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
            let items = vecNew<Type> ()
            let kids = n.Children
            let rec walk (ks : Green list) =
                match ks with
                | GNode p :: rest when isPatKind p.NodeKind ->
                    let ty = patType pvars p
                    (match rest with
                     | GToken c :: GNode a :: rest2 when c.Text = ":" && isTypeKind a.NodeKind ->
                         unify ty (typeFromNode pvars a) |> ignore
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
            | many -> TTuple many
        | _ -> st.Fresh ()

    // ---- expressions ------------------------------------------------------

    let opClass (text : string) : string =
        if text = "&&" || text = "||" then "logic"
        elif text = "::" then "cons"
        elif text = "|>" then "pipe"
        elif text = "<|" then "pipeBack"
        elif text = "=" || text = "<>" || text = "<" || text = ">" || text = "<=" || text = ">=" then "cmp"
        elif text = "+" || text = "-" || text = "*" || text = "/" || text = "%" || text = "**" then "arith"
        elif text = "&&&" || text = "|||" || text = "^^^" || text = "<<<" || text = ">>>" then "bits"
        elif text = "@" then "append"
        elif text = "<-" || text = ":=" then "assign"
        else "unknown"

    let rec exprType (g : Green) : Type =
        match g with
        | GToken _ -> st.Fresh ()
        | GNode n ->
            match n.NodeKind with
            | LiteralExpr ->
                (match tokensOf n |> List.tryHead with
                 | Some t -> literalType t
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
                               | Some (ty, cs) -> owe cs; ty
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
                             | Some t -> List.contains t.Text [ "int"; "int64"; "uint32"; "float"; "float32"; "float16" ]
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
                     // numeric conversions are primitives, not functions
                     let conversion =
                         match head.NodeKind, args with
                         | IdentExpr, [ onlyArg ] ->
                             (match tokensOf head |> List.tryHead with
                              | Some t when t.Text = "int64" && (dictTryFind useDefs t.Offset).IsNone ->
                                  exprType (GNode onlyArg) |> ignore
                                  Some (TCon ("int64", []))
                              | Some t when (t.Text = "int" || t.Text = "uint32")
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
                         // the head may carry explicit type arguments:
                         // `HashSet<'K>(comparer, root)`
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
                                 (match dictTryFind useDefs ht.Offset with
                                  | Some d when d.Kind = Resolve.DefType ->
                                      (match dictTryFind ctors d.Name with
                                       | Some cs when cs.Length > 1 -> Some (ht, cs)
                                       | _ -> None)
                                  | _ -> None)
                             | None -> None
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
                         let fits (sch : Scheme) =
                             match prune (st.Instantiate sch) with
                             | TFun (dom, res) ->
                                 // a trial unification on a private copy:
                                 // committing here would corrupt the others
                                 let probe = st.Instantiate { Quantified = []; Constraints = []; Body = argTy }
                                 (match unify (st.Instantiate { Quantified = []; Constraints = []; Body = dom }) probe with
                                  | None -> Some res
                                  | Some _ -> None)
                             | _ -> None
                         let chosen =
                             cs |> List.tryPick (fun (o, sch) -> fits sch |> Option.map (fun _ -> o, sch))
                         (match chosen with
                          | Some (o, sch) ->
                              vecAdd ctorSitesRaw (ht.Offset, o)
                              (match prune (st.Instantiate sch) with
                               | TFun (dom, res) -> unifyAt ht.Offset dom argTy; res
                               | other -> other)
                          | None ->
                              vecAdd diags (ht.Offset, "no constructor of " + ht.Text + " accepts these arguments")
                              st.Fresh ())
                     | None ->
                     let mutable funTy = exprType (GNode head)
                     let off =
                         match Green.tokens (GNode head) |> List.tryHead with
                         | Some t -> t.Offset
                         | None -> 0
                     let mutable firstArg = true
                     let mutable firstArgTy = None
                     for a in args do
                         if isExprish a.NodeKind then
                             let argTy = exprType (GNode a)
                             if firstArg then
                                 firstArgTy <- Some argTy
                                 firstArg <- false
                             let res = st.Fresh ()
                             // decompose first so a subclass argument can widen
                             (match prune funTy with
                              | TFun (pt, rt) ->
                                  unifyArg off pt argTy
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
                 | [ l; r ], [ op ] ->
                     let lt = exprType (GNode l)
                     let rt = exprType (GNode r)
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
                          let res = st.Fresh ()
                          unifyAt op.Offset rt (TFun (lt, res))
                          res
                      | "pipeBack" ->
                          let res = st.Fresh ()
                          unifyAt op.Offset lt (TFun (rt, res))
                          res
                      | "assign" -> tUnit
                      | _ -> st.Fresh ())
                 | _ ->
                     for m in nodesOf n do exprType (GNode m) |> ignore
                     st.Fresh ())
            | PrefixExpr ->
                let inner =
                    nodesOf n |> List.filter (fun m -> isExprish m.NodeKind)
                    |> List.map (fun m -> exprType (GNode m))
                (match tokensOf n |> List.tryHead with
                 | Some t when t.Text = "not" ->
                     (match inner with
                      | [ i ] -> unifyAt t.Offset i tBool
                      | _ -> ())
                     tBool
                 | Some t when t.Text = "~~~" ->
                     // bitwise complement keeps its operand's integer type
                     (match inner with
                      | [ i ] -> i
                      | _ -> tInt)
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
            | ParenExpr ->
                let vars = dictNew<string, Type> ()
                let inner =
                    n.Children
                    |> List.filter (fun c -> match c with GNode m -> isExprish m.NodeKind | _ -> false)
                    |> List.map exprType
                let ascribed =
                    nodesOf n |> List.tryFind (fun m -> isTypeKind m.NodeKind)
                    |> Option.map (typeFromNode vars)
                match inner, ascribed with
                | [], _ -> tUnit
                | [ t ], Some a -> unify t a |> ignore; t
                | [ t ], None -> t
                | many, _ -> List.last many
            | TupleExpr ->
                TTuple (n.Children
                        |> List.filter (fun c -> match c with GNode m -> isExprish m.NodeKind | _ -> false)
                        |> List.map exprType)
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
                                else unifyArg barOff scrut (patType cvars m)
                        // body: expr children; when-guard is bool but we keep it loose
                        let bodies = nodesOf cl |> List.filter (fun m -> isExprish m.NodeKind)
                        (match List.tryLast bodies with
                         | Some b ->
                             for extra in bodies do
                                 if not (System.Object.ReferenceEquals (extra, b)) then
                                     exprType (GNode extra) |> ignore
                             unifyAt barOff (exprType (GNode b)) result
                         | None -> ())
                result
            | BlockExpr ->
                let mutable last = tUnit
                for m in nodesOf n do
                    last <- exprType (GNode m)
                last
            | LetDecl -> inferLet n
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
                for m in nodesOf n do
                    if m.NodeKind = MemberDecl then
                        inferMember (synth + "." + ifaceName) (dictNew ()) [] selfTy m
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
                (match Green.tokens (GNode n) |> List.tryHead with
                 | Some t -> vecAdd fieldOwnersRaw (t.Offset, instName ty)
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
                if hasOpToken ":?" n then tBool
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
                for m in nodesOf n do
                    if m.NodeKind = ListExpr then exprType (GNode m) |> ignore
                (match lhsTy |> Option.map prune with
                 | Some (TCon ("array", [ e ])) ->
                     (match Green.tokens (GNode n) |> List.tryHead with
                      | Some t -> vecAdd arrKindsRaw (t.Offset, e)
                      | None -> ())
                     e
                 | Some (TCon ("string", [])) ->
                     (match Green.tokens (GNode n) |> List.tryHead with
                      | Some t -> vecAdd arrKindsRaw (t.Offset, tString)
                      | None -> ())
                     tChar
                 | _ -> st.Fresh ())
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
                     | Some t -> vecAdd pendingCasts (t.Offset, result)
                     | None -> ())
                    result
                else
                // `C.M` where C names a type: a static member, so the owner
                // is the type itself and there is no receiver to type
                let staticOwner =
                    // the head may be a bare type name or a generic
                    // application: `Comparer.Instance` or `Comparer<int>.Instance`
                    let headIdent (h : GreenNode) =
                        if h.NodeKind = IdentExpr then tokensOf h |> List.tryFind (fun t -> t.Kind = Ident)
                        elif h.NodeKind = AppExpr then
                            match nodesOf h |> List.tryHead with
                            | Some inner when inner.NodeKind = IdentExpr ->
                                tokensOf inner |> List.tryFind (fun t -> t.Kind = Ident)
                            | _ -> None
                        else None
                    match nodesOf n |> List.tryHead |> Option.bind headIdent with
                    | Some t ->
                        (match dictTryFind useDefs t.Offset with
                         | Some d when d.Kind = Resolve.DefType -> Some d.Name
                         | _ -> None)
                    | None -> None
                match staticOwner, lastIdent with
                | Some tn, Some name when (dictTryFind fields (tn + "." + name.Text)).IsSome ->
                    let fi = (dictTryFind fields (tn + "." + name.Text)).Value
                    let subst = dictNew<int, Type> ()
                    for pv in fi.Params do dictSet subst pv.Id (st.Fresh ())
                    for qv in fi.Quantified do dictSet subst qv.Id (st.Fresh ())
                    vecAdd memberSitesRaw (name.Offset, tn)
                    substVars subst fi.FieldType
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
                          (match Green.tokens (GNode n) |> List.tryHead with
                           | Some t -> vecAdd arrKindsRaw (t.Offset, e)
                           | None -> ())
                          tInt
                      | Some (TCon ("string", [])), Some nm when nm.Text = "Length" ->
                          (match Green.tokens (GNode n) |> List.tryHead with
                           | Some t -> vecAdd arrKindsRaw (t.Offset, tString)
                           | None -> ())
                          tInt
                      | _ ->
                     match lhsTy, lastIdent with
                      | Some lt, Some name ->
                          let result = st.Fresh ()
                          if not (tryResolveDot name.Offset lt result name.Text) then
                              vecAdd pendingDots (name.Offset, lt, result, name.Text)
                          result
                      | _ -> st.Fresh ()))
            | ForExpr | WhileExpr ->
                let fvars = dictNew<string, Type> ()
                // `for x in arr do`: bind x to the element type and record
                // the collection's element name for lowering
                (match nodesOf n |> List.filter (fun m -> isExprish m.NodeKind) with
                 | coll :: _ when n.NodeKind = ForExpr ->
                     let ct = exprType (GNode coll)
                     (match prune ct with
                      | TCon ("array", [ e ]) ->
                          (match Green.tokens (GNode coll) |> List.tryHead with
                           | Some t -> vecAdd arrKindsRaw (t.Offset, ct)
                           | None -> ())
                          (match nodesOf n |> List.tryFind (fun m -> isPatKind m.NodeKind) with
                           | Some ip -> unify (patType fvars ip) e |> ignore
                           | None -> ())
                      | _ -> ())
                 | _ -> ())
                for m in nodesOf n do
                    if isPatKind m.NodeKind then patType fvars m |> ignore
                    elif isExprish m.NodeKind then exprType (GNode m) |> ignore
                tUnit
            | RecordExpr ->
                let fieldNodes = nodesOf n |> List.filter (fun m -> m.NodeKind = RecordExprField)
                let baseExpr = nodesOf n |> List.tryFind (fun m -> m.NodeKind <> RecordExprField && isExprish m.NodeKind)
                let fieldNames =
                    fieldNodes
                    |> List.choose (fun f -> tokensOf f |> List.tryFind (fun t -> t.Kind = Ident))
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
                         let nameTok = tokensOf f |> List.tryFind (fun t -> t.Kind = Ident)
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
                 | Some t -> vecAdd arrKindsRaw (t.Offset, elem)
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
        // NOTE: must be called only after EnterLevel — variables created by
        // the ascription have to live at the binding's level to generalize
        let ascriptionOf () =
            vecToList before
            |> List.tryPick (fun c -> match c with GNode t when isTypeKind t.NodeKind -> Some (typeFromNode vars t) | _ -> None)
        let isDestructure =
            // `let struct(a, b) = e` binds several names, like `let a, b = e`
            (vecToList before |> List.exists (fun c -> match c with GToken t -> t.Kind = Comma | _ -> false))
            || (match pats with [ p ] -> p.NodeKind = StructTuplePat | _ -> false)
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
            let bodyTys = vecToList after |> List.map exprType
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
            // generalize and overwrite the monomorphic scheme
            (match Green.tokens (GNode namePat) |> List.tryFind (fun t -> t.Kind = Ident) with
             | Some t when (dictTryFind defsAt t.Offset).IsSome ->
                 setScheme t.Offset (generalizeBinding declared funTy)
             | _ -> ())
            // `let x = e in body` evaluates to the continuation
            if hasIn then (match List.tryLast bodyTys with Some t -> t | None -> tUnit)
            else tUnit
        | _ ->
            // destructuring: bind all pattern names, unify with the body
            st.EnterLevel ()
            let patTys = pats |> List.map (patType vars)
            let bodyTys = vecToList after |> List.map exprType
            st.ExitLevel ()
            (match patTys, List.tryLast bodyTys with
             | [ single ], Some b -> unify single b |> ignore
             | many, Some b -> unify (TTuple many) b |> ignore
             | _ -> ())
            tUnit

    and inferTypeDecl (n : GreenNode) : unit =
        if pendingStructAttr then
            (match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
             | Some t -> dictSet structTypes t.Text true
             | None -> ())
        pendingStructAttr <- false
        // declared type parameters
        let vars = dictNew<string, Type> ()
        let tyParams = vecNew<Type> ()
        for m in nodesOf n do
            if m.NodeKind = TyParams then
                // 'a sits inside VarType nodes — walk all descendant tokens
                for t in Green.tokens (GNode m) do
                    if t.Kind = Ident && t.Text <> "_" && not (dictTryFind vars t.Text).IsSome then
                        let v = st.Fresh ()
                        dictSet vars t.Text v
                        vecAdd tyParams v
        let name =
            match tokensOf n |> List.tryFind (fun t -> t.Kind = Ident) with
            | Some t -> t.Text
            | None -> "?"
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
                  dictSet bases name (ownParams, typeFromNode vars tn)
              | None -> ())
         | None -> ())
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
                         t.Text, (nodesOf m |> List.filter (fun p -> isPatKind p.NodeKind) |> List.length))))
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
                                   FieldType = ft; DefKey = None; IsStatic = false }
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
                     let sch = { Quantified = freeVars ctorTy |> List.distinctBy (fun v -> v.Id); Constraints = []; Body = ctorTy }
                     setScheme t.Offset sch
                     recordDef t ctorTy
                 | _ -> ())
            | LetDecl -> inferLet m |> ignore
            | MemberDecl when tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "val") ->
                // `val mutable X : T` is a field declaration
                (match tokensOf m |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast,
                       nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                 | Some nameTok, Some tyNode ->
                     let ft = typeFromNode vars tyNode
                     recordDef nameTok ft
                     let info =
                         { TypeName = name; Params = paramVarList (); Quantified = []
                           FieldType = ft; DefKey = None; IsStatic = false }
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
                let csch = { Quantified = freeVars ctorTy |> List.distinctBy (fun v -> v.Id); Constraints = []; Body = ctorTy }
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
                    match nodesOf ty |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                    | Some hd when ty.NodeKind = AppType -> ifaceOf hd
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
                     let sch = { Quantified = freeVars ctorTy |> List.distinctBy (fun v -> v.Id); Constraints = []; Body = ctorTy }
                     setScheme nameTok.Offset sch
                     let prior = match dictTryFind ctors name with Some l -> l | None -> []
                     dictSet ctors name (prior @ [ nameTok.Offset, sch ])
                 | _ -> ())
            | _ -> ()

    and inferMember (tyName : string) (tyVars : Dict<string, Type>) (classParams : Var list) (selfTy : Type) (n : GreenNode) : unit =
        // member scope: the class type variables plus the member's own
        let mvars = dictNew<string, Type> ()
        for k, v in dictPairs tyVars do dictSet mvars k v
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
                 for b in bodies do exprType (GNode b) |> ignore
                 // the written value has the property's type
                 (match pts with
                  | [ only ] -> unifyAt (match tokensOf sa |> List.tryHead with Some t -> t.Offset | None -> 0) only propTy
                  | _ -> ())
                 let setTy = List.foldBack (fun p acc -> TFun (p, acc)) pts tUnit
                 (match tokensOf sa |> List.tryFind (fun t -> t.Kind = Ident) with
                  | Some kt when (dictTryFind defsAt kt.Offset).IsSome ->
                      let defTy = TFun (selfTy, setTy)
                      setScheme kt.Offset { Quantified = freeVars defTy |> List.distinctBy (fun v -> v.Id); Constraints = []; Body = defTy }
                      (match nameTok with
                       | Some pn ->
                           dictSet fields (tyName + ".set_" + pn.Text)
                               { TypeName = tyName; Params = classParams
                                 Quantified = []
                                 FieldType = setTy
                                 DefKey = Some (path, kt.Offset); IsStatic = false }
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
                 dictSet fields (tyName + "." + t.Text)
                     { TypeName = tyName; Params = classParams
                       Quantified =
                           freeVars propTy |> List.distinctBy (fun v -> v.Id)
                           |> List.filter (fun v -> not (Set.contains v.Id classIds))
                       FieldType = propTy
                       DefKey = (if (dictTryFind defsAt t.Offset).IsSome then Some (path, t.Offset) else None)
                       IsStatic = false }
             | None -> ())
        else

        let paramTys = vecToList pats |> List.map (patType mvars)
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
            dictSet fields (tyName + "." + t.Text)
                { TypeName = tyName; Params = classParams; Quantified = quantified
                  FieldType = memberTy
                  DefKey = (if (dictTryFind defsAt t.Offset).IsSome then Some (path, t.Offset) else None)
                  IsStatic = isStatic }
        | None -> ()

    /// An instance member is an ordinary function; the only extra work is
    /// pinning its type to the signature the class declared, at this head.
    and inferInstanceMember (expected : Type option) (t : Token) (m : GreenNode) : unit =
        st.EnterLevel ()
        let mvars = dictNew<string, Type> ()
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
            match dictTryFind classes.Classes name with
            | None -> ()
            | Some cd ->
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

    and inferDecl (g : Green) : unit =
        match g with
        | GToken _ -> ()
        | GNode n ->
            match n.NodeKind with
            | LetDecl -> inferLet n |> ignore
            | TypeDecl -> inferTypeDecl n
            | ModuleDef ->
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
                              MName = t.Text; MTakesUnit = takesUnit }))
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
                        match nodesOf ty |> List.tryFind (fun x -> isTypeKind x.NodeKind) with
                        | Some hd when ty.NodeKind = AppType -> ifaceOf hd
                        | _ ->
                            Green.tokens (GNode ty) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                            |> Option.map (fun t -> t.Text)
                    let names =
                        nodesOf n
                        |> List.filter (fun m -> m.NodeKind = InterfaceImpl)
                        |> List.choose (fun m ->
                            nodesOf m |> List.tryFind (fun x -> isTypeKind x.NodeKind) |> Option.bind ifaceOf)
                    if not (List.isEmpty names) then
                        let prior = match dictTryFind impls nameTok.Text with Some l -> l | None -> []
                        dictSet impls nameTok.Text (prior @ names)
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

    for c in root.Children do inferDecl c
    solveWanted ()

    // Numeric defaulting, as F# does it: a constraint nothing in the program
    // ever pins down resolves at int. `Zero + One` has to mean something, and
    // int is the answer every F# programmer already expects.
    let mutable defaulting = true
    while defaulting do
        defaulting <- false
        match wanted |> List.tryFind (fun (_, c) -> not (isGround c)) with
        | Some (offset, c) ->
            (match Classes.select classes c.Class (c.Args |> List.map (fun _ -> tInt)) [] with
             | Classes.Solved _ ->
                 for a in c.Args do unifyAt offset a tInt
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
            if tryResolveDot offset recvTy result name then progress <- true
            else vecAdd still (offset, recvTy, result, name)
        parked <- vecToList still
    // record literals: name the instantiation once everything is solved
    for offset, ty in vecToList pendingRecords do
        vecAdd fieldOwnersRaw (offset, instName ty)

    // contextual casts: the target is whatever the context settled on
    for offset, ty in vecToList pendingCasts do
        match prune ty with
        | TCon (n, _) -> vecAdd memberSitesRaw (offset, n)
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
        | TCon ("string", []) -> "t"
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
                | TCon (n, _) -> n
                // still a variable: this use sits inside a generic body and
                // instantiates at the ENCLOSING binding's type variable —
                // name it so stamping can substitute the caller's argument
                | TVar v -> "#" + string v.Id
                | _ -> ""))
      MemberSites = vecToList memberSitesRaw
      FieldOwners = vecToList fieldOwnersRaw
      CtorSites = vecToList ctorSitesRaw
      ClassUses = vecToList classUsesRaw
      ClassPending = vecToList classPendingRaw
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
        vecToList arrKindsRaw
        |> List.choose (fun (off, ty) ->
            let nameOf (t : Type) =
                match prune t with
                // the name carries the instantiation, so an array of
                // Pair<int,int> is packed rather than an array of boxes
                | TCon (_, _) -> Some (instName t)
                // element type is the enclosing binding's type variable:
                // name it so stamping substitutes the real element type
                | TVar v -> Some ("#" + string v.Id)
                | _ -> None
            match prune ty with
            | TCon ("array", [ e ]) -> nameOf e |> Option.map (fun n -> off, n)
            | TCon (_, _) -> Some (off, instName ty)
            | TVar v -> Some (off, "#" + string v.Id)
            | _ -> None) }

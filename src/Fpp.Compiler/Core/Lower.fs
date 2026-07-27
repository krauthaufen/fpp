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
          (ctorSites : Dict<int, int>)
          (projectMembers : Dict<string, Resolve.Definition>)
          (ifaces : Dict<string, (string * int) list>)
          (classUses : Dict<int, Fpp.Analysis.Classes.InstMember>)
          (classPending : Dict<int, string>)
          (opTypes : Dict<int, string>) : LowerResult =

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
    let isStaticUse (n : GreenNode) : bool =
        let rec headIdent (h : GreenNode) =
            if h.NodeKind = IdentExpr then
                h.Children |> List.tryPick (fun c -> match c with GToken t when t.Kind = Ident -> Some t | _ -> None)
            elif h.NodeKind = AppExpr then
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
    let offsetOf (n : GreenNode) =
        match Green.tokens (GNode n) |> List.tryHead with
        | Some t -> t.Offset
        | None -> 0

    let isPatKind (k : NodeKind) =
        k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat || k = StructTuplePat
        || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat || k = TypeTestPat
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
                     (match dictTryFind classUses t.Offset with
                      // a class member (`Zero`) is a name for whatever the
                      // selected instance provides
                      | Some im ->
                          let v = { Path = im.MPath; Offset = im.MOffset; Name = im.MName }
                          let sch = mono (TCon ("?", []))
                          if im.MTakesUnit then EApp (EVar (v, sch), [ ELit LUnit ]) else EVar (v, sch)
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
                          List.contains t.Text [ "int"; "int64"; "uint32"; "float"; "float32"; "float16"; "string" ]
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
                      | EVar (bv, _), [ pa ] when bv.Name = "pin" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          EArrayPin (nm, pa)
                      | EVar (bv, _), [ pa ] when bv.Name = "unpin" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          EArrayUnpin (nm, pa)
                      | EVar (bv, _), [ cn ] when bv.Name = "zeroCreate" && bv.Path = "(builtin)" ->
                          let nm = match dictTryFind arrKinds (offsetOf n) with Some x -> x | None -> ""
                          // the zero value is per-representation, so the
                          // marker survives to the emitter, which knows it
                          EArrayCreate (nm, cn, EUnknown "$zero")
                      | EVar (bv, _), [ cn; cv ] when bv.Name = "create" && bv.Path = "(builtin)" ->
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
                                  EApp (EVar ({ Path = im.MPath; Offset = im.MOffset; Name = im.MName }, mono (TCon ("?", []))),
                                        [ lowerExpr (GNode l); lowerExpr (GNode r) ])
                              // ordering has ONE operation: the predicates are
                              // notation for a test on its result
                              if im.MName = "compare" then EPrim (op.Text, [ call; ELit (LInt "0") ])
                              else call
                          | None ->
                              EPrim (op.Text + suffix, [ lowerExpr (GNode l); lowerExpr (GNode r) ]))
                 | _ -> note (offsetOf n) "operator shape")
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
                         EApp (EVar ({ Path = im.MPath; Offset = im.MOffset; Name = im.MName }, mono (TCon ("?", []))),
                               [ lowerExpr (GNode a) ])
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
                    | None -> (fieldOfVar : Dict<string * int, string * string>).Remove k |> ignore
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
                         && d.Path = path
                         && (dictTryFind topLevelDefs d.Offset).IsSome ->
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
                          let v = { Path = im.MPath; Offset = im.MOffset; Name = im.MName }
                          let sch = mono (TCon ("?", []))
                          if im.MTakesUnit then EApp (EVar (v, sch), [ ELit LUnit ]) else EVar (v, sch)
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
                                    ESeq [ lowerExpr (GNode body)
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
                              | PVar (iv, isch) -> ELet (false, iv, isch, elem, lowerExpr (GNode body))
                              | p -> EMatch (elem, [ p, None, lowerExpr (GNode body) ])
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
                                  | _ -> Some (EApp (EVar (varIdOf d, schemeOf d), recv :: args))
                          let anon = mono (TCon ("?", []))
                          let enV = { Path = path; Offset = fo + 4000000; Name = "_en" }
                          (match call (synth "GetEnumerator" 30000000) (lowerExpr (GNode range)) true,
                                 call (synth "MoveNext" 40000000) (EVar (enV, anon)) true,
                                 call (synth "Current" 50000000) (EVar (enV, anon)) false with
                           | Some g, Some m, Some c ->
                               let inner =
                                   match pat with
                                   | PVar (iv, isch) ->
                                       ELet (false, iv, isch, c, lowerExpr (GNode body))
                                   | p ->
                                       // tuple and struct-tuple binders
                                       // destructure the current element
                                       EMatch (c, [ p, None, lowerExpr (GNode body) ])
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
                 | Some (SimpleLet (isRec, v, sch, rhs, _)) -> vecAdd decls (DLet (isRec, v, sch, rhs))
                 | _ -> vecAdd notes (offsetOf n, "top-level let shape"))
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
            | ModuleHeader | OpenDecl -> ()
            | k when isExprish k ->
                vecAdd decls (DLet (false, { Path = path; Offset = offsetOf n; Name = "_it" }, mono tUnit, lowerExpr g))
            | _ -> vecAdd notes (offsetOf n, "declaration " + string n.NodeKind)

    for c in root.Children do lowerDecl c

    { Decls = vecToList decls
      Notes = vecToList notes }

module Fpp.Analysis.Types

open Fpp.Prelude

// Type representation and unification for the HM core. Union-find via
// mutable links on variables, generalization by levels (Rémy-style).
// Non-equality constraints (classes, overloads) will queue for deferred
// solving later; the HM skeleton stays as plain unification.

[<ReferenceEquality>]
type Var =
    { Id : int
      mutable Level : int
      mutable Link : Type option
      /// A type parameter WRITTEN in the enclosing binding's signature. Its
      /// body must work for every instantiation, so inside that body the
      /// variable stands for one it cannot choose — `'K` is not free to
      /// become `Cmp<'K>` just because an overload would like it to.
      ///
      /// Ordinary unification ignores this: the flag exists for overload
      /// resolution, which is the one place that asks a hypothetical
      /// question ("would this candidate fit?") and must not answer it by
      /// helping itself to the caller's type parameters.
      mutable Rigid : bool }

and Type =
    | TVar of Var
    | TCon of string * Type list
    | TFun of Type * Type
    | TTuple of Type list
    /// a CONSTRUCTOR VARIABLE applied to arguments: `'f<'a>`. The head is
    /// always a TVar node; once the head solves to a constructor, `prune`
    /// collapses the application into the TCon — a head bound to a
    /// PARTIAL application (`Result<'e, _>` stored as TCon("Result",['e]))
    /// collapses by appending, which is the whole partial-application
    /// story. No type-level lambdas: heads never solve to TFun/TTuple.
    | TApp of Type * Type list

/// A class applied to types, optionally equating its associated types:
/// `Add<'a,'b> with Result = 'a` is
/// `{ Class = "Add"; Args = ['a; 'b]; Assoc = [("Result", 'a)] }`.
/// A constraint is never a type — it can only appear in a scheme's context,
/// which is why `Type` has no case for it.
and Constraint =
    { Class : string
      Args : Type list
      Assoc : (string * Type) list }

type Scheme =
    { Quantified : Var list
      /// residual class constraints: what the caller must satisfy
      Constraints : Constraint list
      Body : Type }

let mono (t : Type) : Scheme = { Quantified = []; Constraints = []; Body = t }

let tInt = TCon ("int", [])
let tUInt = TCon ("uint32", [])

let tFloat = TCon ("float", [])
let tString = TCon ("string", [])
let tChar = TCon ("char", [])
let tBool = TCon ("bool", [])
let tUnit = TCon ("unit", [])
let tList (t : Type) = TCon ("list", [ t ])

/// What a SPECULATIVE unification has changed, so it can be put back.
/// Threaded explicitly rather than kept in module state: two workspaces
/// type-check at once in the test harness, and a trial that recorded — and
/// then undid — another thread's ordinary unifications corrupted both.
type Trial =
    { Undo : Vec<Var * Type option * int>
      /// do rigid variables refuse to be bound? Only ever inside a trial
      Rigid : bool }

let private noteVar (trial : Trial option) (v : Var) : unit =
    match trial with
    | Some t -> vecAdd t.Undo (v, v.Link, v.Level)
    | None -> ()

/// Follow links to the representative.
let rec prune (t : Type) : Type =
    match t with
    | TVar v ->
        match v.Link with
        | Some inner ->
            let r = prune inner
            // path compression is not recorded: it re-points a variable at
            // the SAME representative it already had, so undoing a trial
            // leaves it pointing where it should either way
            v.Link <- Some r
            r
        | None -> t
    | TApp (h, args) ->
        // a solved head collapses the application; a partial binding
        // appends its stored prefix. NOT cached on the node (there is no
        // var to cache on) — the collapse is cheap and trial-safe.
        (match prune h with
         | TCon (n, pargs) -> TCon (n, pargs @ args)
         | TApp (h2, args2) -> TApp (h2, args2 @ args)
         | hv -> if System.Object.ReferenceEquals (hv, h) then t else TApp (hv, args))
    | _ -> t

/// The name of a type AT an instantiation: `Pair<float,int>` is the distinct
/// type `Pair$float$int`. Generic structs must be stamped per instantiation
/// or their fields stay boxed, so the name has to carry the arguments.
let rec typeConName (t : Type) : string =
    match prune t with
    | TCon (n, []) -> n
    // bracketed so nested arguments stay unambiguous:
    // Pair<int, Pair<int,int>> -> Pair$<int.Pair$<int.int>>
    | TCon (n, args) -> n + "$<" + String.concat "." (List.map typeConName args) + ">"
    | TVar v -> "#" + string v.Id
    | TApp (h, args) ->
        typeConName h + "$<" + String.concat "." (List.map typeConName args) + ">"
    // A tuple is a UNIFORM reference — the same conclusion arrays reached,
    // where a tuple element makes the array a plain `$ref` array whatever it
    // holds. So every tuple instantiation of a generic shares one body, and
    // one name is what says so. Anonymous by design: `Dict<string * string>`
    // and `Dict<int * bool>` have identical layout and identical code.
    | TTuple _ -> "$ref"
    | _ -> ""

/// The name of a type where CLASS-INSTANCE dispatch is the consumer. The
/// same grammar as `typeConName`, except a TUPLE carries its arity and its
/// elements: layout naming deliberately shares every tuple as one "$ref",
/// but `Arb<int * bool>` and a triple are DIFFERENT instances, and a name
/// that cannot tell them apart cannot dispatch.
let rec instConName (t : Type) : string =
    match prune t with
    | TTuple ts ->
        "$tup" + string (List.length ts) + "$<" + String.concat "." (List.map instConName ts) + ">"
    | TCon (n, args) when not (List.isEmpty args) ->
        n + "$<" + String.concat "." (List.map instConName args) + ">"
    | other -> typeConName other

/// Map every type inside a constraint.
let mapConstraint (f : Type -> Type) (c : Constraint) : Constraint =
    { Class = c.Class
      Args = List.map f c.Args
      Assoc = c.Assoc |> List.map (fun (n, t) -> n, f t) }

// Types legitimately SHARE sub-DAGs (a variable solved once, read many
// times); every structural walker must be DAG-aware or a shared node
// expands into an exponential tree walk. Each walker below carries a
// reference-identity visited set.
/// Bucket for a visited set: cheap, and STABLE while the walk runs. It
/// reads only immutable fields — a variable's id, a constructor's name and
/// arity — because unification rewrites `Link` under a live set, and an
/// entry whose hash moved would be lost.
let shallowHash (t : Type) : int =
    match t with
    | TVar v -> v.Id * 4 + 1
    | TCon (n, args) -> (hash n * 31 + List.length args) * 4 + 2
    | TFun (_, _) -> 3
    | TTuple ts -> List.length ts * 4
    | TApp (_, args) -> List.length args * 4 + 3

let freeVars (t : Type) : Var list =
    let seen = refSetNew<Type> shallowHash
    let acc = vecNew<Var> ()
    let rec go (t : Type) : unit =
        let p = prune t
        if refSetAdd seen p then
            match p with
            | TVar v -> vecAdd acc v
            | TCon (_, args) -> List.iter go args
            | TFun (a, b) -> go a; go b
            | TTuple ts -> List.iter go ts
            | TApp (h, args) -> go h; List.iter go args
    go t
    vecToList acc

let private occurs (v : Var) (t : Type) : bool =
    let seen = refSetNew<Type> shallowHash
    let rec go (t : Type) : bool =
        let p = prune t
        if not (refSetAdd seen p) then false
        else
            match p with
            | TVar w -> System.Object.ReferenceEquals (v, w)
            | TCon (_, args) -> List.exists go args
            | TFun (a, b) -> go a || go b
            | TTuple ts -> List.exists go ts
            | TApp (h, args) -> go h || List.exists go args
    go t

/// Clamp levels of all vars in t to at most `level` (link-time invariant
/// that keeps generalization sound).
let private adjustLevels (trial : Trial option) (level : int) (t : Type) : unit =
    let seen = refSetNew<Type> shallowHash
    let rec go (t : Type) : unit =
        let p = prune t
        if refSetAdd seen p then
            match p with
            | TVar w ->
                if w.Level > level then
                    noteVar trial w
                    w.Level <- level
            | TCon (_, args) -> List.iter go args
            | TFun (a, b) -> go a; go b
            | TTuple ts -> List.iter go ts
            | TApp (h, args) -> go h; List.iter go args
    go t

/// Pretty-print with 'a, 'b, ... assigned per call in order of appearance.
/// BUDGETED: a type that shares sub-DAGs expands exponentially as a tree,
/// and a diagnostic renderer must never be where a compile goes to die.
let typeString (t : Type) : string =
    let names = dictNew<int, string> ()
    let mutable budget = 2000
    let nameOf (v : Var) : string =
        match dictTryFind names v.Id with
        | Some n -> n
        | None ->
            let n = "'" + string (char (int 'a' + names.Count))
            dictSet names v.Id n
            n
    let rec go (atom : bool) (t : Type) : string =
        budget <- budget - 1
        if budget <= 0 then "…"
        else
        match prune t with
        | TVar v -> nameOf v
        | TCon (n, []) -> n
        | TCon (n, args) -> n + "<" + String.concat ", " (List.map (go false) args) + ">"
        | TFun (a, b) ->
            let s = go true a + " -> " + go false b
            if atom then "(" + s + ")" else s
        | TTuple ts ->
            let s = String.concat " * " (List.map (go true) ts)
            if atom then "(" + s + ")" else s
        | TApp (h, args) ->
            go true h + "<" + String.concat ", " (List.map (go false) args) + ">"
    go false t

let constraintVars (c : Constraint) : Var list =
    List.collect freeVars c.Args @ List.collect (fun (_, t) -> freeVars t) c.Assoc

/// `Add<'a, 'b> with Result = 'c`, using the same per-call variable naming
/// as `typeString` would — callers that need names to agree across a
/// signature and its context must render them together.
let constraintStringWith (nameOf : Type -> string) (c : Constraint) : string =
    c.Class + "<" + String.concat ", " (List.map nameOf c.Args) + ">"
    + (match c.Assoc with
       | [] -> ""
       | eqs -> " with " + String.concat ", " (eqs |> List.map (fun (n, t) -> n + " = " + nameOf t)))

/// A scheme rendered with its context: `'a -> 'a   when Num<'a>`.
let schemeString (sch : Scheme) : string =
    // one naming pass over body and context together, so 'a means 'a in both
    let names = dictNew<int, string> ()
    let rec collect (t : Type) : unit =
        match prune t with
        | TVar v -> if (dictTryFind names v.Id).IsNone then dictSet names v.Id ("'" + string (char (int 'a' + names.Count)))
        | TCon (_, args) -> List.iter collect args
        | TFun (a, b) -> collect a; collect b
        | TTuple ts -> List.iter collect ts
        | TApp (h, args) -> collect h; List.iter collect args
    collect sch.Body
    for c in sch.Constraints do List.iter collect (constraintVars c |> List.map TVar)
    let rec go (atom : bool) (t : Type) : string =
        match prune t with
        | TVar v -> (match dictTryFind names v.Id with Some n -> n | None -> "'?")
        | TCon (n, []) -> n
        | TCon (n, args) -> n + "<" + String.concat ", " (List.map (go false) args) + ">"
        | TFun (a, b) ->
            let s = go true a + " -> " + go false b
            if atom then "(" + s + ")" else s
        | TTuple ts ->
            let s = String.concat " * " (List.map (go true) ts)
            if atom then "(" + s + ")" else s
        | TApp (h, args) ->
            go true h + "<" + String.concat ", " (List.map (go false) args) + ">"
    go false sch.Body
    + (match sch.Constraints with
       | [] -> ""
       | cs -> "   when " + String.concat ", " (cs |> List.map (constraintStringWith (go false))))

/// Structural unification. Returns an error message on mismatch, None on
/// success. Partial effects on failure are acceptable — the tree is only
/// used for diagnostics and hover after errors.
/// The id a STORED quantified variable answers to NOW: unification may
/// have re-pointed it at another variable, and a substitution keyed on the
/// recorded id would miss every occurrence in the (pruned) body.
let prunedId (v : Var) : int =
    match prune (TVar v) with
    | TVar w -> w.Id
    | _ -> v.Id

/// Installed by inference: nominal subsumption. Given (interface-side,
/// class-side), answer the DECLARED interface instantiation to unify the
/// interface side against — `HashSetDelta<'a>` widening into
/// `IEnumerable<'x>` yields `IEnumerable<SetOperation<'a>>`, so `'x` binds
/// to what the class actually enumerates. The caller performs the returned
/// unification itself, so trials stay undoable.
let mutable subsumeHook : (Type -> Type -> (Type * Type) option) option = None

let rec private unifySeen (seen : RefPairSet<Type>) (trial : Trial option) (t1 : Type) (t2 : Type) : string option =
    let unify a b = unifySeen seen trial a b
    let rigid (v : Var) = v.Rigid && (match trial with Some t -> t.Rigid | None -> false)
    let a = prune t1
    let b = prune t2
    if System.Object.ReferenceEquals (a, b) then None
    // a revisited PAIR is already being unified higher up the walk: the
    // shared sub-DAG expands exponentially as a tree without this cut
    elif not (refPairSetAdd seen a b) then None
    else
    match a, b with
    | TVar v, TVar w when System.Object.ReferenceEquals (v, w) -> None
    | TVar v, TVar w when rigid v && rigid w ->
        // two DIFFERENT parameters of the caller's signature: a candidate
        // that needs them equal needs something the caller never promised
        Some ("type mismatch: " + typeString a + " vs " + typeString b)
    | TVar v, TVar w ->
        // union by LEVEL: the SHALLOWER variable stays the representative.
        // Schemes quantify representatives — re-pointing a class-level
        // variable at a member-level one would make every scheme that
        // quantifies it miss its substitution at instantiation, and the
        // first concrete use would then ground the raw variable for ALL
        // a rigid variable stays the representative: binding it away is
        // what the flag exists to prevent
        if rigid v || (not (rigid w) && v.Level < w.Level) then
            noteVar trial w
            w.Link <- Some (TVar v)
        else
            adjustLevels trial w.Level (TVar v)
            noteVar trial v
            v.Link <- Some (TVar w)
        None
    | TVar v, other | other, TVar v ->
        if rigid v then
            // the caller's type parameter is not ours to choose
            Some ("type mismatch: " + typeString (TVar v) + " vs " + typeString other)
        elif occurs v other then
            Some ("the type " + typeString other + " would contain itself")
        else
            adjustLevels trial v.Level other
            noteVar trial v
            v.Link <- Some other
            None
    | TCon (n1, a1), TCon (n2, a2) ->
        if n1 = n2 && List.length a1 = List.length a2 then
            List.zip a1 a2 |> List.tryPick (fun (x, y) -> unify x y)
        // widening is COMMITTING-only: during an overload TRIAL the
        // question is "does this candidate fit as declared", and letting a
        // seq subsume into a HashSet parameter made the wrong Overlaps
        // overload fit — the runtime then read Root off a seq
        elif n1 <> n2 && subsumeHook.IsSome && trial.IsNone then
            // one side implements the other: the value widens, as it does
            // in F#. The hook names the class's DECLARED instantiation of
            // the interface; unifying against it is what pins the
            // interface's arguments to what the class really provides.
            let resolve = subsumeHook.Value
            (match resolve a b with
             | Some (da, db) -> unify da db
             | None ->
             match resolve b a with
             | Some (da, db) -> unify da db
             | None -> Some ("type mismatch: " + typeString a + " vs " + typeString b))
        else
            Some ("type mismatch: " + typeString a + " vs " + typeString b)
    | TFun (p1, r1), TFun (p2, r2) ->
        match unify p1 p2 with
        | Some e -> Some e
        | None -> unify r1 r2
    | TTuple x, TTuple y ->
        if List.length x <> List.length y then
            Some ("type mismatch: " + typeString a + " vs " + typeString b)
        else
            List.zip x y |> List.tryPick (fun (p, q) -> unify p q)
    // SPINE unification: a constructor variable applied to arguments
    // meets a concrete application — the head binds to the constructor's
    // untouched PREFIX (partial application), the trailing arguments
    // unify pairwise. `'f<'a> ~ Result<string,int>` binds
    // 'f := Result<string,_> and 'a := int.
    | TApp (TVar v, args), TCon (n, cargs) | TCon (n, cargs), TApp (TVar v, args) ->
        let k = List.length args
        let nc = List.length cargs
        if nc < k then
            Some ("type mismatch: " + typeString a + " vs " + typeString b)
        elif rigid v then
            Some ("type mismatch: " + typeString (TVar v) + " vs " + n)
        else
            let prefix = TCon (n, List.truncate (nc - k) cargs)
            let suffix = List.skip (nc - k) cargs
            if occurs v prefix then
                Some ("the type " + typeString prefix + " would contain itself")
            else
                adjustLevels trial v.Level prefix
                noteVar trial v
                v.Link <- Some prefix
                List.zip args suffix |> List.tryPick (fun (x, y) -> unify x y)
    | TApp (h1, a1), TApp (h2, a2) when List.length a1 = List.length a2 ->
        (match unify h1 h2 with
         | Some e -> Some e
         | None -> List.zip a1 a2 |> List.tryPick (fun (x, y) -> unify x y))
    | _ ->
        Some ("type mismatch: " + typeString a + " vs " + typeString b)

let unify (t1 : Type) (t2 : Type) : string option =
    unifySeen (refPairSetNew<Type> shallowHash) None t1 t2

/// Unify with an AMBIENT trail: every binding is recorded so a scope can
/// be rolled back — GADT branch refinement runs a whole clause this way.
/// With None it is plain `unify`.
let unifyWith (trial : Trial option) (t1 : Type) (t2 : Type) : string option =
    unifySeen (refPairSetNew<Type> shallowHash) trial t1 t2

/// Roll a trail back, newest binding first.
let undoTrial (trial : Trial) : unit =
    for v, link, lvl in List.rev (vecToList trial.Undo) do
        v.Link <- link
        v.Level <- lvl

/// A fresh, open trail for scoped unification.
let newTrial () : Trial = { Undo = vecNew<Var * Type option * int> (); Rigid = false }

/// Like unifyTrial, but on success answer HOW MANY variables the fit had to
/// bind. Overload selection uses it as an exactness measure: `IndexOf(Index)`
/// fits an Index argument with 0 bindings where `IndexOf('T)` needs one, and
/// F# picks the exact member — picking the generic one bound the class's own
/// parameter and corrupted every later use of the type.
let unifyTrialScore (rigid : bool) (t1 : Type) (t2 : Type) : int option =
    let trial = { Undo = vecNew<Var * Type option * int> (); Rigid = rigid }
    let r = unifySeen (refPairSetNew<Type> shallowHash) (Some trial) t1 t2
    let n = vecLen trial.Undo
    for v, link, lvl in List.rev (vecToList trial.Undo) do
        v.Link <- link
        v.Level <- lvl
    match r with
    | None -> Some n
    | Some _ -> None

/// Would these unify? Ask, then put everything back exactly as it was.
/// `rigid` makes the caller's own type parameters unbindable for the
/// duration, which is what turns "could this candidate be made to fit" into
/// "does this candidate fit" — the question overload resolution means.
let unifyTrial (rigid : bool) (t1 : Type) (t2 : Type) : string option =
    let trial = { Undo = vecNew<Var * Type option * int> (); Rigid = rigid }
    let r = unifySeen (refPairSetNew<Type> shallowHash) (Some trial) t1 t2
    // newest first, which is the order they have to be undone in
    for v, link, lvl in List.rev (vecToList trial.Undo) do
        v.Link <- link
        v.Level <- lvl
    r

/// Like unifyTrial, but on SUCCESS runs `k` while the trial's bindings are
/// still applied, and answers its result. A candidate's `when` context can
/// only be judged against the shapes the fit would give its variables —
/// after the undo those shapes are gone. Undone either way.
let unifyTrialUnder (rigid : bool) (t1 : Type) (t2 : Type) (k : unit -> 'r) : 'r option =
    let trial = { Undo = vecNew<Var * Type option * int> (); Rigid = rigid }
    let r = unifySeen (refPairSetNew<Type> shallowHash) (Some trial) t1 t2
    let out = match r with None -> Some (k ()) | Some _ -> None
    for v, link, lvl in List.rev (vecToList trial.Undo) do
        v.Link <- link
        v.Level <- lvl
    out

/// Variable supply and level tracking for one inference run.
type TypeState() =
    // the id supply is PROCESS-WIDE: schemes from a cached prelude live
    // across TypeStates, and id-keyed substitutions must never confuse a
    // cached variable with a fresh one that restarted the count
    let mutable nextId = 0
    let mutable level = 0

    member _.Level = level
    member _.EnterLevel () = level <- level + 1
    member _.ExitLevel () = level <- level - 1

    member _.Fresh () : Type =
        nextId <- nextId + 1
        TVar { Id = nextId; Level = level; Link = None; Rigid = false }

    /// Quantify variables deeper than the current level. A constraint is
    /// carried into the scheme when it mentions a quantified variable — the
    /// caller is the one who will have to discharge it.
    member _.GeneralizeWith (cs : Constraint list) (t : Type) : Scheme =
        let qs =
            freeVars t
            |> List.filter (fun v -> v.Level > level)
            |> List.distinctBy (fun v -> v.Id)
        // a constraint is carried when it mentions a quantified variable, and
        // carrying it quantifies the REST of its variables — which can make
        // another constraint eligible, so iterate to a fixpoint. sum()'s
        // Num<'s> reaches the type only through Add<'s,'a>: dropping it left
        // it in the pool, where numeric defaulting bound the scheme's own
        // variable to int behind its back.
        let mutable quantified = qs |> List.map (fun v -> v.Id) |> Set.ofList
        let mutable kept : Constraint list = []
        let mutable rest = cs
        let mutable progress = true
        while progress do
            progress <- false
            let keep =
                rest |> List.filter (fun c ->
                    constraintVars c |> List.exists (fun v -> Set.contains v.Id quantified))
            rest <-
                rest |> List.filter (fun c ->
                    not (constraintVars c |> List.exists (fun v -> Set.contains v.Id quantified)))
            for c in keep do
                for v in constraintVars c do
                    if v.Level > level && not (Set.contains v.Id quantified) then
                        quantified <- Set.add v.Id quantified
                        progress <- true
            kept <- kept @ keep
        // a variable that ONLY appears in the context (an associated-type
        // result, say) is still part of the scheme: it has to be freshened
        // per use or two call sites would share it
        let qids = qs |> List.map (fun v -> v.Id) |> Set.ofList
        let extra =
            kept
            |> List.collect constraintVars
            |> List.filter (fun v -> v.Level > level && not (Set.contains v.Id qids))
            |> List.distinctBy (fun v -> v.Id)
        { Quantified = qs @ extra; Constraints = kept; Body = t }

    member this.Generalize (t : Type) : Scheme = this.GeneralizeWith [] t

    /// Instantiate, also freshening the context. Returns the constraints the
    /// use site now owes.
    member this.InstantiateC (s : Scheme) : Type * Constraint list =
        if List.isEmpty s.Quantified then s.Body, s.Constraints
        else
            let subst = dictNew<int, Type> ()
            for v in s.Quantified do dictSet subst (prunedId v) (this.Fresh ())
            // memoized on node identity: the copy PRESERVES the body's
            // sharing — a naive walk materializes a shared sub-DAG once per
            // path, and the copies grow exponentially
            let memo = refMapNew<Type, Type> shallowHash
            let rec go (t : Type) : Type =
                let p = prune t
                match refMapTryFind memo p with
                | Some r -> r
                | None ->
                    let r =
                        match p with
                        | TVar v ->
                            (match dictTryFind subst v.Id with
                             | Some fresh -> fresh
                             | None -> TVar v)
                        | TCon (n, args) -> TCon (n, List.map go args)
                        | TFun (a, b) -> TFun (go a, go b)
                        | TTuple ts -> TTuple (List.map go ts)
                        | TApp (h, args) -> TApp (go h, List.map go args)
                    refMapSet memo p r
                    r
            go s.Body, List.map (mapConstraint go) s.Constraints

    member this.Instantiate (s : Scheme) : Type = fst (this.InstantiateC s)

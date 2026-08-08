module Fpp.Analysis.Classes

open Fpp.Prelude
open Fpp.Analysis.Types

// The class layer: typeclasses, free-standing instances, and the matching
// that selects one. Nothing here knows about syntax or inference — Infer
// fills these tables and drives the solver, this module owns the shapes and
// the selection rule.
//
// The load-bearing idea: a class member is an ORDINARY constrained scheme.
// `(*)` in `class Mul<'a,'b>` has type `'a -> 'b -> 'r` with the context
// `Mul<'a,'b> with Result = 'r`. So associated types never appear in `Type`
// at all — the projection lives in the constraint, and unification stays
// exactly the first-order HM unification it already was.

/// The auto-opened prelude's pseudo-path. Instances declared there may omit
/// their bodies: the backend implements them as machine instructions.
let builtinPath = "(builtin)"

/// A typeclass declaration.
type ClassDef =
    { Name : string
      Params : Var list
      /// each parameter's declared KIND as an arity: 0 = a plain type,
      /// n = a constructor of n arguments (`'f<_>` is 1)
      ParamKinds : int list
      /// members declared DOT-form (`member 'a.Pin : int`) — resolvable on
      /// a receiver in ANY file, so the names ride the shared table
      DotMembers : string list
      /// associated type names, in declaration order
      Assoc : string list
      /// superclass context: what an instance must also satisfy, and the
      /// associated-type equalities it fixes (`when Add<'a,'a> = 'a`)
      Supers : Constraint list
      Members : (string * Scheme) list
      /// where the class was declared, for the orphan rule and diagnostics
      Path : string
      Offset : int }

/// Where an instance member's body ended up. A member with no parameters
/// (`static Zero = 0`) lifts to a unit-taking function rather than a value
/// initializer, so a use site has to apply it — hence the flag.
type InstMember =
    { MPath : string
      MOffset : int
      MName : string
      MTakesUnit : bool
      /// The selected instance's OWN type arguments at this use site, named
      /// the way an instantiation is named everywhere else. Empty when the
      /// instance is not generic.
      ///
      /// Without this a use of `instance Sized<list<'a>> when Sized<'a>`
      /// resolved to one shared body for every element type, and the
      /// `Sized<'a>` its body depends on was whichever instance happened to
      /// resolve first — so `size [1.0]` ran the `int` body. Carrying the
      /// arguments here is what lets monomorphization stamp one copy per
      /// element type, which is the only place the inner constraint can
      /// become concrete.
      MInst : string list }

/// One instance. `Head` may mention variables listed in `Params` — those are
/// the instance's own, freshened per match.
type InstanceDef =
    { Class : string
      Params : Var list
      Head : Type list
      Assoc : (string * Type) list
      Context : Constraint list
      /// member name -> the function it lowered to
      Members : (string * InstMember) list
      /// a primitive instance: it binds the associated types but supplies no
      /// bodies, because the backend emits the operation as a machine
      /// instruction. Only the builtin prelude may declare these.
      Builtin : bool
      Path : string
      Offset : int }

type Tables =
    { Classes : Dict<string, ClassDef>
      Instances : Dict<string, Vec<InstanceDef>>
      /// member name -> the class declaring it. One symbol, one class: this
      /// is what makes `a + b` a single lookup instead of a search. The
      /// uniqueness is ENFORCED at the class declaration (Infer reports a
      /// collision), because a silent overwrite made the earlier class'
      /// member unreachable and the error surfaced as `no instance` on a
      /// class the user never named.
      MemberOwner : Dict<string, string>
      /// type name (decorated) -> every path that declares it, for the
      /// orphan rule: an instance must live with its class or with a type
      /// its head mentions. Filled by Infer's arity sweep, so it is
      /// complete for a file before any of the file's instances register.
      TypePaths : Dict<string, Vec<string>>
      /// when on, every selection over fully concrete arguments appends a
      /// line here — class, arguments, every candidate head, verdict —
      /// for the pick checker (tests/tooling/verify/check-picks.py),
      /// which re-derives the winner independently and diffs
      LogPicks : Dict<string, bool>
      PickLog : Vec<string> }

let newTables () : Tables =
    { Classes = dictNew<string, ClassDef> ()
      Instances = dictNew<string, Vec<InstanceDef>> ()
      MemberOwner = dictNew<string, string> ()
      TypePaths = dictNew<string, Vec<string>> ()
      LogPicks = dictNew<string, bool> ()
      PickLog = vecNew<string> () }

let addTypePath (t : Tables) (name : string) (path : string) : unit =
    match dictTryFind t.TypePaths name with
    | Some v -> if not (vecToList v |> List.exists (fun p -> p = path)) then vecAdd v path
    | None ->
        let v = vecNew<string> ()
        vecAdd v path
        dictSet t.TypePaths name v

let typeDeclaredAt (t : Tables) (name : string) (path : string) : bool =
    match dictTryFind t.TypePaths name with
    | Some v -> vecToList v |> List.exists (fun p -> p = path)
    | None -> false

let addClass (t : Tables) (c : ClassDef) : unit =
    dictSet t.Classes c.Name c
    for m, _ in c.Members do dictSet t.MemberOwner m c.Name

let rec private sameType (a : Type) (b : Type) : bool =
    match prune a, prune b with
    | TVar v, TVar w -> v.Id = w.Id
    | TCon (n1, a1), TCon (n2, a2) ->
        n1 = n2 && a1.Length = a2.Length && List.forall2 sameType a1 a2
    | TFun (p1, r1), TFun (p2, r2) -> sameType p1 p2 && sameType r1 r2
    | TTuple x, TTuple y -> x.Length = y.Length && List.forall2 sameType x y
    | TApp (h1, a1), TApp (h2, a2) ->
        a1.Length = a2.Length && sameType h1 h2 && List.forall2 sameType a1 a2
    | _ -> false

let addInstance (t : Tables) (i : InstanceDef) : unit =
    match dictTryFind t.Instances i.Class with
    | Some v ->
        // the same DECLARATION registered twice (a re-inference, a table
        // reseed) must not become two candidates: selection excludes the
        // chosen instance from its own competition by reference, so a
        // twin of it would read as an equally-specific rival and turn a
        // clean pick into a phantom ambiguity
        // same site AND same head: derived instances share a synthetic
        // site (Unmanaged registers at offset 0), so the site alone would
        // drop legitimate neighbours
        let dup =
            vecToList v
            |> List.exists (fun j ->
                j.Path = i.Path && j.Offset = i.Offset
                && j.Head.Length = i.Head.Length
                && List.forall2 sameType j.Head i.Head)
        if not dup then vecAdd v i
    | None ->
        let v = vecNew<InstanceDef> ()
        vecAdd v i
        dictSet t.Instances i.Class v

let instancesOf (t : Tables) (cls : string) : InstanceDef list =
    match dictTryFind t.Instances cls with
    | Some v -> vecToList v
    | None -> []

/// The class each operator symbol belongs to. One symbol, one class — that
/// invariant is what makes `a + b` a single lookup instead of a search.
/// `=` and `<>` are absent on purpose: structural equality is total and
/// needs no instance.
let operatorClass (op : string) : string option =
    match op with
    | "+" -> Some "Add"
    | "-" -> Some "Sub"
    | "*" -> Some "Mul"
    | "/" -> Some "Div"
    | "%" -> Some "Rem"
    | "<" | ">" | "<=" | ">=" -> Some "Ordered"
    | "**" -> Some "Floating"
    // the backend spells unary minus `u-`, to keep it apart from binary
    | "~-" | "u-" -> Some "Neg"
    | _ -> None

/// The member an operator resolves to. Usually the operator's own name, but
/// comparison goes through the single `compare`, and `**` through `pow` —
/// neither can be spelled as an operator member (`(**)` opens a comment).
let operatorMemberName (op : string) : string =
    match op with
    | "<" | ">" | "<=" | ">=" -> "compare"
    | "**" -> "pow"
    | "~-" | "u-" -> "(~-)"
    | other -> "(" + other + ")"

/// How the backend spells a class operator as a primitive.
let primOperator (op : string) : string = if op = "~-" then "u-" else op

/// The member name a class uses for its operator, given the symbol.
let operatorMember (op : string) : string = "(" + op + ")"

/// The operator symbol a member name spells, if it is one.
let memberOperator (m : string) : string option =
    if m.Length > 2 && m.StartsWith "(" && m.EndsWith ")" then Some (m.Substring (1, m.Length - 2))
    else None

/// A primitive instance has no body, because `a + b` emits a machine
/// instruction. But `Add.(+)` NAMES the member, and a name has to denote
/// something callable — so one wrapper function is generated per primitive
/// instance member. Ordinary operator uses never reach it, and dead-code
/// elimination drops the ones nobody named.
/// `index` is the member's position in its class, so an instance with
/// several members (Ordered has four) gives each wrapper its own identity.
let wrapperMember (i : InstanceDef) (index : int) (memberName : string) : InstMember =
    { MPath = i.Path
      MOffset = 2000000 + i.Offset * 8 + index
      MName = memberName
      MTakesUnit = false
      MInst = [] }

// ---- matching -------------------------------------------------------------


/// One-way matching: a variable of the INSTANCE may bind, a variable of the
/// target may not. That asymmetry is what makes selection sound — an
/// instance applies only when the use site is at least as specific as the
/// head, never by making the use site more specific behind its back.
let rec private matchTy (ps : Set<int>) (sub : Dict<int, Type>) (pat : Type) (tgt : Type) : bool =
    match prune pat, prune tgt with
    | TVar v, t when Set.contains v.Id ps ->
        (match dictTryFind sub v.Id with
         | Some bound -> sameType bound t
         | None -> dictSet sub v.Id t; true)
    | TVar v, TVar w -> v.Id = w.Id
    | TCon (n1, a1), TCon (n2, a2) ->
        n1 = n2 && a1.Length = a2.Length && List.forall2 (matchTy ps sub) a1 a2
    | TFun (p1, r1), TFun (p2, r2) -> matchTy ps sub p1 p2 && matchTy ps sub r1 r2
    | TTuple x, TTuple y -> x.Length = y.Length && List.forall2 (matchTy ps sub) x y
    | TApp (h1, a1), TApp (h2, a2) ->
        a1.Length = a2.Length && matchTy ps sub h1 h2
        && List.forall2 (matchTy ps sub) a1 a2
    | _ -> false

/// Can these two types still turn out equal once variables are known?
/// Fully concrete on both sides means the answer is already decided.
let private couldEqual (a : Type) (b : Type) : bool =
    if List.isEmpty (freeVars a) && List.isEmpty (freeVars b) then sameType a b
    else true

/// Could this instance still apply once the target's variables are known?
/// Unlike `matchTy` a target variable stands for anything. Used only to
/// count candidates: when exactly one survives, the choice is forced and
/// committing to it is improvement, not guessing.
///
/// `sub` remembers what each instance variable was already paired with:
/// without it, a REPEATED variable checked each slot on its own, so
/// `P2<'a,'a>` counted as "still possible" at (int, string) — the winner
/// was never committed, and the use died in the backend as an
/// unresolvable stub.
let rec private compatible (ps : Set<int>) (sub : Dict<int, Type>) (pat : Type) (tgt : Type) : bool =
    match prune pat, prune tgt with
    | TVar v, t when Set.contains v.Id ps ->
        (match dictTryFind sub v.Id with
         | Some bound -> couldEqual bound t
         | None -> dictSet sub v.Id t; true)
    | _, TVar _ -> true
    | TCon (n1, a1), TCon (n2, a2) ->
        n1 = n2 && a1.Length = a2.Length && List.forall2 (compatible ps sub) a1 a2
    | TFun (p1, r1), TFun (p2, r2) -> compatible ps sub p1 p2 && compatible ps sub r1 r2
    | TTuple x, TTuple y -> x.Length = y.Length && List.forall2 (compatible ps sub) x y
    // an UNRESOLVED application stands for whatever its head becomes,
    // exactly as an unresolved variable does two cases up. Without this a
    // constraint like `Shows<'f<int>>` answered NoInstance — terminal —
    // where more information could still pick an instance.
    | _, TApp _ -> true
    | TVar _, _ -> false
    | _ -> false

/// Is `b`'s head, with `b`'s OWN variables free, a match for `a`'s head?
/// That is: is every type `a` accepts also accepted by `b`? `'a[]` matches
/// `V2d[]` this way, and not the other way round — which is exactly what
/// makes `V2d[]` the more specific of the two.
let private headSubsumes (b : InstanceDef) (a : InstanceDef) : bool =
    let ps = b.Params |> List.map (fun v -> v.Id) |> Set.ofList
    let sub = dictNew<int, Type> ()
    b.Head.Length = a.Head.Length && List.forall2 (matchTy ps sub) b.Head a.Head

/// `a` is STRICTLY more specific than `b`: b accepts everything a does, and
/// a does not accept everything b does.
let moreSpecific (a : InstanceDef) (b : InstanceDef) : bool =
    headSubsumes b a && not (headSubsumes a b)

type Selection =
    /// the instance, and the substitution for its own variables
    | Solved of InstanceDef * Dict<int, Type>
    /// exactly one instance could still apply — committing to its head is
    /// forced, so unify with it and retry
    | Improve of InstanceDef
    /// several instances could still apply; ask again when more is known
    | Deferred
    /// several EXACT matches, none more specific than the others. Unlike
    /// Deferred this cannot improve with more information — the overlap
    /// itself is the problem.
    | Ambiguous of InstanceDef list
    | NoInstance

/// Pick the instance for `cls` at `args`. `assoc` are the associated-type
/// bindings the use site already knows; they narrow the candidate set the
/// same way the arguments do — `Add<'a,'b>` whose result is known to be
/// `int` can only be `Add<int,int>`, and that is what keeps `a + b + 1`
/// inferring `int -> int -> int` rather than a context nobody asked for.
/// `eager` commits an OPEN match (see openMatch below) instead of
/// deferring it: a CLASS MEMBER body has no constraint-carrying scheme, so
/// the eager commit is its only resolution — a let body defers and the
/// constraint rides its scheme to the stamp.
let private selectCore (t : Tables) (eager : bool) (cls : string) (args : Type list) (assoc : (string * Type) list) : Selection =
    let cands = instancesOf t cls
    let exact =
        cands |> List.choose (fun i ->
            let ps = i.Params |> List.map (fun v -> v.Id) |> Set.ofList
            let sub = dictNew<int, Type> ()
            if i.Head.Length = args.Length
               && List.forall2 (matchTy ps sub) i.Head args then Some (i, sub)
            else None)
    /// Could a STRICTLY more specific instance than `chosen` still apply once
    /// the target's own variables are known? If so, committing now would
    /// answer a question the use site has not finished asking: inside a body
    /// generic in 'a, `Serialize<'a[]>` matches exactly, yet at 'a = V2d the
    /// specific instance is the right one. Deferring sends the constraint
    /// down the path that resolves after monomorphization, where the element
    /// type is a concrete name and the choice is no longer a guess.
    let overtakable (chosen : InstanceDef) =
        cands |> List.exists (fun j ->
            not (System.Object.ReferenceEquals (j, chosen))
            && moreSpecific j chosen
            && (let ps = j.Params |> List.map (fun v -> v.Id) |> Set.ofList
                (let sub = dictNew<int, Type> ()
                 j.Head.Length = args.Length && List.forall2 (compatible ps sub) j.Head args)))
    // An OPEN match bound an instance variable to a type still containing a
    // variable: the use has not finished asking. Committing here answers for
    // callers this file has never seen — a strictly more specific instance,
    // legal under the orphan rule in a LATER file, was never ranked, and one
    // program answered 100 and 999 for the same class at the same type
    // (tests/known-issues history: cross-module-specificity). An open match
    // defers to the stamp, where the argument is concrete and the table is
    // the whole program's. A GROUND match may commit: the orphan rule plus
    // declare-before-use means every instance that could match a ground
    // type is already visible when it is solved.
    let openMatch (sub : Dict<int, Type>) =
        dictPairs sub |> List.exists (fun (_, ty) -> not (List.isEmpty (freeVars ty)))
    let settle (i : InstanceDef) (sub : Dict<int, Type>) =
        if overtakable i || (not eager && openMatch sub) then Deferred else Solved (i, sub)
    match exact with
    | [ (i, sub) ] -> settle i sub
    // OVERLAPPING instances: the most specific one wins, and it has to be
    // unique. Two that merely differ — `C<int, 'b>` and `C<'a, bool>` at
    // `C<int, bool>` — order neither way, and picking arbitrarily is how a
    // program's meaning starts depending on declaration order.
    | _ :: _ :: _ ->
        let maximal =
            exact |> List.filter (fun (i, _) ->
                not (exact |> List.exists (fun (j, _) ->
                        not (System.Object.ReferenceEquals (i, j)) && moreSpecific j i)))
        (match maximal with
         | [ (i, sub) ] -> settle i sub
         | _ -> Ambiguous (maximal |> List.map fst))
    | [] ->
        let possible =
            cands |> List.filter (fun i ->
                let ps = i.Params |> List.map (fun v -> v.Id) |> Set.ofList
                // ONE memory across the whole instance: its variables mean
                // the same thing in the head and in the associated types
                let sub = dictNew<int, Type> ()
                i.Head.Length = args.Length && List.forall2 (compatible ps sub) i.Head args
                && assoc |> List.forall (fun (n, want) ->
                    match i.Assoc |> List.tryFind (fun (an, _) -> an = n) with
                    | Some (_, has) -> compatible ps sub has want
                    | None -> true))
        match possible with
        | [] -> NoInstance
        | [ i ] -> Improve i
        | _ -> Deferred

/// One line per selection for the pick checker: a term grammar the checker
/// parses back — `name`, `name(a,b)`, `?7` for a variable, `tup(..)`,
/// `fn(a,b)`, `app(h,a)`.
let rec private dumpTy (t : Type) : string =
    match prune t with
    | TCon (n, []) -> n
    | TCon (n, args) -> n + "(" + String.concat "," (List.map dumpTy args) + ")"
    | TVar v -> "?" + string v.Id
    | TTuple ts -> "tup(" + String.concat "," (List.map dumpTy ts) + ")"
    | TFun (a, b) -> "fn(" + dumpTy a + "," + dumpTy b + ")"
    | TApp (h, args) -> "app(" + dumpTy h + "," + String.concat "," (List.map dumpTy args) + ")"

let select (t : Tables) (eager : bool) (cls : string) (args : Type list) (assoc : (string * Type) list) : Selection =
    let result = selectCore t eager cls args assoc
    // record fully concrete selections only: those have one right answer
    // for the checker to re-derive — an open one defers by design
    if (dictTryFind t.LogPicks "on").IsSome && args |> List.forall (fun a -> List.isEmpty (freeVars a)) then
        let cands = instancesOf t cls
        let verdict, chosen =
            match result with
            | Solved (i, _) ->
                "solved", (cands |> List.tryFindIndex (fun j -> System.Object.ReferenceEquals (i, j)))
            | Improve i ->
                "improve", (cands |> List.tryFindIndex (fun j -> System.Object.ReferenceEquals (i, j)))
            | Deferred -> "deferred", None
            | Ambiguous _ -> "ambiguous", None
            | NoInstance -> "none", None
        vecAdd t.PickLog
            (verdict + "|" + cls + "|"
             + String.concat ";" (List.map dumpTy args) + "|"
             + (match chosen with Some i -> string i | None -> "-") + "|"
             + String.concat "|" (cands |> List.map (fun i ->
                 String.concat ";" (List.map dumpTy i.Head))))
    result

/// Substitute an instance's own variables into one of its types.
let substInst (sub : Dict<int, Type>) (t : Type) : Type =
    let rec go (t : Type) : Type =
        match prune t with
        | TVar v -> (match dictTryFind sub v.Id with Some a -> a | None -> TVar v)
        | TCon (n, args) -> TCon (n, List.map go args)
        | TFun (a, b) -> TFun (go a, go b)
        | TTuple ts -> TTuple (List.map go ts)
        | TApp (h, args) -> TApp (go h, List.map go args)
    go t

/// Does the head of two constraints agree (same class, same argument types)?
let sameHead (a : Constraint) (b : Constraint) : bool =
    a.Class = b.Class && a.Args.Length = b.Args.Length && List.forall2 sameType a.Args b.Args

/// Every constraint entailed by this one: itself, its superclasses, and
/// theirs. Used both to discharge a wanted against a declared `when` and to
/// drop from a context anything a superclass already implies.
/// `seen` refuses a cycle in the super chain the same way the member walk's
/// `seenOwners` does — keyed by whole head, not class name, so a diamond
/// that reaches one class at two argument lists still visits both.
let rec private entailedSeen (t : Tables) (seen : Constraint list) (c : Constraint) : Constraint list =
    if seen |> List.exists (fun s -> sameHead s c) then [] else
    match dictTryFind t.Classes c.Class with
    | None -> [ c ]
    | Some cd when cd.Params.Length <> c.Args.Length -> [ c ]
    | Some cd ->
        let sub = dictNew<int, Type> ()
        List.iter2 (fun (p : Var) a -> dictSet sub p.Id a) cd.Params c.Args
        c :: (cd.Supers
              |> List.collect (fun s ->
                  entailedSeen t (c :: seen) (mapConstraint (substInst sub) s)))

let entailed (t : Tables) (c : Constraint) : Constraint list =
    entailedSeen t [] c

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
      MTakesUnit : bool }

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
      /// is what makes `a + b` a single lookup instead of a search.
      MemberOwner : Dict<string, string> }

let newTables () : Tables =
    { Classes = dictNew<string, ClassDef> ()
      Instances = dictNew<string, Vec<InstanceDef>> ()
      MemberOwner = dictNew<string, string> () }

let addClass (t : Tables) (c : ClassDef) : unit =
    dictSet t.Classes c.Name c
    for m, _ in c.Members do dictSet t.MemberOwner m c.Name

let addInstance (t : Tables) (i : InstanceDef) : unit =
    match dictTryFind t.Instances i.Class with
    | Some v -> vecAdd v i
    | None ->
        let v = vecNew<InstanceDef> ()
        vecAdd v i
        dictSet t.Instances i.Class v

let instancesOf (t : Tables) (cls : string) : InstanceDef list =
    match dictTryFind t.Instances cls with
    | Some v -> vecToList v
    | None -> []

/// The operator each arithmetic class carries. One symbol, one class.
let operatorClass (op : string) : string option =
    match op with
    | "+" -> Some "Add"
    | "-" -> Some "Sub"
    | "*" -> Some "Mul"
    | "/" -> Some "Div"
    | "%" -> Some "Rem"
    | _ -> None

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
let wrapperMember (i : InstanceDef) (memberName : string) : InstMember =
    { MPath = i.Path
      MOffset = 2000000 + i.Offset * 8
      MName = memberName
      MTakesUnit = false }

// ---- matching -------------------------------------------------------------

let rec private sameType (a : Type) (b : Type) : bool =
    match prune a, prune b with
    | TVar v, TVar w -> v.Id = w.Id
    | TCon (n1, a1), TCon (n2, a2) ->
        n1 = n2 && a1.Length = a2.Length && List.forall2 sameType a1 a2
    | TFun (p1, r1), TFun (p2, r2) -> sameType p1 p2 && sameType r1 r2
    | TTuple x, TTuple y -> x.Length = y.Length && List.forall2 sameType x y
    | _ -> false

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
    | _ -> false

/// Could this instance still apply once the target's variables are known?
/// Unlike `matchTy` a target variable stands for anything. Used only to
/// count candidates: when exactly one survives, the choice is forced and
/// committing to it is improvement, not guessing.
let rec private compatible (ps : Set<int>) (pat : Type) (tgt : Type) : bool =
    match prune pat, prune tgt with
    | TVar v, _ when Set.contains v.Id ps -> true
    | _, TVar _ -> true
    | TCon (n1, a1), TCon (n2, a2) ->
        n1 = n2 && a1.Length = a2.Length && List.forall2 (compatible ps) a1 a2
    | TFun (p1, r1), TFun (p2, r2) -> compatible ps p1 p2 && compatible ps r1 r2
    | TTuple x, TTuple y -> x.Length = y.Length && List.forall2 (compatible ps) x y
    | TVar _, _ -> false
    | _ -> false

type Selection =
    /// the instance, and the substitution for its own variables
    | Solved of InstanceDef * Dict<int, Type>
    /// exactly one instance could still apply — committing to its head is
    /// forced, so unify with it and retry
    | Improve of InstanceDef
    /// several instances could still apply; ask again when more is known
    | Deferred
    | NoInstance

/// Pick the instance for `cls` at `args`. `assoc` are the associated-type
/// bindings the use site already knows; they narrow the candidate set the
/// same way the arguments do — `Add<'a,'b>` whose result is known to be
/// `int` can only be `Add<int,int>`, and that is what keeps `a + b + 1`
/// inferring `int -> int -> int` rather than a context nobody asked for.
let select (t : Tables) (cls : string) (args : Type list) (assoc : (string * Type) list) : Selection =
    let cands = instancesOf t cls
    let exact =
        cands |> List.choose (fun i ->
            let ps = i.Params |> List.map (fun v -> v.Id) |> Set.ofList
            let sub = dictNew<int, Type> ()
            if i.Head.Length = args.Length
               && List.forall2 (matchTy ps sub) i.Head args then Some (i, sub)
            else None)
    match exact with
    | [ (i, sub) ] -> Solved (i, sub)
    // coherence makes two exact matches impossible; if it is ever violated,
    // refusing to choose beats choosing arbitrarily
    | _ :: _ :: _ -> Deferred
    | [] ->
        let possible =
            cands |> List.filter (fun i ->
                let ps = i.Params |> List.map (fun v -> v.Id) |> Set.ofList
                i.Head.Length = args.Length && List.forall2 (compatible ps) i.Head args
                && assoc |> List.forall (fun (n, want) ->
                    match i.Assoc |> List.tryFind (fun (an, _) -> an = n) with
                    | Some (_, has) -> compatible ps has want
                    | None -> true))
        match possible with
        | [] -> NoInstance
        | [ i ] -> Improve i
        | _ -> Deferred

/// Substitute an instance's own variables into one of its types.
let substInst (sub : Dict<int, Type>) (t : Type) : Type =
    let rec go (t : Type) : Type =
        match prune t with
        | TVar v -> (match dictTryFind sub v.Id with Some a -> a | None -> TVar v)
        | TCon (n, args) -> TCon (n, List.map go args)
        | TFun (a, b) -> TFun (go a, go b)
        | TTuple ts -> TTuple (List.map go ts)
    go t

/// Every constraint entailed by this one: itself, its superclasses, and
/// theirs. Used both to discharge a wanted against a declared `when` and to
/// drop from a context anything a superclass already implies.
let rec entailed (t : Tables) (c : Constraint) : Constraint list =
    match dictTryFind t.Classes c.Class with
    | None -> [ c ]
    | Some cd when cd.Params.Length <> c.Args.Length -> [ c ]
    | Some cd ->
        let sub = dictNew<int, Type> ()
        List.iter2 (fun (p : Var) a -> dictSet sub p.Id a) cd.Params c.Args
        c :: (cd.Supers
              |> List.collect (fun s ->
                  entailed t (mapConstraint (substInst sub) s)))

/// Does the head of two constraints agree (same class, same argument types)?
let sameHead (a : Constraint) (b : Constraint) : bool =
    a.Class = b.Class && a.Args.Length = b.Args.Length && List.forall2 sameType a.Args b.Args

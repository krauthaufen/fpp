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
let select (t : Tables) (cls : string) (args : Type list) (assoc : (string * Type) list) : Selection =
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
                j.Head.Length = args.Length && List.forall2 (compatible ps) j.Head args))
    let settle (i : InstanceDef) (sub : Dict<int, Type>) =
        if overtakable i then Deferred else Solved (i, sub)
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
        | TApp (h, args) -> TApp (go h, List.map go args)
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

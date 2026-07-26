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
      mutable Link : Type option }

and Type =
    | TVar of Var
    | TCon of string * Type list
    | TFun of Type * Type
    | TTuple of Type list

type Scheme =
    { Quantified : Var list
      Body : Type }

let mono (t : Type) : Scheme = { Quantified = []; Body = t }

let tInt = TCon ("int", [])
let tUInt = TCon ("uint32", [])

let tFloat = TCon ("float", [])
let tString = TCon ("string", [])
let tChar = TCon ("char", [])
let tBool = TCon ("bool", [])
let tUnit = TCon ("unit", [])
let tList (t : Type) = TCon ("list", [ t ])

/// Follow links to the representative.
let rec prune (t : Type) : Type =
    match t with
    | TVar v ->
        match v.Link with
        | Some inner ->
            let r = prune inner
            v.Link <- Some r
            r
        | None -> t
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
    | _ -> ""

let rec freeVars (t : Type) : Var list =
    match prune t with
    | TVar v -> [ v ]
    | TCon (_, args) -> List.collect freeVars args
    | TFun (a, b) -> freeVars a @ freeVars b
    | TTuple ts -> List.collect freeVars ts

let rec private occurs (v : Var) (t : Type) : bool =
    match prune t with
    | TVar w -> System.Object.ReferenceEquals (v, w)
    | TCon (_, args) -> List.exists (occurs v) args
    | TFun (a, b) -> occurs v a || occurs v b
    | TTuple ts -> List.exists (occurs v) ts

/// Clamp levels of all vars in t to at most `level` (link-time invariant
/// that keeps generalization sound).
let rec private adjustLevels (level : int) (t : Type) : unit =
    match prune t with
    | TVar w -> if w.Level > level then w.Level <- level
    | TCon (_, args) -> List.iter (adjustLevels level) args
    | TFun (a, b) -> adjustLevels level a; adjustLevels level b
    | TTuple ts -> List.iter (adjustLevels level) ts

/// Pretty-print with 'a, 'b, ... assigned per call in order of appearance.
let typeString (t : Type) : string =
    let names = dictNew<int, string> ()
    let nameOf (v : Var) : string =
        match dictTryFind names v.Id with
        | Some n -> n
        | None ->
            let n = "'" + string (char (int 'a' + names.Count))
            dictSet names v.Id n
            n
    let rec go (atom : bool) (t : Type) : string =
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
    go false t

/// Structural unification. Returns an error message on mismatch, None on
/// success. Partial effects on failure are acceptable — the tree is only
/// used for diagnostics and hover after errors.
let rec unify (t1 : Type) (t2 : Type) : string option =
    let a = prune t1
    let b = prune t2
    match a, b with
    | TVar v, TVar w when System.Object.ReferenceEquals (v, w) -> None
    | TVar v, other | other, TVar v ->
        if occurs v other then
            Some ("the type " + typeString other + " would contain itself")
        else
            adjustLevels v.Level other
            v.Link <- Some other
            None
    | TCon (n1, a1), TCon (n2, a2) ->
        if n1 <> n2 || List.length a1 <> List.length a2 then
            Some ("type mismatch: " + typeString a + " vs " + typeString b)
        else
            List.zip a1 a2 |> List.tryPick (fun (x, y) -> unify x y)
    | TFun (p1, r1), TFun (p2, r2) ->
        match unify p1 p2 with
        | Some e -> Some e
        | None -> unify r1 r2
    | TTuple x, TTuple y ->
        if List.length x <> List.length y then
            Some ("type mismatch: " + typeString a + " vs " + typeString b)
        else
            List.zip x y |> List.tryPick (fun (p, q) -> unify p q)
    | _ ->
        Some ("type mismatch: " + typeString a + " vs " + typeString b)

/// Variable supply and level tracking for one inference run.
type TypeState() =
    let mutable nextId = 0
    let mutable level = 0

    member _.Level = level
    member _.EnterLevel () = level <- level + 1
    member _.ExitLevel () = level <- level - 1

    member _.Fresh () : Type =
        nextId <- nextId + 1
        TVar { Id = nextId; Level = level; Link = None }

    /// Quantify variables deeper than the current level.
    member _.Generalize (t : Type) : Scheme =
        let qs =
            freeVars t
            |> List.filter (fun v -> v.Level > level)
            |> List.distinctBy (fun v -> v.Id)
        { Quantified = qs; Body = t }

    member this.Instantiate (s : Scheme) : Type =
        if List.isEmpty s.Quantified then s.Body
        else
            let subst = dictNew<int, Type> ()
            for v in s.Quantified do dictSet subst v.Id (this.Fresh ())
            let rec go (t : Type) : Type =
                match prune t with
                | TVar v ->
                    (match dictTryFind subst v.Id with
                     | Some fresh -> fresh
                     | None -> TVar v)
                | TCon (n, args) -> TCon (n, List.map go args)
                | TFun (a, b) -> TFun (go a, go b)
                | TTuple ts -> TTuple (List.map go ts)
            go s.Body

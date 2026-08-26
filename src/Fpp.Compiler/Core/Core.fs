module Fpp.Core.Ir

open Fpp.Analysis.Types

// The typed core: a small, explicit IR in the spirit of GHC Core. Every
// binder carries its inferred scheme; constructors carry theirs. Surface
// sugar (pipelines, blocks, offside) is gone. Emission consumes this and
// nothing else; the linter re-typechecks it after every pass.

type VarId =
    { Path : string
      Offset : int
      Name : string }

type Lit =
    | LInt of string
    | LFloat of string
    | LString of string
    | LChar of string
    | LBool of bool
    /// the null reference — distinct from unit, which is a real value
    | LNull
    | LUnit

type Pat =
    | PWild
    | PLit of Lit
    | PVar of VarId * Scheme
    | PCtor of string * Scheme * Pat list
    | PTuple of Pat list
    | PCons of Pat * Pat
    | PListLit of Pat list
    /// `[| p; q |]` — the element KIND rides along, the way EIndex carries it
    | PArrLit of string * Pat list
    /// `p1 & p2` — both must match, and both sets of binders are in scope
    | PAnd of Pat * Pat
    /// `:? T` — matches when the value is a T (or a subclass)
    | PTypeTest of string
    | PAs of Pat * VarId * Scheme
    | POr of Pat list

type Expr =
    | ELit of Lit
    /// variable use; the string list is the concrete instantiation of the
    /// binding's quantified vars ([] = monomorphic, "" entry = not concrete)
    | EVarI of VarId * Scheme * string list
    | EVar of VarId * Scheme
    /// A name the project does not define (BCL etc.) — the emitter maps
    /// known intrinsics and rejects the rest.
    | EUnknown of string
    | ELam of (VarId * Scheme) list * Expr
    | EApp of Expr * Expr list
    | ELet of bool * VarId * Scheme * Expr * Expr
    | EIf of Expr * Expr * Expr
    | EMatch of Expr * (Pat * Expr option * Expr) list
    | ETuple of Expr list
    | EListLit of Expr list
    | ECtor of string * Scheme * Expr list
    | ERecord of string * (string * Expr) list
    /// build a derived instance: the base part is copied out of a freshly
    /// constructed base instance, then this class' own fields are appended
    | ERecordExt of string * Expr * (string * Expr) list
    /// receiver, field name, owning type ("" when the owner is unknown)
    | EField of Expr * string * string
    | EFieldSet of Expr * string * string * Expr
    | EPrim of string * Expr list
    | ESeq of Expr list
    | EWhile of Expr * Expr
    | EAssign of VarId * Expr
    | ETry of Expr * (Pat * Expr option * Expr) list
    | EArray of string * Expr list
    | EIndex of string * Expr * Expr
    | EIndexSet of string * Expr * Expr * Expr
    | EArrayLen of string * Expr
    | EArrayCreate of string * Expr * Expr
    | EArrayPin of string * Expr
    | EArrayUnpin of string * Expr
    /// how many BYTES a pinned POD array occupies — the blit length, without
    /// anyone outside the compiler having to know the element's layout
    | EArrayBytes of string * Expr
    /// interface name, method name, receiver, arguments — dispatched
    /// through the receiver's vtable, not bound to any one implementation
    | EIfaceCall of string * string * Expr * Expr list
    /// target type, operand, isDowncast (`:?>` checks the class id at
    /// runtime; `:>` is a static widening and checks nothing)
    | ECast of string * Expr * bool
    /// `e :? T` — is the value an instance of T (or a subclass)?
    | ETypeTest of string * Expr

/// Every direct sub-expression, in evaluation order where that is defined.
/// A generic walk over the tree without one more copy of this match at each
/// call site; a PATTERN's own sub-expressions are not expressions, so a
/// match clause contributes its guard and its body.
let children (e : Expr) : Expr list =
    match e with
    | ELit _ | EVar _ | EVarI _ | EUnknown _ -> []
    | ELam (_, b) -> [ b ]
    | EApp (f, xs) -> f :: xs
    | ELet (_, _, _, a, b) -> [ a; b ]
    | EIf (a, b, c) -> [ a; b; c ]
    | EMatch (s, cs) -> s :: (cs |> List.collect (fun (_, g, b) -> (match g with Some x -> [ x ] | None -> []) @ [ b ]))
    | ETuple xs | EListLit xs -> xs
    | ECtor (_, _, xs) -> xs
    | ERecord (_, fs) -> fs |> List.map snd
    | ERecordExt (_, b, fs) -> b :: (fs |> List.map snd)
    | EField (r, _, _) -> [ r ]
    | EFieldSet (r, _, _, v) -> [ r; v ]
    | EPrim (_, xs) -> xs
    | ESeq xs -> xs
    | EWhile (a, b) -> [ a; b ]
    | EAssign (_, v) -> [ v ]
    | ETry (b, cs) -> b :: (cs |> List.collect (fun (_, g, h) -> (match g with Some x -> [ x ] | None -> []) @ [ h ]))
    | EArray (_, xs) -> xs
    | EIndex (_, a, i) -> [ a; i ]
    | EIndexSet (_, a, i, v) -> [ a; i; v ]
    | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) -> [ a ]
    | EArrayCreate (_, a, b) -> [ a; b ]
    | EIfaceCall (_, _, r, xs) -> r :: xs
    | ECast (_, a, _) -> [ a ]
    | ETypeTest (_, a) -> [ a ]

/// Rebuild a node with each direct sub-expression mapped. The companion to
/// `children`: a rewrite that only cares about a few shapes still has to put
/// everything else back together.
let mapChildren (f : Expr -> Expr) (e : Expr) : Expr =
    match e with
    | ELit _ | EVar _ | EVarI _ | EUnknown _ -> e
    | ELam (ps, b) -> ELam (ps, f b)
    | EApp (g, xs) -> EApp (f g, List.map f xs)
    | ELet (r, v, s, a, b) -> ELet (r, v, s, f a, f b)
    | EIf (a, b, c) -> EIf (f a, f b, f c)
    | EMatch (s, cs) -> EMatch (f s, cs |> List.map (fun (p, g, b) -> p, Option.map f g, f b))
    | ETuple xs -> ETuple (List.map f xs)
    | EListLit xs -> EListLit (List.map f xs)
    | ECtor (n, s, xs) -> ECtor (n, s, List.map f xs)
    | ERecord (n, fs) -> ERecord (n, fs |> List.map (fun (k, v) -> k, f v))
    | ERecordExt (n, b, fs) -> ERecordExt (n, f b, fs |> List.map (fun (k, v) -> k, f v))
    | EField (r, n, o) -> EField (f r, n, o)
    | EFieldSet (r, n, o, v) -> EFieldSet (f r, n, o, f v)
    | EPrim (op, xs) -> EPrim (op, List.map f xs)
    | ESeq xs -> ESeq (List.map f xs)
    | EWhile (a, b) -> EWhile (f a, f b)
    | EAssign (v, x) -> EAssign (v, f x)
    | ETry (b, cs) -> ETry (f b, cs |> List.map (fun (p, g, h) -> p, Option.map f g, f h))
    | EArray (k, xs) -> EArray (k, List.map f xs)
    | EIndex (k, a, i) -> EIndex (k, f a, f i)
    | EIndexSet (k, a, i, v) -> EIndexSet (k, f a, f i, f v)
    | EArrayLen (k, a) -> EArrayLen (k, f a)
    | EArrayPin (k, a) -> EArrayPin (k, f a)
    | EArrayUnpin (k, a) -> EArrayUnpin (k, f a)
    | EArrayBytes (k, a) -> EArrayBytes (k, f a)
    | EArrayCreate (k, a, b) -> EArrayCreate (k, f a, f b)
    | EIfaceCall (i, m, r, xs) -> EIfaceCall (i, m, f r, List.map f xs)
    | ECast (t, a, d) -> ECast (t, f a, d)
    | ETypeTest (t, a) -> ETypeTest (t, f a)

type Decl =
    | DLet of bool * VarId * Scheme * Expr
    /// foreign import: name resolves in the host's "env" module
    | DExtern of VarId * Scheme
    /// `[<Export>] let f (x : int) : int` — a function the HOST calls. The
    /// name is what the wasm export is called.
    | DExport of VarId * string
    | DUnion of string * string list * (string * int) list
    /// the DECLARED payload types of each case, flattened through a tuple
    /// payload: `(unionName, [ caseName, [ typeName … ] ])`. Carried beside
    /// DUnion rather than inside it so an older IR still reads (a union with
    /// no entry simply keeps uniform-word payload slots).
    | DUnionFields of string * (string * string list) list
    /// name, type params, fields as (name, kind "f|s|l|i|r"), isStruct
    | DRecord of string * string list * (string * string) list * bool
    /// enum name and its cases as (case, integer value). An enum value IS
    /// its integer; the cases are constants, not constructors.
    | DEnum of string * (string * int) list
    /// interface name, its methods as (name, arity)
    | DInterface of string * (string * int) list
    /// class name, base class, its own members as (name, function), and
    /// per implemented interface the functions implementing its methods
    | DClass of string * string option * (string * VarId) list * (string * (string * VarId) list) list
    /// the INSTANTIATION a class hands its base (`inherit B<aval<bool>>` on
    /// C<'A> records B at [IAdaptiveValue`1$<bool>]) — symbolic in the
    /// class' own variables, substituted when a construction is stamped
    | DBaseInst of string * string list
    /// type name and its own members as (name, function). Emitted for ANY
    /// type that declares members — records and DUs included — so an
    /// override can be found without the type being a class.
    | DMembers of string * (string * VarId) list

type LowerResult =
    { Decls : Decl list
      /// (offset, reason) — constructs outside the v1 emission subset
      Notes : (int * string) list }

/// Compact printer for debugging and snapshot tests.
let rec printExpr (e : Expr) : string =
    let pv (v : VarId, _ : Scheme) = v.Name
    match e with
    | ELit (LInt s) -> s
    | ELit (LFloat s) -> s
    | ELit (LString s) -> s
    | ELit (LChar s) -> s
    | ELit (LBool b) -> if b then "true" else "false"
    | ELit LNull -> "null"
    | ELit LUnit -> "()"
    | EVarI (v, _, inst) -> v.Name + "<" + String.concat "," inst + ">"
    | EVar (v, _) -> v.Name
    | EUnknown n -> "?" + n
    | ELam (ps, b) -> "(λ" + String.concat " " (List.map pv ps) + ". " + printExpr b + ")"
    | EApp (f, args) -> "(" + String.concat " " (List.map printExpr (f :: args)) + ")"
    | ELet (r, v, _, rhs, body) ->
        "(let" + (if r then " rec " else " ") + v.Name + " = " + printExpr rhs + " in " + printExpr body + ")"
    | EIf (c, t, f) -> "(if " + printExpr c + " then " + printExpr t + " else " + printExpr f + ")"
    | EMatch (s, cases) ->
        let pc (p, _, b) = printPat p + " -> " + printExpr b
        "(match " + printExpr s + " with " + String.concat " | " (List.map pc cases) + ")"
    | ETuple xs -> "(" + String.concat ", " (List.map printExpr xs) + ")"
    | EListLit xs -> "[" + String.concat "; " (List.map printExpr xs) + "]"
    | ECtor (n, _, args) ->
        if List.isEmpty args then n else "(" + n + " " + String.concat " " (List.map printExpr args) + ")"
    | ERecordExt (n, b, fs) ->
        "{" + n + "| base " + printExpr b + "; " + String.concat "; " (fs |> List.map (fun (f, v) -> f + " = " + printExpr v)) + "}"
    | ERecord (n, fs) ->
        "{" + n + "| " + String.concat "; " (fs |> List.map (fun (f, v) -> f + " = " + printExpr v)) + "}"
    | EField (r, f, _) -> printExpr r + "." + f
    | EFieldSet (r, f, _, v) -> printExpr r + "." + f + " <- " + printExpr v
    | EPrim (op, args) -> "(" + op + " " + String.concat " " (List.map printExpr args) + ")"
    | ESeq xs -> "(seq " + String.concat "; " (List.map printExpr xs) + ")"
    | EWhile (c, b) -> "(while " + printExpr c + " do " + printExpr b + ")"
    | ETry (b, cs) ->
        "(try " + printExpr b + " with " + String.concat " | " (cs |> List.map (fun (p, _, e) -> printPat p + " -> " + printExpr e)) + ")"
    | EArray (_, xs) -> "[|" + String.concat "; " (List.map printExpr xs) + "|]"
    | EIndex (_, a, i) -> printExpr a + ".[" + printExpr i + "]"
    | EIndexSet (_, a, i, v) -> printExpr a + ".[" + printExpr i + "] <- " + printExpr v
    | EArrayLen (_, a) -> printExpr a + ".Length"
    | EArrayCreate (_, n, v) -> "(Array.create " + printExpr n + " " + printExpr v + ")"
    | EArrayPin (_, a) -> "(Array.pin " + printExpr a + ")"
    | EArrayUnpin (_, a) -> "(Array.unpin " + printExpr a + ")"
    | EArrayBytes (_, a) -> "(Array.byteSize " + printExpr a + ")"
    | EAssign (v, e) -> "(" + v.Name + " <- " + printExpr e + ")"
    | EIfaceCall (i, m, r, args) ->
        "(" + i + "::" + m + " " + String.concat " " (List.map printExpr (r :: args)) + ")"
    | ECast (t, e, down) -> "(" + printExpr e + (if down then " :?> " else " :> ") + t + ")"
    | ETypeTest (t, e) -> "(" + printExpr e + " :? " + t + ")"

and printPat (p : Pat) : string =
    match p with
    | PWild -> "_"
    | PLit l -> printExpr (ELit l)
    | PVar (v, _) -> v.Name
    | PCtor (n, _, args) ->
        if List.isEmpty args then n else "(" + n + " " + String.concat " " (List.map printPat args) + ")"
    | PTuple ps -> "(" + String.concat ", " (List.map printPat ps) + ")"
    | PCons (h, t) -> "(" + printPat h + " :: " + printPat t + ")"
    | PListLit ps -> "[" + String.concat "; " (List.map printPat ps) + "]"
    | PArrLit (_, ps) -> "[|" + String.concat "; " (List.map printPat ps) + "|]"
    | PAnd (a, b) -> printPat a + " & " + printPat b
    | PTypeTest t -> ":? " + t
    | PAs (p, v, _) -> "(" + printPat p + " as " + v.Name + ")"
    | POr ps -> "(" + String.concat " | " (List.map printPat ps) + ")"

/// Every or-free pattern a pattern stands for. An alternative may sit at any
/// depth — `(A n | B n), [x]` is one tuple case, not two top-level ones — so
/// the expansion is the product over the positions, not a peel of the head.
/// Lowering has already aligned the alternatives' binders onto one identity
/// per name, which is what makes the copies interchangeable.
let rec expandOr (p : Pat) : Pat list =
    match p with
    | POr ps -> List.collect expandOr ps
    | PCtor (n, sch, ps) -> orProduct ps |> List.map (fun qs -> PCtor (n, sch, qs))
    | PTuple ps -> orProduct ps |> List.map PTuple
    | PListLit ps -> orProduct ps |> List.map PListLit
    | PArrLit (k, ps) -> orProduct ps |> List.map (fun qs -> PArrLit (k, qs))
    | PAnd (a, b) -> orProduct [ a; b ] |> List.map (fun qs -> match qs with [ x; y ] -> PAnd (x, y) | _ -> PAnd (a, b))
    | PCons (h, t) -> orProduct [ h; t ] |> List.map (fun qs -> PCons (List.head qs, List.item 1 qs))
    | PAs (inner, v, sch) -> expandOr inner |> List.map (fun q -> PAs (q, v, sch))
    | PWild | PLit _ | PVar _ | PTypeTest _ -> [ p ]

and private orProduct (ps : Pat list) : Pat list list =
    match ps with
    | [] -> [ [] ]
    | h :: t ->
        let rest = orProduct t
        expandOr h |> List.collect (fun a -> rest |> List.map (fun r -> a :: r))

let printDecl (d : Decl) : string =
    match d with
    | DExtern (v, _) -> "extern " + v.Name
    | DExport (v, n) -> "export " + v.Name + " as " + n
    | DLet (r, v, _, e) -> "let" + (if r then " rec " else " ") + v.Name + " = " + printExpr e
    | DUnion (n, ps, cases) ->
        "union " + n + (if List.isEmpty ps then "" else "<" + String.concat "," ps + ">")
        + " = " + String.concat " | " (cases |> List.map (fun (c, a) -> c + "/" + string a))
    | DUnionFields (n, cs) ->
        "unionfields " + n + " = "
        + String.concat " | " (cs |> List.map (fun (c, tys) -> c + ":" + String.concat "*" tys))
    | DEnum (n, cs) ->
        "enum " + n + " = " + String.concat " | " (cs |> List.map (fun (c, v) -> c + "=" + string v))
    | DInterface (n, ms) ->
        "interface " + n + " = {" + String.concat "; " (ms |> List.map (fun (m, a) -> m + "/" + string a)) + "}"
    | DMembers (n, own) ->
        "members " + n + " {" + String.concat "; " (own |> List.map fst) + "}"
    | DBaseInst (n, inst) ->
        "baseinst " + n + " <" + String.concat ", " inst + ">"
    | DClass (n, bse, own, impls) ->
        "class " + n
        + (match bse with Some b -> " inherit " + b | None -> "")
        + " members {" + String.concat "; " (own |> List.map fst) + "}"
        + (if List.isEmpty impls then "" else " : " + String.concat ", " (impls |> List.map fst))
    | DRecord (n, ps, fs, st) ->
        (if st then "struct " else "record ") + n
        + (if List.isEmpty ps then "" else "<" + String.concat "," ps + ">")
        + " = {" + String.concat "; " (fs |> List.map (fun (f, k) -> f + ":" + k)) + "}"

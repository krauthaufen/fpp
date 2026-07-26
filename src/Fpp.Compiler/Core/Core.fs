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
    /// interface name, method name, receiver, arguments — dispatched
    /// through the receiver's vtable, not bound to any one implementation
    | EIfaceCall of string * string * Expr * Expr list
    /// target type, operand, isDowncast (`:?>` checks the class id at
    /// runtime; `:>` is a static widening and checks nothing)
    | ECast of string * Expr * bool
    /// `e :? T` — is the value an instance of T (or a subclass)?
    | ETypeTest of string * Expr

type Decl =
    | DLet of bool * VarId * Scheme * Expr
    /// foreign import: name resolves in the host's "env" module
    | DExtern of VarId * Scheme
    | DUnion of string * string list * (string * int) list
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
    | PTypeTest t -> ":? " + t
    | PAs (p, v, _) -> "(" + printPat p + " as " + v.Name + ")"
    | POr ps -> "(" + String.concat " | " (List.map printPat ps) + ")"

let printDecl (d : Decl) : string =
    match d with
    | DExtern (v, _) -> "extern " + v.Name
    | DLet (r, v, _, e) -> "let" + (if r then " rec " else " ") + v.Name + " = " + printExpr e
    | DUnion (n, ps, cases) ->
        "union " + n + (if List.isEmpty ps then "" else "<" + String.concat "," ps + ">")
        + " = " + String.concat " | " (cases |> List.map (fun (c, a) -> c + "/" + string a))
    | DEnum (n, cs) ->
        "enum " + n + " = " + String.concat " | " (cs |> List.map (fun (c, v) -> c + "=" + string v))
    | DInterface (n, ms) ->
        "interface " + n + " = {" + String.concat "; " (ms |> List.map (fun (m, a) -> m + "/" + string a)) + "}"
    | DMembers (n, own) ->
        "members " + n + " {" + String.concat "; " (own |> List.map fst) + "}"
    | DClass (n, bse, own, impls) ->
        "class " + n
        + (match bse with Some b -> " inherit " + b | None -> "")
        + " members {" + String.concat "; " (own |> List.map fst) + "}"
        + (if List.isEmpty impls then "" else " : " + String.concat ", " (impls |> List.map fst))
    | DRecord (n, ps, fs, st) ->
        (if st then "struct " else "record ") + n
        + (if List.isEmpty ps then "" else "<" + String.concat "," ps + ">")
        + " = {" + String.concat "; " (fs |> List.map (fun (f, k) -> f + ":" + k)) + "}"

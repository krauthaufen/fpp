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
    | LUnit

type Pat =
    | PWild
    | PLit of Lit
    | PVar of VarId * Scheme
    | PCtor of string * Scheme * Pat list
    | PTuple of Pat list
    | PCons of Pat * Pat
    | PListLit of Pat list
    | PAs of Pat * VarId * Scheme
    | POr of Pat list

type Expr =
    | ELit of Lit
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
    | EField of Expr * string
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

type Decl =
    | DLet of bool * VarId * Scheme * Expr
    /// foreign import: name resolves in the host's "env" module
    | DExtern of VarId * Scheme
    | DUnion of string * string list * (string * int) list
    /// name, type params, fields as (name, kind "f|s|l|i|r"), isStruct
    | DRecord of string * string list * (string * string) list * bool

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
    | ELit LUnit -> "()"
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
    | ERecord (n, fs) ->
        "{" + n + "| " + String.concat "; " (fs |> List.map (fun (f, v) -> f + " = " + printExpr v)) + "}"
    | EField (r, f) -> printExpr r + "." + f
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
    | PAs (p, v, _) -> "(" + printPat p + " as " + v.Name + ")"
    | POr ps -> "(" + String.concat " | " (List.map printPat ps) + ")"

let printDecl (d : Decl) : string =
    match d with
    | DExtern (v, _) -> "extern " + v.Name
    | DLet (r, v, _, e) -> "let" + (if r then " rec " else " ") + v.Name + " = " + printExpr e
    | DUnion (n, ps, cases) ->
        "union " + n + (if List.isEmpty ps then "" else "<" + String.concat "," ps + ">")
        + " = " + String.concat " | " (cases |> List.map (fun (c, a) -> c + "/" + string a))
    | DRecord (n, ps, fs, st) ->
        (if st then "struct " else "record ") + n
        + (if List.isEmpty ps then "" else "<" + String.concat "," ps + ">")
        + " = {" + String.concat "; " (fs |> List.map (fun (f, k) -> f + ":" + k)) + "}"

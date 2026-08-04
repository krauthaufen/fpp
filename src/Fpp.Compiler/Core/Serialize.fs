module Fpp.Core.Serialize

open Fpp.Prelude
open Fpp.Analysis
open Fpp.Analysis.Types
open Fpp.Core.Ir

// The fat-IR library format (.fppir): s-expressions carrying a library's
// resolver exports, inference schemes and lowered core declarations. This is
// the Rust-rlib idea: the generic's IR is the template; the link step
// instantiates and dedups (tier 1 arrives on top of this format).

// ---- s-expressions --------------------------------------------------------

type Sx =
    | A of string          // atom
    | S of string          // string literal
    | L of Sx list

// chunks, joined once: appending to a string would be quadratic, and a
// builder is not part of the seam
let rec private wr (sb : Vec<string>) (x : Sx) =
    match x with
    | A a -> vecAdd sb a
    | S s ->
        vecAdd sb "\""
        for c in s do
            if c = '"' || c = '\\' then vecAdd sb ("\\" + string c)
            elif c = '\n' then vecAdd sb "\\n"
            else vecAdd sb (string c)
        vecAdd sb "\""
    | L xs ->
        vecAdd sb "("
        xs |> List.iteri (fun i x ->
            if i > 0 then vecAdd sb " "
            wr sb x)
        vecAdd sb ")"

let toText (x : Sx) : string =
    let sb = vecNew<string> ()
    wr sb x
    String.concat "" (vecToList sb)

let parse (text : string) : Sx =
    let n = strLen text
    let mutable i = 0
    let rec node () : Sx =
        while i < n && (charAt text i = ' ' || charAt text i = '\n' || charAt text i = '\r' || charAt text i = '\t') do i <- i + 1
        if i >= n then A ""
        elif charAt text i = '(' then
            i <- i + 1
            let items = vecNew<Sx> ()
            let mutable go = true
            while go do
                while i < n && (charAt text i = ' ' || charAt text i = '\n' || charAt text i = '\r' || charAt text i = '\t') do i <- i + 1
                if i >= n || charAt text i = ')' then
                    i <- i + 1
                    go <- false
                else vecAdd items (node ())
            L (vecToList items)
        elif charAt text i = '"' then
            i <- i + 1
            let sb = vecNew<string> ()
            while i < n && charAt text i <> '"' do
                if charAt text i = '\\' && i + 1 < n then
                    (match charAt text (i + 1) with
                     | 'n' -> vecAdd sb "\n"
                     | c -> vecAdd sb (string c))
                    i <- i + 2
                else
                    vecAdd sb (string (charAt text i))
                    i <- i + 1
            i <- i + 1
            S (String.concat "" (vecToList sb))
        else
            let start = i
            while i < n && charAt text i <> ' ' && charAt text i <> ')' && charAt text i <> '(' && charAt text i <> '\n' && charAt text i <> '\r' && charAt text i <> '\t' do i <- i + 1
            A (substr text start (i - start))
    node ()

// ---- encoding -------------------------------------------------------------

let rec private encTy (t : Type) : Sx =
    match prune t with
    | TVar v -> L [ A "v"; A (string v.Id) ]
    | TCon (n, args) -> L (A "c" :: S n :: List.map encTy args)
    | TFun (a, b) -> L [ A "f"; encTy a; encTy b ]
    | TTuple ts -> L (A "t" :: List.map encTy ts)

let private encConstraint (c : Constraint) : Sx =
    L [ A "k"; S c.Class; L (List.map encTy c.Args)
        L (c.Assoc |> List.map (fun (n, t) -> L [ S n; encTy t ])) ]

let private encScheme (s : Scheme) : Sx =
    L [ A "s"; L (s.Quantified |> List.map (fun v -> A (string v.Id))); encTy s.Body
        L (List.map encConstraint s.Constraints) ]

let private encVarId (v : VarId) : Sx = L [ S v.Path; A (string v.Offset); S v.Name ]

let private encLit (l : Lit) : Sx =
    match l with
    | LInt s -> L [ A "li"; S s ]
    | LFloat s -> L [ A "lf"; S s ]
    | LString s -> L [ A "ls"; S s ]
    | LChar s -> L [ A "lc"; S s ]
    | LBool b -> L [ A "lb"; A (if b then "1" else "0") ]
    | LUnit -> L [ A "lu" ]
    | LNull -> L [ A "ln" ]

let rec private encPat (p : Pat) : Sx =
    match p with
    | PWild -> L [ A "pw" ]
    | PLit l -> L [ A "pl"; encLit l ]
    | PVar (v, s) -> L [ A "pv"; encVarId v; encScheme s ]
    | PCtor (n, s, ps) -> L (A "pc" :: S n :: encScheme s :: List.map encPat ps)
    | PTuple ps -> L (A "pt" :: List.map encPat ps)
    | PTypeTest t -> L [ A "ptt"; S t ]
    | PCons (a, b) -> L [ A "pn"; encPat a; encPat b ]
    | PListLit ps -> L (A "pk" :: List.map encPat ps)
    | PAs (p, v, s) -> L [ A "pa"; encPat p; encVarId v; encScheme s ]
    | POr ps -> L (A "po" :: List.map encPat ps)

let rec private encExpr (e : Expr) : Sx =
    match e with
    | ELit l -> L [ A "el"; encLit l ]
    | EVarI (v, s, inst) -> L (A "eV" :: encVarId v :: encScheme s :: List.map S inst)
    | EVar (v, s) -> L [ A "ev"; encVarId v; encScheme s ]
    | EUnknown n -> L [ A "eu"; S n ]
    | ELam (ps, b) -> L [ A "em"; L (ps |> List.map (fun (v, s) -> L [ encVarId v; encScheme s ])); encExpr b ]
    | EApp (f, args) -> L (A "ea" :: encExpr f :: List.map encExpr args)
    | ELet (r, v, s, rhs, body) -> L [ A "ee"; A (if r then "1" else "0"); encVarId v; encScheme s; encExpr rhs; encExpr body ]
    | EIf (a, b, c) -> L [ A "ei"; encExpr a; encExpr b; encExpr c ]
    | EMatch (s, cs) ->
        L (A "eh" :: encExpr s
           :: (cs |> List.map (fun (p, g, b) ->
                L [ encPat p
                    (match g with Some g -> L [ A "g"; encExpr g ] | None -> L [ A "n" ])
                    encExpr b ])))
    | ETuple xs -> L (A "et" :: List.map encExpr xs)
    | EListLit xs -> L (A "ek" :: List.map encExpr xs)
    | ECtor (n, s, args) -> L (A "ec" :: S n :: encScheme s :: List.map encExpr args)
    | ERecord (n, fs) -> L (A "er" :: S n :: (fs |> List.map (fun (f, v) -> L [ S f; encExpr v ])))
    | ERecordExt (n, bse, fs) -> L (A "ee" :: S n :: encExpr bse :: (fs |> List.map (fun (f, v) -> L [ S f; encExpr v ])))
    | EField (r, f, o) -> L [ A "ef"; encExpr r; S f; S o ]
    | EFieldSet (r, f, o, v) -> L [ A "efs"; encExpr r; S f; S o; encExpr v ]
    | EPrim (op, args) -> L (A "ep" :: S op :: List.map encExpr args)
    | ESeq xs -> L (A "es" :: List.map encExpr xs)
    | EWhile (c, b) -> L [ A "ew"; encExpr c; encExpr b ]
    | EAssign (v, e) -> L [ A "eg"; encVarId v; encExpr e ]
    | ETry (b, cs) ->
        L (A "eT" :: encExpr b
           :: (cs |> List.map (fun (p, g, e) ->
                L [ encPat p
                    (match g with Some g -> L [ A "g"; encExpr g ] | None -> L [ A "n" ])
                    encExpr e ])))
    | EArray (nm, xs) -> L (A "ey" :: S nm :: List.map encExpr xs)
    | EIndex (nm, a, i) -> L [ A "ex"; S nm; encExpr a; encExpr i ]
    | EIndexSet (nm, a, i, v) -> L [ A "ez"; S nm; encExpr a; encExpr i; encExpr v ]
    | EArrayLen (nm, a) -> L [ A "eL"; S nm; encExpr a ]
    | EArrayCreate (nm, n, v) -> L [ A "eC"; S nm; encExpr n; encExpr v ]
    | EArrayPin (nm, a) -> L [ A "eP"; S nm; encExpr a ]
    | EArrayUnpin (nm, a) -> L [ A "eU"; S nm; encExpr a ]
    | EArrayBytes (nm, a) -> L [ A "eB"; S nm; encExpr a ]
    | EIfaceCall (i, m, r, args) -> L (A "ei" :: S i :: S m :: encExpr r :: List.map encExpr args)
    | ECast (t, e, d) -> L [ A "ec"; S t; encExpr e; A (if d then "1" else "0") ]
    | ETypeTest (t, e) -> L [ A "ett"; S t; encExpr e ]

let private encDecl (d : Decl) : Sx =
    match d with
    | DExtern (v, s) -> L [ A "de"; encVarId v; encScheme s ]
    | DExport (v, n) -> L [ A "dx"; encVarId v; S n ]
    | DLet (r, v, s, e) -> L [ A "dl"; A (if r then "1" else "0"); encVarId v; encScheme s; encExpr e ]
    | DUnion (n, ps, cs) ->
        L [ A "du"; S n; L (List.map S ps); L (cs |> List.map (fun (c, a) -> L [ S c; A (string a) ])) ]
    | DRecord (n, ps, fs, st) ->
        L [ A "dr"; S n; L (List.map S ps)
            L (fs |> List.map (fun (f, k) -> L [ S f; A k ])); A (if st then "1" else "0") ]
    | DInterface (n, ms) ->
        L [ A "di"; S n; L (ms |> List.map (fun (m, a) -> L [ S m; A (string a) ])) ]
    | DEnum (n, cs) ->
        L [ A "dn"; S n; L (cs |> List.map (fun (c, v) -> L [ S c; A (string v) ])) ]
    | DMembers (n, own) ->
        L [ A "dm"; S n; L (own |> List.map (fun (m, v) -> L [ S m; encVarId v ])) ]
    | DBaseInst (n, inst) ->
        L [ A "db"; S n; L (inst |> List.map S) ]
    | DClass (n, bse, own, impls) ->
        L [ A "dc"; S n
            (match bse with Some b -> S b | None -> A "-")
            L (own |> List.map (fun (m, v) -> L [ S m; encVarId v ]))
            L (impls |> List.map (fun (i, ms) ->
                L [ S i; L (ms |> List.map (fun (m, v) -> L [ S m; encVarId v ])) ])) ]

let private encDef (full : string, d : Resolve.Definition) : Sx =
    let kind =
        match d.Kind with
        | Resolve.DefLet -> "l" | Resolve.DefType -> "t" | Resolve.DefCase -> "c"
        | Resolve.DefField -> "f" | Resolve.DefModule -> "m" | _ -> "x"
    L [ S full; S d.Name; A kind; S d.Path; A (string d.Offset); A (string d.Length) ]

/// A library: exports for the resolver, schemes for inference, decls for
/// emission and (later) instantiation.
let encodeLib (exports : (string * Resolve.Definition) list)
              (schemes : (string * Scheme) list)
              (decls : Decl list) : string =
    toText (L [ A "fppir1"
                L (A "x" :: List.map encDef exports)
                L (A "s" :: (schemes |> List.map (fun (k, s) -> L [ S k; encScheme s ])))
                L (A "d" :: List.map encDecl decls) ])

// ---- decoding -------------------------------------------------------------

let private freshVars = dictNew<string, Var> ()
let private varById (id : string) : Var =
    match dictTryFind freshVars id with
    | Some v -> v
    | None ->
        let v : Var = { Id = 1000000 + vecLen (vecOfList (dictPairs freshVars)); Level = 0; Link = None; Rigid = false }
        dictSet freshVars id v
        v

let rec private decTy (x : Sx) : Type =
    match x with
    | L (A "v" :: A id :: _) -> TVar (varById id)
    | L (A "c" :: S n :: args) -> TCon (n, List.map decTy args)
    | L [ A "f"; a; b ] -> TFun (decTy a, decTy b)
    | L (A "t" :: ts) -> TTuple (List.map decTy ts)
    | _ -> TCon ("?", [])

let private decConstraint (x : Sx) : Constraint option =
    match x with
    | L [ A "k"; S cls; L args; L assoc ] ->
        Some { Class = cls
               Args = List.map decTy args
               Assoc = assoc |> List.choose (fun a -> match a with L [ S n; t ] -> Some (n, decTy t) | _ -> None) }
    | _ -> None

let private decScheme (x : Sx) : Scheme =
    match x with
    | L [ A "s"; L qs; body; L cs ] ->
        { Quantified = qs |> List.choose (fun q -> match q with A id -> Some (varById id) | _ -> None)
          Constraints = List.choose decConstraint cs
          Body = decTy body }
    | _ -> mono (TCon ("?", []))

let private decVarId (x : Sx) : VarId =
    match x with
    | L [ S p; A o; S n ] -> { Path = p; Offset = int o; Name = n }
    | _ -> { Path = "?"; Offset = 0; Name = "?" }

let private decLit (x : Sx) : Lit =
    match x with
    | L [ A "li"; S s ] -> LInt s
    | L [ A "lf"; S s ] -> LFloat s
    | L [ A "ls"; S s ] -> LString s
    | L [ A "lc"; S s ] -> LChar s
    | L [ A "lb"; A b ] -> LBool (b = "1")
    | L [ A "ln" ] -> LNull
    | _ -> LUnit

let rec private decPat (x : Sx) : Pat =
    match x with
    | L (A "pw" :: _) -> PWild
    | L [ A "pl"; l ] -> PLit (decLit l)
    | L [ A "pv"; v; s ] -> PVar (decVarId v, decScheme s)
    | L (A "pc" :: S n :: s :: ps) -> PCtor (n, decScheme s, List.map decPat ps)
    | L [ A "ptt"; S t ] -> PTypeTest t
    | L (A "pt" :: ps) -> PTuple (List.map decPat ps)
    | L [ A "pn"; a; b ] -> PCons (decPat a, decPat b)
    | L (A "pk" :: ps) -> PListLit (List.map decPat ps)
    | L [ A "pa"; p; v; s ] -> PAs (decPat p, decVarId v, decScheme s)
    | L (A "po" :: ps) -> POr (List.map decPat ps)
    | _ -> PWild

let rec private decExpr (x : Sx) : Expr =
    match x with
    | L [ A "el"; l ] -> ELit (decLit l)
    | L (A "eV" :: v :: s :: inst) ->
        EVarI (decVarId v, decScheme s, inst |> List.choose (fun x -> match x with S t -> Some t | _ -> None))
    | L [ A "ev"; v; s ] -> EVar (decVarId v, decScheme s)
    | L [ A "eu"; S n ] -> EUnknown n
    | L [ A "em"; L ps; b ] ->
        ELam (ps |> List.choose (fun p -> match p with L [ v; s ] -> Some (decVarId v, decScheme s) | _ -> None), decExpr b)
    | L (A "ea" :: f :: args) -> EApp (decExpr f, List.map decExpr args)
    | L [ A "ee"; A r; v; s; rhs; body ] -> ELet ((r = "1"), decVarId v, decScheme s, decExpr rhs, decExpr body)
    | L [ A "ei"; a; b; c ] -> EIf (decExpr a, decExpr b, decExpr c)
    | L (A "eh" :: scrut :: cs) ->
        EMatch (decExpr scrut,
                cs |> List.choose (fun c ->
                    match c with
                    | L [ p; g; b ] ->
                        let guard = match g with L [ A "g"; ge ] -> Some (decExpr ge) | _ -> None
                        Some (decPat p, guard, decExpr b)
                    | _ -> None))
    | L (A "et" :: xs) -> ETuple (List.map decExpr xs)
    | L (A "ek" :: xs) -> EListLit (List.map decExpr xs)
    | L (A "ec" :: S n :: s :: args) -> ECtor (n, decScheme s, List.map decExpr args)
    | L (A "er" :: S n :: fs) ->
        ERecord (n, fs |> List.choose (fun f -> match f with L [ S fn; v ] -> Some (fn, decExpr v) | _ -> None))
    | L (A "ee" :: S n :: bse :: fs) ->
        ERecordExt (n, decExpr bse, fs |> List.choose (fun f -> match f with L [ S fn; v ] -> Some (fn, decExpr v) | _ -> None))
    | L [ A "ef"; r; S f; S o ] -> EField (decExpr r, f, o)
    | L [ A "efs"; r; S f; S o; v ] -> EFieldSet (decExpr r, f, o, decExpr v)
    | L (A "ep" :: S op :: args) -> EPrim (op, List.map decExpr args)
    | L (A "es" :: xs) -> ESeq (List.map decExpr xs)
    | L [ A "ew"; c; b ] -> EWhile (decExpr c, decExpr b)
    | L [ A "eg"; v; e ] -> EAssign (decVarId v, decExpr e)
    | L (A "eT" :: b :: cs) ->
        ETry (decExpr b,
              cs |> List.choose (fun c ->
                  match c with
                  | L [ p; g; e ] ->
                      let guard = match g with L [ A "g"; ge ] -> Some (decExpr ge) | _ -> None
                      Some (decPat p, guard, decExpr e)
                  | _ -> None))
    | L (A "ey" :: S nm :: xs) -> EArray (nm, List.map decExpr xs)
    | L [ A "ex"; S nm; a; i ] -> EIndex (nm, decExpr a, decExpr i)
    | L [ A "ez"; S nm; a; i; v ] -> EIndexSet (nm, decExpr a, decExpr i, decExpr v)
    | L [ A "eL"; S nm; a ] -> EArrayLen (nm, decExpr a)
    | L [ A "eC"; S nm; n; v ] -> EArrayCreate (nm, decExpr n, decExpr v)
    | L [ A "eP"; S nm; a ] -> EArrayPin (nm, decExpr a)
    | L [ A "eU"; S nm; a ] -> EArrayUnpin (nm, decExpr a)
    | L [ A "eB"; S nm; a ] -> EArrayBytes (nm, decExpr a)
    | L (A "ei" :: S i :: S m :: r :: args) -> EIfaceCall (i, m, decExpr r, List.map decExpr args)
    | L [ A "ec"; S t; e; A d ] -> ECast (t, decExpr e, d = "1")
    | L [ A "ett"; S t; e ] -> ETypeTest (t, decExpr e)
    | _ -> ELit LUnit

let private decDecl (x : Sx) : Decl option =
    match x with
    | L [ A "de"; v; s ] -> Some (DExtern (decVarId v, decScheme s))
    | L [ A "dx"; v; S n ] -> Some (DExport (decVarId v, n))
    | L [ A "dl"; A r; v; s; e ] -> Some (DLet ((r = "1"), decVarId v, decScheme s, decExpr e))
    | L [ A "du"; S n; L ps; L cs ] ->
        Some (DUnion (n, ps |> List.choose (fun p -> match p with S s -> Some s | _ -> None),
                      cs |> List.choose (fun c -> match c with L [ S cn; A a ] -> Some (cn, int a) | _ -> None)))
    | L [ A "dr"; S n; L ps; L fs; A st ] ->
        Some (DRecord (n, ps |> List.choose (fun p -> match p with S s -> Some s | _ -> None),
                       fs |> List.choose (fun f -> match f with L [ S fn; A k ] -> Some (fn, k) | _ -> None),
                       st = "1"))
    | L [ A "dm"; S n; L own ] ->
        Some (DMembers (n, own |> List.choose (fun m -> match m with L [ S mn; v ] -> Some (mn, decVarId v) | _ -> None)))
    | L [ A "dn"; S n; L cs ] ->
        Some (DEnum (n, cs |> List.choose (fun c -> match c with L [ S cn; A v ] -> Some (cn, int v) | _ -> None)))
    | L [ A "di"; S n; L ms ] ->
        Some (DInterface (n, ms |> List.choose (fun m -> match m with L [ S mn; A a ] -> Some (mn, int a) | _ -> None)))
    | L [ A "db"; S n; L inst ] ->
        Some (DBaseInst (n, inst |> List.choose (fun i -> match i with S x -> Some x | _ -> None)))
    | L [ A "dc"; S n; b; L own; L impls ] ->
        Some (DClass (n,
                (match b with S bn -> Some bn | _ -> None),
                own |> List.choose (fun m -> match m with L [ S mn; v ] -> Some (mn, decVarId v) | _ -> None),
                impls |> List.choose (fun i ->
                    match i with
                    | L [ S iname; L ms ] ->
                        Some (iname, ms |> List.choose (fun m -> match m with L [ S mn; v ] -> Some (mn, decVarId v) | _ -> None))
                    | _ -> None)))
    | _ -> None

let private decDef (x : Sx) : (string * Resolve.Definition) option =
    match x with
    | L [ S full; S name; A kind; S path; A off; A len ] ->
        let k =
            match kind with
            | "l" -> Resolve.DefLet | "t" -> Resolve.DefType | "c" -> Resolve.DefCase
            | "f" -> Resolve.DefField | "m" -> Resolve.DefModule | _ -> Resolve.DefLet
        let d : Resolve.Definition =
            { Name = name; Kind = k; Path = path; Offset = int off; Length = int len }
        Some (full, d)
    | _ -> None

let decodeLib (text : string) : (string * Resolve.Definition) list * (string * Scheme) list * Decl list =
    match parse text with
    | L [ A "fppir1"; L (A "x" :: exports); L (A "s" :: schemes); L (A "d" :: decls) ] ->
        exports |> List.choose decDef,
        schemes |> List.choose (fun s -> match s with L [ S k; sch ] -> Some (k, decScheme sch) | _ -> None),
        decls |> List.choose decDecl
    | _ -> [], [], []

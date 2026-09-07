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
        // the same one-allocation-per-CHARACTER shape the reader had: a
        // string needing no escape is written whole
        let mutable esc = false
        for c in s do
            if c = '"' || c = '\\' || c = '\n' then esc <- true
        if not esc then vecAdd sb s
        else
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
            // A literal with no escape in it IS a slice of the input. Built
            // a character at a time it allocated one string PER CHARACTER
            // and concatenated the lot: 429 ms of the 502 ms a prelude
            // snapshot took to read back, and every .fppir paid it too.
            // The escaped case is rare, and still walks.
            let start = i
            let mutable esc = false
            while i < n && charAt text i <> '"' do
                if charAt text i = '\\' then
                    esc <- true
                    i <- i + 2
                else i <- i + 1
            let raw = substr text start (i - start)
            i <- i + 1
            if not esc then S raw
            else
                let sb = vecNew<string> ()
                let m = strLen raw
                let mutable j = 0
                while j < m do
                    if charAt raw j = '\\' && j + 1 < m then
                        (match charAt raw (j + 1) with
                         | 'n' -> vecAdd sb "\n"
                         | c -> vecAdd sb (string c))
                        j <- j + 2
                    else
                        vecAdd sb (string (charAt raw j))
                        j <- j + 1
                S (String.concat "" (vecToList sb))
        else
            let start = i
            while i < n && charAt text i <> ' ' && charAt text i <> ')' && charAt text i <> '(' && charAt text i <> '\n' && charAt text i <> '\r' && charAt text i <> '\t' do i <- i + 1
            A (substr text start (i - start))
    node ()

// ---- encoding -------------------------------------------------------------

// While a PRELUDE snapshot is being written every variable it mentions is
// collected, so the snapshot can carry each one's level and rigidity —
// `encTy` names a variable by ID alone, which is all a package needs
// (it re-numbers on the way in) and not enough for a cache that must
// reproduce the compiler's state exactly.
let mutable private varSink = dictNew<int, Var> ()
let mutable private collectVars = false

let rec private encTy (t : Type) : Sx =
    match prune t with
    | TVar v ->
        (if collectVars then dictSet varSink v.Id v)
        L [ A "v"; A (string v.Id) ]
    | TCon (n, args) -> L (A "c" :: S n :: List.map encTy args)
    | TFun (a, b) -> L [ A "f"; encTy a; encTy b ]
    | TTuple ts -> L (A "t" :: List.map encTy ts)
    | TApp (h, args) -> L (A "a" :: encTy h :: List.map encTy args)

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
    | PArrLit (k, ps) -> L (A "pak" :: S k :: List.map encPat ps)
    | PAnd (a, b) -> L [ A "pand"; encPat a; encPat b ]
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
    | DUnionFields (n, cs) ->
        L [ A "duf"; S n; L (cs |> List.map (fun (c, tys) -> L [ S c; L (List.map S tys) ])) ]
    | DRecord (n, ps, fs, st) ->
        L [ A "dr"; S n; L (List.map S ps)
            L (fs |> List.map (fun (f, k) -> L [ S f; A k ])); A (if st then "1" else "0") ]
    | DInterface (n, ms) ->
        L [ A "di"; S n; L (ms |> List.map (fun (m, a) -> L [ S m; A (string a) ])) ]
    | DEnum (n, cs) ->
        L [ A "dn"; S n; L (cs |> List.map (fun (c, v) -> L [ S c; A (string v) ])) ]
    | DMembers (n, own) ->
        L [ A "dm"; S n; L (own |> List.map (fun (m, v) -> L [ S m; encVarId v ])) ]
    | DFieldSubst (n, fs) ->
        L [ A "dfs"; S n; L (fs |> List.map (fun (a, b) -> L [ S a; S b ])) ]
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

// ---- decoding -------------------------------------------------------------

let private freshVars = dictNew<string, Var> ()
/// A PRELUDE snapshot restores variables under their ORIGINAL ids. A package
/// cannot: two libraries would collide, which is why that path re-numbers
/// and then rewrites the markers that name an id inside a string. The cache
/// is a snapshot of ONE compiler run, so keeping the ids is both possible
/// and necessary — a renumbered `$class:Num:One:#4` names nothing.
let mutable private preludeMode = false
let private preludeVars = dictNew<string, Var> ()
let private varById (id : string) : Var =
    if preludeMode then
        match dictTryFind preludeVars id with
        | Some v -> v
        | None ->
            let v : Var = { Id = int id; Level = 0; Link = None; Rigid = false }
            dictSet preludeVars id v
            v
    else
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
    | L (A "a" :: h :: args) -> TApp (decTy h, List.map decTy args)
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
    | L (A "pak" :: S k :: ps) -> PArrLit (k, List.map decPat ps)
    | L [ A "pand"; a; b ] -> PAnd (decPat a, decPat b)
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
    | L [ A "duf"; S n; L cs ] ->
        Some (DUnionFields (n,
                            cs |> List.choose (fun c ->
                                match c with
                                | L [ S cn; L tys ] ->
                                    Some (cn, tys |> List.choose (fun t -> match t with S x -> Some x | _ -> None))
                                | _ -> None)))
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
            { Name = name; Kind = k; Path = path; Offset = int off; Length = int len; Access = 0 }
        Some (full, d)
    | _ -> None

/// Rewrite `#<id>` markers in a decoded body to the ids `varById` handed out.
///
/// A class or operator marker spells its type variable by ID, inside a NAME
/// (`*@#1`, `$class:Num:One:#1`) — text, not a Type node, so decoding rewrote
/// the schemes and left the markers naming the PRODUCER's ids. At the consumer
/// those ids belong to nothing, the stamper's substitution had no entry, and a
/// packaged `let sq (x : 'a) : 'a when Num<'a> = x * x` kept `*@#1`: `sq 3`
/// answered 0 and `sq 1.5` answered 1.5, while the same two files built as one
/// project were right (KNOWN-ISSUES #4).
let private remapMarkers (n : string) : string =
    if not (n.Contains "#") then n
    else
        let out = vecNew<string> ()
        let mutable i = 0
        while i < n.Length do
            if n.[i] = '#' then
                let start = i
                i <- i + 1
                while i < n.Length && isDigit n.[i] do i <- i + 1
                let old = n.Substring (start + 1, i - start - 1)
                vecAdd out
                    (if old = "" then "#"
                     else
                         match dictTryFind freshVars old with
                         | Some (v : Var) -> "#" + string v.Id
                         | None -> "#" + old)
            else
                vecAdd out (n.Substring (i, 1))
                i <- i + 1
        String.concat "" (vecToList out)

let rec private remapDeclMarkers (e : Expr) : Expr =
    let r = remapDeclMarkers
    match e with
    | EUnknown n -> EUnknown (remapMarkers n)
    | EPrim (op, xs) -> EPrim (remapMarkers op, List.map r xs)
    | ELam (ps, b) -> ELam (ps, r b)
    | EApp (g, args) -> EApp (r g, List.map r args)
    | ELet (rc, v, sc, rhs, b) -> ELet (rc, v, sc, r rhs, r b)
    | EIf (a, b, c) -> EIf (r a, r b, r c)
    | EMatch (sx, cs) -> EMatch (r sx, cs |> List.map (fun (p, g, b) -> p, Option.map r g, r b))
    | ETuple xs -> ETuple (List.map r xs)
    | EListLit xs -> EListLit (List.map r xs)
    | ESeq xs -> ESeq (List.map r xs)
    | ECtor (nm, sc, xs) -> ECtor (nm, sc, List.map r xs)
    | ERecord (nm, fs) -> ERecord (nm, fs |> List.map (fun (k, v) -> k, r v))
    | ERecordExt (nm, b, fs) -> ERecordExt (nm, r b, fs |> List.map (fun (k, v) -> k, r v))
    | EField (b, fn, o) -> EField (r b, fn, o)
    | EIfaceCall (i, m, recv, args) -> EIfaceCall (i, m, r recv, List.map r args)
    | ECast (t, b, d) -> ECast (t, r b, d)
    | ETypeTest (t, b) -> ETypeTest (t, r b)
    | EFieldSet (b, fn, o, v) -> EFieldSet (r b, fn, o, r v)
    | EWhile (c, b) -> EWhile (r c, r b)
    | EAssign (v, b) -> EAssign (v, r b)
    | EArray (nm, xs) -> EArray (nm, List.map r xs)
    | EIndex (nm, a, i) -> EIndex (nm, r a, r i)
    | EIndexSet (nm, a, i, v) -> EIndexSet (nm, r a, r i, r v)
    | EArrayLen (nm, a) -> EArrayLen (nm, r a)
    | EArrayCreate (nm, a, b) -> EArrayCreate (nm, r a, r b)
    | EArrayPin (nm, a) -> EArrayPin (nm, r a)
    | EArrayUnpin (nm, a) -> EArrayUnpin (nm, r a)
    | EArrayBytes (nm, a) -> EArrayBytes (nm, r a)
    | ETry (b, cs) -> ETry (r b, cs |> List.map (fun (p, g, x) -> p, Option.map r g, r x))
    | other -> other



// ---- the prelude snapshot -------------------------------------------------
//
// The prelude is parsed, resolved, inferred and lowered on EVERY invocation,
// and it is the same work every time: 1.34 s of a hello-world's 2.89 s, 47%
// of the whole build. This is that state, written once and read back.
//
// Three things make it safe to restore rather than recompute, and each is a
// rule to keep:
//
//  * VARIABLE IDS ARE PRESERVED, including the id SUPPLY the run ended on.
//    Class and operator markers name a variable by id inside a string
//    (`$class:Num:One:#4`), so a renumbered snapshot names nothing — and a
//    supply that restarts lower hands a PROJECT variable an id the prelude
//    already used, which is the same bug one step later. Restoring the
//    counter is what makes the emitted wasm byte-identical either way.
//  * FIELDS ARE TAGGED, not positional. Two fields of the same type sitting
//    next to each other (`ShowTypes`/`StrTypes`, `OrdDerive`/`ShowDerive`)
//    would swap silently under a positional format, and the round-trip
//    check below cannot see a symmetric swap.
//  * IT IS VERIFIED BEFORE IT IS WRITTEN. `decExpr` answers `ELit LUnit`
//    for anything it does not recognise, so a gap in the codec does not
//    fail — it silently replaces code with unit. Re-encoding what was
//    decoded and comparing the TEXT catches exactly that, and the snapshot
//    is discarded rather than written when it does not match.

type PreludeSnapshot =
    { PIdSupply : int
      /// hash of the prelude SOURCE this was made from — the reader checks it
      PSrcHash : string
      PImports : Dict<string, Resolve.Definition>
      PMembers : Dict<string, Resolve.Definition>
      PSchemes : Dict<string, Scheme>
      PAliases : Dict<string, Var list * Type>
      PFields : Dict<string, Infer.FieldInfo>
      PIfaces : Dict<string, (string * int) list>
      PBases : Dict<string, Var list * Type>
      PImpls : Dict<string, string list>
      PImplTys : Dict<string, (Var list * Type) list>
      PStructTypes : Dict<string, bool>
      PCtors : Dict<string, (int * Scheme) list>
      PClasses : Classes.Tables
      PInferred : Infer.InferResult
      PBind : Resolve.BindResult }

let private aI (i : int) : Sx = A (string i)
let private aB (b : bool) : Sx = A (if b then "1" else "0")
let private dB (x : Sx) : bool = match x with A "1" -> true | _ -> false
let private dI (x : Sx) : int = match x with A a -> int a | _ -> 0
let private dS (x : Sx) : string = match x with S t -> t | A t -> t | _ -> ""
let private dL (x : Sx) : Sx list = match x with L xs -> xs | _ -> []

/// Sorted by key: a snapshot must not depend on hash order, both so the
/// round-trip check compares like with like and so the file is reproducible.
let private encMap (enc : 'v -> Sx) (d : Dict<string, 'v>) : Sx =
    L (dictPairs d
       |> List.sortWith (fun (a, _) (b, _) -> compare a b)
       |> List.map (fun (k, v) -> L [ S k; enc v ]))

let private decMap (dec : Sx -> 'v) (x : Sx) : Dict<string, 'v> =
    let d = dictNew<string, 'v> ()
    for it in dL x do
        match it with
        | L [ S k; v ] -> dictSet d k (dec v)
        | _ -> ()
    d

let private encVarP (v : Var) : Sx =
    (if collectVars then dictSet varSink v.Id v)
    A (string v.Id)

let private decVarP (x : Sx) : Var = varById (dS x)
let private encVarsP (vs : Var list) : Sx = L (List.map encVarP vs)
let private decVarsP (x : Sx) : Var list = dL x |> List.map decVarP

let private encKind (k : Resolve.DefKind) : Sx =
    A (match k with
       | Resolve.DefLet -> "l" | Resolve.DefParam -> "p" | Resolve.DefType -> "t"
       | Resolve.DefCase -> "c" | Resolve.DefField -> "f" | Resolve.DefModule -> "m"
       | Resolve.DefSelf -> "s" | Resolve.DefMember -> "b")

let private decKind (x : Sx) : Resolve.DefKind =
    match dS x with
    | "l" -> Resolve.DefLet | "p" -> Resolve.DefParam | "t" -> Resolve.DefType
    | "c" -> Resolve.DefCase | "f" -> Resolve.DefField | "m" -> Resolve.DefModule
    | "s" -> Resolve.DefSelf | _ -> Resolve.DefMember

/// Access IS carried, unlike the package encoding: a package surface is
/// public by construction, the prelude's is not, and a private definition
/// restored as public changes what a project may name.
let private encDefP (d : Resolve.Definition) : Sx =
    L [ S d.Name; encKind d.Kind; S d.Path; aI d.Offset; aI d.Length; aI d.Access ]

let private decDefP (x : Sx) : Resolve.Definition =
    match x with
    | L [ S n; k; S p; o; l; ac ] ->
        { Name = n; Kind = decKind k; Path = p; Offset = dI o; Length = dI l; Access = dI ac }
    | _ -> { Name = "?"; Kind = Resolve.DefLet; Path = "?"; Offset = 0; Length = 0; Access = 0 }

let private encVarsTy (vs : Var list, t : Type) : Sx = L [ encVarsP vs; encTy t ]
let private decVarsTy (x : Sx) : Var list * Type =
    match x with
    | L [ vs; t ] -> decVarsP vs, decTy t
    | _ -> [], TCon ("unit", [])

let private encFieldInfo (f : Infer.FieldInfo) : Sx =
    L [ S f.TypeName; encVarsP f.Params; encVarsP f.Quantified; encTy f.FieldType
        (match f.DefKey with Some (p, o) -> L [ S p; aI o ] | None -> L [])
        aB f.IsStatic; aI f.Optionals
        L (f.ParamNames |> List.map S)
        L (f.Constraints |> List.map encConstraint)
        aI f.Access ]

let private decFieldInfo (x : Sx) : Infer.FieldInfo =
    match x with
    | L [ S tn; ps; qs; ft; dk; st; op; pn; cs; ac ] ->
        { TypeName = tn; Params = decVarsP ps; Quantified = decVarsP qs
          FieldType = decTy ft
          DefKey = (match dk with L [ S p; o ] -> Some (p, dI o) | _ -> None)
          IsStatic = dB st; Optionals = dI op
          ParamNames = dL pn |> List.map dS
          Constraints = dL cs |> List.choose decConstraint
          Access = dI ac }
    | _ ->
        { TypeName = "?"; Params = []; Quantified = []; FieldType = TCon ("unit", [])
          DefKey = None; IsStatic = false; Optionals = 0; ParamNames = []
          Constraints = []; Access = 0 }

let private encInstMember (m : Classes.InstMember) : Sx =
    L [ S m.MPath; aI m.MOffset; S m.MName; aB m.MTakesUnit; aB m.MTupled
        L (m.MInst |> List.map S) ]

let private decInstMember (x : Sx) : Classes.InstMember =
    match x with
    | L [ S p; o; S n; tu; tp; inst ] ->
        { MPath = p; MOffset = dI o; MName = n; MTakesUnit = dB tu; MTupled = dB tp
          MInst = dL inst |> List.map dS }
    | _ -> { MPath = "?"; MOffset = 0; MName = "?"; MTakesUnit = false; MTupled = false; MInst = [] }

let private encInstanceDef (i : Classes.InstanceDef) : Sx =
    L [ S i.Class; encVarsP i.Params; L (List.map encTy i.Head)
        L (i.Assoc |> List.map (fun (n, t) -> L [ S n; encTy t ]))
        L (List.map encConstraint i.Context)
        L (i.Members |> List.map (fun (n, m) -> L [ S n; encInstMember m ]))
        aB i.Builtin; S i.Path; aI i.Offset ]

let private decInstanceDef (x : Sx) : Classes.InstanceDef =
    match x with
    | L [ S c; ps; hd; asc; ctx; ms; b; S p; o ] ->
        { Class = c; Params = decVarsP ps; Head = dL hd |> List.map decTy
          Assoc = dL asc |> List.choose (fun a -> match a with L [ S n; t ] -> Some (n, decTy t) | _ -> None)
          Context = dL ctx |> List.choose decConstraint
          Members = dL ms |> List.choose (fun a -> match a with L [ S n; m ] -> Some (n, decInstMember m) | _ -> None)
          Builtin = dB b; Path = p; Offset = dI o }
    | _ ->
        { Class = "?"; Params = []; Head = []; Assoc = []; Context = []; Members = []
          Builtin = false; Path = "?"; Offset = 0 }

let private encClassDef (c : Classes.ClassDef) : Sx =
    L [ S c.Name; encVarsP c.Params; L (c.ParamKinds |> List.map aI)
        L (c.DotMembers |> List.map S); L (c.Assoc |> List.map S)
        L (List.map encConstraint c.Supers)
        L (c.Members |> List.map (fun (n, sc) -> L [ S n; encScheme sc ]))
        S c.Path; aI c.Offset ]

let private decClassDef (x : Sx) : Classes.ClassDef =
    match x with
    | L [ S n; ps; pk; dm; asc; sup; ms; S p; o ] ->
        { Name = n; Params = decVarsP ps; ParamKinds = dL pk |> List.map dI
          DotMembers = dL dm |> List.map dS; Assoc = dL asc |> List.map dS
          Supers = dL sup |> List.choose decConstraint
          Members = dL ms |> List.choose (fun a -> match a with L [ S mn; sc ] -> Some (mn, decScheme sc) | _ -> None)
          Path = p; Offset = dI o }
    | _ ->
        { Name = "?"; Params = []; ParamKinds = []; DotMembers = []; Assoc = []
          Supers = []; Members = []; Path = "?"; Offset = 0 }

/// Instance ORDER within a class is preserved: selection ranks candidates by
/// registration index, so a reordered table picks a different instance.
let private encTables (t : Classes.Tables) : Sx =
    L [ L [ A "classes"; encMap encClassDef t.Classes ]
        L [ A "instances"
            L (dictPairs t.Instances
               |> List.sortWith (fun (a, _) (b, _) -> compare a b)
               |> List.map (fun (k, v) -> L [ S k; L (vecToList v |> List.map encInstanceDef) ])) ]
        L [ A "memberowner"; encMap S t.MemberOwner ]
        L [ A "typepaths"
            L (dictPairs t.TypePaths
               |> List.sortWith (fun (a, _) (b, _) -> compare a b)
               |> List.map (fun (k, v) -> L [ S k; L (vecToList v |> List.map S) ])) ] ]

let private field (tag : string) (xs : Sx list) : Sx =
    match xs |> List.tryPick (fun x -> match x with L (A t :: rest) when t = tag -> Some rest | _ -> None) with
    | Some [ one ] -> one
    | Some rest -> L rest
    | None -> L []

let private decTables (x : Sx) : Classes.Tables =
    let xs = dL x
    let t = Classes.newTables ()
    for k, v in dictPairs (decMap decClassDef (field "classes" xs)) do dictSet t.Classes k v
    for it in dL (field "instances" xs) do
        match it with
        | L [ S k; L vs ] ->
            let nv = vecNew<Classes.InstanceDef> ()
            for v in vs do vecAdd nv (decInstanceDef v)
            dictSet t.Instances k nv
        | _ -> ()
    for k, v in dictPairs (decMap dS (field "memberowner" xs)) do dictSet t.MemberOwner k v
    for it in dL (field "typepaths" xs) do
        match it with
        | L [ S k; L vs ] ->
            let nv = vecNew<string> ()
            for v in vs do vecAdd nv (dS v)
            dictSet t.TypePaths k nv
        | _ -> ()
    t

// InferResult is plain data — offsets and marker strings, no type graph —
// so each field is a list of tuples and the only hazard is confusing two
// of the same shape. Hence the tags.
let private eIS (xs : (int * string) list) : Sx =
    L (xs |> List.map (fun (i, s) -> L [ aI i; S s ]))
let private dIS (x : Sx) : (int * string) list =
    dL x |> List.choose (fun a -> match a with L [ i; s ] -> Some (dI i, dS s) | _ -> None)

let private eDerive (xs : (string * string * int * bool * int list * (string * string list) list) list) : Sx =
    L (xs |> List.map (fun (k, n, o, u, ps, es) ->
        L [ S k; S n; aI o; aB u; L (ps |> List.map aI)
            L (es |> List.map (fun (cn, cs) -> L [ S cn; L (cs |> List.map S) ])) ]))

let private dDerive (x : Sx) : (string * string * int * bool * int list * (string * string list) list) list =
    dL x |> List.choose (fun a ->
        match a with
        | L [ S k; S n; o; u; ps; es ] ->
            Some (k, n, dI o, dB u, dL ps |> List.map dI,
                  dL es |> List.choose (fun e -> match e with L [ S cn; cs ] -> Some (cn, dL cs |> List.map dS) | _ -> None))
        | _ -> None)

// Two of the snapshot's lists are most of its bytes — every expression's
// type, and every resolved use in the prelude. As s-expressions each entry
// is three or more NODES, and the cost of reading one back is the node
// allocation, not the bytes. Packed into a single atom they are one slice
// and a linear scan.
//
// Length prefixes rather than a separator: a type string can contain
// anything, including whatever character looked safe to delimit with.
let private packInt (sb : Vec<string>) (i : int) : unit =
    vecAdd sb (string i)
    vecAdd sb " "

let private packStr (sb : Vec<string>) (t : string) : unit =
    vecAdd sb (string (strLen t))
    vecAdd sb ":"
    vecAdd sb t

/// A cursor over a packed atom: every reader here is a left-to-right scan.
type private Cur = { Text : string; Len : int; mutable At : int }

let private curNew (t : string) : Cur = { Text = t; Len = strLen t; At = 0 }

let private takeInt (c : Cur) : int =
    let mutable v = 0
    let mutable neg = false
    if c.At < c.Len && charAt c.Text c.At = '-' then
        neg <- true
        c.At <- c.At + 1
    while c.At < c.Len && charAt c.Text c.At <> ' ' && charAt c.Text c.At <> ':' do
        v <- v * 10 + (int (charAt c.Text c.At) - 48)
        c.At <- c.At + 1
    c.At <- c.At + 1
    if neg then -v else v

let private takeStr (c : Cur) : string =
    let n = takeInt c
    let r = substr c.Text c.At n
    c.At <- c.At + n
    r

let private encExprTypes (xs : (int * int * string) list) : Sx =
    let sb = vecNew<string> ()
    for a, b, t in xs do
        packInt sb a
        packInt sb b
        packStr sb t
    S (String.concat "" (vecToList sb))

let private decExprTypes (x : Sx) : (int * int * string) list =
    let c = curNew (dS x)
    let out = vecNew<int * int * string> ()
    while c.At < c.Len do
        let a = takeInt c
        let b = takeInt c
        vecAdd out (a, b, takeStr c)
    vecToList out

let private encResolutions (rs : Resolve.Resolution list) : Sx =
    let sb = vecNew<string> ()
    for r in rs do
        packInt sb r.UseOffset
        packInt sb r.UseLength
        packInt sb r.Def.Offset
        packInt sb r.Def.Length
        packInt sb r.Def.Access
        packStr sb (match encKind r.Def.Kind with A k -> k | _ -> "b")
        packStr sb r.Def.Name
        packStr sb r.Def.Path
    S (String.concat "" (vecToList sb))

let private decResolutions (x : Sx) : Resolve.Resolution list =
    let c = curNew (dS x)
    let out = vecNew<Resolve.Resolution> ()
    while c.At < c.Len do
        let uo = takeInt c
        let ul = takeInt c
        let dof = takeInt c
        let dl = takeInt c
        let ac = takeInt c
        let k = decKind (A (takeStr c))
        let nm = takeStr c
        let pa = takeStr c
        vecAdd out { UseOffset = uo; UseLength = ul
                     Def = { Name = nm; Kind = k; Path = pa; Offset = dof; Length = dl; Access = ac } }
    vecToList out

let private encInferResult (r : Infer.InferResult) : Sx =
    L [ L [ A "diagnostics"; eIS r.Diagnostics ]
        L [ A "freshidents"; L (r.FreshIdents |> List.map aI) ]
        L [ A "deftypes"; L (r.DefTypes |> List.map (fun (a, b, c) -> L [ aI a; aI b; S c ])) ]
        L [ A "opkinds"; eIS r.OpKinds ]
        L [ A "arrkinds"; eIS r.ArrKinds ]
        L [ A "instsites"; L (r.InstSites |> List.map (fun (i, ss) -> L [ aI i; L (ss |> List.map S) ])) ]
        L [ A "ordderive"; eDerive r.OrdDerive ]
        L [ A "showderive"; eDerive r.ShowDerive ]
        L [ A "showtypes"; eIS r.ShowTypes ]
        L [ A "strtypes"; eIS r.StrTypes ]
        L [ A "arbderive"; eDerive r.ArbDerive ]
        L [ A "membersites"; eIS r.MemberSites ]
        L [ A "ctorsites"; L (r.CtorSites |> List.map (fun (a, b) -> L [ aI a; aI b ])) ]
        L [ A "classuses"; L (r.ClassUses |> List.map (fun (i, m) -> L [ aI i; encInstMember m ])) ]
        L [ A "classpending"; eIS r.ClassPending ]
        L [ A "existpack"
            L (r.ExistPack |> List.map (fun (i, es) ->
                L [ aI i; L (es |> List.map (fun (a, b, c, ds) -> L [ S a; aI b; S c; L (ds |> List.map S) ])) ])) ]
        L [ A "existcases"; L (r.ExistCases |> List.map (fun (s, i) -> L [ S s; aI i ])) ]
        L [ A "existmatch"; eIS r.ExistMatch ]
        L [ A "dictuses"; L (r.DictUses |> List.map (fun (i, (a, b)) -> L [ aI i; aI a; aI b ])) ]
        L [ A "optypes"; eIS r.OpTypes ]
        L [ A "exprtypes"; encExprTypes r.ExprTypes ]
        L [ A "fieldowners"; eIS r.FieldOwners ]
        L [ A "compbuilders"; eIS r.CompBuilders ]
        L [ A "customops"; L (r.CustomOps |> List.map (fun (a, b, c) -> L [ S a; S b; S c ])) ]
        L [ A "compstatements"; L (r.CompStatements |> List.map aI) ]
        L [ A "compvalues"; L (r.CompValues |> List.map aI) ] ]

let private decInferResult (x : Sx) : Infer.InferResult =
    let xs = dL x
    { Diagnostics = dIS (field "diagnostics" xs)
      FreshIdents = dL (field "freshidents" xs) |> List.map dI
      DefTypes = dL (field "deftypes" xs) |> List.choose (fun a -> match a with L [ p; q; c ] -> Some (dI p, dI q, dS c) | _ -> None)
      OpKinds = dIS (field "opkinds" xs)
      ArrKinds = dIS (field "arrkinds" xs)
      InstSites = dL (field "instsites" xs) |> List.choose (fun a -> match a with L [ i; ss ] -> Some (dI i, dL ss |> List.map dS) | _ -> None)
      OrdDerive = dDerive (field "ordderive" xs)
      ShowDerive = dDerive (field "showderive" xs)
      ShowTypes = dIS (field "showtypes" xs)
      StrTypes = dIS (field "strtypes" xs)
      ArbDerive = dDerive (field "arbderive" xs)
      MemberSites = dIS (field "membersites" xs)
      CtorSites = dL (field "ctorsites" xs) |> List.choose (fun a -> match a with L [ p; q ] -> Some (dI p, dI q) | _ -> None)
      ClassUses = dL (field "classuses" xs) |> List.choose (fun a -> match a with L [ i; m ] -> Some (dI i, decInstMember m) | _ -> None)
      ClassPending = dIS (field "classpending" xs)
      ExistPack =
        dL (field "existpack" xs)
        |> List.choose (fun a ->
            match a with
            | L [ i; es ] ->
                Some (dI i,
                      dL es |> List.choose (fun e ->
                          match e with
                          | L [ S p; q; S c; ds ] -> Some (p, dI q, c, dL ds |> List.map dS)
                          | _ -> None))
            | _ -> None)
      ExistCases = dL (field "existcases" xs) |> List.choose (fun a -> match a with L [ s; i ] -> Some (dS s, dI i) | _ -> None)
      ExistMatch = dIS (field "existmatch" xs)
      DictUses = dL (field "dictuses" xs) |> List.choose (fun a -> match a with L [ i; p; q ] -> Some (dI i, (dI p, dI q)) | _ -> None)
      OpTypes = dIS (field "optypes" xs)
      ExprTypes = decExprTypes (field "exprtypes" xs)
      FieldOwners = dIS (field "fieldowners" xs)
      CompBuilders = dIS (field "compbuilders" xs)
      CustomOps = dL (field "customops" xs) |> List.choose (fun x -> match x with L [ S a; S b; S c ] -> Some (a, b, c) | _ -> None)
      CompStatements = dL (field "compstatements" xs) |> List.map dI
      CompValues = dL (field "compvalues" xs) |> List.map dI }

let private encBindResult (b : Resolve.BindResult) : Sx =
    L [ L [ A "defs"; L (b.Definitions |> List.map encDefP) ]
        L [ A "missing"; eIS b.Missing ]
        L [ A "accesserrors"; eIS b.AccessErrors ]
        L [ A "resolutions"; encResolutions b.Resolutions ]
        L [ A "exports"; L (b.Exports |> List.map (fun (k, d) -> L [ S k; encDefP d ])) ]
        L [ A "members"; L (b.Members |> List.map (fun (k, d) -> L [ S k; encDefP d ])) ] ]

let private decBindResult (x : Sx) : Resolve.BindResult =
    let xs = dL x
    let kd (y : Sx) = match y with L [ S k; d ] -> Some (k, decDefP d) | _ -> None
    { Definitions = dL (field "defs" xs) |> List.map decDefP
      Missing = dIS (field "missing" xs)
      AccessErrors = dIS (field "accesserrors" xs)
      Resolutions = decResolutions (field "resolutions" xs)
      Exports = dL (field "exports" xs) |> List.choose kd
      Members = dL (field "members" xs) |> List.choose kd }

let private preludeTag = "fppprelude1"

let private encodeSnapshotSx (s : PreludeSnapshot) : Sx =
    L [ A preludeTag
        L [ A "idsupply"; aI s.PIdSupply ]
        L [ A "srchash"; S s.PSrcHash ]
        L [ A "imports"; encMap encDefP s.PImports ]
        L [ A "members"; encMap encDefP s.PMembers ]
        L [ A "schemes"; encMap encScheme s.PSchemes ]
        L [ A "aliases"; encMap encVarsTy s.PAliases ]
        L [ A "fields"; encMap encFieldInfo s.PFields ]
        L [ A "ifaces"; encMap (fun ms -> L (ms |> List.map (fun (n, a) -> L [ S n; aI a ]))) s.PIfaces ]
        L [ A "bases"; encMap encVarsTy s.PBases ]
        L [ A "impls"; encMap (fun ss -> L (ss |> List.map S)) s.PImpls ]
        L [ A "impltys"; encMap (fun ts -> L (ts |> List.map encVarsTy)) s.PImplTys ]
        L [ A "structtypes"; encMap aB s.PStructTypes ]
        L [ A "ctors"; encMap (fun cs -> L (cs |> List.map (fun (n, sc) -> L [ aI n; encScheme sc ]))) s.PCtors ]
        L [ A "classes"; encTables s.PClasses ]
        L [ A "inferred"; encInferResult s.PInferred ]
        L [ A "bind"; encBindResult s.PBind ]
        // LAST: every encoder above feeds the sink, so the variable table is
        // only complete once they have all run
        L [ A "vars"
            L (dictPairs varSink
               |> List.sortWith (fun (a, _) (b, _) -> compare a b)
               |> List.map (fun (_, v) -> L [ aI v.Id; aI v.Level; aB v.Rigid ])) ] ]

let private decodeSnapshotSx (x : Sx) : PreludeSnapshot option =
    match x with
    | L (A t :: xs) when t = preludeTag ->
        let snap =
            { PIdSupply = dI (field "idsupply" xs)
              PSrcHash = dS (field "srchash" xs)
              PImports = decMap decDefP (field "imports" xs)
              PMembers = decMap decDefP (field "members" xs)
              PSchemes = decMap decScheme (field "schemes" xs)
              PAliases = decMap decVarsTy (field "aliases" xs)
              PFields = decMap decFieldInfo (field "fields" xs)
              PIfaces =
                decMap (fun m -> dL m |> List.choose (fun a -> match a with L [ n; ar ] -> Some (dS n, dI ar) | _ -> None))
                       (field "ifaces" xs)
              PBases = decMap decVarsTy (field "bases" xs)
              PImpls = decMap (fun m -> dL m |> List.map dS) (field "impls" xs)
              PImplTys = decMap (fun m -> dL m |> List.map decVarsTy) (field "impltys" xs)
              PStructTypes = decMap dB (field "structtypes" xs)
              PCtors =
                decMap (fun m -> dL m |> List.choose (fun a -> match a with L [ n; sc ] -> Some (dI n, decScheme sc) | _ -> None))
                       (field "ctors" xs)
              PClasses = decTables (field "classes" xs)
              PInferred = decInferResult (field "inferred" xs)
              PBind = decBindResult (field "bind" xs) }
        // levels and rigidity, applied once every variable exists
        for it in dL (field "vars" xs) do
            match it with
            | L [ i; lv; rg ] ->
                let v = varById (dS i)
                v.Level <- dI lv
                v.Rigid <- dB rg
            | _ -> ()
        Some snap
    | _ -> None

/// Write a snapshot — and PROVE it reads back first. `decExpr` answers unit
/// for a node it does not know, so a codec gap is silent; re-encoding what
/// was decoded and comparing the text is what turns that into a refusal.
/// Answers None when the snapshot does not survive the trip.
let encodePrelude (s : PreludeSnapshot) : string option =
    varSink <- dictNew<int, Var> ()
    collectVars <- true
    let text = toText (encodeSnapshotSx s)
    collectVars <- false
    let savedMode = preludeMode
    let savedVars = dictPairs preludeVars
    preludeMode <- true
    for k, _ in savedVars do dictRemove preludeVars k
    let again =
        match decodeSnapshotSx (parse text) with
        | Some back ->
            varSink <- dictNew<int, Var> ()
            collectVars <- true
            let t2 = toText (encodeSnapshotSx back)
            collectVars <- false
            Some t2
        | None -> None
    for k, _ in dictPairs preludeVars do dictRemove preludeVars k
    for k, v in savedVars do dictSet preludeVars k v
    preludeMode <- savedMode
    match again with
    | Some t2 when t2 = text -> Some text
    | _ -> None

let decodePrelude (text : string) : PreludeSnapshot option =
    let saved = preludeMode
    preludeMode <- true
    for k, _ in dictPairs preludeVars do dictRemove preludeVars k
    let r = decodeSnapshotSx (parse text)
    preludeMode <- saved
    r

/// What a library carries. Exports and schemes and decls are what it always
/// carried; the TABLES are what it did not, and their absence is why a
/// library was only usable for plain functions.
///
/// A class declared in a library (`class Real<'a>` in fpp.base) put its
/// instances in the producer's class table and nowhere else, so the
/// consumer met `$class:Real:Pi:float` — a marker naming an instance member
/// — with no instance to resolve it against, and the backend stubbed the
/// enclosing function. `--strict` named it; an ordinary build trapped at
/// whichever global initializer touched it first. The same hole took type
/// MEMBERS with it: `fields` is where `.Dot` on a library type is found.
type LibContents =
    { LExports : (string * Resolve.Definition) list
      LSchemes : (string * Scheme) list
      LDecls : Decl list
      LFields : Dict<string, Infer.FieldInfo>
      LClasses : Classes.Tables
      LIfaces : Dict<string, (string * int) list>
      LBases : Dict<string, Var list * Type>
      LImpls : Dict<string, string list>
      LImplTys : Dict<string, (Var list * Type) list>
      LStructTypes : Dict<string, bool>
      LCtors : Dict<string, (int * Scheme) list>
      LAliases : Dict<string, Var list * Type> }

let emptyLib () : LibContents =
    { LExports = []; LSchemes = []; LDecls = []
      LFields = dictNew<string, Infer.FieldInfo> ()
      LClasses = Classes.newTables ()
      LIfaces = dictNew<string, (string * int) list> ()
      LBases = dictNew<string, Var list * Type> ()
      LImpls = dictNew<string, string list> ()
      LImplTys = dictNew<string, (Var list * Type) list> ()
      LStructTypes = dictNew<string, bool> ()
      LCtors = dictNew<string, (int * Scheme) list> ()
      LAliases = dictNew<string, Var list * Type> () }

/// A library: exports for the resolver, schemes and TABLES for inference,
/// decls for emission and (later) instantiation.
let encodeLib (c : LibContents) : string =
    toText (L [ A "fppir2"
                L (A "x" :: List.map encDef c.LExports)
                L (A "s" :: (c.LSchemes |> List.map (fun (k, sc) -> L [ S k; encScheme sc ])))
                L (A "d" :: List.map encDecl c.LDecls)
                L [ A "fields"; encMap encFieldInfo c.LFields ]
                L [ A "classes"; encTables c.LClasses ]
                L [ A "ifaces"; encMap (fun ms -> L (ms |> List.map (fun (n, ar) -> L [ S n; aI ar ]))) c.LIfaces ]
                L [ A "bases"; encMap encVarsTy c.LBases ]
                L [ A "impls"; encMap (fun ss -> L (ss |> List.map S)) c.LImpls ]
                L [ A "impltys"; encMap (fun ts -> L (ts |> List.map encVarsTy)) c.LImplTys ]
                L [ A "structtypes"; encMap aB c.LStructTypes ]
                L [ A "ctors"; encMap (fun cs -> L (cs |> List.map (fun (n, sc) -> L [ aI n; encScheme sc ]))) c.LCtors ]
                L [ A "aliases"; encMap encVarsTy c.LAliases ] ])

/// Reads both shapes. `fppir1` — exports, schemes, decls and nothing else —
/// is what every library built before the tables existed; it still loads,
/// and still cannot resolve a class or a member declared inside it.
let decodeLib (text : string) : LibContents =
    // a TABLE section is `(tag value)` — one child, unwrapped
    let named (xs : Sx list) (tag : string) : Sx =
        match xs |> List.tryPick (fun x -> match x with L (A t :: rest) when t = tag -> Some rest | _ -> None) with
        | Some [ one ] -> one
        | Some rest -> L rest
        | None -> L []
    // a LIST section is `(tag item item ...)` and is VARIADIC, so it must
    // never unwrap: a library with exactly one export, scheme or decl would
    // otherwise hand back that item's children in its place — which is how
    // a one-function package stopped resolving its own name
    let section (xs : Sx list) (tag : string) : Sx list =
        match xs |> List.tryPick (fun x -> match x with L (A t :: rest) when t = tag -> Some rest | _ -> None) with
        | Some rest -> rest
        | None -> []
    let decls (xs : Sx list) =
        section xs "d"
        |> List.choose decDecl
        |> List.map (fun d ->
            match d with
            | DLet (rc, v, sc, b) -> DLet (rc, v, sc, remapDeclMarkers b)
            | other -> other)
    let exportsOf (xs : Sx list) = section xs "x" |> List.choose decDef
    let schemesOf (xs : Sx list) =
        section xs "s"
        |> List.choose (fun sx -> match sx with L [ S k; sch ] -> Some (k, decScheme sch) | _ -> None)
    // spelled out rather than `{ emptyLib () with ... }`: copy-and-update
    // over a CALL is not in the self-hosting subset — it reached Lower as an
    // unresolved `BraceExpr` and the fixpoint stopped with "not lowerable:
    // computation/sequence body", naming no line
    match parse text with
    | L (A "fppir2" :: xs) ->
        { LExports = exportsOf xs
          LSchemes = schemesOf xs
          LDecls = decls xs
          LFields = decMap decFieldInfo (named xs "fields")
          LClasses = decTables (named xs "classes")
          LIfaces =
            decMap (fun m -> dL m |> List.choose (fun e -> match e with L [ n; ar ] -> Some (dS n, dI ar) | _ -> None))
                   (named xs "ifaces")
          LBases = decMap decVarsTy (named xs "bases")
          LImpls = decMap (fun m -> dL m |> List.map dS) (named xs "impls")
          LImplTys = decMap (fun m -> dL m |> List.map decVarsTy) (named xs "impltys")
          LStructTypes = decMap dB (named xs "structtypes")
          LCtors =
            decMap (fun m -> dL m |> List.choose (fun e -> match e with L [ n; sc ] -> Some (dI n, decScheme sc) | _ -> None))
                   (named xs "ctors")
          LAliases = decMap decVarsTy (named xs "aliases") }
    | L (A "fppir1" :: xs) ->
        { LExports = exportsOf xs
          LSchemes = schemesOf xs
          LDecls = decls xs
          LFields = dictNew<string, Infer.FieldInfo> ()
          LClasses = Classes.newTables ()
          LIfaces = dictNew<string, (string * int) list> ()
          LBases = dictNew<string, Var list * Type> ()
          LImpls = dictNew<string, string list> ()
          LImplTys = dictNew<string, (Var list * Type) list> ()
          LStructTypes = dictNew<string, bool> ()
          LCtors = dictNew<string, (int * Scheme) list> ()
          LAliases = dictNew<string, Var list * Type> () }
    | _ -> emptyLib ()

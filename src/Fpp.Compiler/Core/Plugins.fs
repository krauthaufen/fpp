module Fpp.Core.Plugins

open Fpp.Prelude
open Fpp.Syntax
open Fpp.Analysis.Types
open Fpp.Core.Ir

// Compiler plugins: deterministic TAST -> TAST transforms over typed core.
// Registered in project config (never via source annotations), run in order
// after lowering and before linking; the core linter validates each
// plugin's output, so a broken plugin is a compiler error naming it rather
// than a miscompilation. Annotation-free derivation is practical because
// dead-code elimination drops whatever nobody calls.

type Plugin =
    { Name : string
      /// per-file: sees one file's declarations, returns replacements
      PerFile : Decl list -> Decl list
      /// whole-program: sees everything at link time (registries, tables)
      WholeProgram : Decl list -> Decl list }

// ---- generators: declarations that go through the FRONT END ---------------
//
// A PerFile/WholeProgram plugin rewrites LOWERED core, which is too late to
// declare a type, a class or an instance: resolution and inference are over,
// and the IR keeps field KINDS rather than field types. A Generator instead
// runs BEFORE analysis and returns SOURCE, which is compiled like any other
// file — so it can emit anything the language has.
//
// STAGING RULE: a generator sees the program's HAND-WRITTEN declarations only,
// never another generator's output, and generation runs exactly ONCE. Generated
// code may freely REFERENCE other generated code — it is all compiled together,
// and generated files come last in compile order — but a generator cannot
// INSPECT what another produced. One round, no fixpoint to reach, and the
// output never depends on the order plugins were registered.

type GenField =
    { FName : string
      /// the field's type AS WRITTEN, ready to be emitted back into source
      FType : string }

type GenCase =
    { CName : string
      /// one entry per payload type, as written
      CArgs : string list }

type GenTypeDecl =
    { TName : string
      TParams : string list
      /// "record" | "union" | "other"
      TKind : string
      TFields : GenField list
      TCases : GenCase list
      TFile : string
      /// the module that declares it, "" at file top level. A type NAME is
      /// visible across files regardless, but a union CASE is not: generated
      /// code has to `open` this.
      TModule : string }

/// What a generator gets to look at: the hand-written declarations.
type ProgramView = { Types : GenTypeDecl list }

type Generator =
    { GName : string
      /// returns (path, source) pairs; the path only names the file in
      /// diagnostics, so keep it stable across runs
      Generate : ProgramView -> (string * string) list }

/// the node kinds that spell a TYPE (Lower has its own copy, inside a closure)
let private isTypeNode (k : NodeKind) =
    k = NamedType || k = VarType || k = AnonType || k = TupleType || k = StructTupleType
    || k = FunType || k = AppType || k = PostfixType || k = ParenType

let private nodes (n : GreenNode) =
    n.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)

let private toks (n : GreenNode) =
    n.Children |> List.choose (fun c -> match c with GToken t -> Some t | _ -> None)

/// the source text of a type node, reassembled from its tokens
let private typeText (n : GreenNode) =
    Green.tokens (GNode n) |> List.map (fun t -> t.Text) |> String.concat ""

/// Every type declaration in a parse tree, at any module depth.
let typeDeclsOf (path : string) (root : GreenNode) : GenTypeDecl list =
    let out = vecNew<GenTypeDecl> ()
    let rec walk (modName : string) (n : GreenNode) =
        if n.NodeKind = TypeDecl then
            let name =
                toks n
                |> List.filter (fun t -> t.Kind = Ident)
                |> List.tryHead
                |> Option.map (fun t -> t.Text)
            let tyParams =
                nodes n
                |> List.filter (fun m -> m.NodeKind = TyParams)
                |> List.collect (fun m -> Green.tokens (GNode m))
                |> List.filter (fun t -> t.Kind = Ident && t.Text <> "_")
                |> List.map (fun t -> t.Text)
            let fields =
                nodes n
                |> List.filter (fun m -> m.NodeKind = RecordRepr)
                |> List.collect nodes
                |> List.filter (fun m -> m.NodeKind = RecordField)
                |> List.choose (fun f ->
                    let fn = toks f |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead
                    let ft = nodes f |> List.tryFind (fun x -> isTypeNode x.NodeKind)
                    match fn, ft with
                    | Some a, Some b -> Some { FName = a.Text; FType = typeText b }
                    | _ -> None)
            let cases =
                nodes n
                |> List.filter (fun m -> m.NodeKind = UnionCase)
                |> List.choose (fun c ->
                    match toks c |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead with
                    | Some nt ->
                        Some { CName = nt.Text
                               CArgs =
                                 nodes c
                                 |> List.filter (fun x -> isTypeNode x.NodeKind)
                                 |> List.map typeText }
                    | None -> None)
            (match name with
             | Some nm ->
                 let kind =
                     if not (List.isEmpty cases) then "union"
                     elif not (List.isEmpty fields) then "record"
                     else "other"
                 vecAdd out
                     { TName = nm; TParams = tyParams; TKind = kind
                       TFields = fields; TCases = cases; TFile = path; TModule = modName }
             | None -> ())
        // `module X` is a HEADER: a sibling of the declarations it scopes, not
        // their parent, so its name flows to the following siblings. A nested
        // `module X = ...` (ModuleDef) scopes only its own subtree.
        let nameOf (m : GreenNode) =
            Green.tokens (GNode m)
            |> List.filter (fun t -> t.Kind = Ident)
            |> List.map (fun t -> t.Text)
            |> String.concat "."
        let mutable scope = modName
        for c in nodes n do
            if c.NodeKind = ModuleHeader then
                let nm = nameOf c
                if nm <> "" then scope <- nm
            elif c.NodeKind = ModuleDef then
                let nm = nameOf c
                walk (if nm = "" then scope else nm) c
            else walk scope c
    walk "" root
    vecToList out

let idPlugin (name : string) =
    { Name = name; PerFile = id; WholeProgram = id }

// ---- constant folding: the simplest real TAST -> TAST rewrite ------------

let constFold =
    let rec foldE (e : Expr) : Expr =
        match e with
        | EPrim (op, [ a; b ]) ->
            let a2 = foldE a
            let b2 = foldE b
            (match a2, b2 with
             | ELit (LInt x), ELit (LInt y) ->
                 let xi = int x
                 let yi = int y
                 (match op with
                  | "+" -> ELit (LInt (string (xi + yi)))
                  | "-" -> ELit (LInt (string (xi - yi)))
                  | "*" -> ELit (LInt (string (xi * yi)))
                  | _ -> EPrim (op, [ a2; b2 ]))
             | _ -> EPrim (op, [ a2; b2 ]))
        | EPrim (op, xs) -> EPrim (op, List.map foldE xs)
        | EVarI (v, s, i) -> EVarI (v, s, i)
        | ELam (ps, b) -> ELam (ps, foldE b)
        | EApp (f, args) -> EApp (foldE f, List.map foldE args)
        | ELet (r, v, s, rhs, body) -> ELet (r, v, s, foldE rhs, foldE body)
        | EIf (c, t, f) -> EIf (foldE c, foldE t, foldE f)
        | EMatch (s, cs) -> EMatch (foldE s, cs |> List.map (fun (p, g, b) -> p, Option.map foldE g, foldE b))
        | ETuple xs -> ETuple (List.map foldE xs)
        | EListLit xs -> EListLit (List.map foldE xs)
        | ESeq xs -> ESeq (List.map foldE xs)
        | ECtor (n, s, xs) -> ECtor (n, s, List.map foldE xs)
        | ERecord (n, fs) -> ERecord (n, fs |> List.map (fun (f, v) -> f, foldE v))
        | EField (r, f, o) -> EField (foldE r, f, o)
        | EFieldSet (r, f, o, v) -> EFieldSet (foldE r, f, o, foldE v)
        | ERecordExt (n, b, fs) -> ERecordExt (n, foldE b, fs |> List.map (fun (k, v) -> k, foldE v))
        | EIfaceCall (i, m, r, args) -> EIfaceCall (i, m, foldE r, List.map foldE args)
        | ECast (t, e, d) -> ECast (t, foldE e, d)
        | ETypeTest (t, e) -> ETypeTest (t, foldE e)
        | EWhile (c, b) -> EWhile (foldE c, foldE b)
        | EAssign (v, x) -> EAssign (v, foldE x)
        | EArray (n, xs) -> EArray (n, List.map foldE xs)
        | EIndex (n, a, i) -> EIndex (n, foldE a, foldE i)
        | EIndexSet (n, a, i, v) -> EIndexSet (n, foldE a, foldE i, foldE v)
        | EArrayLen (n, a) -> EArrayLen (n, foldE a)
        | EArrayCreate (n, a, b) -> EArrayCreate (n, foldE a, foldE b)
        | ETry (b, cs) -> ETry (foldE b, cs |> List.map (fun (p, g, x) -> p, Option.map foldE g, foldE x))
        | other -> other
    let perFile (ds : Decl list) =
        ds |> List.map (fun d ->
            match d with
            | DLet (r, v, s, e) -> DLet (r, v, s, foldE e)
            | other -> other)
    { Name = "constFold"; PerFile = perFile; WholeProgram = id }

// ---- derive shallowEquals for every record/struct type ------------------
// Emits `shallowEq_<Type> a b` comparing fields one level deep: scalars by
// value, references by identity. No annotations; DCE removes unused ones.

let deriveShallowEquals =
    let perFile (ds : Decl list) =
        let extra = vecNew<Decl> ()
        let mutable off = 900000
        for d in ds do
            match d with
            | DRecord (name, _, fields, _) when not (List.isEmpty fields) ->
                off <- off + 1
                let path = "(derive)"
                let fn = { Path = path; Offset = off; Name = "shallowEq_" + name }
                let av = { Path = path; Offset = off + 100000; Name = "a" }
                let bv = { Path = path; Offset = off + 200000; Name = "b" }
                let sch = mono (TCon ("?", []))
                let cmpField (f : string, kind : string) =
                    let ea = EField (EVar (av, sch), f, name)
                    let eb = EField (EVar (bv, sch), f, name)
                    if kind = "r" then EApp (EUnknown "refEq", [ ea; eb ])
                    else EPrim ("=", [ ea; eb ])
                let body =
                    fields
                    |> List.map cmpField
                    |> List.reduce (fun x y -> EPrim ("&&", [ x; y ]))
                vecAdd extra (DLet (false, fn, sch, ELam ([ av, sch; bv, sch ], body)))
            | _ -> ()
        ds @ vecToList extra
    { Name = "deriveShallowEquals"; PerFile = perFile; WholeProgram = id }

// ---- building generated code as DATA, not text ----------------------------
//
// Source is the wire format between a generator and the compiler, but nobody
// should have to write it: indentation is significant, quotes need escaping,
// and a missing paren surfaces as a parse error in a file the user never wrote.
// Declarations are built as values here and rendered once, correctly.

type GTy =
    | GTyName of string
    | GTyVar of string
    | GTyApp of string * GTy list
    | GTyFun of GTy * GTy
    /// escape hatch: a type spelled exactly as given
    | GTyRaw of string

type GPat =
    | GPWild
    | GPVar of string
    /// a union case and the names it binds
    | GPCase of string * string list

type GEx =
    | GInt of int
    | GStr of string
    | GBool of bool
    | GVar of string
    | GApp of GEx * GEx list
    | GBin of string * GEx * GEx
    | GLam of string list * GEx
    /// `let n = v` followed by the rest — a statement, so only valid in a body
    | GLet of string * GEx * GEx
    | GRec of (string * GEx) list
    | GRecWith of GEx * (string * GEx) list
    | GField of GEx * string
    | GMatch of GEx * (GPat * GEx) list
    | GIf of GEx * GEx * GEx
    | GTuple of GEx list
    | GList of GEx list
    /// escape hatch: an expression spelled exactly as given
    | GRaw of string

type GMember =
    { MName : string
      MParams : (string * GTy option) list
      MBody : GEx }

type GDecl =
    | GComment of string
    | GOpen of string
    | GValue of string * (string * GTy option) list * GTy option * GEx
    | GRecordType of string * string list * (string * GTy) list
    | GUnionType of string * string list * (string * GTy list) list
    /// class name, type variables, member signatures
    | GClassOf of string * string list * (string * GTy) list
    /// class name, head types, member bodies
    | GInstanceOf of string * GTy list * GMember list

let rec tyText (t : GTy) : string =
    match t with
    | GTyName n -> n
    | GTyVar v -> "'" + v
    | GTyApp (n, args) -> n + "<" + String.concat ", " (List.map tyText args) + ">"
    | GTyFun (a, b) -> "(" + tyText a + " -> " + tyText b + ")"
    | GTyRaw s -> s

/// F++ string literals take the same escapes F# does
let strLit (s : string) : string =
    let mutable out = ""
    for ch in s do
        if ch = '\\' then out <- out + "\\\\"
        elif ch = '"' then out <- out + "\\\""
        elif ch = '\n' then out <- out + "\\n"
        elif ch = '\t' then out <- out + "\\t"
        else out <- out + string ch
    "\"" + out + "\""

let private patText (p : GPat) : string =
    match p with
    | GPWild -> "_"
    | GPVar v -> v
    | GPCase (n, []) -> n
    | GPCase (n, args) -> n + " " + String.concat " " args

/// One line, or None when the shape needs several (a `let` sequence, a match).
let rec private inlineOf (e : GEx) : string option =
    // annotated because the self-hosted checker otherwise reads the result as
    // IEnumerable<string> and String.concat wants a list
    let all (xs : GEx list) : string list option =
        let rendered = List.map inlineOf xs
        if rendered |> List.exists (fun r -> r.IsNone) then None
        else Some (rendered |> List.map (fun r -> match r with Some x -> x | None -> ""))
    match e with
    | GInt i -> Some (string i)
    | GStr s -> Some (strLit s)
    | GBool b -> Some (if b then "true" else "false")
    | GVar v -> Some v
    | GRaw s -> Some s
    | GField (t, f) -> inlineOf t |> Option.map (fun x -> x + "." + f)
    | GApp (f, args) ->
        match inlineOf f, all args with
        | Some fs, Some argTexts -> Some ("(" + fs + " " + String.concat " " argTexts + ")")
        | _ -> None
    | GBin (op, a, b) ->
        match inlineOf a, inlineOf b with
        | Some x, Some y -> Some ("(" + x + " " + op + " " + y + ")")
        | _ -> None
    | GLam (ps, body) ->
        inlineOf body |> Option.map (fun b -> "(fun " + String.concat " " ps + " -> " + b + ")")
    | GIf (c, t, f) ->
        match inlineOf c, inlineOf t, inlineOf f with
        | Some cs, Some ts, Some fs -> Some ("(if " + cs + " then " + ts + " else " + fs + ")")
        | _ -> None
    | GTuple xs -> all xs |> Option.map (fun (ts : string list) -> "(" + String.concat ", " ts + ")")
    | GList xs -> all xs |> Option.map (fun (ts : string list) -> "[ " + String.concat "; " ts + " ]")
    | GRec fields ->
        // rendered per field rather than through List.map2: pairing two lists
        // is one construct the self-hosted checker reads differently
        let parts = fields |> List.map (fun (n, v) -> inlineOf v |> Option.map (fun t -> n + " = " + t))
        if parts |> List.exists (fun (t : string option) -> t.IsNone) then None
        else
            let texts = parts |> List.map (fun (t : string option) -> match t with Some x -> x | None -> "")
            Some ("{ " + String.concat "; " texts + " }")
    | GRecWith (b, fields) ->
        let parts = fields |> List.map (fun (n, v) -> inlineOf v |> Option.map (fun t -> n + " = " + t))
        if parts |> List.exists (fun (t : string option) -> t.IsNone) then None
        else
            let texts = parts |> List.map (fun (t : string option) -> match t with Some x -> x | None -> "")
            match inlineOf b with
            | Some bs -> Some ("{ " + bs + " with " + String.concat "; " texts + " }")
            | None -> None
    // a `let` sequence is statements, and a match reads far better broken up
    | GLet (_, _, _) -> None
    | GMatch (_, _) -> None

let private pad (n : int) = String.replicate n " "

/// An expression as lines at the given indent. Anything that cannot be one
/// line becomes several, with the layout the parser accepts.
let rec exLines (ind : int) (e : GEx) : string list =
    let fits (one : string) =
        // generated code gets READ: keep a one-liner only while it is one
        ind + one.Length <= 96
    match inlineOf e with
    | Some one when fits one -> [ pad ind + one ]
    | _ ->
        match e with
        | GLet (n, v, rest) ->
            (match inlineOf v with
             | Some vs -> [ pad ind + "let " + n + " = " + vs ]
             | None -> (pad ind + "let " + n + " =") :: exLines (ind + 4) v)
            @ exLines ind rest
        | GMatch (scr, arms) ->
            let head =
                match inlineOf scr with
                | Some s -> pad ind + "match " + s + " with"
                | None -> pad ind + "match " + String.concat " " (List.map (fun (l : string) -> l.Trim ()) (exLines 0 scr)) + " with"
            head
            :: (arms
                |> List.collect (fun (p, body) ->
                    match inlineOf body with
                    | Some b -> [ pad ind + "| " + patText p + " -> " + b ]
                    | None -> (pad ind + "| " + patText p + " ->") :: exLines (ind + 4) body))
        | GRec fields ->
            // `{ f = v` then the rest aligned under it, closing on the last
            let rendered =
                fields
                |> List.map (fun (n, v) ->
                    match inlineOf v with
                    | Some vs -> [ n + " = " + vs ]
                    | None ->
                        let inner = exLines (ind + 6) v
                        (n + " =") :: inner)
            let flat =
                rendered
                |> List.mapi (fun i ls ->
                    ls |> List.mapi (fun j l ->
                        if i = 0 && j = 0 then pad ind + "{ " + l
                        elif j = 0 then pad (ind + 2) + l
                        else l))
                |> List.concat
            match List.rev flat with
            | last :: before -> List.rev ((last + " }") :: before)
            | [] -> [ pad ind + "{ }" ]
        | GLam (ps, body) ->
            let head = pad ind + "(fun " + String.concat " " ps + " ->"
            let inner = exLines (ind + 4) body
            (match List.rev inner with
             | last :: before -> head :: List.rev ((last + ")") :: before)
             | [] -> [ head + ")" ])
        | GIf (c, t, f) ->
            let cs = match inlineOf c with Some x -> x | None -> "(* cond *)"
            (pad ind + "if " + cs + " then")
            :: exLines (ind + 4) t
            @ [ pad ind + "else" ]
            @ exLines (ind + 4) f
        | other ->
            // every remaining shape is inline-able by construction
            // never silently: an unbound name here names the bug in the error
            [ pad ind + (match inlineOf other with Some x -> x | None -> "__generator_cannot_render__") ]

let private paramText (ps : (string * GTy option) list) =
    ps
    |> List.map (fun (n, t) ->
        match t with
        | Some ty -> "(" + n + " : " + tyText ty + ")"
        | None -> n)
    |> String.concat " "

let declLines (d : GDecl) : string list =
    match d with
    | GComment c -> [ "// " + c ]
    | GOpen m -> [ "open " + m ]
    | GValue (name, ps, ret, body) ->
        let head =
            "let " + name
            + (if List.isEmpty ps then "" else " " + paramText ps)
            + (match ret with Some t -> " : " + tyText t | None -> "")
            + " ="
        (match inlineOf body with
         | Some one when one.Length + head.Length < 70 -> [ head + " " + one ]
         | _ -> head :: exLines 4 body)
    | GRecordType (name, ps, fields) ->
        let tp = if List.isEmpty ps then "" else "<" + String.concat ", " (List.map (fun p -> "'" + p) ps) + ">"
        [ "type " + name + tp + " ="
          "    { " + String.concat "; " (fields |> List.map (fun (n, t) -> n + " : " + tyText t)) + " }" ]
    | GUnionType (name, ps, cases) ->
        let tp = if List.isEmpty ps then "" else "<" + String.concat ", " (List.map (fun p -> "'" + p) ps) + ">"
        ("type " + name + tp + " =")
        :: (cases
            |> List.map (fun (cn, args) ->
                if List.isEmpty args then "    | " + cn
                else "    | " + cn + " of " + String.concat " * " (List.map tyText args)))
    | GClassOf (name, tvs, members) ->
        ("class " + name + "<" + String.concat ", " (List.map (fun v -> "'" + v) tvs) + ">")
        :: (members |> List.map (fun (mn, mt) -> "    static " + mn + " : " + tyText mt))
    | GInstanceOf (name, heads, members) ->
        ("instance " + name + "<" + String.concat ", " (List.map tyText heads) + ">")
        :: (members
            |> List.collect (fun m ->
                let head =
                    "    static " + m.MName
                    + (if List.isEmpty m.MParams then "" else " " + paramText m.MParams)
                    + " ="
                match inlineOf m.MBody with
                | Some one -> [ head + " " + one ]
                | None -> head :: exLines 8 m.MBody))

/// A whole generated file. No module header on purpose: top-level bindings are
/// what a later file can name without an `open`.
let renderFile (decls : GDecl list) : string =
    let spaced (d : GDecl) =
        match d with
        // a comment belongs to what follows it, and opens come in a block
        | GComment _ -> declLines d
        | GOpen _ -> declLines d
        | _ -> declLines d @ [ "" ]
    String.concat "\n" ("" :: (decls |> List.collect spaced)) + "\n"

// ---- deriveGen: a property-test generator for every user type -------------
// The generator a PerFile plugin could not write: it emits SOURCE, so the
// values it produces are ordinary `Gen<T>` records built from the field types
// the front end has not even looked at yet.
//
// Limits, each because the emitted code has to be obviously correct rather
// than clever: monomorphic types only (a generic one would need a generator
// per parameter), no recursive types (their generator needs a size bound to
// terminate), and payload types drawn from the primitives, `list`, `option`
// and other user types.

let private compact (t : string) = t.Replace (" ", "")

/// The generator EXPRESSION for a type, or None when nothing sensible exists.
let rec private genExprFor (isUser : string -> bool) (ty : string) : string option =
    let t = compact ty
    if t = "int" then Some "Gen.int"
    elif t = "bool" then Some "Gen.bool"
    elif t = "string" then Some "Gen.string"
    elif t = "float" then Some "Gen.float"
    elif t = "char" then Some "Gen.char"
    elif t.StartsWith "list<" && t.EndsWith ">" then
        genExprFor isUser (t.Substring (5, t.Length - 6)) |> Option.map (fun e -> "(Gen.list " + e + ")")
    elif t.StartsWith "Option<" && t.EndsWith ">" then
        genExprFor isUser (t.Substring (7, t.Length - 8)) |> Option.map (fun e -> "(Gen.option " + e + ")")
    elif t.EndsWith "list" && t.Length > 4 then
        genExprFor isUser (t.Substring (0, t.Length - 4)) |> Option.map (fun e -> "(Gen.list " + e + ")")
    elif t.EndsWith "option" && t.Length > 6 then
        genExprFor isUser (t.Substring (0, t.Length - 6)) |> Option.map (fun e -> "(Gen.option " + e + ")")
    elif isUser t then Some ("(gen" + t + " ())")
    else None

/// every user type name a declaration mentions, for the recursion check
let private mentions (isUser : string -> bool) (d : GenTypeDecl) : string list =
    let fromFields = d.TFields |> List.map (fun f -> compact f.FType)
    let fromCases = d.TCases |> List.collect (fun c -> c.CArgs |> List.map compact)
    (fromFields @ fromCases)
    |> List.collect (fun t ->
        // a name shows up bare, or inside list<...> / option
        [ t
          (if t.StartsWith "list<" && t.EndsWith ">" then t.Substring (5, t.Length - 6) else "")
          (if t.StartsWith "Option<" && t.EndsWith ">" then t.Substring (7, t.Length - 8) else "")
          (if t.EndsWith "list" && t.Length > 4 then t.Substring (0, t.Length - 4) else "")
          (if t.EndsWith "option" && t.Length > 6 then t.Substring (0, t.Length - 6) else "") ])
    |> List.filter isUser
    |> List.distinct

let deriveGen =
    let generate (view : ProgramView) : (string * string) list =
        let named = dictNew<string, GenTypeDecl> ()
        for t in view.Types do
            if t.TKind = "record" || t.TKind = "union" then dictSet named t.TName t
        let isUser (n : string) = (dictTryFind named n).IsSome
        // a type that reaches itself needs a size-bounded generator; skip it
        let rec reaches (seen : string list) (from : string) (target : string) : bool =
            if List.contains from seen then false
            else
                match dictTryFind named from with
                | None -> false
                | Some d ->
                    let ms = mentions isUser d
                    List.contains target ms || ms |> List.exists (fun m -> reaches (from :: seen) m target)
        let decls = vecNew<GDecl> ()
        let skipped = vecNew<string> ()
        // one `Gen<T>` per type, as DATA — the renderer worries about layout
        for name, d in dictPairs named do
            let generic = not (List.isEmpty d.TParams)
            let recursive = reaches [] name name
            if generic then vecAdd skipped (name + " (generic)")
            elif recursive then vecAdd skipped (name + " (recursive)")
            else
                let parts =
                    if d.TKind = "record" then d.TFields |> List.map (fun f -> f.FName, f.FType)
                    else d.TCases |> List.collect (fun c -> c.CArgs |> List.mapi (fun i a -> c.CName + string i, a))
                let resolved = parts |> List.map (fun (n, t) -> n, genExprFor isUser t)
                if resolved |> List.exists (fun (_, e) -> e.IsNone) then
                    vecAdd skipped (name + " (unsupported field type)")
                else
                    let slot (n : string) = GVar ("g_" + n)
                    let draw =
                        if d.TKind = "record" then
                            GLam ([ "r" ],
                                  GRec (d.TFields |> List.map (fun f -> f.FName, GApp (GField (slot f.FName, "Draw"), [ GVar "r" ]))))
                        else
                            // pick a case, then draw its payload
                            let n = List.length d.TCases
                            let build (c : GenCase) =
                                if List.isEmpty c.CArgs then GVar c.CName
                                else
                                    GApp (GVar c.CName,
                                          c.CArgs |> List.mapi (fun j _ -> GApp (GField (slot (c.CName + string j), "Draw"), [ GVar "r" ])))
                            let rec chain (i : int) (cs : GenCase list) =
                                match cs with
                                | [] -> GRaw "()"
                                | [ last ] -> build last
                                | c :: rest -> GIf (GBin ("=", GVar "k", GInt i), build c, chain (i + 1) rest)
                            GLam ([ "r" ], GLet ("k", GApp (GVar "Gen.rngBelow", [ GVar "r"; GInt n ]), chain 0 d.TCases))
                    let smaller =
                        if d.TKind = "record" && not (List.isEmpty d.TFields) then
                            // one candidate per field, each with that field shrunk
                            let per =
                                d.TFields
                                |> List.map (fun f ->
                                    GApp (GVar "List.map",
                                          [ GLam ([ "v" ], GRecWith (GVar "x", [ f.FName, GVar "v" ]))
                                            GApp (GField (slot f.FName, "Smaller"), [ GField (GVar "x", f.FName) ]) ]))
                            GLam ([ "x" ], per |> List.reduce (fun a b -> GBin ("@", a, b)))
                        else GLam ([ "x" ], GList [])
                    let render =
                        if d.TKind = "record" then
                            let body =
                                d.TFields
                                |> List.map (fun f ->
                                    GBin ("+", GStr (f.FName + " = "), GApp (GField (slot f.FName, "Render"), [ GField (GVar "x", f.FName) ])))
                                |> List.reduce (fun a b -> GBin ("+", GBin ("+", a, GStr "; "), b))
                            GLam ([ "x" ], GBin ("+", GBin ("+", GStr "{ ", body), GStr " }"))
                        else
                            GLam ([ "x" ],
                                  GMatch (GVar "x",
                                          d.TCases
                                          |> List.map (fun c ->
                                              let pats = c.CArgs |> List.mapi (fun j _ -> "a" + string j)
                                              let body =
                                                  if List.isEmpty c.CArgs then GStr c.CName
                                                  else
                                                      let shown =
                                                          c.CArgs
                                                          |> List.mapi (fun j _ ->
                                                              GApp (GField (slot (c.CName + string j), "Render"), [ GVar ("a" + string j) ]))
                                                          |> List.reduce (fun a b -> GBin ("+", GBin ("+", a, GStr " "), b))
                                                      GBin ("+", GStr (c.CName + " "), shown)
                                              GPCase (c.CName, pats), body)))
                    // the field generators, bound before the record that uses them
                    let body =
                        List.foldBack
                            (fun (n, e) acc ->
                                GLet ("g_" + n, GRaw (match e with Some x -> x | None -> "Gen.int"), acc))
                            resolved
                            (GRec [ "Draw", draw; "Smaller", smaller; "Render", render ])
                    vecAdd decls (GComment ("generated by deriveGen"))
                    vecAdd decls (GValue ("gen" + name, [ "()", None ], Some (GTyApp ("Gen", [ GTyName name ])), body))
        if vecLen decls = 0 then []
        else
            let opens =
                view.Types
                |> List.filter (fun t -> (dictTryFind named t.TName).IsSome && t.TModule <> "")
                |> List.map (fun t -> t.TModule)
                |> List.distinct
                |> List.sort
                |> List.map (fun m -> GOpen m)
            let header =
                [ GComment "deriveGen: generators for the program's own types."
                  GComment "Built as declaration DATA and rendered — see GDecl in Plugins.fs." ]
                @ (if vecLen skipped = 0 then []
                   else [ GComment ("skipped: " + String.concat ", " (vecToList skipped)) ])
            [ "deriveGen.fpp", renderFile (header @ opens @ vecToList decls) ]
    { GName = "deriveGen"; Generate = generate }

let builtinGenerators = [ deriveGen ]

let builtinPlugins = [ constFold; deriveShallowEquals ]

let byName (n : string) : Plugin option =
    builtinPlugins |> List.tryFind (fun p -> p.Name = n)

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
        let out = vecNew<string> ()
        let skipped = vecNew<string> ()
        for name, d in dictPairs named do
            let generic = not (List.isEmpty d.TParams)
            let recursive = reaches [] name name
            if generic then vecAdd skipped (name + " (generic)")
            elif recursive then vecAdd skipped (name + " (recursive)")
            else
                // one generator per field or payload, bound up front
                let parts =
                    if d.TKind = "record" then d.TFields |> List.map (fun f -> f.FName, f.FType)
                    else d.TCases |> List.collect (fun c -> c.CArgs |> List.mapi (fun i a -> c.CName + string i, a))
                let resolved = parts |> List.map (fun (n, t) -> n, t, genExprFor isUser t)
                if resolved |> List.exists (fun (_, _, e) -> e.IsNone) then
                    vecAdd skipped (name + " (unsupported field type)")
                else
                    let genOf (nm : string) =
                        match resolved |> List.tryPick (fun (n, _, e) -> if n = nm then e else None) with
                        | Some e -> e
                        | None -> "Gen.int"
                    let binds =
                        resolved
                        |> List.map (fun (n, _, e) -> "    let g_" + n + " = " + (match e with Some x -> x | None -> "Gen.int"))
                        |> String.concat "\n"
                    let body =
                        if d.TKind = "record" then
                            let draws =
                                d.TFields
                                |> List.map (fun f -> f.FName + " = g_" + f.FName + ".Draw r")
                                |> String.concat "; "
                            let smalls =
                                d.TFields
                                |> List.map (fun f ->
                                    "List.map (fun v -> { x with " + f.FName + " = v }) (g_" + f.FName + ".Smaller x." + f.FName + ")")
                                |> String.concat " @ "
                            let renders =
                                d.TFields
                                |> List.map (fun f -> "\"" + f.FName + " = \" + g_" + f.FName + ".Render x." + f.FName)
                                |> String.concat " + \"; \" + "
                            "    { Draw = (fun r -> { " + draws + " })\n"
                            + "      Smaller = (fun x -> " + (if List.isEmpty d.TFields then "[]" else smalls) + ")\n"
                            + "      Render = (fun x -> \"{ \" + " + renders + " + \" }\") }"
                        else
                            let n = List.length d.TCases
                            let drawCase (i : int) (c : GenCase) =
                                let build =
                                    if List.isEmpty c.CArgs then c.CName
                                    else c.CName + " " + (c.CArgs |> List.mapi (fun j _ -> "(g_" + c.CName + string j + ".Draw r)") |> String.concat " ")
                                if i = 0 && n = 1 then "            " + build
                                elif i = 0 then "            if k = " + string i + " then " + build
                                elif i = n - 1 then "            else " + build
                                else "            elif k = " + string i + " then " + build
                            let renderCase (c : GenCase) =
                                if List.isEmpty c.CArgs then "            | " + c.CName + " -> \"" + c.CName + "\""
                                else
                                    let pats = c.CArgs |> List.mapi (fun j _ -> "a" + string j) |> String.concat " "
                                    let shows =
                                        c.CArgs
                                        |> List.mapi (fun j _ -> "g_" + c.CName + string j + ".Render a" + string j)
                                        |> String.concat " + \" \" + "
                                    "            | " + c.CName + " " + pats + " -> \"" + c.CName + " \" + " + shows
                            "    { Draw =\n        (fun r ->\n            let k = Gen.rngBelow r " + string n + "\n"
                            + (d.TCases |> List.mapi drawCase |> String.concat "\n") + ")\n"
                            + "      Smaller = (fun x -> [])\n"
                            + "      Render =\n        (fun x ->\n            match x with\n"
                            + (d.TCases |> List.map renderCase |> String.concat "\n") + ") }"
                    ignore (genOf "")
                    vecAdd out
                        ("/// generated by deriveGen\nlet gen" + name + " () : Gen<" + name + "> =\n"
                         + (if binds = "" then "" else binds + "\n") + body)
        if vecLen out = 0 then []
        else
            let opens =
                view.Types
                |> List.filter (fun t -> (dictTryFind named t.TName).IsSome && t.TModule <> "")
                |> List.map (fun t -> t.TModule)
                |> List.distinct
                |> List.sort
                |> List.map (fun m -> "open " + m)
            let header =
                "// deriveGen: generators for the program's own types. No module header, so\n"
                + "// these are top-level bindings any later file can name without an open.\n"
                + (if vecLen skipped = 0 then ""
                   else "// skipped: " + String.concat ", " (vecToList skipped) + "\n")
            let opensText = if List.isEmpty opens then "" else String.concat "\n" opens + "\n"
            [ "deriveGen.fpp", header + "\n" + opensText + "\n" + String.concat "\n\n" (vecToList out) + "\n" ]
    { GName = "deriveGen"; Generate = generate }

let builtinGenerators = [ deriveGen ]

let builtinPlugins = [ constFold; deriveShallowEquals ]

let byName (n : string) : Plugin option =
    builtinPlugins |> List.tryFind (fun p -> p.Name = n)

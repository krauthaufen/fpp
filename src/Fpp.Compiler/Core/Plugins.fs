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
      /// "record" | "union" | "class" | "abbrev" | "other". A class is
      /// distinguished by having a constructor or members; an abbreviation by
      /// being nothing but a type.
      TKind : string
      TFields : GenField list
      TCases : GenCase list
      TFile : string
      /// the module that declares it, "" at file top level. A type NAME is
      /// visible across files regardless, but a union CASE is not: generated
      /// code has to `open` this.
      TModule : string
      /// the `[<...>]` attributes written on it, name first then any literal
      /// arguments — this is how a generator is TOLD what to derive, rather
      /// than deriving for everything in sight
      TAttrs : (string * string list) list
      /// for a class: the members it declares, by name
      TMembers : string list }

type GenValueDecl =
    { VName : string
      /// parameters as written: name and, where annotated, type
      VParams : (string * string) list
      /// the return type when annotated, "" otherwise
      VReturn : string
      VFile : string
      VModule : string
      VAttrs : (string * string list) list }

let private isPatNodeK (k : NodeKind) =
    k = IdentPat || k = WildcardPat || k = LiteralPat || k = TuplePat || k = StructTuplePat
    || k = ConsPat || k = AppPat || k = ParenPat || k = ListPat || k = AsPat || k = TypeTestPat
    || k = SplicePat

let private isTypeNode (k : NodeKind) =
    k = NamedType || k = VarType || k = AnonType || k = TupleType || k = StructTupleType
    || k = FunType || k = AppType || k = PostfixType || k = ParenType

let private isExprNode (k : NodeKind) =
    not (isPatNodeK k) && not (isTypeNode k) && k <> TyParams && k <> AttributeList

let private nodes (n : GreenNode) =
    n.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)

let private toks (n : GreenNode) =
    n.Children |> List.choose (fun c -> match c with GToken t -> Some t | _ -> None)

/// the source text of a type node, reassembled from its tokens
let private typeText (n : GreenNode) =
    Green.tokens (GNode n) |> List.map (fun t -> t.Text) |> String.concat ""


/// Where a node starts and ends in the source, so a rewrite can cut exactly.
/// Where a node starts and ends in the source, so a rewrite can cut exactly.
let nodeSpan (n : GreenNode) : int * int =
    match Green.tokens (GNode n) |> List.filter (fun t -> t.Kind <> Eof) with
    | [] -> 0, 0
    | toks ->
        let first = List.head toks
        let last = List.last toks
        first.Offset, last.Offset + last.Text.Length

// ---- the typed tree -------------------------------------------------------
// A REAL typed tree: every node carries the type inference settled on, so a
// plugin pattern matches on shape and reads types off the node rather than
// looking offsets up in a side table. `TOther` keeps the walk TOTAL — a
// construct without its own case still appears, with its kind and its type,
// so nothing is silently dropped.

type TExpr =
    | TLit of string * string
    | TName of string * string
    | TApp of TExpr * TExpr list * string
    | TBin of string * TExpr * TExpr * string
    | TLam of string list * TExpr * string
    | TLet of string * TExpr * TExpr * string
    | TIf of TExpr * TExpr * TExpr * string
    | TMatch of TExpr * (string * TExpr) list * string
    | TField of TExpr * string * string
    | TTuple of TExpr list * string
    | TList of TExpr list * string
    /// node kind and type, for a construct with no case of its own
    | TOther of string * string

/// the type of any node, without caring which shape it is
let typeOfT (e : TExpr) : string =
    match e with
    | TLit (_, t) | TName (_, t) | TApp (_, _, t) | TBin (_, _, _, t)
    | TLam (_, _, t) | TLet (_, _, _, t) | TIf (_, _, _, t)
    | TMatch (_, _, t) | TField (_, _, t) | TTuple (_, t)
    | TList (_, t) | TOther (_, t) -> t

type TDecl =
    /// name, parameters with their types, return type, body
    | TDLet of string * (string * string) list * string * TExpr
    /// name, kind ("record" | "union" | "class" | ...)
    | TDType of string * string
    | TDOther of string

/// One hand-written file: its parse tree, and the type inference gave each
/// DEFINITION in it. (Per-EXPRESSION types are not exposed: this compiler keeps
/// typing in side tables keyed by definition, so that is what there is to give.)
type GenFile =
    { FPath : string
      FTree : GreenNode
      /// the type at a definition's offset, where inference has one
      FTypeAt : int -> string option
      /// the file as a TYPED TREE — every expression node with its type
      FTast : TDecl list }

/// What a generator RETURNS for a file.
type GenOutput =
    /// the file's whole text
    | Source of string
    /// a syntax tree, rendered back to source by the compiler
    | Tree of GreenNode
    /// surgical replacements: (start, end, text), applied back-to-front so
    /// earlier spans stay valid. This is the one to reach for when rewriting
    /// what someone else wrote.
    | Edits of (int * int * string) list

/// What a generator gets to look at: the hand-written declarations. Types AND
/// values — deriving needs the first, anything AOP-shaped (tracing, wrapping,
/// serialization entry points) needs the second.
type ProgramView =
    { Types : GenTypeDecl list
      Values : GenValueDecl list
      /// every hand-written file: path and its ORIGINAL text. A generator that
      /// returns one of these paths REPLACES that file — the tier a shader
      /// language or any source-to-source pass needs, where augmenting with
      /// new declarations is not enough.
      Sources : (string * string) list
      /// the same files PARSED, each with what inference knows about it. A
      /// rewriting plugin works from the tree and the types, never by searching
      /// text.
      Files : GenFile list }

type Generator =
    { GName : string
      /// Where new files land, since a file sees only EARLIER files: directly
      /// after this hand-written one. `None` takes the default — after the last
      /// file that declares a TYPE, or after the FIRST file when none does.
      /// Set it when the default cannot be right for your program.
      GAfter : string option
      /// returns (path, output) pairs. A path that names a hand-written file
      /// REWRITES it; any other path becomes a new generated file.
      Generate : ProgramView -> (string * GenOutput) list }

/// the node kinds that spell a TYPE (Lower has its own copy, inside a closure)
/// Build the typed tree for a file: the syntax, with each node's type read off
/// what inference recorded for it.
let tastOf (typeAt : int -> int -> string option) (root : GreenNode) : TDecl list =
    let tyOf (n : GreenNode) =
        let st, en = nodeSpan n
        match typeAt st en with
        | Some ty -> ty
        | None -> "?"
    let identOf (n : GreenNode) =
        match Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead with
        | Some t -> t.Text
        | None -> "_"
    let rec expr (n : GreenNode) : TExpr =
        let kids = nodes n |> List.filter (fun x -> isExprNode x.NodeKind)
        let ty = tyOf n
        match n.NodeKind with
        | LiteralExpr ->
            (match toks n |> List.tryHead with
             | Some t -> TLit (t.Text, ty)
             | None -> TOther ("LiteralExpr", ty))
        | IdentExpr -> TName (identOf n, ty)
        | ParenExpr -> (match kids with [ one ] -> expr one | _ -> TTuple (List.map expr kids, ty))
        | TupleExpr -> TTuple (List.map expr kids, ty)
        | ListExpr ->
            let items =
                match kids with
                | [ single ] when single.NodeKind = BlockExpr ->
                    nodes single |> List.filter (fun x -> isExprNode x.NodeKind)
                | other -> other
            TList (List.map expr items, ty)
        | BinaryExpr ->
            let op = toks n |> List.tryFind (fun t -> t.Kind = Operator)
            (match op, kids with
             | Some o, [ l; r ] -> TBin (o.Text, expr l, expr r, ty)
             | _ -> TOther ("BinaryExpr", ty))
        | AppExpr ->
            (match kids with
             | f :: args -> TApp (expr f, List.map expr args, ty)
             | [] -> TOther ("AppExpr", ty))
        | LambdaExpr ->
            let ps = nodes n |> List.filter (fun x -> x.NodeKind = IdentPat) |> List.map identOf
            (match List.tryLast kids with
             | Some b -> TLam (ps, expr b, ty)
             | None -> TOther ("LambdaExpr", ty))
        | DotExpr ->
            let fld = Green.tokens (GNode n) |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
            (match kids, fld with
             | recv :: _, Some f -> TField (expr recv, f.Text, ty)
             | _ -> TOther ("DotExpr", ty))
        | IfExpr ->
            (match kids with
             | [ c; t; e ] -> TIf (expr c, expr t, expr e, ty)
             | _ -> TOther ("IfExpr", ty))
        | MatchExpr ->
            let arms =
                nodes n
                |> List.filter (fun x -> x.NodeKind = MatchClause)
                |> List.map (fun cl ->
                    let pat =
                        nodes cl
                        |> List.tryFind (fun x -> isPatNodeK x.NodeKind)
                        |> Option.map (fun x -> (Green.toText (GNode x)).Trim ())
                    let body = nodes cl |> List.filter (fun x -> isExprNode x.NodeKind) |> List.tryLast
                    (match pat with Some p -> p | None -> "_"),
                    (match body with Some b -> expr b | None -> TOther ("MatchClause", "?")))
            (match kids with
             | scrut :: _ -> TMatch (expr scrut, arms, ty)
             | [] -> TOther ("MatchExpr", ty))
        | BlockExpr ->
            (match nodes n with
             | d :: rest when d.NodeKind = LetDecl ->
                 let value = nodes d |> List.filter (fun x -> isExprNode x.NodeKind) |> List.tryLast
                 let body = rest |> List.filter (fun x -> isExprNode x.NodeKind) |> List.tryHead
                 (match value, body with
                  | Some v, Some b -> TLet (identOf d, expr v, expr b, ty)
                  | _ -> TOther ("BlockExpr", ty))
             | inner :: _ when isExprNode inner.NodeKind -> expr inner
             | _ -> TOther ("BlockExpr", ty))
        | k -> TOther (string k, ty)
    let decl (n : GreenNode) : TDecl =
        match n.NodeKind with
        | LetDecl ->
            let pats = nodes n |> List.filter (fun x -> x.NodeKind = IdentPat || x.NodeKind = ParenPat)
            let body = nodes n |> List.filter (fun x -> isExprNode x.NodeKind) |> List.tryLast
            (match pats, body with
             | nameNode :: paramNodes, Some b ->
                 let ps =
                     paramNodes
                     |> List.map (fun pn ->
                         let ty =
                             nodes pn
                             |> List.filter (fun y -> isTypeNode y.NodeKind)
                             |> List.tryHead
                             |> Option.map typeText
                         identOf pn, (match ty with Some t -> t | None -> "?"))
                 TDLet (identOf nameNode, ps, typeOfT (expr b), expr b)
             | _ -> TDOther "LetDecl")
        | TypeDecl ->
            let kids = nodes n
            let kind =
                if kids |> List.exists (fun x -> x.NodeKind = UnionCase) then "union"
                elif kids |> List.exists (fun x -> x.NodeKind = RecordRepr) then "record"
                elif kids |> List.exists (fun x -> x.NodeKind = MemberDecl || x.NodeKind = ParenPat) then "class"
                else "abbrev"
            TDType (identOf n, kind)
        | k -> TDOther (string k)
    let rec top (n : GreenNode) : TDecl list =
        nodes n
        |> List.collect (fun c ->
            if c.NodeKind = ModuleDef then top c
            elif c.NodeKind = LetDecl || c.NodeKind = TypeDecl then [ decl c ]
            else [])
    top root

/// Every top-level value declaration in a parse tree, with its attributes.
let valueDeclsOf (path : string) (root : GreenNode) : GenValueDecl list =
    let out = vecNew<GenValueDecl> ()
    let attrsOfList (m : GreenNode) : (string * string list) list =
        let ts = Green.tokens (GNode m)
        let names = ts |> List.filter (fun t -> t.Kind = Ident) |> List.map (fun t -> t.Text)
        let args =
            ts
            |> List.filter (fun t -> t.Kind = StringLit)
            |> List.map (fun t ->
                let raw = t.Text
                if raw.Length >= 2 && raw.StartsWith "\"" then raw.Substring (1, raw.Length - 2) else raw)
        match names with
        | [] -> []
        | first :: _ -> [ first, args ]
    let rec walk (modName : string) (pending : (string * string list) list) (n : GreenNode) =
        let mutable scope = modName
        let mutable attrs = pending
        for c in n.Children |> List.choose (fun x -> match x with GNode m -> Some m | _ -> None) do
            if c.NodeKind = AttributeList then attrs <- attrs @ attrsOfList c
            elif c.NodeKind = ModuleHeader then
                let nm =
                    Green.tokens (GNode c)
                    |> List.filter (fun t -> t.Kind = Ident)
                    |> List.map (fun t -> t.Text)
                    |> String.concat "."
                if nm <> "" then scope <- nm
            elif c.NodeKind = LetDecl then
                // `let f (x : int) : string = ...` — the NAME is an IdentPat
                // child, the parameters are the pattern children after it, and
                // a return annotation is a bare type child
                let kids = c.Children |> List.choose (fun x -> match x with GNode m -> Some m | _ -> None)
                let firstIdent (m : GreenNode) =
                    match Green.tokens (GNode m) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead with
                    | Some t -> t.Text
                    | None -> ""
                let isPatNode (k : NodeKind) = k = IdentPat || k = ParenPat || k = TuplePat || k = WildcardPat
                let pats = kids |> List.filter (fun m -> isPatNode m.NodeKind)
                let retTy =
                    kids
                    |> List.filter (fun m -> isTypeNode m.NodeKind)
                    |> List.map typeText
                    |> List.tryHead
                (match pats with
                 | nameNode :: paramNodes ->
                     vecAdd out
                         { VName = firstIdent nameNode
                           VParams =
                             paramNodes
                             |> List.map (fun pn ->
                                 let ty =
                                     pn.Children
                                     |> List.choose (fun x -> match x with GNode m -> Some m | _ -> None)
                                     |> List.filter (fun m -> isTypeNode m.NodeKind)
                                     |> List.map typeText
                                     |> List.tryHead
                                 firstIdent pn, (match ty with Some t -> t | None -> ""))
                           VReturn = (match retTy with Some t -> t | None -> "")
                           VFile = path
                           VModule = scope
                           VAttrs = attrs }
                 | [] -> ())
                attrs <- []
            else
                walk scope [] c
                attrs <- []
    walk "" [] root
    vecToList out

/// Every type declaration in a parse tree, at any module depth.
let typeDeclsOf (path : string) (root : GreenNode) : GenTypeDecl list =
    let out = vecNew<GenTypeDecl> ()
    let mutable pendingAttrs : (string * string list) list = []
    let attrsOf (m : GreenNode) : (string * string list) list =
        // `[<Derive("Gen")>]` — the first ident names it, string literals are
        // its arguments
        let ts = Green.tokens (GNode m)
        let names = ts |> List.filter (fun t -> t.Kind = Ident) |> List.map (fun t -> t.Text)
        let args =
            ts
            |> List.filter (fun t -> t.Kind = StringLit)
            |> List.map (fun t ->
                let raw = t.Text
                if raw.Length >= 2 && raw.StartsWith "\"" then raw.Substring (1, raw.Length - 2) else raw)
        match names with
        | [] -> []
        | first :: _ -> [ first, args ]
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
                                 // `Both of int * string` holds TWO things, and
                                 // a consumer needs them apart, not as one blob
                                 |> List.collect (fun x ->
                                     if x.NodeKind = TupleType then
                                         let parts = nodes x |> List.filter (fun y -> isTypeNode y.NodeKind)
                                         if List.isEmpty parts then [ typeText x ] else List.map typeText parts
                                     else [ typeText x ]) }
                    | None -> None)
            (match name with
             | Some nm ->
                 let kids = nodes n
                 let hasMembers = kids |> List.exists (fun x -> x.NodeKind = MemberDecl)
                 let hasCtor = kids |> List.exists (fun x -> x.NodeKind = ParenPat)
                 let isAbbrev =
                     List.isEmpty cases && List.isEmpty fields && not hasMembers && not hasCtor
                     && (kids |> List.exists (fun x -> isTypeNode x.NodeKind))
                 let kind =
                     if not (List.isEmpty cases) then "union"
                     elif not (List.isEmpty fields) then "record"
                     elif hasMembers || hasCtor then "class"
                     elif isAbbrev then "abbrev"
                     else "other"
                 vecAdd out
                     { TName = nm; TParams = tyParams; TKind = kind
                       TFields = fields; TCases = cases; TFile = path; TModule = modName
                       TAttrs = pendingAttrs
                       TMembers =
                         nodes n
                         |> List.filter (fun x -> x.NodeKind = MemberDecl)
                         |> List.choose (fun x ->
                             // `member x.Name ...` — the second ident is the name
                             match Green.tokens (GNode x) |> List.filter (fun t -> t.Kind = Ident) with
                             | _ :: nm :: _ -> Some nm.Text
                             | _ -> None) }
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
        // an attribute list precedes the declaration it decorates
        for c in nodes n do
            if c.NodeKind = AttributeList then pendingAttrs <- pendingAttrs @ attrsOf c
            elif c.NodeKind = ModuleHeader then
                let nm = nameOf c
                if nm <> "" then scope <- nm
            elif c.NodeKind = ModuleDef then
                let nm = nameOf c
                walk (if nm = "" then scope else nm) c
            else
                walk scope c
                // attributes decorate ONE declaration
                if c.NodeKind = TypeDecl then pendingAttrs <- []
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
    /// Literal F++ source — quotation. Write the code, splice the holes with
    /// `exText` / `tyText` (F# interpolation supplies the brackets F# keeps for
    /// its own typed quotations), and `renderFileChecked` parses it so a
    /// mistake is reported against the QUOTE rather than the assembled file.
    | GQuote of string

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
    | GPCase (n, [ one ]) -> n + " " + one
    // a case with SEVERAL payload fields holds them as a tuple, and that is how
    // it must be matched — `Both p0 p1` binds nothing useful
    | GPCase (n, args) -> n + " (" + String.concat ", " args + ")"

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
    // a `let` sequence is statements: no inline form exists
    | GLet (_, _, _) -> None
    // a match DOES have one, and needs it: nested in an expression there is
    // nowhere to break the line
    | GMatch (scrut, arms) ->
        let armTexts =
            arms
            |> List.map (fun (p, b) -> inlineOf b |> Option.map (fun t -> "| " + patText p + " -> " + t))
        if armTexts |> List.exists (fun (t : string option) -> t.IsNone) then None
        else
            match inlineOf scrut with
            | Some s ->
                let texts = armTexts |> List.map (fun (t : string option) -> match t with Some x -> x | None -> "")
                Some ("(match " + s + " with " + String.concat " " texts + ")")
            | None -> None

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
    | GQuote text ->
        // trailing blank lines would stack up between declarations
        let ls = text.Replace("\r", "").Split '\n' |> Array.toList
        let rec trimTail (xs : string list) =
            match List.rev xs with
            | last :: rest when last.Trim () = "" -> trimTail (List.rev rest)
            | _ -> xs
        let rec trimHead (xs : string list) =
            match xs with
            | first :: rest when first.Trim () = "" -> trimHead rest
            | _ -> xs
        trimTail (trimHead ls)
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

/// An expression as source at a given indent — the splice helper. `tyText`
/// does the same for a type.
let exText (ind : int) (e : GEx) : string = String.concat "\n" (exLines ind e)

/// An expression as ONE line, whatever its size. This is the splice to reach
/// for inside a quoted template: it drops into any column without the author
/// having to know the indentation, where a multi-line splice would land its
/// continuation lines in the wrong place and break the off-side rule.
let exInline (e : GEx) : string =
    match inlineOf e with
    | Some one -> one
    | None ->
        // shapes with no one-line form (a `let` sequence, a match) become one
        // by parenthesising and joining — legal, just long
        let joined = exLines 0 e |> List.map (fun (l : string) -> l.Trim ()) |> String.concat " "
        "(" + joined + ")"

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

/// Render, and report every quoted fragment that does not parse. The message
/// names the quote and its own line, so a broken template is a generator error
/// rather than a puzzle in a file nobody wrote.
let renderFileChecked (decls : GDecl list) : string * string list =
    let problems = vecNew<string> ()
    for d in decls do
        match d with
        | GQuote text ->
            let parsed = Fpp.Syntax.Parser.parse (text + "\n")
            for diag in parsed.Diagnostics do
                // `min a b` and `Seq.toList` over a string both read
                // differently in the self-hosted checker; keep it plain
                let cut = if diag.Offset < text.Length then diag.Offset else text.Length
                let upto = text.Substring (0, cut)
                let line = List.length (Array.toList (upto.Split '\n'))
                vecAdd problems ("quoted code does not parse at line " + string line + ": " + diag.Message)
        | _ -> ()
    renderFile decls, vecToList problems

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
    let generate (view : ProgramView) : (string * GenOutput) list =
        // `[<Derive("Gen")>]` on any type switches deriveGen from "everything
        // in the program" to exactly what was asked for — the Template Haskell
        // workflow, where the splice names its target
        let wants (t : GenTypeDecl) =
            t.TAttrs |> List.exists (fun (n, args) -> n = "Derive" && List.contains "Gen" args)
        let targeted = view.Types |> List.exists wants
        let named = dictNew<string, GenTypeDecl> ()
        for t in view.Types do
            if (t.TKind = "record" || t.TKind = "union") && (not targeted || wants t) then
                dictSet named t.TName t
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
            [ "deriveGen.fpp", Source (renderFile (header @ opens @ vecToList decls)) ]
    { GName = "deriveGen"; GAfter = None; Generate = generate }

// ---- deriveToString: a printer for every type in the program --------------
// Records print their fields, unions their case and payload, classes their name
// and a stable id (the identity hash: same instance, same number; different
// instances, different numbers). A field whose type is another derived type
// uses THAT type's printer, so nesting prints properly rather than bottoming
// out in a placeholder.

let deriveToString =
    let generate (view : ProgramView) : (string * GenOutput) list =
        let printable = dictNew<string, GenTypeDecl> ()
        for t in view.Types do
            if t.TKind = "record" || t.TKind = "union" || t.TKind = "class" then
                dictSet printable t.TName t
        let isPrintable (n : string) = (dictTryFind printable n).IsSome
        let fnOf (n : string) = "toString" + n
        /// the expression that prints `value`, or None when nothing sensible does
        let rec printerFor (ty : string) (value : GEx) : GEx option =
            let t = compact ty
            if t = "int" || t = "float" || t = "bool" || t = "char" || t = "int64" then
                Some (GApp (GVar "string", [ value ]))
            elif t = "string" then
                // a string prints as itself, quoted, so nesting stays readable
                Some (GBin ("+", GBin ("+", GStr "\"", value), GStr "\""))
            elif isPrintable t then Some (GApp (GVar (fnOf t), [ value ]))
            elif t.StartsWith "list<" && t.EndsWith ">" then
                inner t 5 1 value (fun item -> "[" , "]", "; ")
            elif t.EndsWith "list" && t.Length > 4 then
                listOf (t.Substring (0, t.Length - 4)) value
            elif t.StartsWith "Option<" && t.EndsWith ">" then
                optionOf (t.Substring (7, t.Length - 8)) value
            elif t.EndsWith "option" && t.Length > 6 then
                optionOf (t.Substring (0, t.Length - 6)) value
            else None
        and inner (t : string) (skip : int) (drop : int) (value : GEx) (_ : string -> string * string * string) =
            listOf (t.Substring (skip, t.Length - skip - drop)) value
        and listOf (elemTy : string) (value : GEx) : GEx option =
            match printerFor elemTy (GVar "v") with
            | Some p ->
                // "[" + String.concat "; " (List.map (fun v -> <p>) xs) + "]"
                let mapped = GApp (GVar "List.map", [ GLam ([ "v" ], p); value ])
                let joined = GApp (GVar "String.concat", [ GStr "; "; mapped ])
                Some (GBin ("+", GBin ("+", GStr "[", joined), GStr "]"))
            | None -> None
        and optionOf (elemTy : string) (value : GEx) : GEx option =
            match printerFor elemTy (GVar "v") with
            | Some p ->
                Some (GMatch (value,
                              [ GPCase ("Some", [ "v" ]), GBin ("+", GStr "Some ", p)
                                GPCase ("None", []), GStr "None" ]))
            | None -> None
        let decls = vecNew<GDecl> ()
        let skipped = vecNew<string> ()
        for name, d in dictPairs printable do
            if not (List.isEmpty d.TParams) then vecAdd skipped (name + " (generic)")
            else
                let isStruct = d.TAttrs |> List.exists (fun (a, _) -> a = "Struct")
                let body =
                    if d.TKind = "class" then
                        // no fields to read: the name and a STABLE ID, which is
                        // what identifies one instance from another
                        Some (GBin ("+", GStr (name + "#"), GApp (GVar "string", [ GApp (GVar "hash", [ GVar "x" ]) ])))
                    elif d.TKind = "record" then
                        let parts =
                            d.TFields
                            |> List.map (fun f -> f.FName, printerFor f.FType (GField (GVar "x", f.FName)))
                        if parts |> List.exists (fun (_, p) -> p.IsNone) then None
                        else
                            let rendered =
                                parts
                                |> List.map (fun (fn, p) ->
                                    GBin ("+", GStr (fn + " = "), (match p with Some e -> e | None -> GStr "?")))
                            let joined =
                                match rendered with
                                | [] -> GStr ""
                                | first :: rest ->
                                    List.fold (fun acc r -> GBin ("+", GBin ("+", acc, GStr "; "), r)) first rest
                            let head = (if isStruct then "struct " else "") + name + " { "
                            Some (GBin ("+", GBin ("+", GStr head, joined), GStr " }"))
                    else
                        // a union: one arm per case, payload printed by its type
                        let arms =
                            d.TCases
                            |> List.map (fun c ->
                                match c.CArgs with
                                | [] -> Some (GPCase (c.CName, []), GStr c.CName)
                                | [ one ] ->
                                    (match printerFor one (GVar "p") with
                                     | Some p -> Some (GPCase (c.CName, [ "p" ]), GBin ("+", GStr (c.CName + " "), p))
                                     | None -> None)
                                | many ->
                                    // several payload fields: print them as a tuple
                                    let names = many |> List.mapi (fun i _ -> "p" + string i)
                                    let ps = List.map2 (fun t n -> printerFor t (GVar n)) many names
                                    if ps |> List.exists (fun p -> p.IsNone) then None
                                    else
                                        let rendered = ps |> List.map (fun p -> match p with Some e -> e | None -> GStr "?")
                                        let joined =
                                            match rendered with
                                            | [] -> GStr ""
                                            | first :: rest ->
                                                List.fold (fun acc r -> GBin ("+", GBin ("+", acc, GStr ", "), r)) first rest
                                        Some (GPCase (c.CName, names),
                                              GBin ("+", GBin ("+", GStr (c.CName + " ("), joined), GStr ")")))
                        if arms |> List.exists (fun a -> a.IsNone) then None
                        else Some (GMatch (GVar "x", arms |> List.map (fun a -> match a with Some x -> x | None -> (GPWild, GStr "?"))))
                match body with
                | None -> vecAdd skipped (name + " (a field or payload type has no printer)")
                | Some b ->
                    vecAdd decls (GComment ("generated by deriveToString"))
                    vecAdd decls (GValue (fnOf name, [ "x", Some (GTyName name) ], Some (GTyName "string"), b))
        if vecLen decls = 0 then []
        else
            let opens =
                view.Types
                |> List.filter (fun t -> isPrintable t.TName && t.TModule <> "")
                |> List.map (fun t -> t.TModule)
                |> List.distinct
                |> List.sort
                |> List.map GOpen
            let header =
                [ GComment "deriveToString: a printer for the program's own types." ]
                @ (if vecLen skipped = 0 then []
                   else [ GComment ("skipped: " + String.concat ", " (vecToList skipped)) ])
            [ "deriveToString.fpp", Source (renderFile (header @ opens @ vecToList decls)) ]
    { GName = "deriveToString"; GAfter = None; Generate = generate }

// ---- logCalls: enter/exit tracing around every function -------------------
// The AOP case: this one REWRITES what the user wrote rather than adding to it.
// It cuts by the parse tree's spans — never by searching the text — so a body
// that happens to contain the word `let`, or a string with braces in it, is not
// a hazard.

let logCalls =
    let generate (view : ProgramView) : (string * GenOutput) list =
        view.Files
        |> List.choose (fun f ->
            let src = view.Sources |> List.tryPick (fun (p, t) -> if p = f.FPath then Some t else None)
            match src with
            | None -> None
            | Some text ->
                // every top-level FUNCTION: a `let` with at least one parameter
                let edits =
                    nodes f.FTree
                    |> List.filter (fun d -> d.NodeKind = LetDecl)
                    |> List.choose (fun d ->
                        let pats = nodes d |> List.filter (fun x -> x.NodeKind = IdentPat || x.NodeKind = ParenPat)
                        let body = nodes d |> List.filter (fun x -> isExprNode x.NodeKind) |> List.tryLast
                        match pats, body with
                        | nameNode :: (_ :: _), Some b ->
                            let name =
                                match Green.tokens (GNode nameNode) |> List.filter (fun t -> t.Kind = Ident) |> List.tryHead with
                                | Some t -> t.Text
                                | None -> "?"
                            let dStart, _ = nodeSpan d
                            let bStart, bEnd = nodeSpan b
                            // where the declaration sits decides the indent
                            let lineStart =
                                let before = text.Substring (0, dStart)
                                let i = before.LastIndexOf '\n'
                                if i < 0 then 0 else i + 1
                            let indent = String.replicate (dStart - lineStart + 4) " "
                            let bodyText = text.Substring (bStart, bEnd - bStart)
                            let bodyLineStart =
                                let before = text.Substring (0, bStart)
                                let i = before.LastIndexOf '\n'
                                if i < 0 then 0 else i + 1
                            let bodyCol = bStart - bodyLineStart
                            let targetCol = indent.Length + 4
                            let shiftLine (l : string) =
                                if targetCol >= bodyCol then String.replicate (targetCol - bodyCol) " " + l
                                else
                                    let drop = min (bodyCol - targetCol) (l.Length - (l.TrimStart ' ').Length)
                                    l.Substring drop
                            let bound =
                                if not (bodyText.Contains "\n") then indent + "let __log = " + bodyText
                                else
                                    let lines = bodyText.Replace("\r", "").Split '\n' |> Array.toList
                                    let rest = List.tail lines |> List.map shiftLine
                                    indent + "let __log ="
                                    + "\n" + String.replicate targetCol " " + List.head lines
                                    + (if List.isEmpty rest then "" else "\n" + String.concat "\n" rest)
                            let replacement =
                                "\n" + indent + "print \"-> " + name + "\""
                                + "\n" + bound
                                + "\n" + indent + "print \"<- " + name + "\""
                                + "\n" + indent + "__log"
                            Some (bStart, bEnd, replacement)
                        | _ -> None)
                if List.isEmpty edits then None else Some (f.FPath, Edits edits))

    { GName = "logCalls"; GAfter = None; Generate = generate }

let builtinGenerators = [ deriveGen; deriveToString; logCalls ]

let builtinPlugins = [ constFold; deriveShallowEquals ]

let byName (n : string) : Plugin option =
    builtinPlugins |> List.tryFind (fun p -> p.Name = n)

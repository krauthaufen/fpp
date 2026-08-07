namespace Fpp

open Fpp.Prelude
open Fpp.Syntax
open Fpp.Query

/// Offset -> line/column translation (0-based, LSP convention).
module Lines =

    let starts (text : string) : int[] =
        let v = vecNew<int> ()
        vecAdd v 0
        for i in 0 .. strLen text - 1 do
            if charAt text i = '\n' then vecAdd v (i + 1)
        vecToArray v

    let toLineCol (starts : int[]) (offset : int) : int * int =
        let mutable lo = 0
        let mutable hi = Array.length starts - 1
        while lo < hi do
            let mid = (lo + hi + 1) / 2
            if starts.[mid] <= offset then lo <- mid else hi <- mid - 1
        lo, offset - starts.[lo]

type DiagnosticInfo =
    { Path : string
      Line : int
      Col : int
      EndLine : int
      EndCol : int
      Message : string }

type OutlineItem =
    { Name : string
      /// "module" | "type" | "let"
      Detail : string
      StartLine : int
      StartCol : int
      EndLine : int
      EndCol : int
      Children : OutlineItem list }

module private Outline =

    let span (starts : int[]) (n : GreenNode) : (int * int) * (int * int) =
        match Green.tokens (GNode n) with
        | [] -> (0, 0), (0, 0)
        | ts ->
            let first = List.head ts
            let last = List.last ts
            Lines.toLineCol starts first.Offset,
            Lines.toLineCol starts (last.Offset + strLen last.Text)

    let private firstIdentText (g : Green) : string option =
        Green.tokens g
        |> List.tryFind (fun t -> t.Kind = Ident)
        |> Option.map (fun t -> t.Text)

    /// Dotted name after `module` / `open`: leading Ident/"." token run.
    let private dottedName (n : GreenNode) : string =
        let ts =
            Green.tokens (GNode n)
            |> List.filter (fun t -> t.Kind = Ident || (t.Kind = Operator && t.Text = "."))
        match ts with
        | [] -> "?"
        | _ ->
            let rec take acc (rest : Token list) (wantIdent : bool) =
                match rest with
                | t :: tl when wantIdent && t.Kind = Ident -> take (t.Text :: acc) tl false
                | t :: tl when not wantIdent && t.Text = "." -> take ("." :: acc) tl true
                | _ -> List.rev acc
            take [] ts true |> String.concat ""

    let rec items (starts : int[]) (children : Green list) : OutlineItem list =
        children
        |> List.choose (fun c ->
            match c with
            | GNode n ->
                let (sl, sc), (el, ec) = span starts n
                let make name detail kids =
                    Some { Name = name; Detail = detail
                           StartLine = sl; StartCol = sc; EndLine = el; EndCol = ec
                           Children = kids }
                match n.NodeKind with
                | LetDecl ->
                    let name =
                        n.Children
                        |> List.tryPick (fun ch ->
                            match ch with
                            | GNode p when p.NodeKind = IdentPat || p.NodeKind = ParenPat || p.NodeKind = TuplePat ->
                                firstIdentText ch
                            | _ -> None)
                    make (defaultArg name "let") "let" []
                | TypeDecl ->
                    let name =
                        n.Children
                        |> List.tryPick (fun ch ->
                            match ch with
                            | GToken t when t.Kind = Ident -> Some t.Text
                            | _ -> None)
                    make (defaultArg name "type") "type" []
                | ModuleDef | ModuleHeader ->
                    make (dottedName n) "module" (items starts n.Children)
                | _ -> None
            | GToken _ -> None)

/// The workspace: one query database over a set of files. Both the LSP
/// server and the batch CLI talk to the compiler exclusively through this.
/// The auto-opened builtin prelude (FSharp.Core's role): well-known types
/// every file sees without an `open`. No module header, so its exports live
/// under bare names. `option<'a>` aliases the nominal `Option<'a>` so
/// postfix `'v option` and constructor results unify.
module Builtin =

    /// The prelude LIVES in stdlib/prelude.fpp — a real F++ source file with
    /// editor support. WHERE the text comes from is a host service (see
    /// Prelude.preludeSource): the .NET build reads an embedded resource so
    /// the binary stays self-contained, a wasm host supplies what it
    /// preloaded. Nothing here reaches past the seam.
    let source : string = preludeSource ()

    let path = Analysis.Classes.builtinPath

type ProjectResults =
    { Files : Fpp.Prelude.Dict<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult>
      Schemes : Fpp.Prelude.Dict<string, Analysis.Types.Scheme>
      /// interface name -> its methods as (name, arity), project-wide
      Interfaces : Fpp.Prelude.Dict<string, (string * int) list>
      /// derived class -> (its own type params, its base type), project-wide
      Bases : Fpp.Prelude.Dict<string, Analysis.Types.Var list * Analysis.Types.Type>
      /// "TypeName.MemberName" -> definition, project-wide
      Members : Fpp.Prelude.Dict<string, Analysis.Resolve.Definition>
      /// inference's member table, keyed by the receiver's DECORATED type
      /// name (Name`N for a multi-arity name) — what Lower consults first
      Fields : Fpp.Prelude.Dict<string, Analysis.Infer.FieldInfo>
      /// classes and their instances, project-wide
      Classes : Analysis.Classes.Tables
      /// the REWRITTEN tree per file: computation expressions are gone from
      /// it, and it is the one resolution, inference and lowering all saw
      Trees : Fpp.Prelude.Dict<string, Parser.ParseResult>
      /// type abbreviations, short name -> (params, target): what lets
      /// lowering resolve `interface aval<'T> with` to the interface it
      /// stands for, so every implementor lands in the same vtable slot
      Aliases : Fpp.Prelude.Dict<string, Analysis.Types.Var list * Analysis.Types.Type>
      /// the prelude's own inference result — it is source like any other
      /// file, and its bodies use the classes it declares
      BuiltinInfer : Analysis.Infer.InferResult }

/// The prelude is a process-wide CONSTANT: parse, resolve and infer it once,
/// then seed every project with COPIES of its tables. Without this every
/// Workspace re-inferred ~1400 prelude lines, which the test suite (one
/// Workspace per test) paid hundreds of times over.
module private BuiltinCache =
    type Cached =
        { Parse : Parser.ParseResult
          Bind : Analysis.Resolve.BindResult
          Inferred : Analysis.Infer.InferResult
          Imports : Fpp.Prelude.Dict<string, Analysis.Resolve.Definition>
          Schemes : Fpp.Prelude.Dict<string, Analysis.Types.Scheme>
          Aliases : Fpp.Prelude.Dict<string, Analysis.Types.Var list * Analysis.Types.Type>
          Fields : Fpp.Prelude.Dict<string, Analysis.Infer.FieldInfo>
          Ifaces : Fpp.Prelude.Dict<string, (string * int) list>
          Bases : Fpp.Prelude.Dict<string, Analysis.Types.Var list * Analysis.Types.Type>
          Impls : Fpp.Prelude.Dict<string, string list>
          ImplTys : Fpp.Prelude.Dict<string, (Analysis.Types.Var list * Analysis.Types.Type) list>
          StructTypes : Fpp.Prelude.Dict<string, bool>
          Ctors : Fpp.Prelude.Dict<string, (int * Analysis.Types.Scheme) list>
          Classes : Analysis.Classes.Tables
          Members : Fpp.Prelude.Dict<string, Analysis.Resolve.Definition> }
    let copyDict (src : Fpp.Prelude.Dict<'k, 'v>) : Fpp.Prelude.Dict<'k, 'v> =
        let d = dictNew<'k, 'v> ()
        for k, v in dictPairs src do dictSet d k v
        d

    let copyTables (t : Analysis.Classes.Tables) : Analysis.Classes.Tables =
        // instance VECTORS are mutated when a project adds instances, so
        // each project gets its own vectors, not the cached ones
        let inst = dictNew<string, Fpp.Prelude.Vec<Analysis.Classes.InstanceDef>> ()
        for k, v in dictPairs t.Instances do
            let nv = vecNew<Analysis.Classes.InstanceDef> ()
            for x in vecToList v do vecAdd nv x
            dictSet inst k nv
        { Classes = copyDict t.Classes
          Instances = inst
          MemberOwner = copyDict t.MemberOwner }

    let compute () =
            let imports = dictNew<string, Analysis.Resolve.Definition> ()
            let schemes = dictNew<string, Analysis.Types.Scheme> ()
            let aliases = dictNew<string, Analysis.Types.Var list * Analysis.Types.Type> ()
            let fields = dictNew<string, Analysis.Infer.FieldInfo> ()
            let ifaces = dictNew<string, (string * int) list> ()
            let bases = dictNew<string, Analysis.Types.Var list * Analysis.Types.Type> ()
            let impls = dictNew<string, string list> ()
            let implTys = dictNew<string, (Analysis.Types.Var list * Analysis.Types.Type) list> ()
            let structTypes = dictNew<string, bool> ()
            let ctors = dictNew<string, (int * Analysis.Types.Scheme) list> ()
            let classes = Analysis.Classes.newTables ()
            let members = dictNew<string, Analysis.Resolve.Definition> ()
            let bp = Parser.parse Builtin.source
            let bb = Analysis.Resolve.resolve Builtin.path imports bp.Root
            for full, d in bb.Exports do dictSet imports full d
            for k, d in bb.Members do dictSet members k d
            let binf =
                Analysis.Infer.infer Builtin.path bp.Root bb schemes aliases fields ifaces bases impls implTys structTypes ctors classes
            { Parse = bp; Bind = bb; Inferred = binf; Imports = imports
              Schemes = schemes; Aliases = aliases; Fields = fields
              Ifaces = ifaces; Bases = bases; Impls = impls; ImplTys = implTys
              StructTypes = structTypes; Ctors = ctors; Classes = classes
              Members = members }
    // Memoized by hand rather than with `lazy`: one cell, computed on first
    // use. F#'s `lazy` adds thread safety this single-threaded cache does
    // not need, and it is not part of the subset the compiler compiles.
    let mutable cell : Cached option = None
    let force () : Cached =
        match cell with
        | Some c -> c
        | None ->
            let c = compute ()
            cell <- Some c
            c

type Workspace() =
    let db = Db()
    do db.SetInput "project" "" (box ([] : string list))
    do db.SetInput "libs" "" (box ([] : (string * string) list))
    let plugins = vecNew<Fpp.Core.Plugins.Plugin> ()
    let generators = vecNew<Fpp.Core.Plugins.Generator> ()
    /// plugins written in F++ ITSELF: name and sources, compiled and RUN at
    /// compile time
    let fppGenerators = vecNew<string * (string * string) list> ()
    /// generated path -> the generator that wrote it, for blaming diagnostics
    let generatedBy = dictNew<string, string> ()
    /// where each piece of the last emitted module came from
    let mutable lastPositions : (int * string * int) list = []
    /// hand-written text, captured before any generator rewrites a file: the
    /// INPUT to generation must stay what the human wrote, or a second compile
    /// would feed a generator its own output
    let originalText = dictNew<string, string> ()
    let pluginErrors = vecNew<string> ()

    /// Register a compiler plugin (project config, never source annotations).
    member _.AddPlugin (p : Fpp.Core.Plugins.Plugin) : unit = vecAdd plugins p

    /// A generator emits SOURCE before analysis, so it can declare types,
    /// classes and instances — see the staging rule in Plugins.fs.
    member _.AddGenerator (g : Fpp.Core.Plugins.Generator) : unit = vecAdd generators g

    /// A generator written in F++ ITSELF. Its sources are compiled and RUN
    /// during this compilation; whatever it prints becomes a generated file.
    /// It reads the program it is generating for from `viewTypes`, which is
    /// handed to it as ordinary F++ data.
    member _.AddFppGenerator (name : string) (sources : (string * string) list) : unit =
        vecAdd fppGenerators (name, sources)
    member _.PluginErrors : string list = vecToList pluginErrors

    /// Run the per-file plugin pipeline, linting after each stage.
    member private _.RunPerFile (decls : Fpp.Core.Ir.Decl list) : Fpp.Core.Ir.Decl list =
        let mutable cur = decls
        for p in vecToList plugins do
            let out = p.PerFile cur
            match Fpp.Core.Lint.lint out with
            | [] -> cur <- out
            | errs ->
                for e in errs |> List.truncate 3 do
                    vecAdd pluginErrors ("plugin '" + p.Name + "' produced invalid core: " + e)
        cur

    member private _.RunWholeProgram (decls : Fpp.Core.Ir.Decl list) : Fpp.Core.Ir.Decl list =
        let mutable cur = decls
        for p in vecToList plugins do
            let out = p.WholeProgram cur
            match Fpp.Core.Lint.lint out with
            | [] -> cur <- out
            | errs ->
                for e in errs |> List.truncate 3 do
                    vecAdd pluginErrors ("plugin '" + p.Name + "' (whole-program) produced invalid core: " + e)
        cur

    /// Register a fat-IR library (.fppir contents) for linking.
    member this.AddLibrary (name : string) (text : string) : unit =
        let libs = unbox<(string * string) list> (db.GetInput "libs" "")
        db.SetInput "libs" "" (box (libs @ [ name, text ]))

    member private _.Libraries : (string * string) list =
        unbox<(string * string) list> (db.GetInput "libs" "")

    member _.Db = db

    /// Set the compile order explicitly (CLI: argument order).
    member _.SetProjectFiles (paths : string list) : unit =
        db.SetInput "project" "" (box paths)

    member _.ProjectFiles : string list =
        unbox<string list> (db.GetInput "project" "")

    /// Load a `*.fppproj`: its sources become the compile order, its
    /// libraries are linked. Files already open in the editor keep the text
    /// the editor has — an unsaved buffer is the truth, not the file on disk.
    /// Returns the project and any errors in the manifest itself.
    member this.LoadProject (projectPath : string) : Project.Project * (int * string) list =
        let r = Project.read projectPath
        let open_ = this.ProjectFiles |> Set.ofList
        for l in r.Loaded.Libs do
            match hostReadText l with
            | Some text -> this.AddLibrary l text
            | None -> ()
        db.SetInput "project" "" (box r.Loaded.Sources)
        for s in r.Loaded.Sources do
            if not (Set.contains s open_) then
                let text = match hostReadText s with Some t -> t | None -> ""
                db.SetInput "text" s (box text)
        r.Loaded, r.Errors

    member this.SetFileText (path : string) (text : string) : unit =
        // unknown files join the project in arrival order (LSP didOpen)
        let files = this.ProjectFiles
        if not (List.contains path files) then
            db.SetInput "project" "" (box (files @ [ path ]))
        db.SetInput "text" path (box text)

    member _.FileText (path : string) : string =
        unbox<string> (db.GetInput "text" path)

    /// The parse EXACTLY as written — the tree the round-trip gate and the
    /// editor's view of the text are about.
    member this.ParseRaw (path : string) : Parser.ParseResult =
        db.MemoT "parse" path (fun () -> Parser.parse (this.FileText path))

    /// The tree everything semantic runs on: computation expressions are
    /// rewritten into ordinary syntax first, so resolution, inference and
    /// lowering all see ONE shape and cannot disagree about it.
    /// The tree everything semantic runs on: computation expressions have
    /// been rewritten into ordinary syntax, so resolution, inference and
    /// lowering all see ONE shape and cannot disagree about it. Inside a
    /// project that rewrite is type-directed and ProjectCheck did it; a lone
    /// file has no builder types to go on and gets the conservative form.
    member this.ParseFile (path : string) : Parser.ParseResult =
        if List.contains path this.ProjectFiles then
            match dictTryFind (this.ProjectCheck ()).Trees path with
            | Some t -> t
            | None -> this.ParseStandalone path
        else this.ParseStandalone path

    member private this.ParseStandalone (path : string) : Parser.ParseResult =
        db.MemoT "desugar" path (fun () ->
            let p = this.ParseRaw path
            if Desugar.hasComp (GNode p.Root) then { p with Root = Desugar.desugar p.Root } else p)

    /// Whole-project resolution + inference in compile order. Exports and
    /// generalized schemes of earlier files flow into later ones.
    member this.ProjectCheck () : ProjectResults =
        db.MemoT "projectCheck" "" (fun () ->
            // seed from the prelude cache: COPIES, since the project mutates
            let cached = BuiltinCache.force ()
            let imports = BuiltinCache.copyDict cached.Imports
            let schemes = BuiltinCache.copyDict cached.Schemes
            let aliases = BuiltinCache.copyDict cached.Aliases
            let fields = BuiltinCache.copyDict cached.Fields
            let ifaces = BuiltinCache.copyDict cached.Ifaces
            let bases = BuiltinCache.copyDict cached.Bases
            let impls = BuiltinCache.copyDict cached.Impls
            let implTys = BuiltinCache.copyDict cached.ImplTys
            let structTypes = BuiltinCache.copyDict cached.StructTypes
            let ctors = BuiltinCache.copyDict cached.Ctors
            // classes and instances are project-wide: the prelude declares
            // the numeric tower, every later file may extend it
            let classes = BuiltinCache.copyTables cached.Classes
            // members are looked up by "Type.Member" across the whole
            // project, not just the file that declares them
            let members = BuiltinCache.copyDict cached.Members
            let results = dictNew<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult> ()
            let binf = cached.Inferred
            // linked libraries: exports feed the resolver, schemes feed inference
            for _, text in this.Libraries do
                let exps, schs, _ = Fpp.Core.Serialize.decodeLib text
                for full, d in exps do dictSet imports full d
                for k, sch in schs do dictSet schemes k sch
            let trees = dictNew<string, Parser.ParseResult> ()
            for path in this.ProjectFiles do
                let raw = this.ParseRaw path
                // The PROBE. A computation expression's shape depends on what
                // its builder declares — `Run` and `Delay` are there only if
                // the builder has them — so the file is resolved and inferred
                // once BEFORE the rewrite, with every computation expression
                // left alone but its builder typed. Everything the probe
                // touches is a COPY: inference registers instances and
                // schemes as it goes, and doing that twice is not free of
                // consequence. Its diagnostics are dropped — they would be
                // about a body that is one pass away from not existing.
                let p =
                    if not (Desugar.hasComp (GNode raw.Root)) then raw
                    else
                        let b0 = Analysis.Resolve.resolve path imports raw.Root
                        let members0 = BuiltinCache.copyDict members
                        for k, d in b0.Members do dictSet members0 k d
                        let inf0 =
                            Analysis.Infer.infer path raw.Root b0
                                (BuiltinCache.copyDict schemes) (BuiltinCache.copyDict aliases)
                                (BuiltinCache.copyDict fields) (BuiltinCache.copyDict ifaces)
                                (BuiltinCache.copyDict bases) (BuiltinCache.copyDict impls)
                                (BuiltinCache.copyDict implTys)
                                (BuiltinCache.copyDict structTypes) (BuiltinCache.copyDict ctors)
                                (BuiltinCache.copyTables classes)
                        let builders = dictNew<int, Desugar.CeBuilder> ()
                        for off, tyName in inf0.CompBuilders do
                            let has (m : string) = (dictTryFind members0 (tyName + "." + m)).IsSome
                            dictSet builders off
                                { Name = tyName
                                  HasRun = has "Run"
                                  HasDelay = has "Delay"
                                  HasReturn = has "Return"
                                  HasBindReturn = has "BindReturn"
                                  HasBind2 = has "Bind2"
                                  HasBind3 = has "Bind3"
                                  HasBind2Return = has "Bind2Return"
                                  HasBind3Return = has "Bind3Return"
                                  HasMergeSources = has "MergeSources"
                                  HasMergeSources3 = has "MergeSources3" }
                        let lookup (off : int) =
                            match dictTryFind builders off with
                            | Some b -> b
                            | None -> Desugar.unknownBuilder "?"
                        let stmts = dictNew<int, bool> ()
                        for off in inf0.CompStatements do dictSet stmts off true
                        let isStatement (off : int) = (dictTryFind stmts off).IsSome
                        { raw with Root = Desugar.desugarWithStatements lookup isStatement raw.Root }
                dictSet trees path p
                let b = Analysis.Resolve.resolve path imports p.Root
                for full, d in b.Exports do dictSet imports full d
                // An extension on an ABBREVIATION belongs to what the
                // abbreviation names: `type List<'T> with` adds members to
                // ResizeArray, because that is what `List` IS. Resolution is
                // per file and cannot know that — the abbreviation is
                // usually in another one — so the key is aligned here, where
                // the project's aliases are known.
                for k, d in b.Members do
                    dictSet members k d
                    let dot = k.IndexOf "."
                    if dot > 0 then
                        let owner = k.Substring (0, dot)
                        match dictTryFind aliases owner with
                        | Some (_, body) ->
                            (match body with
                             | Analysis.Types.TCon (target, _) when target <> owner ->
                                 dictSet members (target + k.Substring dot) d
                             | _ -> ())
                        | None -> ()
                let inf = Analysis.Infer.infer path p.Root b schemes aliases fields ifaces bases impls implTys structTypes ctors classes
                dictSet results path (b, inf)
            // libraries declare their interfaces in their serialized core
            for _, text in this.Libraries do
                let _, _, ds = Fpp.Core.Serialize.decodeLib text
                for d in ds do
                    match d with
                    | Fpp.Core.Ir.DInterface (n, ms) -> dictSet ifaces n ms
                    | Fpp.Core.Ir.DClass (n, bse, _, cimpls) ->
                        (match bse with
                         | Some b -> dictSet bases n ([], Analysis.Types.TCon (b, []))
                         | None -> ())
                        dictSet impls n (cimpls |> List.map fst)
                    | _ -> ()
            { Files = results; Schemes = schemes; Interfaces = ifaces; Bases = bases
              Members = members; Fields = fields; Classes = classes; Trees = trees
              Aliases = aliases; BuiltinInfer = binf })

    member this.TypeCheck (path : string) : Analysis.Infer.InferResult =
        match dictTryFind (this.ProjectCheck ()).Files path with
        | Some (_, i) -> i
        | None ->
            Analysis.Infer.infer path (this.ParseFile path).Root (this.Resolve path)
                (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ())
                (Analysis.Classes.newTables ())

    member this.Diagnostics (path : string) : DiagnosticInfo list =
        db.MemoT "diagnostics" path (fun () ->
            let r = this.ParseFile path
            let t = this.TypeCheck path
            let starts = Lines.starts (this.FileText path)
            let at (offset : int) (msg : string) =
                let line, col = Lines.toLineCol starts offset
                { Path = path; Line = line; Col = col
                  EndLine = line; EndCol = col + 1; Message = msg }
            (r.Diagnostics |> List.map (fun d -> at d.Offset d.Message))
            @ (t.Diagnostics |> List.map (fun (off, msg) -> at off msg))
            // by (Line, Col), spelled out: `Ordered` has no instance at a
            // TUPLE type, so a tuple key cannot drive `sortBy` (see PLAN.md)
            |> List.sortWith (fun a b ->
                if a.Line <> b.Line then compare a.Line b.Line else compare a.Col b.Col))

    member this.Outline (path : string) : OutlineItem list =
        db.MemoT "outline" path (fun () ->
            let r = this.ParseFile path
            let starts = Lines.starts (this.FileText path)
            Outline.items starts r.Root.Children)

    member this.Resolve (path : string) : Analysis.Resolve.BindResult =
        match dictTryFind (this.ProjectCheck ()).Files path with
        | Some (b, _) -> b
        | None -> Analysis.Resolve.resolve path (dictNew ()) (this.ParseFile path).Root

    /// Lower the whole project (builtin first, then files in compile order)
    /// and emit a wasm module. Returns (wat, all errors incl. diagnostics).
    /// Emit with the optimizer OFF. The passes that run before it — stamping,
    /// scalarization — are gated by asserting their symbols appear in the
    /// output, and inlining legitimately removes the very functions those
    /// gates look for. Each pass is checked on its own output rather than
    /// through whatever survives the ones after it.
    member this.EmitProgramWasmRaw () : byte[] * string list = this.EmitCore false

    /// Marks a file as generated: such files are compiled, but never shown to
    /// a generator (the staging rule) and never regenerated from.
    static member GeneratedPrefix = "(generated)/"

    /// Run the registered generators ONCE over the hand-written declarations
    /// and add their output as project files. Generated files land at the END
    /// of the compile order, so they see every user declaration, and each
    /// generator writes to a stable path, so running twice replaces rather
    /// than accumulates.
    member private this.RunGenerators () : unit =
        if vecLen generators > 0 || vecLen fppGenerators > 0 then
            for path in this.ProjectFiles do
                if not (path.StartsWith Workspace.GeneratedPrefix)
                   && not (dictTryFind originalText path).IsSome then
                    dictSet originalText path (this.FileText path)
            // parse the ORIGINAL text, never a rewritten file
            for path in this.ProjectFiles do
                match dictTryFind originalText path with
                | Some t when t <> this.FileText path -> db.SetInput "text" path (box t)
                | _ -> ()
            let types = vecNew<Fpp.Core.Plugins.GenTypeDecl> ()
            for path in this.ProjectFiles do
                if not (path.StartsWith Workspace.GeneratedPrefix) then
                    let pr = this.ParseFile path
                    for t in Fpp.Core.Plugins.typeDeclsOf path pr.Root do vecAdd types t
            let values = vecNew<Fpp.Core.Plugins.GenValueDecl> ()
            for path in this.ProjectFiles do
                if not (path.StartsWith Workspace.GeneratedPrefix) then
                    let pr = this.ParseFile path
                    for v in Fpp.Core.Plugins.valueDeclsOf path pr.Root do vecAdd values v
            let instances = vecNew<Fpp.Core.Plugins.GenInstanceDecl> ()
            for path in this.ProjectFiles do
                if not (path.StartsWith Workspace.GeneratedPrefix) then
                    let pr = this.ParseFile path
                    for i in Fpp.Core.Plugins.instanceDeclsOf path pr.Root do vecAdd instances i
            let sources =
                this.ProjectFiles
                |> List.filter (fun p -> not (p.StartsWith Workspace.GeneratedPrefix))
                |> List.map (fun p ->
                    p, (match dictTryFind originalText p with Some t -> t | None -> this.FileText p))
            let checkedFiles = this.ProjectCheck ()
            let genFiles =
                this.ProjectFiles
                |> List.filter (fun p -> not (p.StartsWith Workspace.GeneratedPrefix))
                |> List.map (fun p ->
                    let typeAt (off : int) : string option =
                        match dictTryFind checkedFiles.Schemes (p + ":" + string off) with
                        | Some sch -> Some (Analysis.Types.schemeString sch)
                        | None ->
                            match dictTryFind checkedFiles.Files p with
                            | Some (_, inf) ->
                                inf.DefTypes
                                |> List.tryPick (fun (o, _, ts) -> if o = off then Some ts else None)
                            | None -> None
                    let tree = (this.ParseFile p).Root
                    // one dictionary per file: a linear scan per node would be
                    // quadratic in the size of the file
                    let spanTypes = dictNew<int * int, string> ()
                    (match dictTryFind checkedFiles.Files p with
                     | Some (_, inf) -> for a, b, ts in inf.ExprTypes do dictSet spanTypes (a, b) ts
                     | None -> ())
                    let exprTypeAt (st : int) (en : int) : string option = dictTryFind spanTypes (st, en)
                    { FPath = p
                      FTree = tree
                      FTypeAt = typeAt
                      // the typed tree: syntax with every node's inferred type
                      FTast = Fpp.Core.Plugins.tastOf exprTypeAt tree } : Fpp.Core.Plugins.GenFile)
            let view : Fpp.Core.Plugins.ProgramView =
                { Types = vecToList types; Values = vecToList values
                  Instances = vecToList instances
                  Sources = sources; Files = genFiles }
            // A file sees only EARLIER files, so generated code goes directly
            // after the last file that declared a type: it can name every type
            // it derives from, and anything in a later file can name it. A
            // consumer therefore has to live in a later file than the types —
            // the same staging F# projects and Template Haskell splices have.
            let declaring =
                vecToList types |> List.map (fun t -> t.TFile) |> List.distinct
            // Generated code must land after what it reads and before what
            // reads IT. The default is after the last file declaring a TYPE;
            // with no types anywhere, after the FIRST file — putting it last
            // would hide it from every consumer.
            let defaultAnchor =
                let files = this.ProjectFiles
                let idxs =
                    files
                    |> List.mapi (fun i p -> i, p)
                    |> List.filter (fun (_, p) -> List.contains p declaring)
                    |> List.map fst
                if List.isEmpty idxs then 0 else List.max idxs
            let anchorFor (g : Fpp.Core.Plugins.Generator) =
                match g.GAfter with
                | Some want ->
                    (match this.ProjectFiles |> List.mapi (fun i p -> i, p) |> List.tryFind (fun (_, p) -> p = want) with
                     | Some (i, _) -> i
                     | None ->
                         vecAdd pluginErrors
                             ("generator '" + g.GName + "' asks to emit after " + want + ", which is not a file here")
                         defaultAnchor)
                | None -> defaultAnchor
            // F++-written plugins live in their own member: a function that
            // cannot be lowered is stubbed WHOLE, so keeping this out of
            // RunGenerators is what lets the self-hosted compiler run at all
            if vecLen fppGenerators > 0 then this.RunFppGenerators view defaultAnchor

            for g in vecToList generators do
                let anchorIndex = anchorFor g
                try
                    for name, output in g.Generate view do
                      match output with
                      | Fpp.Core.Plugins.Diagnostics ds ->
                        // a generator's own errors, against a file the user
                        // wrote: positioned like any other diagnostic
                        for off, msg in ds do
                            let text = match dictTryFind originalText name with
                                       | Some t -> t
                                       | None -> this.FileText name
                            let cut = if off < text.Length then off else text.Length
                            let upto = (text.Substring (0, cut)).Replace ("\r", "")
                            let ls = upto.Split '\n'
                            let line = ls.Length
                            let col = (if ls.Length > 0 then ls.[ls.Length - 1].Length else 0) + 1
                            vecAdd pluginErrors
                                (name + ":" + string line + ":" + string col + ": " + msg
                                 + " (" + g.GName + ")")
                      | _ ->
                        let src =
                            match output with
                            | Fpp.Core.Plugins.Source t -> t
                            | Fpp.Core.Plugins.Tree t -> Syntax.Green.toText (Syntax.GNode t)
                            | Fpp.Core.Plugins.Diagnostics _ -> ""
                            | Fpp.Core.Plugins.Edits es ->
                                // back to front, so earlier spans stay valid
                                let baseText =
                                    match dictTryFind originalText name with
                                    | Some t -> t
                                    | None -> this.FileText name
                                let ordered = es |> List.sortByDescending (fun (st, _, _) -> st)
                                let mutable acc = baseText
                                for st, en, rep in ordered do
                                    if st >= 0 && en <= acc.Length && st <= en then
                                        acc <- acc.Substring (0, st) + rep + acc.Substring en
                                acc
                        let files = this.ProjectFiles
                        if List.contains name files && not (name.StartsWith Workspace.GeneratedPrefix) then
                            // REWRITE: the generator returned a hand-written
                            // path, so it replaces that file wholesale
                            match dictTryFind generatedBy name with
                            | Some other when other <> g.GName ->
                                vecAdd pluginErrors
                                    ("generators '" + other + "' and '" + g.GName + "' both rewrite " + name)
                            | _ ->
                                dictSet generatedBy name g.GName
                                db.SetInput "text" name (box src)
                        else
                            let path = Workspace.GeneratedPrefix + name
                            dictSet generatedBy path g.GName
                            db.SetInput "text" path (box src)
                            if not (List.contains path files) then
                                let before = files |> List.truncate (anchorIndex + 1)
                                let after = files |> List.skip (min (List.length files) (anchorIndex + 1))
                                db.SetInput "project" "" (box (before @ [ path ] @ after))
                with e -> vecAdd pluginErrors ("generator " + g.GName + " failed: " + e.Message)

    /// The files the generators produced this run: path, generator, source.
    /// A generated file is compiled like any other, so it is worth being able
    /// to read the thing the errors are about.
    member this.GeneratedFiles : (string * string * string) list =
        this.ProjectFiles
        |> List.filter (fun p -> p.StartsWith Workspace.GeneratedPrefix)
        |> List.map (fun p ->
            p, (match dictTryFind generatedBy p with Some g -> g | None -> "?"), this.FileText p)

    /// Compile and RUN the plugins written in F++ itself. Kept separate
    /// because it spawns a process: unlowerable in the self-hosted build, and a
    /// stubbed function traps as a whole, so it must not sit on the common path.
    member private this.RunFppGenerators (view : Fpp.Core.Plugins.ProgramView) (anchorIndex : int) : unit =
        // ---- plugins written in F++, compiled and run right here -------
        if vecLen fppGenerators > 0 then
            let q (t : string) = "\"" + t.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""
            let typeRows =
                view.Types
                |> List.map (fun t ->
                    let members =
                        if t.TKind = "record" then
                            t.TFields |> List.map (fun f -> "(" + q f.FName + ", " + q f.FType + ")")
                        else
                            t.TCases
                            |> List.map (fun c ->
                                "(" + q c.CName + ", " + q (match c.CArgs with a :: _ -> a | [] -> "") + ")")
                    "      (" + q t.TName + ", " + q t.TKind + ", [ " + String.concat "; " members + " ])")
            let viewSrc =
                "// the program being compiled, as data for an F++ generator\n"
                + "let viewTypes : (string * string * (string * string) list) list =\n"
                + (if List.isEmpty typeRows then "    []\n"
                   else "    [\n" + String.concat "\n" typeRows + " ]\n")
            let wasmtime =
                match System.Environment.GetEnvironmentVariable "FPP_WASMTIME" with
                | null | "" ->
                    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
                    + "/.wasmtime/bin/wasmtime"
                | p -> p
            for gname, gsources in vecToList fppGenerators do
                let pw = Workspace()
                pw.SetFileText "(view)/view.fpp" viewSrc
                for path, text in gsources do pw.SetFileText path text
                let bytes, perrs = pw.EmitProgramWasm ()
                if not (List.isEmpty perrs) then
                    for e in perrs |> List.truncate 3 do
                        vecAdd pluginErrors ("F++ generator '" + gname + "' does not compile: " + e)
                else
                    let tmp = System.IO.Path.GetTempFileName () + ".wasm"
                    System.IO.File.WriteAllBytes (tmp, bytes)
                    let psi =
                        System.Diagnostics.ProcessStartInfo (wasmtime, "run -W gc=y,exceptions=y " + tmp)
                    psi.RedirectStandardOutput <- true
                    psi.RedirectStandardError <- true
                    use proc = System.Diagnostics.Process.Start psi
                    let out = proc.StandardOutput.ReadToEnd ()
                    let err = proc.StandardError.ReadToEnd ()
                    proc.WaitForExit ()
                    System.IO.File.Delete tmp
                    if proc.ExitCode <> 0 then
                        vecAdd pluginErrors
                            ("F++ generator '" + gname + "' failed at run time: "
                             + err.Substring (0, min 300 err.Length))
                    else
                        let path = Workspace.GeneratedPrefix + gname + ".fpp"
                        dictSet generatedBy path gname
                        db.SetInput "text" path (box out)
                        let files = this.ProjectFiles
                        if not (List.contains path files) then
                            let before = files |> List.truncate (anchorIndex + 1)
                            let after = files |> List.skip (min (List.length files) (anchorIndex + 1))
                            db.SetInput "project" "" (box (before @ [ path ] @ after))


    member private this.EmitCore (optimize : bool) : byte[] * string list =
        this.EmitCoreMapped optimize ""

    /// Everything both backends share: generators, check, lower, link,
    /// monomorphize, optimize, DCE. Returns the linked program and any
    /// errors; an erroring program returns an empty decl list.
    member private this.LinkedCore (optimize : bool) : Fpp.Core.Ir.Decl list * string list =
        this.RunGenerators ()
        let r = this.ProjectCheck ()
        let errs = vecNew<string> ()
        let allDecls = vecNew<Fpp.Core.Ir.Decl> ()
        // Nobody WROTE a generated file, so a bare position in one is useless:
        // name the generator and quote the line it produced.
        let blame (path : string) (line : int) (col : int) (msg : string) : string =
            let where =
                if line >= 0 then path + ":" + string (line + 1) + ":" + string (col + 1) + ": "
                else path + ": "
            match dictTryFind generatedBy path with
            | Some who ->
                let lines = (this.FileText path).Replace("\r", "").Split '\n'
                let src = if line >= 0 && line < lines.Length then lines.[line] else ""
                let caret =
                    if src = "" then ""
                    else "\n    " + String.replicate (max 0 col) " " + "^"
                "generator '" + who + "' produced code that does not compile\n  " + where + msg
                + (if src = "" then "" else "\n    " + src + caret)
            | None -> where + msg
        let lineColOf (path : string) (off : int) : int * int =
            let text = this.FileText path
            let cut = if off < text.Length then off else text.Length
            let upto = (text.Substring (0, cut)).Replace ("\r", "")
            let ls = upto.Split '\n'
            ls.Length - 1, (if ls.Length > 0 then ls.[ls.Length - 1].Length else 0)
        let blameAt (path : string) (off : int) (msg : string) : string =
            let line, col = lineColOf path off
            blame path line col msg

        let lowerOne (path : string) (root : Syntax.GreenNode) =
            match dictTryFind r.Files path with
            | Some (b, inf) ->
                let ok = dictNew<int, string> ()
                for off, k in inf.OpKinds do dictSet ok off k
                let ak = dictNew<int, string> ()
                for off, k in inf.ArrKinds do dictSet ak off k
                let ik = dictNew<int, string list> ()
                for off, i in inf.InstSites do dictSet ik off i
                let ms = dictNew<int, string> ()
                for off, o in inf.MemberSites do dictSet ms off o
                let fo = dictNew<int, string> ()
                for off, o in inf.FieldOwners do dictSet fo off o
                let cs = dictNew<int, int> ()
                for off, o in inf.CtorSites do dictSet cs off o
                let cu = dictNew<int, Analysis.Classes.InstMember> ()
                for off, m in inf.ClassUses do dictSet cu off m
                let cp = dictNew<int, string> ()
                for off, t in inf.ClassPending do dictSet cp off t
                let ot = dictNew<int, string> ()
                for off, t in inf.OpTypes do dictSet ot off t
                let ep = dictNew<int, (string * int * string * string list) list> ()
                for off, fns in inf.ExistPack do dictSet ep off fns
                let ecs = dictNew<string, int> ()
                for cn, nm in inf.ExistCases do dictSet ecs cn nm
                let em = dictNew<int, string> ()
                for off, cn in inf.ExistMatch do dictSet em off cn
                let du = dictNew<int, int * int> ()
                for off, pm in inf.DictUses do dictSet du off pm
                let low = Fpp.Core.Lower.lower path root b r.Schemes ok ak ik ms fo cs r.Members r.Fields r.Interfaces cu cp ot r.Aliases inf.ArbDerive ep ecs em du
                for d in this.RunPerFile low.Decls do vecAdd allDecls d
                for off, why in low.Notes do
                    vecAdd errs (blameAt path off ("not lowerable: " + why))
            | None -> ()
        for path in this.ProjectFiles do
            for d in this.Diagnostics path do
                vecAdd errs (blame path d.Line d.Col d.Message)
        // builtin decls (Option etc.) come first — from the process cache
        let cached = BuiltinCache.force ()
        let bp = cached.Parse
        let bb = cached.Bind
        // the prelude is source like any other file: its own bodies call the
        // class members it declares, so it needs its own tables
        let bi = r.BuiltinInfer
        let bok = dictNew<int, string> ()
        for k, v in bi.OpKinds do dictSet bok k v
        let bak = dictNew<int, string> ()
        for k, v in bi.ArrKinds do dictSet bak k v
        let bik = dictNew<int, string list> ()
        for k, v in bi.InstSites do dictSet bik k v
        let bms = dictNew<int, string> ()
        for k, v in bi.MemberSites do dictSet bms k v
        let bfo = dictNew<int, string> ()
        for k, v in bi.FieldOwners do dictSet bfo k v
        let bcs = dictNew<int, int> ()
        for k, v in bi.CtorSites do dictSet bcs k v
        let bcu = dictNew<int, Analysis.Classes.InstMember> ()
        for k, v in bi.ClassUses do dictSet bcu k v
        let bcp = dictNew<int, string> ()
        for k, v in bi.ClassPending do dictSet bcp k v
        let bot = dictNew<int, string> ()
        for k, v in bi.OpTypes do dictSet bot k v
        let bep = dictNew<int, (string * int * string * string list) list> ()
        for off, fns in bi.ExistPack do dictSet bep off fns
        let becs = dictNew<string, int> ()
        for cn, nm in bi.ExistCases do dictSet becs cn nm
        let bem = dictNew<int, string> ()
        for off, cn in bi.ExistMatch do dictSet bem off cn
        let bdu = dictNew<int, int * int> ()
        for off, pm in bi.DictUses do dictSet bdu off pm
        let blow =
            Fpp.Core.Lower.lower Builtin.path bp.Root bb r.Schemes bok bak bik bms bfo bcs
                r.Members r.Fields r.Interfaces bcu bcp bot r.Aliases bi.ArbDerive bep becs bem bdu
        for d in blow.Decls do vecAdd allDecls d
        // one function per primitive instance member, so `Add.(+)` denotes
        // something callable even where `a + b` is a machine instruction
        for d in Fpp.Core.Link.builtinInstanceWrappers r.Classes do vecAdd allDecls d
        for path in this.ProjectFiles do
            lowerOne path (this.ParseFile path).Root
        // linked library declarations join the program before emission
        let libDecls = vecNew<Fpp.Core.Ir.Decl> ()
        for _, text in this.Libraries do
            let _, _, ds = Fpp.Core.Serialize.decodeLib text
            for d in ds do vecAdd libDecls d
        for pe in this.PluginErrors do vecAdd errs pe
        if vecLen errs > 0 then [], vecToList errs
        else
            let program = this.RunWholeProgram (vecToList libDecls @ vecToList allDecls)
            // tier-1: stamp per struct instantiation, share one body for
            // reference instantiations, error on anything unclassifiable
            let structNames =
                program
                |> List.choose (fun d ->
                    match d with
                    | Fpp.Core.Ir.DRecord (n, _, _, true) -> Some n
                    | _ -> None)
            let isStruct (n : string) = List.contains n structNames
            // an instance member is the operator's implementation once
            // stamping has made the operand type concrete
            let instanceFns = Fpp.Core.Link.instanceFunctions r.Classes
            let mono0, monoErrs = Fpp.Core.Link.monomorphizeWith isStruct instanceFns program
            // stamped clones have concrete instantiations, so record layouts
            // can only be settled once monomorphization has run
            let mono = Fpp.Core.Link.stampRecords mono0
            // optimization runs on the MONOMORPHIC ir: every call is
            // concrete here, and dead-code elimination afterwards collects
            // the definitions inlining made unreachable
            let opt = if optimize then Fpp.Core.Optimize.optimize mono else mono
            let linked = Fpp.Core.Link.deadCodeEliminate opt
            if not (List.isEmpty monoErrs) then [], monoErrs
            else linked, []

    member private this.EmitCoreMapped (optimize : bool) (mapUrl : string) : byte[] * string list =
        let linked, errs = this.LinkedCore optimize
        if not (List.isEmpty errs) then [||], errs
        else
            let bytes, berrs, warns, positions =
                Fpp.Backend.BinDriver.emitBinaryWithPositions mapUrl linked
            for w in warns do ewarn ("warn: " + w)
            lastPositions <- positions
            bytes, berrs

    /// The program as ONE C translation unit against the fpprt runtime
    /// (runtime/): gcc for native, emcc for wasm-linear. PLAN-CBACK.md.
    member this.EmitProgramC () : string * string list =
        let linked, errs = this.LinkedCore true
        if not (List.isEmpty errs) then "", errs
        else Fpp.Backend.CEmit.emitC linked

    /// The program as a direct .wasm module: bytes out, no text anywhere.
    member this.EmitProgramWasm () : byte[] * string list = this.EmitCore true

    /// The program AND its source map. The module carries a `sourceMappingURL`
    /// custom section naming `mapUrl`, so a browser loads the map and shows the
    /// .fpp files — with their text embedded, so the sources need not be
    /// fetchable separately.
    member this.EmitProgramWasmWithSourceMap (mapUrl : string) : byte[] * string * string list =
        // NOT optimized: inlining dissolves frames and moves code between
        // lines, and a debugger that disagrees with the source is worse than
        // no debugger. A debug build is for stepping; ship the plain one.
        let bytes, errs = this.EmitCoreMapped false mapUrl
        let sources =
            // the prelude too, under the path its declarations carry: stepping
            // into a library function should show that function, not nothing
            ("(builtin)", Fpp.Prelude.preludeSource ())
            :: (this.ProjectFiles |> List.map (fun p -> p, this.FileText p))
        let map = Fpp.Backend.SourceMap.build mapUrl lastPositions sources
        bytes, map, errs

    /// Produce a fat-IR library from the current project files.
    member this.BuildLibrary () : string * string list =
        let r = this.ProjectCheck ()
        let errs = vecNew<string> ()
        let decls = vecNew<Fpp.Core.Ir.Decl> ()
        let exports = vecNew<string * Analysis.Resolve.Definition> ()
        for path in this.ProjectFiles do
            for d in this.Diagnostics path do
                vecAdd errs (path + ": " + d.Message)
            match dictTryFind r.Files path with
            | Some (b, inf) ->
                for e in b.Exports do vecAdd exports e
                let ok = dictNew<int, string> ()
                for off, k in inf.OpKinds do dictSet ok off k
                let ak = dictNew<int, string> ()
                for off, k in inf.ArrKinds do dictSet ak off k
                let ik = dictNew<int, string list> ()
                for off, i in inf.InstSites do dictSet ik off i
                let ms = dictNew<int, string> ()
                for off, o in inf.MemberSites do dictSet ms off o
                let fo = dictNew<int, string> ()
                for off, o in inf.FieldOwners do dictSet fo off o
                let cs = dictNew<int, int> ()
                for off, o in inf.CtorSites do dictSet cs off o
                let cu = dictNew<int, Analysis.Classes.InstMember> ()
                for off, m in inf.ClassUses do dictSet cu off m
                let cp = dictNew<int, string> ()
                for off, t in inf.ClassPending do dictSet cp off t
                let ot = dictNew<int, string> ()
                for off, t in inf.OpTypes do dictSet ot off t
                let ep = dictNew<int, (string * int * string * string list) list> ()
                for off, fns in inf.ExistPack do dictSet ep off fns
                let ecs = dictNew<string, int> ()
                for cn, nm in inf.ExistCases do dictSet ecs cn nm
                let em = dictNew<int, string> ()
                for off, cn in inf.ExistMatch do dictSet em off cn
                let du = dictNew<int, int * int> ()
                for off, pm in inf.DictUses do dictSet du off pm
                let low = Fpp.Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Fields r.Interfaces cu cp ot r.Aliases inf.ArbDerive ep ecs em du
                for d in low.Decls do vecAdd decls d
            | None -> ()
        let schemes =
            dictPairs r.Schemes
            |> List.filter (fun (k, _) -> not (k.StartsWith "(builtin)"))
        for pe in this.PluginErrors do vecAdd errs pe
        if vecLen errs > 0 then "", vecToList errs
        else Fpp.Core.Serialize.encodeLib (vecToList exports) schemes (vecToList decls), []

    /// Lower a file to typed core (Stage 3). Runs on top of the project check.
    member this.LowerFile (path : string) : Core.Ir.LowerResult =
        let r = this.ProjectCheck ()
        match dictTryFind r.Files path with
        | Some (b, inf) ->
            let ok = dictNew<int, string> ()
            for off, k in inf.OpKinds do dictSet ok off k
            let ak = dictNew<int, string> ()
            for off, k in inf.ArrKinds do dictSet ak off k
            let ik = dictNew<int, string list> ()
            for off, i in inf.InstSites do dictSet ik off i
            let ms = dictNew<int, string> ()
            for off, o in inf.MemberSites do dictSet ms off o
            let fo = dictNew<int, string> ()
            for off, o in inf.FieldOwners do dictSet fo off o
            let cs = dictNew<int, int> ()
            for off, o in inf.CtorSites do dictSet cs off o
            let cu = dictNew<int, Analysis.Classes.InstMember> ()
            for off, m in inf.ClassUses do dictSet cu off m
            let cp = dictNew<int, string> ()
            for off, t in inf.ClassPending do dictSet cp off t
            let ot = dictNew<int, string> ()
            for off, t in inf.OpTypes do dictSet ot off t
            let ep = dictNew<int, (string * int * string * string list) list> ()
            for off, fns in inf.ExistPack do dictSet ep off fns
            let ecs = dictNew<string, int> ()
            for cn, nm in inf.ExistCases do dictSet ecs cn nm
            let em = dictNew<int, string> ()
            for off, cn in inf.ExistMatch do dictSet em off cn
            let du = dictNew<int, int * int> ()
            for off, pm in inf.DictUses do dictSet du off pm
            Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Fields r.Interfaces cu cp ot r.Aliases inf.ArbDerive ep ecs em du
        | None -> { Decls = []; Notes = [] }

    /// Definition for the name whose use (or definition) covers the offset.
    member this.DefinitionAt (path : string) (offset : int) : Analysis.Resolve.Definition option =
        let r = this.Resolve path
        let atUse =
            r.Resolutions
            |> List.tryFind (fun u -> offset >= u.UseOffset && offset < u.UseOffset + u.UseLength)
            |> Option.map (fun u -> u.Def)
        match atUse with
        | Some d -> Some d
        | None ->
            r.Definitions
            |> List.tryFind (fun d -> offset >= d.Offset && offset < d.Offset + d.Length)

    /// Completion candidates: everything the project EXPORTS, plus this
    /// file's own definitions. Not scope-aware — a local from another
    /// binding can still appear — but every entry is real and carries its
    /// generalized type, which is the part that makes a list worth reading.
    /// Returns (label, kind, type, qualified name).
    member this.Completions (path : string) : (string * string * string * string) list =
        let r = this.ProjectCheck ()
        let seen = dictNew<string, bool> ()
        let out = vecNew<string * string * string * string> ()
        let typeOf (d : Analysis.Resolve.Definition) =
            match dictTryFind r.Schemes (d.Path + ":" + string d.Offset) with
            | Some sch -> Analysis.Types.schemeString sch
            | None -> ""
        let offer (label : string) (full : string) (d : Analysis.Resolve.Definition) =
            // a class member is exported twice, bare and as `Class.Member`;
            // one entry per DEFINITION, not per spelling
            let key = label + "/" + d.Path + ":" + string d.Offset
            if (dictTryFind seen key).IsNone then
                dictSet seen key true
                vecAdd out (label, Analysis.Resolve.kindLabel d.Kind, typeOf d, full)
        // the prelude first, so the numeric classes and their members are
        // offered in a project that has not opened anything
        let bb = (BuiltinCache.force ()).Bind
        for full, d in bb.Exports do offer d.Name full d
        for _, (b : Analysis.Resolve.BindResult, _) in dictPairs r.Files do
            for full, d in b.Exports do offer d.Name full d
        match dictTryFind r.Files path with
        | Some (b, _) -> for d in b.Definitions do offer d.Name d.Name d
        | None -> ()
        vecToList out

    member this.HoverAt (path : string) (offset : int) : string option =
        this.DefinitionAt path offset
        |> Option.map (fun d ->
            let basis = Analysis.Resolve.kindLabel d.Kind + " `" + d.Name + "`"
            // the generalized scheme is the better answer where there is one:
            // it carries the class context, which is most of what a reader
            // needs from a signature in this language. It also works when the
            // definition lives in ANOTHER file, where this file's DefTypes
            // has nothing to say.
            let scheme =
                dictTryFind (this.ProjectCheck ()).Schemes (d.Path + ":" + string d.Offset)
            match scheme with
            | Some sch -> basis + " : " + Analysis.Types.schemeString sch
            | None ->
                match (this.TypeCheck d.Path).DefTypes |> List.tryFind (fun (off, _, _) -> off = d.Offset) with
                | Some (_, _, ts) -> basis + " : " + ts
                | None -> basis)

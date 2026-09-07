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
      /// carried so `fpp lib` can ship what the LIBRARY declared: these are
      /// project-wide tables a consumer cannot rediscover from decls alone
      Impls : Fpp.Prelude.Dict<string, string list>
      ImplTys : Fpp.Prelude.Dict<string, (Analysis.Types.Var list * Analysis.Types.Type) list>
      StructTypes : Fpp.Prelude.Dict<string, bool>
      Ctors : Fpp.Prelude.Dict<string, (int * Analysis.Types.Scheme) list>
      BuiltinInfer : Analysis.Infer.InferResult }

/// The prelude is a process-wide CONSTANT: parse, resolve and infer it once,
/// then seed every project with COPIES of its tables. Without this every
/// Workspace re-inferred ~1400 prelude lines, which the test suite (one
/// Workspace per test) paid hundreds of times over.
/// The prelude snapshot, as TEXT. The compiler library neither reads nor
/// writes it — the host hands in whatever it found and takes back whatever
/// was produced.
///
/// File IO does not belong here: `Workspace.fs` is COMPILED BY THIS
/// COMPILER, and a host API the self-hosted build does not implement
/// becomes a stub that takes its whole enclosing function with it. Reading
/// the cache from here trapped the self-host at module init — the fixpoint
/// caught it, nothing else did.
module PreludeCache =
    /// what the host loaded; "" for none
    let mutable input : string = ""
    /// what a MISS produced and the host should store; "" for nothing
    let mutable output : string = ""
    /// whether the host will actually STORE what a miss produces. OFF by
    /// default, and not a micro-optimisation: building a snapshot nobody
    /// reads costs a 2.4 MB string (three times over, for the round-trip
    /// check) and everything it is built from. Under the WASM-HOSTED
    /// compiler, which can store nothing, that ran the self-host out of
    /// memory against wasm32's 2 GB — the fixpoint failed with "we have the
    /// space but mmap didn't work" and no diagnostic anywhere else.
    let mutable wanted : bool = false

    /// FNV-1a over the prelude text, carried INSIDE the snapshot and checked
    /// on the way in. The host keys its file by the compiler binary, which
    /// cannot see a prelude edited underneath it.
    let srcHash (t : string) : string =
        let mutable a = 166136261
        let mutable b = 97
        for i in 0 .. strLen t - 1 do
            let c = int (charAt t i)
            a <- ((a ^^^ c) * 16777619) &&& 0x3FFFFFFF
            b <- ((b * 31) + c) &&& 0x3FFFFFFF
        string a + "x" + string b

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
        // type-path vectors grow as a project declares types — own copies too
        let tps = dictNew<string, Fpp.Prelude.Vec<string>> ()
        for k, v in dictPairs t.TypePaths do
            let nv = vecNew<string> ()
            for x in vecToList v do vecAdd nv x
            dictSet tps k nv
        { Classes = copyDict t.Classes
          Instances = inst
          MemberOwner = copyDict t.MemberOwner
          TypePaths = tps
          LogPicks = dictNew<string, bool> ()
          PickLog = Fpp.Prelude.vecNew<string> () }

    let compute (defines : string list) =
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
            // the prelude preprocesses like any other source: `#if NATIVE`
            // is how it gives the fpprt leg real monitors while the
            // single-threaded oracle keeps the no-op truth
            let src = fst (Fpp.Project.preprocess defines Builtin.source)
            // the tree is always built: it is what LOWERING walks, and
            // lowering is not cached (see below)
            let bp = Parser.parse src
            // the guard is HERE, not inside tryLoad: the self-hosted
            // compiler may stub an unsupported host API, and a stub takes
            // the whole enclosing function with it — so a disabled cache
            // must not CALL into the disk path at all, only skip it
            let wantHash = PreludeCache.srcHash src
            match (if PreludeCache.input = "" then None
                   else
                       match Fpp.Core.Serialize.decodePrelude PreludeCache.input with
                       // the host keys its file by the COMPILER binary, which
                       // cannot notice a prelude edited underneath it — so the
                       // snapshot carries its source's hash and is refused here
                       | Some sn when sn.PSrcHash = wantHash -> Some sn
                       | _ -> None) with
            | Some snap ->
                // the id supply is restored to where the run that wrote this
                // left it, so a project variable minted next gets the id it
                // would have got anyway
                Analysis.Types.reserveIds snap.PIdSupply
                { Parse = bp; Bind = snap.PBind; Inferred = snap.PInferred
                  Imports = snap.PImports; Schemes = snap.PSchemes
                  Aliases = snap.PAliases; Fields = snap.PFields
                  Ifaces = snap.PIfaces; Bases = snap.PBases; Impls = snap.PImpls
                  ImplTys = snap.PImplTys; StructTypes = snap.PStructTypes
                  Ctors = snap.PCtors; Classes = snap.PClasses
                  Members = snap.PMembers }
            | None ->
            let bb = Analysis.Resolve.resolve Builtin.path imports bp.Root
            for full, d in bb.Exports do dictSet imports full d
            for k, d in bb.Members do dictSet members k d
            let binf =
                Analysis.Infer.infer Builtin.path bp.Root bb schemes aliases fields ifaces bases impls implTys structTypes ctors classes
            // AFTER inference, so the mark covers every variable the prelude
            // minted — including ones no table still mentions
            (if not PreludeCache.wanted then () else
             match Fpp.Core.Serialize.encodePrelude
                       { PIdSupply = Analysis.Types.idSupplyMark ()
                         PSrcHash = wantHash
                         PImports = imports; PMembers = members; PSchemes = schemes
                         PAliases = aliases; PFields = fields; PIfaces = ifaces
                         PBases = bases; PImpls = impls; PImplTys = implTys
                         PStructTypes = structTypes; PCtors = ctors; PClasses = classes
                         PInferred = binf; PBind = bb } with
             | Some t -> PreludeCache.output <- t
             | None -> ())
            { Parse = bp; Bind = bb; Inferred = binf; Imports = imports
              Schemes = schemes; Aliases = aliases; Fields = fields
              Ifaces = ifaces; Bases = bases; Impls = impls; ImplTys = implTys
              StructTypes = structTypes; Ctors = ctors; Classes = classes
              Members = members }
    // Memoized by hand rather than with `lazy`: one cell, computed on first
    // use. F#'s `lazy` adds thread safety this single-threaded cache does
    // not need, and it is not part of the subset the compiler compiles.
    // keyed by the DEFINE SET: the prelude preprocesses per target, so a
    // NATIVE workspace and a WASM one see different prelude text in the
    // same process (the test suite makes both)
    let mutable cells : (string * Cached) list = []
    let force (defines : string list) : Cached =
        let key = String.concat ";" (List.sort defines)
        match cells |> List.tryFind (fun (k, _) -> k = key) with
        | Some (_, c) -> c
        | None ->
            let c = compute defines
            cells <- (key, c) :: cells
            c

// serializes wasm-linear emissions: WasmLin's state is module-global
module private WasmLinGate =
    let gate = obj ()

type Workspace() =
    let db = Db()
    /// What a computation expression asked its builder for and did not get,
    /// per file. Collected during the REWRITE — the only pass that knows
    /// which control constructs a CE used — and merged into the file's
    /// diagnostics, because the rewrite's own tokens are synthetic and the
    /// missing-member check deliberately ignores those.
    let ceDiagsByPath = dictNew<string, Fpp.Prelude.Vec<int * string>> ()
    // the ORACLE's view by default — the LSP and the tests see #if WASM
    // code; the CLI overrides per build target
    let mutable defines : string list = [ "WASM" ]
    do db.SetInput "project" "" (box ([] : string list))
    do db.SetInput "libs" "" (box ([] : (string * string) list))
    // the prelude pseudo-file reads like any other: definition jumps and
    // line math land on it (hover already takes the cached-inference path)
    do db.SetInput "text" Builtin.path (box Builtin.source)
    let plugins = vecNew<Fpp.Core.Plugins.Plugin> ()
    let generators = vecNew<Fpp.Core.Plugins.Generator> ()
    /// plugins written in F++ ITSELF: name and sources, compiled and RUN at
    /// compile time
    let fppGenerators = vecNew<string * (string * string) list> ()
    /// external generator COMMANDS (`generator <cmd>` in the project):
    /// (display name, command line, working directory)
    let cmdGenerators = vecNew<string * string * string> ()
    /// generated path -> the generator that wrote it, for blaming diagnostics
    let generatedBy = dictNew<string, string> ()
    /// where each piece of the last emitted module came from
    /// record instance selections for the pick checker (set BEFORE the
    /// first check — the project check is memoized)
    let mutable logPicks = false
    /// the backend warnings of the last emit — a stub here means a
    /// function that will TRAP if reached; `fpp build --strict` fails on
    /// them instead of warning, since a clean check that hands over a
    /// trapping binary was this project's most repeated bug shape
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

    member _.AddCommandGenerator (name : string, cmd : string, workDir : string) : unit =
        vecAdd cmdGenerators (name, cmd, workDir)

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
        // the manifest's `define` symbols join whatever the target already set
        for d in r.Loaded.Defines do
            if not (List.contains d this.Defines) then
                this.Defines <- this.Defines @ [ d ]
        let open_ = this.ProjectFiles |> Set.ofList
        for l in r.Loaded.Libs do
            match hostReadText l with
            | Some text -> this.AddLibrary l text
            | None -> ()
        db.SetInput "project" "" (box r.Loaded.Sources)
        for s in r.Loaded.Sources do
            if not (Set.contains s open_) then
                let text = match hostReadText s with Some t -> t | None -> ""
                let text2, _ = Fpp.Project.preprocess this.Defines text
                db.SetInput "text" s (box text2)
        let projDir =
            let i = r.Loaded.Path.LastIndexOf '/'
            if i > 0 then r.Loaded.Path.Substring (0, i) else "."
        r.Loaded.Generators
        |> List.iteri (fun i cmd ->
            let gname =
                let first = (cmd.Split ' ').[0]
                let j = first.LastIndexOf '/'
                (if j >= 0 then first.Substring (j + 1) else first) + (if i = 0 then "" else string i)
            this.AddCommandGenerator (gname, cmd, projDir))
        r.Loaded, r.Errors

    /// conditional-compilation symbols; the CLI sets WASM or NATIVE from
    /// the build target before feeding sources
    member _.Defines
        with get () : string list = defines
        and set (v : string list) = defines <- v

    member this.SetFileText (path : string) (text : string) : unit =
        // unknown files join the project in arrival order (LSP didOpen)
        let files = this.ProjectFiles
        if not (List.contains path files) then
            db.SetInput "project" "" (box (files @ [ path ]))
        // `#if` regions are resolved HERE, before the lexer: blanked to
        // spaces, so every byte offset survives untouched
        let text2, _ = Fpp.Project.preprocess this.Defines text
        db.SetInput "text" path (box text2)

    member _.FileText (path : string) : string =
        unbox<string> (db.GetInput "text" path)

    /// The parse EXACTLY as written — the tree the round-trip gate and the
    /// editor's view of the text are about.
    /// Every ACTIVE-PATTERN definition in the project (and in linked
    /// libraries, whose exports carry the `$ap$...` names): the parser's
    /// use-site rewrite is PARSE-time and its tables are per-file, so a
    /// cross-file use needs this seed. A memo, not an input — it reads the
    /// file texts, so editing a definer invalidates every parse through it.
    /// Every `[<CustomOperation("op")>] member T.Method` across the project,
    /// as (builder type, op name, method name) — a builder declared in one
    /// file and used in another needs this, exactly as active patterns do.
    /// Scanned from the parse trees (attribute + member are green nodes), so
    /// no inference and no cycle. A memo over the file texts.
    member private this.CustomOpSeed () : (string * string * string) list =
        db.MemoT "customopseed" "" (fun () ->
            let out = vecNew<string * string * string> ()
            let rec scan (curType : string) (g : Green) : unit =
                match g with
                | GToken _ -> ()
                | GNode n when n.NodeKind = TypeDecl ->
                    let tn =
                        Green.tokens (GNode n)
                        |> List.filter (fun t -> t.Kind = Ident)
                        |> List.tryHead
                        |> Option.map (fun t -> t.Text)
                    let ty = match tn with Some t -> t | None -> curType
                    // a preceding AttributeList applies to the next MemberDecl
                    let mutable pending : string option = None
                    for c in n.Children do
                        match c with
                        | GNode a when a.NodeKind = AttributeList ->
                            let ats = Green.tokens (GNode a)
                            if ats |> List.exists (fun t -> t.Kind = Ident && t.Text = "CustomOperation") then
                                (match ats |> List.tryFind (fun t -> t.Kind = StringLit) with
                                 | Some st ->
                                     let raw = st.Text
                                     pending <-
                                         Some (if strLen raw >= 2 && charAt raw 0 = '"' && charAt raw (strLen raw - 1) = '"'
                                               then substr raw 1 (strLen raw - 2) else raw)
                                 | None -> ())
                        | GNode m when m.NodeKind = MemberDecl ->
                            (match pending with
                             | Some opn ->
                                 // the method name is the last ident BEFORE
                                 // the first `(` — `member x.Texture (s, t)`
                                 // has idents [x; Texture] there; the body's
                                 // idents (a `tryLast` over the whole member)
                                 // grabbed those instead
                                 let toksBeforeParen =
                                     let rec upto acc (ts : Token list) =
                                         match ts with
                                         | t :: _ when t.Kind = LParen -> List.rev acc
                                         | t :: rest -> upto (t :: acc) rest
                                         | [] -> List.rev acc
                                     upto [] (Green.tokens (GNode m))
                                 let mn = toksBeforeParen |> List.filter (fun t -> t.Kind = Ident) |> List.tryLast
                                 (match mn with Some t -> vecAdd out (ty, opn, t.Text) | None -> ())
                             | None -> ())
                            pending <- None
                            scan ty c
                        | GNode _ -> scan ty c
                        | GToken _ -> ()
                | GNode n -> for c in n.Children do scan curType c
            for pth in this.ProjectFiles do scan "" (GNode (this.ParseRaw pth).Root)
            vecToList out)

    member private this.ApSeed () : Parser.ApDef list =
        db.MemoT "apseed" "" (fun () ->
            let fromFiles =
                this.ProjectFiles
                |> List.collect (fun p -> Parser.scanActivePatterns (this.FileText p))
            let fromLibs =
                this.Libraries
                |> List.collect (fun (_, text) ->
                    (Fpp.Core.Serialize.decodeLib text).LExports
                    |> List.collect (fun (full, d) ->
                        if d.Name.StartsWith "$ap$" then
                            let parts = (substr d.Name 4 (strLen d.Name - 4)).Split '$' |> List.ofArray
                            let partial = (match List.tryLast parts with Some "_" -> true | _ -> false)
                            let names = parts |> List.filter (fun c -> c <> "_")
                            ignore full
                            names |> List.mapi (fun ix c ->
                                { Parser.ApCase = c; Parser.ApFn = d.Name; Parser.ApIndex = ix
                                  Parser.ApCount = List.length names; Parser.ApPartial = partial
                                  // extra use-site parameters are not
                                  // recoverable from the export name alone;
                                  // 0 covers every matcher shape
                                  Parser.ApParams = 0 })
                        else []))
            if System.Environment.GetEnvironmentVariable "FPP_APSEED_DBG" = "1" then
                for r in fromFiles @ fromLibs do
                    eprintfn "APSEED %s -> %s idx=%d n=%d partial=%b params=%d" r.ApCase r.ApFn r.ApIndex r.ApCount r.ApPartial r.ApParams
            fromFiles @ fromLibs)

    member this.ParseRaw (path : string) : Parser.ParseResult =
        db.MemoT "parse" path (fun () ->
            let p = Parser.parseSeeded (this.ApSeed ()) (this.FileText path)
            // `lazy e` -> `Lazy (fun () -> e)`, here so EVERY consumer of a
            // parse sees the rewritten form (the raw parse stays lossless
            // for the round-trip tests, which call the parser directly)
            let p = if Desugar.hasLazy (GNode p.Root) then { p with Root = Desugar.desugarLazy p.Root } else p
            let p = if Desugar.hasMemberVal p.Root then { p with Root = Desugar.desugarMemberVal p.Root } else p
            // `[<Literal>] let N = 10` makes N a PATTERN constant
            if Desugar.hasLiteralDecl p.Root then { p with Root = Desugar.desugarLiteralPats p.Root } else p)

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
            let cached = BuiltinCache.force defines
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
            if logPicks then dictSet classes.LogPicks "on" true
            // members are looked up by "Type.Member" across the whole
            // project, not just the file that declares them
            let members = BuiltinCache.copyDict cached.Members
            let results = dictNew<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult> ()
            let binf = cached.Inferred
            // linked libraries: exports feed the resolver, schemes feed inference
            for _, text in this.Libraries do
                let lc = Fpp.Core.Serialize.decodeLib text
                let exps = lc.LExports
                let schs = lc.LSchemes
                let lds = lc.LDecls
                for full, d in exps do dictSet imports full d
                for k, sch in schs do dictSet schemes k sch
                // The TABLES a library declares. Without these a class or a
                // type MEMBER declared inside the library is invisible: its
                // instances live nowhere, so `$class:Real:Pi:float` resolves
                // to nothing and the backend stubs whatever mentions it.
                //
                // The project's own entries WIN — these are merged first and
                // only where the key is free, so a project may still declare
                // its own type of the same name, exactly as it could when the
                // library was referenced by source.
                for k, v in dictPairs lc.LFields do
                    if (dictTryFind fields k).IsNone then dictSet fields k v
                for k, v in dictPairs lc.LIfaces do
                    if (dictTryFind ifaces k).IsNone then dictSet ifaces k v
                for k, v in dictPairs lc.LBases do
                    if (dictTryFind bases k).IsNone then dictSet bases k v
                for k, v in dictPairs lc.LImpls do
                    if (dictTryFind impls k).IsNone then dictSet impls k v
                for k, v in dictPairs lc.LImplTys do
                    if (dictTryFind implTys k).IsNone then dictSet implTys k v
                for k, v in dictPairs lc.LStructTypes do
                    if (dictTryFind structTypes k).IsNone then dictSet structTypes k v
                for k, v in dictPairs lc.LCtors do
                    if (dictTryFind ctors k).IsNone then dictSet ctors k v
                for k, v in dictPairs lc.LAliases do
                    if (dictTryFind aliases k).IsNone then dictSet aliases k v
                for k, v in dictPairs lc.LClasses.Classes do
                    if (dictTryFind classes.Classes k).IsNone then dictSet classes.Classes k v
                for k, v in dictPairs lc.LClasses.MemberOwner do
                    if (dictTryFind classes.MemberOwner k).IsNone then dictSet classes.MemberOwner k v
                for k, v in dictPairs lc.LClasses.TypePaths do
                    if (dictTryFind classes.TypePaths k).IsNone then dictSet classes.TypePaths k v
                // instances REGISTER rather than overwrite: a class may be
                // extended by both the library and the project, and selection
                // ranks the whole candidate list
                for _, v in dictPairs lc.LClasses.Instances do
                    for i in vecToList v do Analysis.Classes.addInstance classes i
                // MEMBERS too, and before the per-file resolution below: a
                // library's `DMembers` never reached the project-wide
                // "Type.Member" index, so a STATIC member of a library type
                // did not resolve. `M44d.RotationZ 0.5` against fpp.base left
                // a bare reference to the type, and the backend stubbed the
                // enclosing function, which trapped if reached. Instance
                // members were unaffected — they are found through the
                // receiver — which is why only the statics showed it.
                for d in lds do
                    match d with
                    | Fpp.Core.Ir.DMembers (n, own) ->
                        for m, v in own do
                            dictSet members (n + "." + m)
                                { Analysis.Resolve.Name = m
                                  Analysis.Resolve.Kind = Analysis.Resolve.DefMember
                                  Analysis.Resolve.Path = v.Path
                                  Analysis.Resolve.Offset = v.Offset
                                  Analysis.Resolve.Length = strLen m
                                  Analysis.Resolve.Access = 0 }
                    | _ -> ()
            let trees = dictNew<string, Parser.ParseResult> ()
            let mutable tParse = 0
            let mutable tResolve = 0
            let mutable tInfer = 0
            let slowest = vecNew<string * int> ()
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
                        // custom operations, per builder type: op name -> method.
                        // seeded project-wide first (a builder from another
                        // file), then this file's own inference on top.
                        let customOps = dictNew<string, Dict<string, string>> ()
                        for (bt, opName, mName) in this.CustomOpSeed () @ inf0.CustomOps do
                            let d =
                                match dictTryFind customOps bt with
                                | Some d -> d
                                | None -> let d = dictNew<string, string> () in dictSet customOps bt d; d
                            dictSet d opName mName
                        let builders = dictNew<int, Desugar.CeBuilder> ()
                        for off, tyName in inf0.CompBuilders do
                            let has (m : string) = (dictTryFind members0 (tyName + "." + m)).IsSome
                            let copOf (opn : string) : string option =
                                match dictTryFind customOps tyName with
                                | Some d -> dictTryFind d opn
                                | None -> None
                            dictSet builders off
                                { Name = tyName
                                  At = off
                                  Has = has
                                  HasRun = has "Run"
                                  HasDelay = has "Delay"
                                  HasReturn = has "Return"
                                  HasBindReturn = has "BindReturn"
                                  HasBind2 = has "Bind2"
                                  HasBind3 = has "Bind3"
                                  HasBind2Return = has "Bind2Return"
                                  HasBind3Return = has "Bind3Return"
                                  HasMergeSources = has "MergeSources"
                                  HasMergeSources3 = has "MergeSources3"
                                  CustomOp = copOf }
                        let lookup (off : int) =
                            match dictTryFind builders off with
                            | Some b -> b
                            | None -> Desugar.unknownBuilder "?"
                        let stmts = dictNew<int, bool> ()
                        for off in inf0.CompStatements do dictSet stmts off true
                        let isStatement (off : int) = (dictTryFind stmts off).IsSome
                        let vals = dictNew<int, bool> ()
                        for off in inf0.CompValues do dictSet vals off true
                        let isValue (off : int) = (dictTryFind vals off).IsSome
                        let rewritten, ceDiags = Desugar.desugarWithDiags lookup isStatement isValue raw.Root
                        (if not (List.isEmpty ceDiags) then
                            let v = vecNew<int * string> ()
                            for d in ceDiags do vecAdd v d
                            dictSet ceDiagsByPath path v)
                        { raw with Root = rewritten }
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
                let ds = (Fpp.Core.Serialize.decodeLib text).LDecls
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
              Aliases = aliases
              Impls = impls; ImplTys = implTys; StructTypes = structTypes; Ctors = ctors
              BuiltinInfer = binf })

    /// The LINKED (monomorphized, DCE'd) top-level names for the wasm-linear
    /// target. The stamping tests used to read clone names out of the emitted
    /// module's name section; the linear emitter names functions by hash, so
    /// they assert on the names the stamper actually produced instead.
    member this.LinkedNames () : string list =
        let linked, _ = this.LinkedCoreFor false true
        linked
        |> List.choose (fun d ->
            match d with
            | Fpp.Core.Ir.DLet (_, v, _, _) -> Some v.Name
            | _ -> None)

    /// Turn on selection recording — call before the first check.
    member this.RecordPicks () : unit = logPicks <- true
    /// The backend warnings of the last emit (each stub names its function
    /// and why it could not be compiled).
    member this.EmitWarnings : string list = Fpp.Backend.WasmLin.lastWarnings ()
    /// The recorded selections, one line each (see Classes.select).
    member this.InstancePicks : string list =
        vecToList (this.ProjectCheck ()).Classes.PickLog

    member this.TypeCheck (path : string) : Analysis.Infer.InferResult =
        // the prelude is a PSEUDO-file: its inference result is cached on
        // the project, never recomputed per path. Falling through to the
        // standalone path asked the query store for text nobody ever set,
        // and hover on any prelude-defined name killed the language server.
        if path = Builtin.path then (this.ProjectCheck ()).BuiltinInfer else
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
            @ (match dictTryFind ceDiagsByPath path with
               | Some v -> vecToList v |> List.map (fun (off, msg) -> at off msg)
               | None -> [])
            // resolver misses with a known fix — a value some module
            // exports but this file never opened — CONFIRMED against
            // inference: only a use that really bottomed out at a fresh
            // variable errors, so a name a later stage owns (a builtin, a
            // class member) never false-positives
            @ (let fresh = Set.ofList t.FreshIdents
               (this.Resolve path).Missing
               |> List.filter (fun (off, _) -> Set.contains off fresh)
               |> List.map (fun (off, msg) -> at off msg))
            // access violations always surface: the use RESOLVED, the
            // definition just forbids it from here
            @ ((this.Resolve path).AccessErrors
               |> List.map (fun (off, msg) -> at off msg))
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
    /// Marks a file as generated: such files are compiled, but never shown to
    /// a generator (the staging rule) and never regenerated from.
    static member GeneratedPrefix = "(generated)/"

    /// Run the registered generators ONCE over the hand-written declarations
    /// and add their output as project files. Generated files land at the END
    /// of the compile order, so they see every user declaration, and each
    /// generator writes to a stable path, so running twice replaces rather
    /// than accumulates.
    /// External COMMAND generators (`generator <cmd>` in the project):
    /// the command runs once with the project's source paths appended, its
    /// STDOUT becomes a generated file after the last type-declaring source
    /// — the same contract an F++ generator has, over a process boundary.
    /// fpp.shader's reflection tool is the first customer: it linked
    /// Fpp.Compiler as a pre-build step because nothing could run it.
    member private this.RunCommandGenerators () : unit =
        if vecLen cmdGenerators > 0 then
            let srcs =
                this.ProjectFiles
                |> List.filter (fun p -> not (p.StartsWith Workspace.GeneratedPrefix))
            for gname, cmd, workDir in vecToList cmdGenerators do
                try
                    let parts = cmd.Split ' ' |> Array.filter (fun x -> x <> "")
                    let psi =
                        System.Diagnostics.ProcessStartInfo (
                            parts.[0],
                            String.concat " " (List.ofArray parts.[1..] @ (srcs |> List.map (fun p -> "\"" + p + "\""))))
                    psi.WorkingDirectory <- workDir
                    psi.RedirectStandardOutput <- true
                    psi.RedirectStandardError <- true
                    use proc = System.Diagnostics.Process.Start psi
                    let out = proc.StandardOutput.ReadToEnd ()
                    let err = proc.StandardError.ReadToEnd ()
                    if not (proc.WaitForExit 120000) then
                        proc.Kill ()
                        vecAdd pluginErrors ("generator '" + gname + "' did not finish within 120s")
                    elif proc.ExitCode <> 0 then
                        vecAdd pluginErrors
                            ("generator '" + gname + "' failed: "
                             + err.Substring (0, min 300 err.Length))
                    else
                        let path = Workspace.GeneratedPrefix + gname + ".fpp"
                        dictSet generatedBy path gname
                        db.SetInput "text" path (box out)
                        let files = this.ProjectFiles
                        if not (List.contains path files) then
                            // the same default anchor an F++ generator gets:
                            // directly after the LAST file declaring a type,
                            // so the output can name every type it derives
                            // from and later files can name IT
                            let anchor =
                                let idxs =
                                    files
                                    |> List.mapi (fun i p -> i, p)
                                    |> List.filter (fun (_, p) ->
                                        not (p.StartsWith Workspace.GeneratedPrefix)
                                        && not (List.isEmpty (Fpp.Core.Plugins.typeDeclsOf p (this.ParseFile p).Root)))
                                    |> List.map fst
                                if List.isEmpty idxs then 0 else List.max idxs
                            let before = files |> List.truncate (anchor + 1)
                            let after = files |> List.skip (min (List.length files) (anchor + 1))
                            db.SetInput "project" "" (box (before @ [ path ] @ after))
                with ex ->
                    vecAdd pluginErrors ("generator '" + gname + "' could not run: " + ex.Message)

    member private this.RunGenerators () : unit =
        // guarded at the CALL, like RunFppGenerators below: the member spawns
        // processes, so the self-hosted compiler stubs it WHOLE — an
        // unconditional call trapped stage-1 at the first build
        if vecLen cmdGenerators > 0 then this.RunCommandGenerators ()
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
                    // the resolver's QUALIFIED target per use offset: module
                    // path + name, so a TName carries what a bare identifier
                    // actually resolved to (a cross-file value, a case)
                    let resolvedNames = dictNew<int, string> ()
                    (match dictTryFind checkedFiles.Files p with
                     | Some (b, _) ->
                         for r in b.Resolutions do
                             let d = r.Def
                             // Name, and the file it came from when that is
                             // another file — enough for a shader compiler to
                             // tell a cross-file/prelude target from a local
                             let full =
                                 if d.Path <> "" && d.Path <> p then d.Name + " @" + d.Path
                                 else d.Name
                             dictSet resolvedNames r.UseOffset full
                     | None -> ())
                    let resolvedAt (off : int) : string option = dictTryFind resolvedNames off
                    { FPath = p
                      FTree = tree
                      FTypeAt = typeAt
                      // the typed tree: syntax with every node's inferred type
                      FTast = Fpp.Core.Plugins.tastOf exprTypeAt resolvedAt tree } : Fpp.Core.Plugins.GenFile)
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
            let userHome = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
            let wasmtime =
                match System.Environment.GetEnvironmentVariable "FPP_WASMTIME" with
                | null | "" -> userHome + "/.wasmtime/bin/wasmtime"
                | p -> p
            // a generator is a REACTOR-LINEAR module now: it imports fpprt, so
            // it runs under --preload. Same resolution order as the CLI's.
            let reactor =
                let candidates =
                    [ System.Environment.GetEnvironmentVariable "FPP_REACTOR"
                      System.IO.Path.Combine (System.AppContext.BaseDirectory, "fpprt_reactor_mmc.wasm")
                      userHome + "/projects/fpp-lowir/tests/tooling/gc/fpprt_reactor_mmc.wasm"
                      userHome + "/projects/fpp-lowir/runtime/build/wasm/fpprt_reactor_mmc.wasm" ]
                match candidates |> List.tryFind (fun c -> not (isNull c) && c <> "" && System.IO.File.Exists c) with
                | Some r -> r
                | None -> userHome + "/projects/fpp-lowir/tests/tooling/gc/fpprt_reactor_mmc.wasm"
            for gname, gsources in vecToList fppGenerators do
                let pw = Workspace()
                pw.SetFileText "(view)/view.fpp" viewSrc
                for path, text in gsources do pw.SetFileText path text
                let bytes, perrs = pw.EmitProgramWasmPreload ()
                if not (List.isEmpty perrs) then
                    for e in perrs |> List.truncate 3 do
                        vecAdd pluginErrors ("F++ generator '" + gname + "' does not compile: " + e)
                else
                    let tmp = System.IO.Path.GetTempFileName () + ".wasm"
                    System.IO.File.WriteAllBytes (tmp, bytes)
                    let psi =
                        System.Diagnostics.ProcessStartInfo (
                            wasmtime,
                            "run -W gc=y,exceptions=y --env FPPRT_HEAP_MB=256 --preload fpprt=" + reactor + " " + tmp)
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


    /// Everything both backends share: generators, check, lower, link,
    /// monomorphize, optimize, DCE. Returns the linked program and any
    /// errors; an erroring program returns an empty decl list.
    member private this.LinkedCore (optimize : bool) : Fpp.Core.Ir.Decl list * string list =
        this.LinkedCoreFor optimize false
    // `forLinear` = the wasm-linear/LowIR target, whose backend unboxes concrete
    // scalars — so monomorphization stamps a specialised clone per boxed-scalar
    // instantiation there, keeping value types out of a box in generics. The
    // wasm-GC and C paths keep the shared body (false).
    member private this.LinkedCoreFor (optimize : bool) (forLinear : bool) : Fpp.Core.Ir.Decl list * string list =
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
                let low = Fpp.Core.Lower.lower path root b r.Schemes ok ak ik ms fo cs r.Members r.Fields r.Interfaces r.Bases cu cp ot r.Aliases inf.ArbDerive inf.OrdDerive inf.ShowDerive inf.ShowTypes inf.StrTypes ep ecs em du
                for d in this.RunPerFile low.Decls do vecAdd allDecls d
                for off, why in low.Notes do
                    vecAdd errs (blameAt path off ("not lowerable: " + why))
            | None -> ()
        for path in this.ProjectFiles do
            for d in this.Diagnostics path do
                vecAdd errs (blame path d.Line d.Col d.Message)
        // builtin decls (Option etc.) come first — from the process cache
        let cached = BuiltinCache.force defines
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
                r.Members r.Fields r.Interfaces r.Bases bcu bcp bot r.Aliases bi.ArbDerive bi.OrdDerive bi.ShowDerive bi.ShowTypes bi.StrTypes bep becs bem bdu
        for d in blow.Decls do vecAdd allDecls d
        // one function per primitive instance member, so `Add.(+)` denotes
        // something callable even where `a + b` is a machine instruction
        for d in Fpp.Core.Link.builtinInstanceWrappers r.Classes do vecAdd allDecls d
        for path in this.ProjectFiles do
            lowerOne path (this.ParseFile path).Root
        // linked library declarations join the program before emission
        let libDecls = vecNew<Fpp.Core.Ir.Decl> ()
        for _, text in this.Libraries do
            let ds = (Fpp.Core.Serialize.decodeLib text).LDecls
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
            let mono0, monoErrs = Fpp.Core.Link.monomorphizeWith forLinear isStruct instanceFns program
            Fpp.Core.Link.keyCollisionCheck mono0
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

    /// The program as ONE C translation unit against the fpprt runtime
    /// (runtime/): gcc for native, emcc for wasm-linear. PLAN-CBACK.md.
    /// The program as a wasm-LINEAR module emitted DIRECTLY — no C
    /// compiler, no emscripten. Slice 1 of the linear backend (see
    /// Backend/WasmLin.fs): the int/string/control-flow subset.
    member this.EmitProgramWasmLinear () : byte[] * string list =
        this.EmitProgramWasmLinearWith false

    /// LowIR wasm-linear in REACTOR mode (the `--gc` flavor: fpprt imports,
    /// Whippet heap). One method so the linear-fixpoint DRIVER and harness
    /// cannot disagree about the flag.
    member this.EmitProgramWasmReactor () : byte[] * string list =
        withLock WasmLinGate.gate (fun () ->
            Fpp.Backend.WasmLin.gc <- true
            Fpp.Backend.WasmLin.intStamped <- Fpp.Core.Link.intStampNarrow
            Fpp.Backend.WasmLin.gcExportMem <- false
            this.EmitProgramWasmLinearWith true)

    /// reactor mode for PRELOAD linking (wasmtime --preload fpprt=reactor):
    /// same module, but the imported memory is re-exported as "memory" so
    /// WASI binds — no wasm-merge in the path. The test harness's emitter.
    member this.EmitProgramWasmPreload () : byte[] * string list =
        withLock WasmLinGate.gate (fun () ->
            Fpp.Backend.WasmLin.gc <- true
            Fpp.Backend.WasmLin.intStamped <- Fpp.Core.Link.intStampNarrow
            Fpp.Backend.WasmLin.gcExportMem <- true
            this.EmitProgramWasmLinearWith true)

    /// `low = true` routes function bodies through the shared LowIR
    /// (Core/LowIR.fs) where the subset covers them, else the hand-lowering.
    member this.EmitProgramWasmLinearWith (low : bool) : byte[] * string list =
      // WasmLin keeps its emission state in module-level mutables (the gc
      // flags, the jslin/jsxl/env registries), so two concurrent emissions
      // interleave into garbage. Monitor is re-entrant, so the flag-setting
      // wrappers above can hold the same gate.
      withLock WasmLinGate.gate (fun () ->
        // the linear backend lowers UNOPTIMIZED core: the wasm-GC optimizer's
        // inlining shares and beta-reduces lambda nodes, which the reference-
        // keyed lambda lift is not built for. Slice work first, speed later.
        // bake the prelude text so a WasmLin-hosted COMPILER (the only thing that
        // references preludeSourceRaw) can load its own prelude; ordinary programs
        // never touch it, so the constant is not emitted for them.
        Fpp.Backend.WasmLin.preludeSrc <- Fpp.Prelude.preludeSource ()
        let linked0, errs = this.LinkedCoreFor false true
        // INLINING, for the by-value struct work. The note on `Optimize.optimize`
        // measured this pass as worthless and said why: on an all-anyref IR the
        // copied body boxed exactly as the call did, so nothing was enabled. A
        // struct now crosses a call in REGISTERS and returns through a
        // destination, so inlining a small struct accessor removes a real
        // memory round trip. Measured on box-extend: a non-inlined struct
        // return costs clang 166 ms in this same engine and costs us 152 — the
        // ABI is not the gap, the call is.
        // ON BY DEFAULT; FPP_INLINE=0 turns it off for a bisection.
        //
        // What it is worth, measured on the fpp.base benchmarks against .NET:
        // rot-transform 1.30x -> 0.90x, rot-compose 1.33x -> 1.00x,
        // transform-trafo 4.25x -> 1.86x, transform-m44 3.27x -> 2.15x,
        // ray-triangle 4.58x -> 4.24x. That is the pass the old note on
        // `Optimize.optimize` said would start paying "with the unboxing
        // work" — the by-value struct ABI is that work, and it does.
        //
        // It was opt-in while two things were open, and both are closed. The
        // first was a lost BOX: an inlined body dropped a box the call
        // boundary used to place, so a large uint32 reached a consumer as a
        // raw even word and was read as a heap pointer — `[ 3u; 1u; 2u;
        // 4000000000u ]` sorted faulted at 0xee6b2800, which is the value
        // itself. That was the inliner RENAMING binders; it keeps the
        // originals now (see `expand`) and the repro prints.
        //
        // The second was the SELF-HOST: stage-1 did not reproduce stage-0.
        // That one was not the inliner at all — `inlineMax` took its default
        // from `System.Int32.MaxValue`, which the self-hosted compiler does
        // not have and read as ZERO, so stage-1 capped itself at "inline no
        // sites" while stage-0 inlined 2277. Same source, same flags, a
        // smaller binary. It reads the flag with `intOr` now and the fixpoint
        // is byte-exact with the pass on.
        let linked =
            if System.Environment.GetEnvironmentVariable "FPP_INLINE" = "0" then linked0
            else
                // fuseTuples AFTER inlining: an inlined tupled call leaves
                // `let t = (a, b) in match t with (x, y) -> ...`, and fusing
                // it back into two lets is what keeps the arguments in
                // registers. Without it inlining is a large REGRESSION.
                Fpp.Core.Optimize.fuseTuples (Fpp.Core.Optimize.inlineCalls linked0)
        // LOOP-INVARIANT CODE MOTION, after inlining because an un-inlined
        // call hides the arithmetic that would move. ON by default;
        // FPP_LICM=0 turns it off for a bisection.
        //
        // Worth, on the fpp.base benchmarks: ray/triangle 98 -> 52 ms and
        // Trafo3d.TransformPos 39 -> 21 (both with repeat inlining, which is
        // what exposes the arithmetic to move). Moeller-Trumbore builds `e1`,
        // `e2`, `pv`, `det` and `inv` from the triangle and the ray direction
        // and none of them move, so all five were recomputed two million
        // times. clang's wasm holds 8 multiplies in that loop where the
        // source writes 15.
        let linked =
            if System.Environment.GetEnvironmentVariable "FPP_LICM" = "0" then linked
            else Fpp.Core.Optimize.hoistInvariants linked
        if System.Environment.GetEnvironmentVariable "FPP_CORE_DUMP" = "1" then
            for d in linked do
                match d with
                | Fpp.Core.Ir.DLet (_, v, _, e) when v.Path <> "(builtin)" ->
                    eprintfn "COREDECL %s:%d %s = %s" v.Path v.Offset v.Name (Fpp.Core.Ir.printExpr e)
                | Fpp.Core.Ir.DLet (_, v, _, e) ->
                    // builtin bodies are dumped only when asked by NAME, so a
                    // whole-prelude dump does not drown the interesting one
                    (match System.Environment.GetEnvironmentVariable "FPP_CORE_FN" with
                     | null | "" -> eprintfn "COREFN %s:%d %s" v.Path v.Offset v.Name
                     | want when v.Name.StartsWith want ->
                         eprintfn "COREFN %s = %s" v.Name (Fpp.Core.Ir.printExpr e)
                     | _ -> ())
                | Fpp.Core.Ir.DClass (n, b, own, impls) ->
                    // no %A: it lowers to showv, which the SELF-HOSTED linear
                    // backend stubs — and one gap stubs the WHOLE enclosing
                    // lambda (here the emit thunk itself)
                    eprintfn "CORECLASS %s base=%s own=[%s] impls=[%s]" n
                        (match b with Some x -> x | None -> "-")
                        (own |> List.map fst |> String.concat ",")
                        (impls |> List.map (fun (i, ms) -> i + ":" + (ms |> List.map fst |> String.concat "/")) |> String.concat ";")
                | _ -> ()
        if not (List.isEmpty errs) then [||], errs
        elif low then Fpp.Backend.WasmLin.emitLinearLow linked
        else Fpp.Backend.WasmLin.emitLinear linked)

    member this.EmitProgramC () : string * string list =
        let linked, errs = this.LinkedCore true
        if not (List.isEmpty errs) then "", errs
        else Fpp.Backend.CEmit.emitC linked

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
                let low = Fpp.Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Fields r.Interfaces r.Bases cu cp ot r.Aliases inf.ArbDerive inf.OrdDerive inf.ShowDerive inf.ShowTypes inf.StrTypes ep ecs em du
                for d in low.Decls do vecAdd decls d
            | None -> ()
        let schemes =
            dictPairs r.Schemes
            |> List.filter (fun (k, _) -> not (k.StartsWith "(builtin)"))
        for pe in this.PluginErrors do vecAdd errs pe
        // The library's OWN tables, and only those. `r` is project-wide, so
        // it holds the prelude's entries too — shipping those would have a
        // consumer overwrite its own prelude with re-numbered copies of the
        // same thing. The prelude cache is the exact key set to subtract.
        let cached = BuiltinCache.force defines
        let mine (pre : Fpp.Prelude.Dict<string, 'v>) (src : Fpp.Prelude.Dict<string, 'w>) : Fpp.Prelude.Dict<string, 'w> =
            let d = dictNew<string, 'w> ()
            for k, v in dictPairs src do
                if (dictTryFind pre k).IsNone then dictSet d k v
            d
        let libClasses = Analysis.Classes.newTables ()
        for k, v in dictPairs (mine cached.Classes.Classes r.Classes.Classes) do dictSet libClasses.Classes k v
        for k, v in dictPairs (mine cached.Classes.MemberOwner r.Classes.MemberOwner) do dictSet libClasses.MemberOwner k v
        for k, v in dictPairs (mine cached.Classes.TypePaths r.Classes.TypePaths) do dictSet libClasses.TypePaths k v
        // an instance is filtered by its OWN path, not by its class: a
        // library may add instances to a PRELUDE class, and those are
        // exactly the ones a consumer cannot rediscover
        for cls, v in dictPairs r.Classes.Instances do
            for i in vecToList v do
                if i.Path <> Builtin.path then
                    match dictTryFind libClasses.Instances cls with
                    | Some nv -> vecAdd nv i
                    | None ->
                        let nv = vecNew<Analysis.Classes.InstanceDef> ()
                        vecAdd nv i
                        dictSet libClasses.Instances cls nv
        if vecLen errs > 0 then "", vecToList errs
        else
            Fpp.Core.Serialize.encodeLib
                { LExports = vecToList exports
                  LSchemes = schemes
                  LDecls = vecToList decls
                  LFields = mine cached.Fields r.Fields
                  LClasses = libClasses
                  LIfaces = mine cached.Ifaces r.Interfaces
                  LBases = mine cached.Bases r.Bases
                  LImpls = mine cached.Impls r.Impls
                  LImplTys = mine cached.ImplTys r.ImplTys
                  LStructTypes = mine cached.StructTypes r.StructTypes
                  LCtors = mine cached.Ctors r.Ctors
                  LAliases = mine cached.Aliases r.Aliases }, []

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
            Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Fields r.Interfaces r.Bases cu cp ot r.Aliases inf.ArbDerive inf.OrdDerive inf.ShowDerive inf.ShowTypes inf.StrTypes ep ecs em du
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
        let bb = (BuiltinCache.force defines).Bind
        for full, d in bb.Exports do offer d.Name full d
        for _, (b : Analysis.Resolve.BindResult, _) in dictPairs r.Files do
            for full, d in b.Exports do offer d.Name full d
        match dictTryFind r.Files path with
        | Some (b, _) -> for d in b.Definitions do offer d.Name d.Name d
        | None -> ()
        vecToList out

    /// Receiver-aware candidates for `expr.` completion: the fields and
    /// members of the receiver's TYPE, walked up its base chain — what a
    /// dot actually offers, where the flat export list cannot know the
    /// receiver. (label, rendered type).
    member this.MemberCompletions (path : string) (dotOffset : int) : (string * string) list =
        let r = this.ProjectCheck ()
        let inf = this.TypeCheck path
        let byExpr =
            inf.ExprTypes
            |> List.filter (fun (_, en, _) -> en = dotOffset)
            |> List.sortBy (fun (st, en, _) -> en - st)
            |> List.tryHead
            |> Option.map (fun (_, _, tys) -> tys)
        // a dangling `a.` mid-edit types its receiver through the
        // qualified route, which records no expression span — the token
        // ending at the dot still names a definition, and the
        // definition's rendered type is the same answer hover gives
        let byToken =
            match byExpr with
            | Some _ -> byExpr
            | None ->
                Green.tokens (GNode (this.ParseFile path).Root)
                |> List.tryFind (fun t ->
                    t.Kind = Syntax.Ident && t.Offset + strLen t.Text = dotOffset)
                |> Option.bind (fun t -> this.DefinitionAt path t.Offset)
                |> Option.bind (fun d ->
                    match dictTryFind r.Schemes (d.Path + ":" + string d.Offset) with
                    | Some sch -> Some (Analysis.Types.typeString sch.Body)
                    | None ->
                        (this.TypeCheck d.Path).DefTypes
                        |> List.tryFind (fun (off, _, _) -> off = d.Offset)
                        |> Option.map (fun (_, _, ts) -> ts))
        match byToken with
        | None -> []
        | Some tys ->
            let head =
                let i = tys.IndexOf "<"
                (if i > 0 then tys.Substring (0, i) else tys).Trim ()
            let out = vecNew<string * string> ()
            let seen = dictNew<string, bool> ()
            let mutable tn = head
            let mutable fuel = 8
            while tn <> "" && fuel > 0 do
                fuel <- fuel - 1
                for k, fi in dictPairs r.Fields do
                    if k.StartsWith (tn + ".") && not ((k.Substring (tn.Length + 1)).Contains ".") then
                        let m = k.Substring (tn.Length + 1)
                        if (dictTryFind seen m).IsNone && not (m.StartsWith "$")
                           && not (m.StartsWith "__") then
                            dictSet seen m true
                            vecAdd out (m, Analysis.Types.typeString fi.FieldType)
                tn <-
                    match dictTryFind r.Bases tn with
                    | Some (_, bt) ->
                        (match Analysis.Types.prune bt with
                         | Analysis.Types.TCon (bn, _) -> bn
                         | _ -> "")
                    | None -> ""
            vecToList out |> List.sortBy fst

    member this.HoverAt (path : string) (offset : int) : string option =
        match this.DefinitionAt path offset with
        | Some d ->
            let basis = Analysis.Resolve.kindLabel d.Kind + " `" + d.Name + "`"
            // the generalized scheme is the better answer where there is one:
            // it carries the class context, which is most of what a reader
            // needs from a signature in this language. It also works when the
            // definition lives in ANOTHER file, where this file's DefTypes
            // has nothing to say.
            let scheme =
                dictTryFind (this.ProjectCheck ()).Schemes (d.Path + ":" + string d.Offset)
            (match scheme with
             | Some sch -> Some (basis + " : " + Analysis.Types.schemeString sch)
             | None ->
                 match (this.TypeCheck d.Path).DefTypes |> List.tryFind (fun (off, _, _) -> off = d.Offset) with
                 | Some (_, _, ts) -> Some (basis + " : " + ts)
                 | None -> Some basis)
        | None ->
            // no resolved definition — a CLASS MEMBER spelled through the
            // class (`Num<float>.Zero`) binds in the class layer, which
            // the resolver never sees. The member's declared scheme is
            // still the right hover.
            let tok =
                Green.tokens (GNode (this.ParseFile path).Root)
                |> List.tryFind (fun t ->
                    t.Kind = Ident && offset >= t.Offset && offset < t.Offset + strLen t.Text)
            match tok with
            | Some t ->
                let cls = this.ProjectCheck ()
                (match dictTryFind cls.Classes.MemberOwner t.Text with
                 | Some owner ->
                     (match dictTryFind cls.Classes.Classes owner with
                      | Some cd ->
                          cd.Members
                          |> List.tryFind (fun (mn, _) -> mn = t.Text)
                          |> Option.map (fun (mn, sch) ->
                              "member `" + owner + "." + mn + "` : " + Analysis.Types.schemeString sch)
                      | None -> None)
                 | None -> None)
            | None -> None

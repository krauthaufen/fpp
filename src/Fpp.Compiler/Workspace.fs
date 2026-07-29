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
      /// classes and their instances, project-wide
      Classes : Analysis.Classes.Tables
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
            let structTypes = dictNew<string, bool> ()
            let ctors = dictNew<string, (int * Analysis.Types.Scheme) list> ()
            let classes = Analysis.Classes.newTables ()
            let members = dictNew<string, Analysis.Resolve.Definition> ()
            let bp = Parser.parse Builtin.source
            let bb = Analysis.Resolve.resolve Builtin.path imports bp.Root
            for full, d in bb.Exports do dictSet imports full d
            for k, d in bb.Members do dictSet members k d
            let binf =
                Analysis.Infer.infer Builtin.path bp.Root bb schemes aliases fields ifaces bases impls structTypes ctors classes
            { Parse = bp; Bind = bb; Inferred = binf; Imports = imports
              Schemes = schemes; Aliases = aliases; Fields = fields
              Ifaces = ifaces; Bases = bases; Impls = impls
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
    let pluginErrors = vecNew<string> ()

    /// Register a compiler plugin (project config, never source annotations).
    member _.AddPlugin (p : Fpp.Core.Plugins.Plugin) : unit = vecAdd plugins p
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

    member this.ParseFile (path : string) : Parser.ParseResult =
        db.MemoT "parse" path (fun () -> Parser.parse (this.FileText path))

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
            for path in this.ProjectFiles do
                let p = this.ParseFile path
                let b = Analysis.Resolve.resolve path imports p.Root
                for full, d in b.Exports do dictSet imports full d
                for k, d in b.Members do dictSet members k d
                let inf = Analysis.Infer.infer path p.Root b schemes aliases fields ifaces bases impls structTypes ctors classes
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
              Members = members; Classes = classes; BuiltinInfer = binf })

    member this.TypeCheck (path : string) : Analysis.Infer.InferResult =
        match dictTryFind (this.ProjectCheck ()).Files path with
        | Some (_, i) -> i
        | None ->
            Analysis.Infer.infer path (this.ParseFile path).Root (this.Resolve path)
                (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ())
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
    member this.EmitProgramRaw () : string * string list = this.EmitWith false

    member this.EmitProgram () : string * string list = this.EmitWith true

    member private this.EmitWith (optimize : bool) : string * string list =
        match this.EmitCore optimize false with
        | (wat, _, errs) -> wat, errs

    member private this.EmitCore (optimize : bool) (binary : bool) : string * byte[] * string list =
        let r = this.ProjectCheck ()
        let errs = vecNew<string> ()
        let allDecls = vecNew<Fpp.Core.Ir.Decl> ()
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
                let low = Fpp.Core.Lower.lower path root b r.Schemes ok ak ik ms fo cs r.Members r.Interfaces cu cp ot
                for d in this.RunPerFile low.Decls do vecAdd allDecls d
                for off, why in low.Notes do
                    vecAdd errs (path + ": not lowerable at offset " + string off + ": " + why)
            | None -> ()
        for path in this.ProjectFiles do
            for d in this.Diagnostics path do
                vecAdd errs (path + ":" + string (d.Line + 1) + ":" + string (d.Col + 1) + ": " + d.Message)
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
        let blow =
            Fpp.Core.Lower.lower Builtin.path bp.Root bb r.Schemes bok bak bik bms bfo bcs
                r.Members r.Interfaces bcu bcp bot
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
        if vecLen errs > 0 then "", [||], vecToList errs
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
            if not (List.isEmpty monoErrs) then "", [||], monoErrs
            elif binary then
                let bytes, berrs = Fpp.Backend.BinDriver.emitBinary linked
                "", bytes, berrs
            else
                let res = Fpp.Backend.EmitWasm.emit linked
                res.Wat, [||], res.Errors

    /// The BINARY program: same pipeline, bytes out, no text anywhere.
    member this.EmitProgramWasm () : byte[] * string list =
        match this.EmitCore true true with
        | (_, bytes, errs) -> bytes, errs

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
                let low = Fpp.Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Interfaces cu cp ot
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
            Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Interfaces cu cp ot
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

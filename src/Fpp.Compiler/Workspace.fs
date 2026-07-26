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
        v.ToArray()

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
    let source =
        String.concat "\n" [
            "type Option<'a> ="
            "    | None"
            "    | Some of 'a"
            "type option<'a> = Option<'a>"
            "type Result<'t, 'e> ="
            "    | Ok of 't"
            "    | Error of 'e"
            "type exn ="
            "    | Failure of string"
            "module Array ="
            "    extern let create : int -> 'a -> 'a[]"
            "    extern let pin : 'a[] -> int"
            "    extern let unpin : 'a[] -> int"
            ""
        ]

    let path = "(builtin)"

type ProjectResults =
    { Files : Fpp.Prelude.Dict<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult>
      Schemes : Fpp.Prelude.Dict<string, Analysis.Types.Scheme>
      /// interface name -> its methods as (name, arity), project-wide
      Interfaces : Fpp.Prelude.Dict<string, (string * int) list> }

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
            let imports = dictNew<string, Analysis.Resolve.Definition> ()
            let schemes = dictNew<string, Analysis.Types.Scheme> ()
            let aliases = dictNew<string, Analysis.Types.Var list * Analysis.Types.Type> ()
            let fields = dictNew<string, Analysis.Infer.FieldInfo> ()
            let ifaces = dictNew<string, (string * int) list> ()
            let results = dictNew<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult> ()
            // the builtin prelude seeds imports and schemes for every file
            let bp = Parser.parse Builtin.source
            let bb = Analysis.Resolve.resolve Builtin.path imports bp.Root
            for full, d in bb.Exports do dictSet imports full d
            Analysis.Infer.infer Builtin.path bp.Root bb schemes aliases fields ifaces |> ignore
            // linked libraries: exports feed the resolver, schemes feed inference
            for _, text in this.Libraries do
                let exps, schs, _ = Fpp.Core.Serialize.decodeLib text
                for full, d in exps do dictSet imports full d
                for k, sch in schs do dictSet schemes k sch
            for path in this.ProjectFiles do
                let p = this.ParseFile path
                let b = Analysis.Resolve.resolve path imports p.Root
                for full, d in b.Exports do dictSet imports full d
                let inf = Analysis.Infer.infer path p.Root b schemes aliases fields ifaces
                dictSet results path (b, inf)
            // libraries declare their interfaces in their serialized core
            for _, text in this.Libraries do
                let _, _, ds = Fpp.Core.Serialize.decodeLib text
                for d in ds do
                    match d with
                    | Fpp.Core.Ir.DInterface (n, ms) -> dictSet ifaces n ms
                    | _ -> ()
            { Files = results; Schemes = schemes; Interfaces = ifaces })

    member this.TypeCheck (path : string) : Analysis.Infer.InferResult =
        match dictTryFind (this.ProjectCheck ()).Files path with
        | Some (_, i) -> i
        | None ->
            Analysis.Infer.infer path (this.ParseFile path).Root (this.Resolve path)
                (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ())

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
            |> List.sortBy (fun d -> d.Line, d.Col))

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
    member this.EmitProgram () : string * string list =
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
                let low = Fpp.Core.Lower.lower path root b r.Schemes ok ak ik ms r.Interfaces
                for d in this.RunPerFile low.Decls do vecAdd allDecls d
                for off, why in low.Notes do
                    vecAdd errs (path + ": not lowerable at offset " + string off + ": " + why)
            | None -> ()
        for path in this.ProjectFiles do
            for d in this.Diagnostics path do
                vecAdd errs (path + ":" + string (d.Line + 1) + ":" + string (d.Col + 1) + ": " + d.Message)
        // builtin decls (Option etc.) come first
        let bp = Parser.parse Builtin.source
        let bb = Analysis.Resolve.resolve Builtin.path (dictNew ()) bp.Root
        let blow = Fpp.Core.Lower.lower Builtin.path bp.Root bb r.Schemes (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) r.Interfaces
        for d in blow.Decls do vecAdd allDecls d
        for path in this.ProjectFiles do
            lowerOne path (this.ParseFile path).Root
        // linked library declarations join the program before emission
        let libDecls = vecNew<Fpp.Core.Ir.Decl> ()
        for _, text in this.Libraries do
            let _, _, ds = Fpp.Core.Serialize.decodeLib text
            for d in ds do vecAdd libDecls d
        for pe in this.PluginErrors do vecAdd errs pe
        if vecLen errs > 0 then "", vecToList errs
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
            let mono, monoErrs = Fpp.Core.Link.monomorphize isStruct program
            let linked = Fpp.Core.Link.deadCodeEliminate mono
            if not (List.isEmpty monoErrs) then "", monoErrs
            else
                let res = Fpp.Backend.EmitWasm.emit linked
                res.Wat, res.Errors

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
                let low = Fpp.Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms r.Interfaces
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
            Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms r.Interfaces
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

    member this.HoverAt (path : string) (offset : int) : string option =
        this.DefinitionAt path offset
        |> Option.map (fun d ->
            let basis = Analysis.Resolve.kindLabel d.Kind + " `" + d.Name + "`"
            let ty =
                (this.TypeCheck path).DefTypes
                |> List.tryFind (fun (off, _, _) -> off = d.Offset)
            match ty with
            | Some (_, _, ts) -> basis + " : " + ts
            | None -> basis)

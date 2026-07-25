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
            ""
        ]

    let path = "(builtin)"

type Workspace() =
    let db = Db()
    do db.SetInput "project" "" (box ([] : string list))

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
    member this.ProjectCheck () : Dict<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult> =
        db.MemoT "projectCheck" "" (fun () ->
            let imports = dictNew<string, Analysis.Resolve.Definition> ()
            let schemes = dictNew<string, Analysis.Types.Scheme> ()
            let aliases = dictNew<string, Analysis.Types.Var list * Analysis.Types.Type> ()
            let fields = dictNew<string, Analysis.Infer.FieldInfo> ()
            let results = dictNew<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult> ()
            // the builtin prelude seeds imports and schemes for every file
            let bp = Parser.parse Builtin.source
            let bb = Analysis.Resolve.resolve Builtin.path imports bp.Root
            for full, d in bb.Exports do dictSet imports full d
            Analysis.Infer.infer Builtin.path bp.Root bb schemes aliases fields |> ignore
            for path in this.ProjectFiles do
                let p = this.ParseFile path
                let b = Analysis.Resolve.resolve path imports p.Root
                for full, d in b.Exports do dictSet imports full d
                let inf = Analysis.Infer.infer path p.Root b schemes aliases fields
                dictSet results path (b, inf)
            results)

    member this.TypeCheck (path : string) : Analysis.Infer.InferResult =
        match dictTryFind (this.ProjectCheck ()) path with
        | Some (_, i) -> i
        | None ->
            Analysis.Infer.infer path (this.ParseFile path).Root (this.Resolve path)
                (dictNew ()) (dictNew ()) (dictNew ())

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
        match dictTryFind (this.ProjectCheck ()) path with
        | Some (b, _) -> b
        | None -> Analysis.Resolve.resolve path (dictNew ()) (this.ParseFile path).Root

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

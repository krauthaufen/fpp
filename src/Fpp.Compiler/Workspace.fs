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
type Workspace() =
    let db = Db()

    member _.Db = db

    member _.SetFileText (path : string) (text : string) : unit =
        db.SetInput "text" path (box text)

    member _.FileText (path : string) : string =
        unbox<string> (db.GetInput "text" path)

    member this.ParseFile (path : string) : Parser.ParseResult =
        db.MemoT "parse" path (fun () -> Parser.parse (this.FileText path))

    member this.Diagnostics (path : string) : DiagnosticInfo list =
        db.MemoT "diagnostics" path (fun () ->
            let r = this.ParseFile path
            let starts = Lines.starts (this.FileText path)
            r.Diagnostics
            |> List.map (fun d ->
                let line, col = Lines.toLineCol starts d.Offset
                { Path = path; Line = line; Col = col
                  EndLine = line; EndCol = col + 1; Message = d.Message }))

    member this.Outline (path : string) : OutlineItem list =
        db.MemoT "outline" path (fun () ->
            let r = this.ParseFile path
            let starts = Lines.starts (this.FileText path)
            Outline.items starts r.Root.Children)

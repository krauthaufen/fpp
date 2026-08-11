namespace Fpp.Syntax

open Fpp.Prelude

/// Node kinds of the lossless syntax tree. Coarse on purpose — the tree is a
/// faithful, error-tolerant view of the text; semantic precision comes later.
type NodeKind =
    // structure
    | File
    | ModuleHeader
    | ModuleDef
    | OpenDecl
    | LetDecl
    | TypeDecl
    | TyParams
    | UnionCase
    | RecordRepr
    | RecordField
    | AttributeList
    | MemberDecl
    | AccessorDecl
    | InterfaceImpl
    | InheritDecl
    /// `class C<'a, 'b>` — a typeclass declaration
    | ClassDecl
    /// `instance C<int, int>` — a free-standing instance
    | InstanceDecl
    /// `when C<'a> with Result = 'a` — one constraint
    | WhenDecl
    // expressions
    | LiteralExpr
    | IdentExpr
    | AppExpr
    | BinaryExpr
    | PrefixExpr
    /// `<@ ... @>` — quoted CODE. Ordinary syntax inside, so it resolves, type
    /// checks and hovers like any other expression.
    | QuoteExpr
    /// `%x` inside a quotation — splice the code that `x` denotes
    | SpliceExpr
    | ParenExpr
    | BraceExpr
    | RecordExpr
    | RecordExprField
    | TupleExpr
    | StructTupleExpr
    | ListExpr
    | ArrayExpr
    | LambdaExpr
    | IfExpr
    | MatchExpr
    | MatchClause
    | BlockExpr
    | DotExpr
    | CastExpr
    | ObjExpr
    /// `builder { ... }` — a computation expression. The first child is the
    /// builder, the second the braced body.
    | CompExpr
    | ForExpr
    | WhileExpr
    | TryExpr
    // patterns
    /// `%p` in PATTERN position inside a quotation
    | SplicePat
    | WildcardPat
    | IdentPat
    | LiteralPat
    | TuplePat
    | StructTuplePat
    | ConsPat
    | AppPat
    | ParenPat
    | ListPat
    | AsPat
    | TypeTestPat
    // types
    /// `%t` in TYPE position inside a quotation
    | SpliceType
    | NamedType
    | VarType
    | AnonType
    | TupleType
    | StructTupleType
    | FunType
    | AppType
    | AssocType
    | PostfixType
    | ParenType
    // recovery
    | ErrorNode

/// Green tree: immutable, position-independent, width-cached. Sharing-safe.
type Green =
    | GToken of Token
    | GNode of GreenNode

and GreenNode =
    { NodeKind : NodeKind
      Children : Green list
      Width : int }

module Green =

    let private triviaWidth (ts : Trivia list) : int =
        List.sumBy (fun t -> strLen t.TriviaText) ts

    /// Full width of a token including its leading and trailing trivia.
    let tokenWidth (t : Token) : int =
        triviaWidth t.Leading + strLen t.Text + triviaWidth t.Trailing

    let width (g : Green) : int =
        match g with
        | GToken t -> tokenWidth t
        | GNode n -> n.Width

    let node (kind : NodeKind) (children : Green list) : Green =
        GNode { NodeKind = kind; Children = children; Width = List.sumBy width children }

    /// All tokens of a subtree, in source order.
    let rec tokens (g : Green) : Token list =
        match g with
        | GToken t -> [ t ]
        | GNode n -> List.collect tokens n.Children

    /// Lossless-ness witness: the exact source text of a subtree.
    let toText (g : Green) : string =
        tokens g
        |> List.collect (fun t ->
            List.map (fun (tr : Trivia) -> tr.TriviaText) t.Leading
            @ [ t.Text ]
            @ List.map (fun (tr : Trivia) -> tr.TriviaText) t.Trailing)
        |> String.concat ""

    let rec collectNodes (kind : NodeKind) (g : Green) : GreenNode list =
        match g with
        | GToken _ -> []
        | GNode n ->
            let inner = List.collect (collectNodes kind) n.Children
            if n.NodeKind = kind then n :: inner else inner

/// Red tree: a lazy positional view over a green node. Cheap to create, holds
/// absolute offsets; the LSP layer works exclusively in terms of these.
type SyntaxNode =
    { Green : GreenNode
      Position : int }

module Red =

    let root (g : GreenNode) : SyntaxNode = { Green = g; Position = 0 }

    /// Children with their absolute positions (full-width, trivia included).
    let children (nd : SyntaxNode) : (Green * int) list =
        let mutable pos = nd.Position
        let acc = vecNew<Green * int> ()
        for c in nd.Green.Children do
            vecAdd acc (c, pos)
            pos <- pos + Green.width c
        vecToList acc

    let childNodes (nd : SyntaxNode) : SyntaxNode list =
        children nd
        |> List.choose (fun (c, p) ->
            match c with
            | GNode n -> Some { Green = n; Position = p }
            | GToken _ -> None)

    /// Innermost node whose full span contains the offset.
    let rec nodeAt (offset : int) (nd : SyntaxNode) : SyntaxNode =
        let hit =
            childNodes nd
            |> List.tryFind (fun c -> offset >= c.Position && offset < c.Position + c.Green.Width)
        match hit with
        | Some c -> nodeAt offset c
        | None -> nd

module Fpp.Syntax.Desugar

open Fpp.Prelude
open Fpp.Syntax

// Computation expressions, rewritten into ordinary syntax before anything
// semantic runs.
//
// The rewrite happens HERE, between parsing and resolution, and that
// placement is the whole design. Resolution walks the rewritten tree, so the
// names the rewrite introduces bind like any others and the lambdas it
// builds scope their patterns correctly — none of it needs a second
// mechanism. Inference and lowering then see one tree, which is what keeps
// them from disagreeing: a desugaring done twice, once per pass, is the
// shape that has cost this compiler the most (a construct type-checks under
// one reading and traps under the other).
//
// The price of running before inference is that we cannot ask what members
// the builder HAS. F# can, and uses it to omit `Run`, `Delay`, `Zero` and
// friends when a builder does not define them. So the rule here is
// structural instead: a method is emitted only where the CONSTRUCT requires
// it, and never speculatively.
//
//   Delay   the second argument of Combine, the body of While, the body of
//           TryWith and TryFinally — the places where evaluating eagerly
//           would be wrong. NOT at the top level.
//   Zero    an empty body, an `if` with no `else`, the tail after a `do!`.
//   Run     never.
//
// The top-level Delay is the visible consequence: statements ahead of the
// first yield run when the expression is BUILT, not when it is consumed.
// F# defers them. In exchange, a builder that defines only Bind and Return —
// which is most of FSharp.Data.Adaptive's — works without defining methods
// it has no use for.
//
// The original tree is untouched: this returns a new one, and the lossless
// parse the editor and the round-trip gate see is the parser's.

/// Synthesized tokens need offsets no real token can own: every table
/// downstream — definitions, member sites, instantiations — is keyed by
/// offset, and two nodes sharing one would share its entry. Real offsets are
/// bounded by the file's length, and inference derives its own synthetic
/// keys by adding to them; this base sits above both.
let private synthBase = 500000000

let mutable private counter = synthBase

let private freshOffset () : int =
    let n = counter
    counter <- counter + 1
    n

// ---- building syntax ------------------------------------------------------

let private tk (kind : TokenKind) (text : string) : Green =
    GToken { Kind = kind; Text = text; Leading = []; Trailing = []; Offset = freshOffset () }

let private ident (name : string) : Green = Green.node IdentExpr [ tk Ident name ]

let private identPat (name : string) : Green = Green.node IdentPat [ tk Ident name ]

let private unitPat () : Green = Green.node ParenPat [ tk LParen "("; tk RParen ")" ]

let private unitExpr () : Green = Green.node ParenExpr [ tk LParen "("; tk RParen ")" ]

let private paren (inner : Green) : Green =
    Green.node ParenExpr [ tk LParen "("; inner; tk RParen ")" ]

let private tuple (items : Green list) : Green =
    let acc = vecNew<Green> ()
    let mutable first = true
    for i in items do
        if not first then vecAdd acc (tk Comma ",")
        first <- false
        vecAdd acc i
    Green.node TupleExpr (vecToList acc)

/// `recv.Name(args)` — the tuple form, which is how a builder's methods are
/// declared and how F# calls them.
let private call (recv : string) (name : string) (args : Green list) : Green =
    let target = Green.node DotExpr [ ident recv; tk Operator "."; tk Ident name ]
    match args with
    | [] -> Green.node AppExpr [ target; unitExpr () ]
    | [ a ] -> Green.node AppExpr [ target; paren a ]
    | many -> Green.node AppExpr [ target; paren (tuple many) ]

let private lambda (pats : Green list) (body : Green) : Green =
    Green.node LambdaExpr ((tk Keyword "fun" :: pats) @ [ tk Operator "->"; body ])

/// `fun () -> e`, the shape every Delay takes
let private thunk (body : Green) : Green = lambda [ unitPat () ] body

// ---- reading syntax -------------------------------------------------------

let private nodesOf (n : GreenNode) : GreenNode list =
    n.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)

let private tokensOf (n : GreenNode) : Token list =
    n.Children |> List.choose (fun c -> match c with GToken t -> Some t | _ -> None)

let private isExprish (k : NodeKind) : bool =
    match k with
    | LiteralExpr | IdentExpr | AppExpr | BinaryExpr | PrefixExpr | QuoteExpr
    | SpliceExpr | ParenExpr | BraceExpr | RecordExpr | TupleExpr
    | StructTupleExpr | ListExpr | ArrayExpr | LambdaExpr | IfExpr | MatchExpr
    | BlockExpr | DotExpr | CastExpr | ObjExpr | CompExpr | ForExpr
    | WhileExpr | TryExpr -> true
    | _ -> false

let private isPatKind (k : NodeKind) : bool =
    match k with
    | WildcardPat | IdentPat | LiteralPat | TuplePat | StructTuplePat | ConsPat
    | AppPat | ParenPat | ListPat | AsPat | TypeTestPat | SplicePat -> true
    | _ -> false

let private hasKw (n : GreenNode) (text : string) : bool =
    tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = text)

/// `let!`, `use!`, `do!`, `yield!`, `return!` — the bang is its own token
let private hasBang (n : GreenNode) : bool =
    tokensOf n |> List.exists (fun t -> t.Kind = Operator && t.Text = "!")

/// A `do` statement and a multi-item block are both BlockExpr; the keyword
/// is what tells them apart.
let private isDoStmt (n : GreenNode) : bool =
    n.NodeKind = BlockExpr && hasKw n "do"

/// The NAME a `use!` binder introduces, so the resource can be handed to
/// Using as a value. Only a plain binder has one.
let private patName (n : GreenNode) : string option =
    if n.NodeKind = IdentPat then
        match tokensOf n |> List.tryHead with
        | Some t -> Some t.Text
        | None -> None
    else None

// ---- the rewrite ----------------------------------------------------------

let rec private walk (g : Green) : Green =
    match g with
    | GToken _ -> g
    | GNode n ->
        if n.NodeKind = CompExpr then comp n
        else Green.node n.NodeKind (List.map walk n.Children)

/// `builder { body }`. The builder is evaluated ONCE, into a binding the
/// rewrite then names: duplicating its expression would duplicate every
/// token offset in it, and the tables downstream are keyed by offset.
and private comp (n : GreenNode) : Green =
    let kids = nodesOf n
    let b = "_ce" + string (freshOffset ())
    match kids with
    | [ builder; body ] when body.NodeKind = BraceExpr ->
        let bind =
            Green.node LetDecl
                [ tk Keyword "let"; identPat b; tk Operator "="; walk (GNode builder) ]
        Green.node BlockExpr [ bind; block b (bodyItems body) ]
    | _ -> Green.node n.NodeKind (List.map walk n.Children)

/// The statements of a braced body. `parseBlock` hands back a lone item
/// unwrapped, so a single statement arrives without its block.
and private bodyItems (brace : GreenNode) : GreenNode list =
    match nodesOf brace with
    | [ one ] when one.NodeKind = BlockExpr && not (isDoStmt one) -> nodesOf one
    | ms -> ms

/// Does the body name a value anywhere — `yield`, `yield!`, `return`,
/// `return!`? If it never does, a bare expression is an IMPLICIT yield,
/// which is F#'s rule and the only reading under which `seq { 1; 2 }` means
/// anything. Nested computation expressions have their own answer, so the
/// scan does not descend into them.
and private namesAValue (items : GreenNode list) : bool =
    let rec scan (n : GreenNode) : bool =
        if n.NodeKind = CompExpr then false
        elif n.NodeKind = PrefixExpr && (hasKw n "yield" || hasKw n "return") then true
        else nodesOf n |> List.exists scan
    items |> List.exists scan

and private block (b : string) (items : GreenNode list) : Green =
    blockYielding b (namesAValue items) items

and private blockYielding (b : string) (explicit : bool) (items : GreenNode list) : Green =
    match items with
    | [] -> call b "Zero" []
    | item :: rest -> item1 b explicit item rest

/// One statement and everything after it.
and private item1 (b : string) (explicit : bool) (item : GreenNode) (rest : GreenNode list) : Green =
    let tail () = blockYielding b explicit rest
    let combine (value : Green) : Green =
        if List.isEmpty rest then value
        else call b "Combine" [ value; call b "Delay" [ thunk (tail ()) ] ]
    // a statement that is not a computation form: run it, then carry on
    let sequential () =
        Green.node BlockExpr [ walk (GNode item); tail () ]
    match item.NodeKind with
    | LetDecl when hasBang item ->
        // `let! p = e` and `and! p = e`. F# binds an `and!` group in
        // PARALLEL through MergeSources; here it chains, which computes the
        // same value over a slightly different graph.
        (match bangBinder item with
         | Some (pat, rhs) when hasKw item "use" ->
             (match patName pat with
              | Some nm ->
                  call b "Bind"
                      [ rhs
                        lambda [ GNode pat ]
                            (call b "Using" [ ident nm; lambda [ Green.node WildcardPat [ tk Ident "_" ] ] (tail ()) ]) ]
              | None -> call b "Bind" [ rhs; lambda [ GNode pat ] (tail ()) ])
         | Some (pat, rhs) -> call b "Bind" [ rhs; lambda [ GNode pat ] (tail ()) ]
         | None -> sequential ())
    | LetDecl when hasKw item "use" ->
        (match bangBinder item with
         | Some (pat, rhs) -> call b "Using" [ rhs; lambda [ GNode pat ] (tail ()) ]
         | None -> sequential ())
    | LetDecl -> Green.node BlockExpr [ walk (GNode item); tail () ]
    | BlockExpr when isDoStmt item && hasBang item ->
        (match nodesOf item |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast with
         | Some e ->
             let k = if List.isEmpty rest then call b "Zero" [] else tail ()
             call b "Bind" [ walk (GNode e); thunk k ]
         | None -> sequential ())
    | PrefixExpr when hasKw item "yield" || hasKw item "return" ->
        let name =
            if hasKw item "yield" then (if hasBang item then "YieldFrom" else "Yield")
            else (if hasBang item then "ReturnFrom" else "Return")
        (match nodesOf item |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast with
         | Some e -> combine (call b name [ walk (GNode e) ])
         | None -> combine (call b "Zero" []))
    | ForExpr ->
        let pat = nodesOf item |> List.tryFind (fun m -> isPatKind m.NodeKind)
        let exprs = nodesOf item |> List.filter (fun m -> isExprish m.NodeKind)
        (match pat, exprs with
         | Some p, [ coll; body ] ->
             combine (call b "For" [ walk (GNode coll); lambda [ GNode p ] (nested b explicit body) ])
         | _ -> sequential ())
    | WhileExpr ->
        (match nodesOf item |> List.filter (fun m -> isExprish m.NodeKind) with
         | [ cond; body ] ->
             combine (call b "While"
                          [ thunk (walk (GNode cond))
                            call b "Delay" [ thunk (nested b explicit body) ] ])
         | _ -> sequential ())
    | IfExpr -> combine (ifExpr b explicit item)
    | MatchExpr -> combine (clauses b explicit item)
    | TryExpr -> combine (tryExpr b explicit item)
    // A bare expression. With no `yield` or `return` anywhere in the body it
    // is an implicit yield; otherwise it is a statement, and a statement in
    // final position leaves the computation with nothing to be.
    | _ when not explicit -> combine (call b "Yield" [ walk (GNode item) ])
    | _ when List.isEmpty rest -> Green.node BlockExpr [ walk (GNode item); call b "Zero" [] ]
    | _ -> sequential ()

/// The pattern and the right-hand side of a `let!`/`use!`/`use` binder.
and private bangBinder (item : GreenNode) : (GreenNode * Green) option =
    let pat = nodesOf item |> List.tryFind (fun m -> isPatKind m.NodeKind)
    let rhs = nodesOf item |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast
    match pat, rhs with
    | Some p, Some r -> Some (p, walk (GNode r))
    | _ -> None

/// A nested body — a loop's, a branch's — is a computation of its own.
and private nested (b : string) (explicit : bool) (body : GreenNode) : Green =
    if body.NodeKind = BlockExpr && not (isDoStmt body) then blockYielding b explicit (nodesOf body)
    else blockYielding b explicit [ body ]

/// `if`/`elif`/`else`, where the BRANCHES are computations and the
/// conditions are not. A missing `else` is where Zero comes from.
and private ifExpr (b : string) (explicit : bool) (item : GreenNode) : Green =
    let acc = vecNew<Green> ()
    let mutable branchNext = false
    let mutable sawElse = false
    for c in item.Children do
        match c with
        | GToken t ->
            if t.Kind = Keyword && (t.Text = "then" || t.Text = "else") then branchNext <- true
            elif t.Kind = Keyword && (t.Text = "if" || t.Text = "elif") then branchNext <- false
            if t.Kind = Keyword && t.Text = "else" then sawElse <- true
            vecAdd acc c
        | GNode m ->
            if branchNext && isExprish m.NodeKind then
                // an `elif` chain arrives as a nested IfExpr in the else
                // slot; it is a branch, and recursing keeps it one
                if m.NodeKind = IfExpr then vecAdd acc (ifExpr b explicit m)
                else vecAdd acc (nested b explicit m)
                branchNext <- false
            else vecAdd acc (walk c)
    if not sawElse then
        vecAdd acc (tk Keyword "else")
        vecAdd acc (call b "Zero" [])
    Green.node IfExpr (vecToList acc)

/// Every clause body of a `match` is a computation; the scrutinee, the
/// patterns and the guards are not.
and private clauses (b : string) (explicit : bool) (item : GreenNode) : Green =
    let rewrite (c : Green) : Green =
        match c with
        | GNode cl when cl.NodeKind = MatchClause ->
            let bodies = nodesOf cl |> List.filter (fun m -> isExprish m.NodeKind)
            (match List.tryLast bodies with
             | Some last ->
                 Green.node MatchClause
                     (cl.Children
                      |> List.map (fun x ->
                          match x with
                          | GNode m when System.Object.ReferenceEquals (m, last) -> nested b explicit m
                          | other -> walk other))
             | None -> walk c)
        | other -> walk other
    Green.node item.NodeKind (List.map rewrite item.Children)

/// `try`/`with` and `try`/`finally`. Both bodies must be delayed: the
/// builder decides when to run them, and running one to build the handler
/// would defeat the point.
and private tryExpr (b : string) (explicit : bool) (item : GreenNode) : Green =
    let body = nodesOf item |> List.tryFind (fun m -> m.NodeKind <> MatchClause && isExprish m.NodeKind)
    match body with
    | None -> walk (GNode item)
    | Some bd ->
        let delayed = call b "Delay" [ thunk (nested b explicit bd) ]
        if hasKw item "finally" then
            let fin = nodesOf item |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast
            match fin with
            | Some f when not (System.Object.ReferenceEquals (f, bd)) ->
                call b "TryFinally" [ delayed; thunk (walk (GNode f)) ]
            | _ -> walk (GNode item)
        else
            // `fun e -> match e with <the written clauses>`
            let e = "_exn" + string (freshOffset ())
            let acc = vecNew<Green> ()
            vecAdd acc (tk Keyword "match")
            vecAdd acc (ident e)
            vecAdd acc (tk Keyword "with")
            for c in item.Children do
                match c with
                | GNode cl when cl.NodeKind = MatchClause ->
                    let bodies = nodesOf cl |> List.filter (fun m -> isExprish m.NodeKind)
                    (match List.tryLast bodies with
                     | Some last ->
                         vecAdd acc
                             (Green.node MatchClause
                                 (cl.Children
                                  |> List.map (fun x ->
                                      match x with
                                      | GNode m when System.Object.ReferenceEquals (m, last) -> nested b explicit m
                                      | other -> walk other)))
                     | None -> vecAdd acc (walk c))
                | _ -> ()
            call b "TryWith" [ delayed; lambda [ identPat e ] (Green.node MatchExpr (vecToList acc)) ]

/// Rewrite every computation expression in a file. Files are independent, so
/// the counter restarts: the same text desugars to the same tree, which is
/// what lets the result be cached like any other parse.
let desugar (root : GreenNode) : GreenNode =
    counter <- synthBase
    match walk (GNode root) with
    | GNode n -> n
    | _ -> root

module Fpp.Syntax.Desugar

open Fpp.Prelude
open Fpp.Syntax

// Computation expressions, rewritten into the calls F# rewrites them into.
//
// The shape is not a matter of taste: it was READ OFF the F# compiler, by
// quoting `builder { ... }` for a battery of builders and printing the
// desugared quotation. Everything below is what came back, and the tests in
// EmitTests mirror those cases.
//
//   b { return e }              b.Run(b.Delay(fun () -> b.Return(e)))
//   b { let! p = e; REST }      b.Bind(e, fun p -> REST)
//   b { let! p = e; return v }  b.BindReturn(e, fun p -> v)      [if present]
//   b { let! p = e; and! q = f
//       return v }              b.BindReturn(b.MergeSources(e, f), fun (p, q) -> v)
//   b { do! e }                 b.Bind(e, fun () -> b.Return(()))  [b.Zero() if no Return]
//   b { do! e; REST }           b.Bind(e, fun () -> REST)
//   b { use p = e; REST }       b.Using(e, fun p -> REST)
//   b { use! p = e; REST }      b.Bind(e, fun p -> b.Using(p, fun _ -> REST))
//   b { yield e; REST }         b.Combine(b.Yield(e), b.Delay(fun () -> REST))
//   b { for p in e do BODY }    b.For(e, fun p -> BODY)
//   b { while c do BODY }       b.While((fun () -> c), b.Delay(fun () -> BODY))
//   b { if c then BODY }        if c then BODY else b.Zero()
//   b { try BODY with CS }      b.TryWith(b.Delay(fun () -> BODY), fun e -> match e with CS)
//   b { try BODY finally F }    b.TryFinally(b.Delay(fun () -> BODY), fun () -> F)
//   b { stmt; REST }            stmt; REST          — a plain sequential
//   b { stmt }                  stmt; b.Zero()
//
// **`Run` and `Delay` wrap the whole body if and only if the builder
// declares them**, independently of each other, and that is the one decision
// the shape of the source cannot make. It needs the builder's TYPE, so this
// pass runs after a probe: the file is resolved and inferred once with every
// computation expression left alone but its BUILDER typed, and what comes
// back tells this pass which methods exist. Files with no computation
// expression skip the probe and cost nothing.
//
// Inside `Combine`, `While`, `TryWith` and `TryFinally` the `Delay` is NOT
// optional — F# rejects those constructs outright on a builder without one —
// so those are emitted unconditionally.
//
// Running before RESOLUTION is what keeps the rest honest: resolution walks
// the rewritten tree, so the names this pass introduces bind like any others
// and the lambdas it builds scope their patterns correctly. Inference and
// lowering then see one tree, and cannot disagree about it — a desugaring
// done twice, once per pass, is the shape that has cost this compiler the
// most.
//
// The original tree is untouched: this returns a new one, and the lossless
// parse the editor and the round-trip gate see is still the parser's.

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

/// What the builder DECLARES. F# picks a computation expression's shape from
/// this, so the rewrite cannot run until a probe pass has typed the builder
/// and this has been read off its type.
type CeBuilder =
    { Name : string
      HasRun : bool
      HasDelay : bool
      HasReturn : bool
      HasBindReturn : bool
      HasBind2 : bool
      HasBind3 : bool
      HasBind2Return : bool
      HasBind3Return : bool
      HasMergeSources : bool
      HasMergeSources3 : bool }

/// What to assume when the probe could not type the builder — a builder in a
/// file that does not type check, or a lone file with no project around it.
/// Omitting `Run` and `Delay` is the choice that still compiles against the
/// SMALLEST builder, so an unknown one degrades to the minimum rather than to
/// a call that cannot resolve.
let unknownBuilder (name : string) : CeBuilder =
    { Name = name; HasRun = false; HasDelay = false; HasReturn = true
      HasBindReturn = false; HasBind2 = false; HasBind3 = false
      HasBind2Return = false; HasBind3Return = false
      HasMergeSources = false; HasMergeSources3 = false }

/// `recv.Name(args)` — the tuple form, which is how a builder's methods are
/// declared and how F# calls them.
let private callOn (recv : string) (name : string) (args : Green list) : Green =
    let target = Green.node DotExpr [ ident recv; tk Operator "."; tk Ident name ]
    match args with
    | [] -> Green.node AppExpr [ target; unitExpr () ]
    | [ a ] -> Green.node AppExpr [ target; paren a ]
    | many -> Green.node AppExpr [ target; paren (tuple many) ]

let private call (b : CeBuilder) (name : string) (args : Green list) : Green =
    callOn b.Name name args

let private lambda (pats : Green list) (body : Green) : Green =
    Green.node LambdaExpr ((tk Keyword "fun" :: pats) @ [ tk Operator "->"; body ])

/// `fun () -> e`, the shape every Delay takes
let private thunk (body : Green) : Green = lambda [ unitPat () ] body

// ---- reading syntax -------------------------------------------------------

let private nodesOf (n : GreenNode) : GreenNode list =
    n.Children |> List.choose (fun c -> match c with GNode m -> Some m | _ -> None)

let private offsetOf (n : GreenNode) : int =
    match Green.tokens (GNode n) |> List.tryHead with
    | Some t -> t.Offset
    | None -> 0

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

/// How the probe answered for the computation expression at an offset.
let mutable private builderAt : int -> CeBuilder = fun _ -> unknownBuilder "?"

/// Body items the probe typed as having NO value. F# reads a bare expression
/// as an implicit `yield` unless it is a statement, and its type is the only
/// thing that tells those apart — `seq { 1 }` yields, `seq { printfn "x" }`
/// does not.
let mutable private statementAt : int -> bool = fun _ -> false

let rec private walk (g : Green) : Green =
    match g with
    | GToken _ -> g
    | GNode n ->
        if n.NodeKind = CompExpr then comp n
        else Green.node n.NodeKind (List.map walk n.Children)

/// `builder { body }`, which F# renders as
/// `let b = <builder> in b.Run(b.Delay(fun () -> BODY))` — with `Run` and
/// `Delay` each there only if the builder declares it. The builder is
/// evaluated ONCE into a binding: duplicating its expression would duplicate
/// every token offset in it, and the tables downstream are keyed by offset.
and private comp (n : GreenNode) : Green =
    let kids = nodesOf n
    let at = match Green.tokens (GNode n) |> List.tryHead with Some t -> t.Offset | None -> 0
    let probed = builderAt at
    let b = { probed with Name = "_ce" + string (freshOffset ()) }
    match kids with
    | [ builder; body ] when body.NodeKind = BraceExpr ->
        let bind =
            Green.node LetDecl
                [ tk Keyword "let"; identPat b.Name; tk Operator "="; walk (GNode builder) ]
        let core = block b (bodyItems body)
        // Delay first, then Run around it — the order F# emits, and the one
        // a builder whose Delay changes the type (`unit -> M<'a>`) needs
        let delayed = if b.HasDelay then call b "Delay" [ thunk core ] else core
        let ran = if b.HasRun then call b "Run" [ delayed ] else delayed
        Green.node BlockExpr [ bind; ran ]
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

and private block (b : CeBuilder) (items : GreenNode list) : Green =
    blockYielding b (namesAValue items) items

and private blockYielding (b : CeBuilder) (explicit : bool) (items : GreenNode list) : Green =
    match items with
    | [] -> call b "Zero" []
    | item :: rest -> item1 b explicit item rest

/// One statement and everything after it.
and private item1 (b : CeBuilder) (explicit : bool) (item : GreenNode) (rest : GreenNode list) : Green =
    let tail () = blockYielding b explicit rest
    let combine (value : Green) : Green =
        if List.isEmpty rest then value
        else call b "Combine" [ value; call b "Delay" [ thunk (tail ()) ] ]
    // a statement that is not a computation form: run it, then carry on
    let sequential () =
        Green.node BlockExpr [ walk (GNode item); tail () ]
    match item.NodeKind with
    | LetDecl when hasBang item -> bangLet b explicit item rest

    | LetDecl when hasKw item "use" ->
        (match bangBinder item with
         | Some (pat, rhs) -> call b "Using" [ rhs; lambda [ GNode pat ] (tail ()) ]
         | None -> sequential ())
    | LetDecl -> Green.node BlockExpr [ walk (GNode item); tail () ]
    | BlockExpr when isDoStmt item && hasBang item ->
        // `do! e` is `let! () = e`. With nothing after it the continuation is
        // the unit VALUE when the builder can return one, and Zero when it
        // cannot — which is what F# emits for each.
        (match nodesOf item |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast with
         | Some e ->
             let k =
                 if not (List.isEmpty rest) then tail ()
                 elif b.HasReturn then call b "Return" [ unitExpr () ]
                 else call b "Zero" []
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
    // is an implicit yield — unless the probe found it has no value, which
    // is exactly what makes it a statement instead.
    | _ when not explicit && not (statementAt (offsetOf item)) ->
        // a bare RANGE splices: `seq { a .. b }` yields the range's
        // ELEMENTS — F#'s reading — where a Yield would hand the builder
        // the whole range as one value
        let isRange =
            item.NodeKind = BinaryExpr
            && (item.Children
                |> List.exists (fun c ->
                    match c with
                    | GToken t -> t.Kind = Operator && t.Text = ".."
                    | _ -> false))
        if isRange then combine (call b "YieldFrom" [ walk (GNode item) ])
        else combine (call b "Yield" [ walk (GNode item) ])
    | _ when List.isEmpty rest -> Green.node BlockExpr [ walk (GNode item); call b "Zero" [] ]
    | _ -> sequential ()

/// `let!` — and the `and!` group that may follow it, which F# binds in
/// PARALLEL through `MergeSources` rather than in sequence. Two special
/// shapes ride on this one:
///
///   * `use! p = e` is a `Bind` whose continuation is a `Using` on what was
///     bound — F# writes it as two nested lambdas over the same name;
///   * a continuation that ENDS in `return e` fuses into `BindReturn`, when
///     the builder has one. It is not an optimisation the builder can be
///     denied: `AValBuilder.BindReturn` is `AVal.map` where `Bind` is
///     `AVal.bind`, and the adaptive graph that comes out is a different
///     one.
and private bangLet (b : CeBuilder) (explicit : bool) (item : GreenNode) (rest : GreenNode list) : Green =
    let rec peel (acc : (GreenNode * Green) list) (rs : GreenNode list) =
        match rs with
        | r :: more when r.NodeKind = LetDecl && hasBang r && hasKw r "and" ->
            (match bangBinder r with
             | Some pr -> peel (acc @ [ pr ]) more
             | None -> acc, rs)
        | _ -> acc, rs
    match bangBinder item with
    | None -> Green.node BlockExpr [ walk (GNode item); blockYielding b explicit rest ]
    | Some (pat, rhs) ->
        let ands, after = peel [] rest
        let tail () = blockYielding b explicit after
        // `use!` binds, then scopes what it bound
        let body () =
            if hasKw item "use" && List.isEmpty ands then
                match patName pat with
                | Some nm ->
                    call b "Using" [ ident nm
                                     lambda [ Green.node WildcardPat [ tk Ident "_" ] ] (tail ()) ]
                | None -> tail ()
            else tail ()
        let sources = (GNode pat, rhs) :: (ands |> List.map (fun (p, r) -> GNode p, r))
        let n = List.length sources
        let canMerge = b.HasMergeSources || b.HasMergeSources3
        let k =
            if canMerge || List.isEmpty ands then body ()
            else sequentialAnds b (ands |> List.map (fun (p, r) -> GNode p, r)) (body ())
        let returned = if b.HasBindReturn && not (hasKw item "use") then stripReturn b k else None
        let arity (want : int) (hasIt : bool) = n = want && hasIt
        if arity 2 b.HasBind2Return && returned.IsSome then
            match sources, returned with
            | [ (p1, r1); (p2, r2) ], Some inner ->
                call b "Bind2Return" [ r1; r2; lambda [ tuplePat [ p1; p2 ] ] inner ]
            | _ -> call b "Bind" [ rhs; lambda [ GNode pat ] k ]
        elif arity 3 b.HasBind3Return && returned.IsSome then
            match sources, returned with
            | [ (p1, r1); (p2, r2); (p3, r3) ], Some inner ->
                call b "Bind3Return" [ r1; r2; r3; lambda [ tuplePat [ p1; p2; p3 ] ] inner ]
            | _ -> call b "Bind" [ rhs; lambda [ GNode pat ] k ]
        elif arity 2 b.HasBind2 then
            match sources with
            | [ (p1, r1); (p2, r2) ] -> call b "Bind2" [ r1; r2; lambda [ tuplePat [ p1; p2 ] ] k ]
            | _ -> call b "Bind" [ rhs; lambda [ GNode pat ] k ]
        elif arity 3 b.HasBind3 then
            match sources with
            | [ (p1, r1); (p2, r2); (p3, r3) ] ->
                call b "Bind3" [ r1; r2; r3; lambda [ tuplePat [ p1; p2; p3 ] ] k ]
            | _ -> call b "Bind" [ rhs; lambda [ GNode pat ] k ]
        else
            let source, binder =
                if List.isEmpty ands || not canMerge then rhs, GNode pat
                else merge b sources
            match returned with
            | Some inner -> call b "BindReturn" [ source; lambda [ binder ] inner ]
            | None -> call b "Bind" [ source; lambda [ binder ] k ]

/// The sources of an `and!` group, merged the way F# merges them: the first
/// two stay where they are and everything after them folds into a THIRD,
/// recursively. Four sources come out as
/// `MergeSources3(a, b, MergeSources(c, d))` and five as
/// `MergeSources3(a, b, MergeSources3(c, d, e))` — measured, not guessed.
/// The binder mirrors the nesting.
and private merge (b : CeBuilder) (sources : (Green * Green) list) : Green * Green =
    match sources with
    | [] -> unitExpr (), unitPat ()
    | [ (p, r) ] -> r, p
    | [ (p1, r1); (p2, r2) ] when b.HasMergeSources ->
        call b "MergeSources" [ r1; r2 ], tuplePat [ p1; p2 ]
    | [ (p1, r1); (p2, r2); (p3, r3) ] when b.HasMergeSources3 ->
        call b "MergeSources3" [ r1; r2; r3 ], tuplePat [ p1; p2; p3 ]
    | (p1, r1) :: (p2, r2) :: more when b.HasMergeSources3 ->
        let rr, rp = merge b more
        call b "MergeSources3" [ r1; r2; rr ], tuplePat [ p1; p2; rp ]
    | (p1, r1) :: more ->
        let rr, rp = merge b more
        call b "MergeSources" [ r1; rr ], tuplePat [ p1; rp ]

/// A group the builder cannot merge binds in SEQUENCE instead. The value is
/// the same; for an adaptive builder the graph is not, which is why this is
/// the last resort rather than the shape.
and private sequentialAnds (b : CeBuilder) (ands : (Green * Green) list) (inner : Green) : Green =
    List.foldBack (fun (p, r) acc -> call b "Bind" [ r; lambda [ p ] acc ]) ands inner

/// Is this exactly `b.Return(e)`, possibly after some statements? F# fuses
/// `let! p = e` with a continuation of that shape into `BindReturn`, and the
/// statements ride along inside the lambda.
and private stripReturn (b : CeBuilder) (g : Green) : Green option =
    match g with
    | GNode n when n.NodeKind = AppExpr ->
        (match n.Children with
         | [ GNode d; GNode a ] when d.NodeKind = DotExpr && a.NodeKind = ParenExpr ->
             let names = d.Children |> List.choose (fun c -> match c with GToken t -> Some t.Text | _ -> None)
             let recv =
                 match d.Children |> List.tryHead with
                 | Some (GNode r) when r.NodeKind = IdentExpr ->
                     (match r.Children |> List.tryHead with
                      | Some (GToken t) -> t.Text
                      | _ -> "")
                 | _ -> ""
             if recv = b.Name && List.contains "Return" names then
                 match a.Children |> List.tryPick (fun c -> match c with GNode e -> Some (GNode e) | _ -> None) with
                 | Some e -> Some e
                 | None -> None
             else None
         | _ -> None)
    | GNode n when n.NodeKind = BlockExpr ->
        (match List.rev n.Children with
         | last :: before ->
             (match stripReturn b last with
              | Some inner -> Some (Green.node BlockExpr (List.rev (inner :: before)))
              | None -> None)
         | [] -> None)
    | _ -> None

/// The pattern and the right-hand side of a `let!`/`use!`/`use` binder.
and private bangBinder (item : GreenNode) : (GreenNode * Green) option =
    let pat = nodesOf item |> List.tryFind (fun m -> isPatKind m.NodeKind)
    let rhs = nodesOf item |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast
    match pat, rhs with
    | Some p, Some r -> Some (p, walk (GNode r))
    | _ -> None

/// `(a, b, c)` as a binder — the parenthesised, comma-separated form a
/// lambda takes.
and private tuplePat (ps : Green list) : Green =
    let acc = vecNew<Green> ()
    vecAdd acc (tk LParen "(")
    let mutable first = true
    for p in ps do
        if not first then vecAdd acc (tk Comma ",")
        first <- false
        vecAdd acc p
    vecAdd acc (tk RParen ")")
    Green.node ParenPat (vecToList acc)

/// A nested body — a loop's, a branch's — is a computation of its own.
and private nested (b : CeBuilder) (explicit : bool) (body : GreenNode) : Green =
    if body.NodeKind = BlockExpr && not (isDoStmt body) then blockYielding b explicit (nodesOf body)
    else blockYielding b explicit [ body ]

/// `if`/`elif`/`else`, where the BRANCHES are computations and the
/// conditions are not. A missing `else` is where Zero comes from.
and private ifExpr (b : CeBuilder) (explicit : bool) (item : GreenNode) : Green =
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
and private clauses (b : CeBuilder) (explicit : bool) (item : GreenNode) : Green =
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
and private tryExpr (b : CeBuilder) (explicit : bool) (item : GreenNode) : Green =
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

/// Rewrite every computation expression in a file, given what the probe pass
/// learned about each one's builder. Files are independent, so the counter
/// restarts: the same text and the same answers desugar to the same tree,
/// which is what lets the result be cached like any other parse.
/// Any allocation will do as the lock's identity; a Vec is one this compiler
/// can also compile ITSELF, which `obj ()` is not.
let private rewriteLock = vecNew<int> ()

/// Not to be called except through the lock below. The module state it sets
/// is read by every constructor above, and the assignments live in a plain
/// function rather than in the lock's lambda because assigning to a
/// module-level mutable from inside a closure is not something this compiler
/// can compile itself.
let private rewriteUnlocked (lookup : int -> CeBuilder) (isStatement : int -> bool) (root : GreenNode) : GreenNode =
    counter <- synthBase
    builderAt <- lookup
    statementAt <- isStatement
    let r =
        match walk (GNode root) with
        | GNode n -> n
        | _ -> root
    builderAt <- (fun _ -> unknownBuilder "?")
    statementAt <- (fun _ -> false)
    r

let desugarWithStatements (lookup : int -> CeBuilder) (isStatement : int -> bool) (root : GreenNode) : GreenNode =
    // The offset counter and the probe's answers are module state — every
    // constructor above reads them, and threading them through forty call
    // sites would say nothing this does not. It has to BE a lock: two
    // workspaces rewriting at once corrupted each other's answers, and the
    // symptom was a `BindReturn` that fused in one run and not the next.
    lock rewriteLock (fun () -> rewriteUnlocked lookup isStatement root)

/// Is there anything here for the rewrite to do? Files without a computation
/// expression — which is nearly all of them, the compiler's own sources and
/// the prelude included — skip the probe pass entirely.
let rec hasComp (g : Green) : bool =
    match g with
    | GToken _ -> false
    | GNode n -> n.NodeKind = CompExpr || List.exists hasComp n.Children

let desugarWith (lookup : int -> CeBuilder) (root : GreenNode) : GreenNode =
    desugarWithStatements lookup (fun _ -> false) root

/// The rewrite with no probe behind it: a lone file, or one whose builder
/// could not be typed.
let desugar (root : GreenNode) : GreenNode =
    desugarWithStatements (fun _ -> unknownBuilder "?") (fun _ -> false) root

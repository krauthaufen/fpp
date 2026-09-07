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
      /// the CE expression's OWN offset, so a missing builder method can be
      /// reported at the source rather than at the rewrite's synthetic
      /// tokens — which sit above 500000000 and are deliberately excluded
      /// from the missing-member diagnostic, since blaming a position the
      /// author never wrote is worse than saying nothing
      At : int
      /// does the builder declare this method? General, because the control
      /// constructs need arbitrary names and the flags below only cover the
      /// ones the REWRITE branches on
      Has : string -> bool
      HasRun : bool
      HasDelay : bool
      HasReturn : bool
      HasBindReturn : bool
      HasBind2 : bool
      HasBind3 : bool
      HasBind2Return : bool
      HasBind3Return : bool
      HasMergeSources : bool
      HasMergeSources3 : bool
      /// a CUSTOM OPERATION name -> the builder method it calls, for
      /// `builder { op arg }`. Empty for an ordinary builder.
      CustomOp : string -> string option }

/// What to assume when the probe could not type the builder — a builder in a
/// file that does not type check, or a lone file with no project around it.
/// Omitting `Run` and `Delay` is the choice that still compiles against the
/// SMALLEST builder, so an unknown one degrades to the minimum rather than to
/// a call that cannot resolve.
let unknownBuilder (name : string) : CeBuilder =
    // `Has` answers TRUE for an unknown builder: it could not be typed, so
    // every method is assumed present and nothing is reported. Guessing the
    // other way would turn a file that does not type check into a pile of
    // missing-method errors that vanish once it does.
    { Name = name; At = 0; Has = (fun _ -> true)
      HasRun = false; HasDelay = false; HasReturn = true
      HasBindReturn = false; HasBind2 = false; HasBind3 = false
      HasBind2Return = false; HasBind3Return = false
      HasMergeSources = false; HasMergeSources3 = false
      CustomOp = (fun _ -> None) }

/// `recv.Name(args)` — the tuple form, which is how a builder's methods are
/// declared and how F# calls them.
let private callOn (recv : string) (name : string) (args : Green list) : Green =
    let target = Green.node DotExpr [ ident recv; tk Operator "."; tk Ident name ]
    match args with
    | [] -> Green.node AppExpr [ target; unitExpr () ]
    | [ a ] -> Green.node AppExpr [ target; paren a ]
    | many -> Green.node AppExpr [ target; paren (tuple many) ]

/// What a computation expression asked its builder for and did not get.
/// Module state, like the offset counter above, and drained by the entry
/// point under the same lock so two files cannot mix.
let private ceDiags = vecNew<int * string> ()

let private call (b : CeBuilder) (name : string) (args : Green list) : Green =
    // F# FS0708. Without this the rewrite emitted a call to a method that is
    // not there: it compiled, and the module TRAPPED when the construct was
    // reached — a diagnostic F# gives at compile time, arriving at run time.
    if not (b.Has name) then
        vecAdd ceDiags
            (b.At, "this control construct may only be used if the computation "
                   + "expression builder defines a '" + name + "' method")
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
    | AppPat | ParenPat | ListPat | ArrayPat | AsPat | TypeTestPat | SplicePat -> true
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

/// Body items the probe typed and found to HAVE a value. The complement of
/// `statementAt` only where the probe RAN: an item it never typed — a branch
/// body, a loop body — answers false to both, and the mixed-yield rule below
/// needs the difference (see item1).
let mutable private valueAt : int -> bool = fun _ -> false

let rec private walk (g : Green) : Green =
    match g with
    | GToken _ -> g
    | GNode n ->
        if n.NodeKind = CompExpr then comp n
        elif n.NodeKind = AppExpr then
            match tryBarrierLift n with
            | Some lifted -> lifted
            | None -> Green.node n.NodeKind (List.map walk n.Children)
        else Green.node n.NodeKind (List.map walk n.Children)


// ---- barrier lift ---------------------------------------------------------
// `Parallel.dispatch n (fun vt -> ... vt.Sync() ...)` fissions at every
// top-level `vt.Sync ()` into phases of `Parallel.dispatchPhased`; a local
// LIVE across a barrier spills into a per-thread array. Only the literal
// lambda form lifts, and only top-level Syncs — a barrier under control
// flow is not uniformly encountered, and the kernel is left for the
// runtime Vt, whose Sync explains the rule when reached.

and private isVtSyncDot (vt : string) (d : GreenNode) : bool =
    d.NodeKind = DotExpr
    && (match d.Children with
        | [ GNode i; GToken _; GToken s ] ->
            i.NodeKind = IdentExpr && s.Text = "Sync"
            && (match i.Children with
                | [ GToken t ] -> t.Text = vt
                | _ -> false)
        | _ -> false)

and private isSyncStmt (vt : string) (m : GreenNode) : bool =
    if isVtSyncDot vt m then true
    elif m.NodeKind = AppExpr then
        (match m.Children |> List.tryHead with
         | Some (GNode d) -> isVtSyncDot vt d
         | _ -> false)
    else false

and private anySyncBelow (vt : string) (g : Green) : bool =
    match g with
    | GToken _ -> false
    | GNode d ->
        isVtSyncDot vt d || List.exists (anySyncBelow vt) d.Children

/// every bare identifier read of `name`, rewritten by `mk` (an assignment
/// left side included — the caller decides what the write becomes)
and private substIdent (name : string) (mk : unit -> Green) (g : Green) : Green =
    match g with
    | GToken _ -> g
    | GNode d when d.NodeKind = IdentExpr ->
        (match d.Children with
         | [ GToken t ] when t.Text = name -> mk ()
         | _ -> g)
    | GNode d -> Green.node d.NodeKind (List.map (substIdent name mk) d.Children)

and private indexExpr (arr : string) (ix : string) : Green =
    Green.node DotExpr
        [ ident arr; tk Operator "."
          Green.node ListExpr [ tk LBracket "["; ident ix; tk RBracket "]" ] ]

and private letBoundName (m : GreenNode) : string option =
    if m.NodeKind <> LetDecl then None
    else
        m.Children
        |> List.tryPick (fun c ->
            match c with
            | GNode p when p.NodeKind = IdentPat ->
                (match p.Children with
                 | [ GToken t ] -> Some t.Text
                 | _ -> None)
            | _ -> None)

and private mentions (name : string) (g : Green) : bool =
    match g with
    | GToken _ -> false
    | GNode d when d.NodeKind = IdentExpr ->
        (match d.Children with
         | [ GToken t ] -> t.Text = name
         | _ -> false)
    | GNode d -> List.exists (mentions name) d.Children

and private tryBarrierLift (n : GreenNode) : Green option =
    // AppExpr: [ DotExpr(Parallel . dispatch); nArg; (fun vt -> ...) ] —
    // the lambda usually rides inside its parens
    let unparen (m : GreenNode) : GreenNode =
        if m.NodeKind = ParenExpr then
            match nodesOf m with
            | [ inner ] when inner.NodeKind = LambdaExpr -> inner
            | _ -> m
        else m
    match nodesOf n |> List.map unparen with
    | [ head; nArg; lam ] when
          n.NodeKind = AppExpr && head.NodeKind = DotExpr && lam.NodeKind = LambdaExpr
          && (match head.Children with
              | [ GNode m; GToken _; GToken d ] ->
                  d.Text = "dispatch" && m.NodeKind = IdentExpr
                  && (match m.Children with
                      | [ GToken t ] -> t.Text = "Parallel"
                      | _ -> false)
              | _ -> false) ->
        // the kernel parameter's name
        let vt =
            nodesOf lam
            |> List.filter (fun p -> p.NodeKind = IdentPat)
            |> List.tryHead
            |> Option.bind (fun p -> tokensOf p |> List.tryFind (fun t -> t.Kind = Ident))
            |> Option.map (fun t -> t.Text)
        match vt with
        | None -> None
        | Some vt ->
            let body = nodesOf lam |> List.filter (fun m -> isExprish m.NodeKind) |> List.tryLast
            match body with
            | None -> None
            | Some body ->
                let items =
                    // statements INCLUDE let-bindings — they are exactly
                    // what spills across a barrier
                    if body.NodeKind = BlockExpr then
                        nodesOf body |> List.filter (fun m -> isExprish m.NodeKind || m.NodeKind = LetDecl)
                    else [ body ]
                if not (items |> List.exists (isSyncStmt vt)) then None
                else
                // fission at top-level Syncs
                let phases = vecNew<GreenNode list> ()
                let cur = vecNew<GreenNode> ()
                let mutable illegal = false
                for it in items do
                    if isSyncStmt vt it then
                        vecAdd phases (vecToList cur)
                        vecClear cur
                    else
                        if anySyncBelow vt (GNode it) then illegal <- true
                        vecAdd cur it
                vecAdd phases (vecToList cur)
                if illegal then None
                else
                let phaseList = vecToList phases
                let k = List.length phaseList
                let iv = "__vt" + string (freshOffset ())
                let pv = "__p" + string (freshOffset ())
                let nv = "__n" + string (freshOffset ())
                // vt.Index -> the index variable; done before spilling
                let fixIndex (g : Green) : Green =
                    let rec go (x : Green) : Green =
                        match x with
                        | GToken _ -> x
                        | GNode d when
                              d.NodeKind = DotExpr
                              && (match d.Children with
                                  | [ GNode i; GToken _; GToken f ] ->
                                      f.Text = "Index" && i.NodeKind = IdentExpr
                                      && (match i.Children with
                                          | [ GToken t ] -> t.Text = vt
                                          | _ -> false)
                                  | _ -> false) -> ident iv
                        | GNode d -> Green.node d.NodeKind (List.map go d.Children)
                    go g
                let phaseList = phaseList |> List.map (List.map (fun m -> match fixIndex (GNode m) with GNode x -> x | _ -> m))
                // the LIVE SET: let-bound in phase p, mentioned after it
                let spills = vecNew<string * string * int> ()   // name, arr, phase
                phaseList |> List.iteri (fun p stmts ->
                    for st in stmts do
                        match letBoundName st with
                        | Some nm when
                              phaseList
                              |> List.mapi (fun q ss -> q, ss)
                              |> List.exists (fun (q, ss) ->
                                  q > p && ss |> List.exists (fun s2 -> mentions nm (GNode s2))) ->
                            vecAdd spills (nm, "__arr_" + nm + string (freshOffset ()), p)
                        | _ -> ())
                let spillList = vecToList spills
                // rewrite each phase: the binding becomes an element WRITE,
                // later reads become element READS
                let rewritePhase (p : int) (stmts : GreenNode list) : Green list =
                    stmts
                    |> List.map (fun st ->
                        let asW =
                            match letBoundName st with
                            | Some nm ->
                                (match spillList |> List.tryFind (fun (n2, _, ph) -> n2 = nm && ph = p) with
                                 | Some (_, arr, _) ->
                                     // `let x = e` -> `arr.[i] <- e`
                                     let rhs =
                                         st.Children
                                         |> List.rev
                                         |> List.tryPick (fun c ->
                                             match c with
                                             | GNode m when isExprish m.NodeKind -> Some (GNode m)
                                             | _ -> None)
                                     (match rhs with
                                      | Some e ->
                                          Some (Green.node BinaryExpr
                                                  [ indexExpr arr iv; tk Operator "<-"; e ])
                                      | None -> None)
                                 | None -> None)
                            | None -> None
                        match asW with
                        | Some w -> w
                        | None ->
                            // reads of any spill from an EARLIER phase
                            let mutable g : Green = GNode st
                            for nm, arr, ph in spillList do
                                if ph < p then g <- substIdent nm (fun () -> indexExpr arr iv) g
                                elif ph = p then
                                    // same-phase reads keep the local ONLY if
                                    // the binding stayed; it did not — read
                                    // the array here too
                                    g <- substIdent nm (fun () -> indexExpr arr iv) g
                            g)
                let phaseBodies =
                    phaseList |> List.mapi (fun p stmts ->
                        match rewritePhase p stmts with
                        | [] -> unitExpr ()
                        | [ one ] -> one
                        | many -> Green.node BlockExpr many)
                // if __p = 0 then B0 elif ... else Bk-1
                let rec chain (p : int) (bodies : Green list) : Green =
                    match bodies with
                    | [ last ] -> last
                    | b0 :: rest ->
                        Green.node IfExpr
                            [ tk Keyword "if"
                              Green.node BinaryExpr
                                  [ ident pv; tk Operator "="
                                    Green.node LiteralExpr [ tk IntLit (string p) ] ]
                              tk Keyword "then"; b0
                              tk Keyword "else"; chain (p + 1) rest ]
                    | [] -> unitExpr ()
                let kernel = lambda [ identPat pv; identPat iv ] (chain 0 phaseBodies)
                let callP =
                    Green.node AppExpr
                        [ Green.node DotExpr [ ident "Parallel"; tk Operator "."; tk Ident "dispatchPhased" ]
                          ident nv
                          Green.node LiteralExpr [ tk IntLit "1" ]
                          Green.node LiteralExpr [ tk IntLit (string k) ]
                          paren kernel ]
                let decls = vecNew<Green> ()
                vecAdd decls (Green.node LetDecl [ tk Keyword "let"; identPat nv; tk Operator "="; walk (GNode nArg) ])
                for nm, arr, _ in spillList do
                    vecAdd decls
                        (Green.node LetDecl
                            [ tk Keyword "let"; identPat arr; tk Operator "="
                              Green.node AppExpr
                                  [ Green.node DotExpr [ ident "Array"; tk Operator "."; tk Ident "zeroCreate" ]
                                    ident nv ] ])
                vecAdd decls callP
                Some (Green.node BlockExpr (vecToList decls))
    | _ -> None

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
        let items = bodyItems body
        // CUSTOM OPERATIONS (`sampler2d { texture X; filter F }`): every item
        // is `op arg...` where `op` is a `[<CustomOperation>]` on the builder.
        // Each threads the accumulator: `b.Method(acc, arg...)`, starting from
        // `b.Yield(())`, then `Run`. Only when EVERY item is a custom op — a
        // mix with yield/let/for is not this shape and takes the normal path
        // (and F# would reject the custom op there anyway).
        let asCustomOp (it : GreenNode) : (string * Green list) option =
            let headArgs (n : GreenNode) =
                match n.NodeKind with
                | IdentExpr -> (match Green.tokens (GNode n) |> List.tryHead with Some t when t.Kind = Ident -> Some (t.Text, []) | _ -> None)
                | AppExpr ->
                    (match nodesOf n |> List.filter (fun x -> isExprish x.NodeKind) with
                     | h :: args when h.NodeKind = IdentExpr ->
                         (match Green.tokens (GNode h) |> List.tryHead with
                          | Some t when t.Kind = Ident -> Some (t.Text, args |> List.map (fun a -> GNode a))
                          | _ -> None)
                     | _ -> None)
                | _ -> None
            let unwrap (n : GreenNode) =
                match n.NodeKind with
                | BlockExpr -> (match nodesOf n |> List.filter (fun x -> isExprish x.NodeKind) with [ one ] -> one | _ -> n)
                | _ -> n
            match headArgs (unwrap it) with
            | Some (opn, args) -> (match b.CustomOp opn with Some m -> Some (m, args) | None -> None)
            | None -> None
        let ops = items |> List.map asCustomOp
        if not (List.isEmpty ops) && List.forall Option.isSome ops then
            // b.Yield(()) is the seed; each op wraps it: b.Method(acc, args)
            let seed = call b "Yield" []
            let folded =
                (ops |> List.map Option.get)
                |> List.fold (fun acc (m, args) -> callOn b.Name m (acc :: args)) seed
            let ran = if b.HasRun then call b "Run" [ folded ] else folded
            Green.node BlockExpr [ bind; ran ]
        else
        let core = block b items
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
        // `use p = e` and `use p = e in BODY` both bind a resource whose
        // scope is the continuation. In the block form the continuation is
        // `rest`; in the `in` form the body sits INSIDE this node after the
        // `in`, and `rest` follows it. bangBinder's tryLast would take that
        // body for the resource — so read the resource as the FIRST exprish
        // child and splice any post-`in` body ahead of rest.
        let pat = nodesOf item |> List.tryFind (fun m -> isPatKind m.NodeKind)
        let exprs = nodesOf item |> List.filter (fun m -> isExprish m.NodeKind)
        (match pat, exprs with
         | Some p, rhs :: after ->
             let body =
                 match after with
                 | _ :: _ -> blockYielding b explicit (after @ rest)
                 | [] -> tail ()
             call b "Using" [ walk (GNode rhs); lambda [ GNode p ] body ]
         | _ -> sequential ())
    | LetDecl ->
        // `let b = 3 in <body>` inside a builder: the BODY is a computation
        // item too. Walked plainly it left a bare `return` in the tree, which
        // is not an expression the builder ever sees. Keep the binding — it
        // has to scope over the body — and desugar what follows `in`.
        let mutable seenEq = false
        let mutable seenIn = false
        let mutable spliced = false
        let rebuilt =
            item.Children |> List.map (fun c ->
                match c with
                | GToken t when t.Kind = Operator && t.Text = "=" && not seenIn -> seenEq <- true; c
                | GToken t when t.Kind = Keyword && t.Text = "in" -> seenIn <- true; c
                | GNode nd when seenIn && not spliced ->
                    spliced <- true
                    blockYielding b explicit (nd :: rest)
                | GNode nd when seenEq && not seenIn -> walk (GNode nd)
                | _ -> c)
        if spliced then Green.node LetDecl rebuilt
        else Green.node BlockExpr [ walk (GNode item); tail () ]
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
    // A VALUE beside an explicit `yield`. F# reads it as a statement and
    // DISCARDS it (warning FS0020), so `div { "bare"; yield "x" }` silently
    // loses "bare" — this compiler has no warnings, and losing a value the
    // author wrote is exactly the shape it refuses to ship. A DIVERGENCE,
    // deliberately: fsc accepts the program. It cost fpp.dom the most
    // debugging time of its milestone, twice (~/claude/fpp-base-snags.md #51),
    // and it is the historic wombat.dom scar repeating.
    | _ when explicit && valueAt (offsetOf item) ->
        vecAdd ceDiags
            (offsetOf item,
             "a computation expression may not mix implicit and explicit yields: this value would be discarded — write `yield` before it")
        combine (call b "Yield" [ walk (GNode item) ])
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
        // `let! v = e in body` keeps its continuation INSIDE the binding where
        // the block form has it as the next statement, and bangBinder takes the
        // LAST expression as the source — so the body became the source and the
        // binder went unbound. Split it: the source is what precedes `in`, and
        // the body joins the front of the continuation, where the block form
        // would have put it.
        let pat, rhs, rest =
            // the continuation is the node AFTER the `in`, whatever kind it
            // is: a chained `let! a = e in let! b = e2 in body` nests a
            // LetDecl there, which is not "exprish" and was missed
            let rec afterIn (cs : Green list) (seen : bool) (acc : GreenNode option) : GreenNode option =
                match cs with
                | GToken t :: more when t.Kind = Keyword && t.Text = "in" -> afterIn more true acc
                | GNode nd :: more -> afterIn more seen (if seen then Some nd else acc)
                | _ :: more -> afterIn more seen acc
                | [] -> acc
            let exprs = nodesOf item |> List.filter (fun m -> isExprish m.NodeKind)
            match afterIn item.Children false None, exprs with
            | Some body, first :: _ -> pat, walk (GNode first), body :: rest
            | _ -> pat, rhs, rest
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
let private rewriteUnlocked (lookup : int -> CeBuilder) (isStatement : int -> bool) (isValue : int -> bool) (root : GreenNode) : GreenNode =
    counter <- synthBase
    builderAt <- lookup
    statementAt <- isStatement
    valueAt <- isValue
    let r =
        match walk (GNode root) with
        | GNode n -> n
        | _ -> root
    builderAt <- (fun _ -> unknownBuilder "?")
    statementAt <- (fun _ -> false)
    valueAt <- (fun _ -> false)
    // FPP_CE_DUMP=1 prints what a computation expression became. The rewrite
    // is where a CE's meaning is decided, and a wrong tree here reads as a
    // type error at a synthetic offset or as a silently empty result — the
    // text is the only place the shape is legible.
    if System.Environment.GetEnvironmentVariable "FPP_CE_DUMP" = "1" then
        eprintfn "CEDUMP %s" (Green.toText (GNode r))
    r

/// Answers the rewritten tree AND what the builders could not supply. The
/// diagnostics are drained under the SAME lock the rewrite holds — they are
/// module state for the same reason the offset counter is.
let desugarWithDiags (lookup : int -> CeBuilder) (isStatement : int -> bool) (isValue : int -> bool) (root : GreenNode) : GreenNode * (int * string) list =
    // The offset counter and the probe's answers are module state — every
    // constructor above reads them, and threading them through forty call
    // sites would say nothing this does not. It has to BE a lock: two
    // workspaces rewriting at once corrupted each other's answers, and the
    // symptom was a `BindReturn` that fused in one run and not the next.
    lock rewriteLock (fun () ->
        vecClear ceDiags
        let tree = rewriteUnlocked lookup isStatement isValue root
        tree, vecToList ceDiags)

let desugarWithStatements (lookup : int -> CeBuilder) (isStatement : int -> bool) (isValue : int -> bool) (root : GreenNode) : GreenNode =
    fst (desugarWithDiags lookup isStatement isValue root)

/// Is there anything here for the rewrite to do? Files without a computation
/// expression — which is nearly all of them, the compiler's own sources and
/// the prelude included — skip the probe pass entirely.
let rec hasComp (g : Green) : bool =
    match g with
    | GToken _ -> false
    | GNode n ->
        n.NodeKind = CompExpr
        // a Parallel.dispatch call may need the barrier lift — cheap to
        // over-approximate here, the lift itself decides
        || (n.NodeKind = DotExpr
            && (match n.Children with
                | [ GNode m; GToken _; GToken d ] ->
                    d.Text = "dispatch" && m.NodeKind = IdentExpr
                    && (match m.Children with
                        | [ GToken t ] -> t.Text = "Parallel"
                        | _ -> false)
                | _ -> false))
        || List.exists hasComp n.Children

let desugarWith (lookup : int -> CeBuilder) (root : GreenNode) : GreenNode =
    desugarWithStatements lookup (fun _ -> false) (fun _ -> false) root

/// The rewrite with no probe behind it: a lone file, or one whose builder
/// could not be typed.
let desugar (root : GreenNode) : GreenNode =
    desugarWithStatements (fun _ -> unknownBuilder "?") (fun _ -> false) (fun _ -> false) root

/// Does the tree contain a `lazy` keyword at all? Cheap gate for the
/// rewrite below, mirroring hasComp.
let rec hasLazy (g : Green) : bool =
    match g with
    | GToken t -> t.Kind = Keyword && t.Text = "lazy"
    | GNode n -> List.exists hasLazy n.Children

/// `lazy e` IS `Lazy (fun () -> e)` — rewritten AFTER parsing (the parse
/// stays lossless) so the prelude ctor resolves, types and lowers exactly
/// like the call the source could have written. The synthetic offsets sit
/// INSIDE the 4-char keyword, where no real token can start.
let rec desugarLazy (n : GreenNode) : GreenNode =
    let mapped =
        n.Children |> List.map (fun c ->
            match c with
            | GNode m -> GNode (desugarLazy m)
            | t -> t)
    let rebuilt =
        match Green.node n.NodeKind mapped with
        | GNode m -> m
        | _ -> n
    if rebuilt.NodeKind <> PrefixExpr then rebuilt
    else
        match rebuilt.Children with
        | [ GToken kw; (GNode _ as arg) ] when kw.Kind = Keyword && kw.Text = "lazy" ->
            let tok (k : TokenKind) (txt : string) (off : int) : Green =
                GToken { Kind = k; Text = txt; Leading = []; Trailing = []; Offset = off }
            let unitPat =
                Green.node ParenPat [ tok LParen "(" (kw.Offset + 2); tok RParen ")" (kw.Offset + 3) ]
            let lam =
                Green.node LambdaExpr
                    [ tok Keyword "fun" (kw.Offset + 1); unitPat
                      tok Operator "->" (kw.Offset + 3); arg ]
            match Green.node AppExpr [ Green.node IdentExpr [ tok Ident "Lazy" kw.Offset ]; lam ] with
            | GNode m -> m
            | _ -> rebuilt
        | _ -> rebuilt

/// Does the tree contain a `member val` auto-property? Cheap gate,
/// mirroring hasLazy. Explicit fields (`val mutable x : int`) carry no
/// `member` keyword and do not fire this.
let rec hasMemberVal (n : GreenNode) : bool =
    (n.NodeKind = MemberDecl
     && (tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "val"))
     && (tokensOf n |> List.exists (fun t -> t.Kind = Keyword && t.Text = "member")))
    || (nodesOf n |> List.exists hasMemberVal)

/// `member val P = init [with get[, set]]` IS a backing field plus an
/// accessor property:
///
///   let mutable __mv_P = init
///   member __mvself.P with get () = __mv_P [and set v = __mv_P <- v]
///
/// — rewritten AFTER parsing, like `lazy`, so the shapes that already work
/// (class lets, accessor members) carry the semantics: init runs ONCE at
/// construction, bare form is get-only, `with get, set` adds the setter.
/// `static member val` with a getter only drops to `static member P = init`;
/// a static SETTER needs static state and is left alone (it will not bind).
/// Synthetic offsets are deterministic per declaration — a 32-slot block
/// keyed by the name token's offset, above Desugar's own synthesis base.
let rec desugarMemberVal (n : GreenNode) : GreenNode =
    let expand (c : Green) : Green list =
        match c with
        | GNode m when
              m.NodeKind = MemberDecl
              && (tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "val"))
              && (tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "member")) ->
            let isStatic = tokensOf m |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")
            let nameTok = tokensOf m |> List.tryFind (fun t -> t.Kind = Ident)
            let init = nodesOf m |> List.filter (fun x -> isExprish x.NodeKind) |> List.tryHead
            let accessors =
                nodesOf m
                |> List.filter (fun x -> x.NodeKind = AccessorDecl)
                |> List.choose (fun x -> tokensOf x |> List.tryHead |> Option.map (fun t -> t.Text))
            let hasSet = List.contains "set" accessors
            match nameTok, init with
            | Some nt, Some ie when not isStatic ->
                let mutable k = 600000000 + nt.Offset * 32
                let tok (kd : TokenKind) (txt : string) : Green =
                    let g = GToken { Kind = kd; Text = txt; Leading = []; Trailing = []; Offset = k }
                    k <- k + 1
                    g
                let back = "__mv_" + nt.Text
                let backing =
                    Green.node LetDecl
                        [ tok Keyword "let"; tok Keyword "mutable"
                          Green.node IdentPat [ tok Ident back ]
                          tok Operator "="; GNode ie ]
                let getter =
                    Green.node AccessorDecl
                        [ tok Ident "get"
                          Green.node ParenPat [ tok LParen "("; tok RParen ")" ]
                          tok Operator "="
                          Green.node IdentExpr [ tok Ident back ] ]
                let setterParts =
                    if not hasSet then []
                    else
                        [ tok Keyword "and"
                          Green.node AccessorDecl
                              [ tok Ident "set"
                                Green.node IdentPat [ tok Ident "__mvv" ]
                                tok Operator "="
                                Green.node BinaryExpr
                                    [ Green.node IdentExpr [ tok Ident back ]
                                      tok Operator "<-"
                                      Green.node IdentExpr [ tok Ident "__mvv" ] ] ] ]
                let prop =
                    Green.node MemberDecl
                        ([ tok Keyword "member"; tok Ident "__mvself"; tok Operator "."
                           GToken nt; tok Keyword "with"; getter ] @ setterParts)
                [ backing; prop ]
            | _ -> [ c ]
        | GNode m when
              // a TYPE with `static member val` members: their backing state
              // is PER TYPE, so the field hoists to module level, BEFORE the
              // type, and the member becomes a static accessor property over
              // it — init runs once at module init, F#'s static-init order
              nodesOf m |> List.exists (fun d ->
                  d.NodeKind = MemberDecl
                  && (tokensOf d |> List.exists (fun t -> t.Kind = Keyword && t.Text = "val"))
                  && (tokensOf d |> List.exists (fun t -> t.Kind = Keyword && t.Text = "member"))
                  && (tokensOf d |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static"))) ->
            let tyName =
                match tokensOf m |> List.tryFind (fun t -> t.Kind = Ident) with
                | Some t -> t.Text
                | None -> "T"
            let hoisted = vecNew<Green> ()
            let newKids =
                m.Children |> List.map (fun c2 ->
                    match c2 with
                    | GNode d when
                          d.NodeKind = MemberDecl
                          && (tokensOf d |> List.exists (fun t -> t.Kind = Keyword && t.Text = "val"))
                          && (tokensOf d |> List.exists (fun t -> t.Kind = Keyword && t.Text = "member"))
                          && (tokensOf d |> List.exists (fun t -> t.Kind = Keyword && t.Text = "static")) ->
                        let nameTok = tokensOf d |> List.tryFind (fun t -> t.Kind = Ident)
                        let init = nodesOf d |> List.filter (fun x -> isExprish x.NodeKind) |> List.tryHead
                        let hasSet =
                            nodesOf d
                            |> List.filter (fun x -> x.NodeKind = AccessorDecl)
                            |> List.exists (fun x -> (tokensOf x |> List.tryHead |> Option.map (fun t -> t.Text)) = Some "set")
                        (match nameTok, init with
                         | Some nt, Some ie ->
                             let mutable k = 700000000 + nt.Offset * 32
                             let tok (kd : TokenKind) (txt : string) : Green =
                                 let g = GToken { Kind = kd; Text = txt; Leading = []; Trailing = []; Offset = k }
                                 k <- k + 1
                                 g
                             let back = "__mv_" + tyName + "_" + nt.Text
                             vecAdd hoisted
                                 (Green.node LetDecl
                                     [ tok Keyword "let"; tok Keyword "mutable"
                                       Green.node IdentPat [ tok Ident back ]
                                       tok Operator "="; GNode ie ])
                             let getter =
                                 Green.node AccessorDecl
                                     [ tok Ident "get"
                                       Green.node ParenPat [ tok LParen "("; tok RParen ")" ]
                                       tok Operator "="
                                       Green.node IdentExpr [ tok Ident back ] ]
                             let setterParts =
                                 if not hasSet then []
                                 else
                                     [ tok Keyword "and"
                                       Green.node AccessorDecl
                                           [ tok Ident "set"
                                             Green.node IdentPat [ tok Ident "__mvv" ]
                                             tok Operator "="
                                             Green.node BinaryExpr
                                                 [ Green.node IdentExpr [ tok Ident back ]
                                                   tok Operator "<-"
                                                   Green.node IdentExpr [ tok Ident "__mvv" ] ] ] ]
                             Green.node MemberDecl
                                 ([ tok Keyword "static"; tok Keyword "member"
                                    GToken nt; tok Keyword "with"; getter ] @ setterParts)
                         | _ -> c2)
                    | _ -> c2)
            let rebuilt =
                match Green.node m.NodeKind newKids with
                | GNode r -> desugarMemberVal r
                | _ -> m
            vecToList hoisted @ [ GNode rebuilt ]
        | GNode m -> [ GNode (desugarMemberVal m) ]
        | t -> [ t ]
    match Green.node n.NodeKind (n.Children |> List.collect expand) with
    | GNode r -> r
    | _ -> n

/// Does the tree carry a `[<Literal>]` attribute at all? Cheap gate,
/// mirroring hasLazy.
let rec hasLiteralDecl (n : GreenNode) : bool =
    (n.NodeKind = AttributeList
     && (tokensOf n |> List.exists (fun t -> t.Kind = Ident && t.Text = "Literal")))
    || (nodesOf n |> List.exists hasLiteralDecl)

/// `[<Literal>] let Threshold = 10` makes the NAME usable as a pattern:
/// `| Threshold ->` matches the value 10, it does not bind. Without this the
/// name reads as a union case (F#'s uppercase rule) and the compile fails
/// with "unknown case". The rewrite substitutes the literal token, so the
/// pattern is the one the source could have written by hand.
///
/// Only MATCH CLAUSE patterns are rewritten: a `let` binder is an IdentPat
/// too, and the declaration itself must keep its name.
let desugarLiteralPats (root : GreenNode) : GreenNode =
    // the declared constants: name -> its literal token
    let consts = dictNew<string, Token> ()
    let mutable found = 0
    // the attribute is a SIBLING of the declaration it decorates, not a
    // child of it — the collector carries it forward one node
    let rec collect (n : GreenNode) : unit =
        let mutable pending = false
        for c in nodesOf n do
            if c.NodeKind = AttributeList then
                pending <- tokensOf c |> List.exists (fun t -> t.Kind = Ident && t.Text = "Literal")
            else
                if pending && c.NodeKind = LetDecl then
                    let name =
                        nodesOf c
                        |> List.tryFind (fun x -> x.NodeKind = IdentPat)
                        |> Option.bind (fun x -> tokensOf x |> List.tryHead)
                    let value =
                        nodesOf c
                        |> List.tryFind (fun x -> x.NodeKind = LiteralExpr)
                        |> Option.bind (fun x -> tokensOf x |> List.tryHead)
                    match name, value with
                    | Some nt, Some vt ->
                        dictSet consts nt.Text vt
                        found <- found + 1
                    | _ -> ()
                pending <- false
                collect c
    collect root
    if found = 0 then root
    else
        let rec inPat (g : Green) : Green =
            match g with
            | GNode m when m.NodeKind = IdentPat ->
                (match tokensOf m |> List.tryHead with
                 | Some t ->
                     (match dictTryFind consts t.Text with
                      | Some v ->
                          Green.node LiteralPat
                              [ GToken { v with Leading = t.Leading; Trailing = t.Trailing; Offset = freshOffset () } ]
                      | None -> g)
                 | None -> g)
            | GNode m -> Green.node m.NodeKind (m.Children |> List.map inPat)
            | t -> t
        let rec walkTree (g : Green) : Green =
            match g with
            | GNode m when m.NodeKind = MatchClause ->
                Green.node MatchClause
                    (m.Children |> List.map (fun c ->
                        match c with
                        | GNode p when isPatKind p.NodeKind -> inPat c
                        | other -> walkTree other))
            | GNode m -> Green.node m.NodeKind (m.Children |> List.map walkTree)
            | t -> t
        match walkTree (GNode root) with
        | GNode r -> r
        | _ -> root

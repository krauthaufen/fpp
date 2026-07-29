module Fpp.Backend.BinDriver

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir
open Fpp.Backend.WasmBinary
open Fpp.Backend.EmitBin

// The BINARY driver: Decl list -> executable .wasm bytes, no text anywhere.
// This grows exactly as the runtime did — the expression cases it can emit
// are the ones proven by running programs; anything else raises a named
// error so the next case to port is always explicit.
//
// Numbering is self-consistent within this backend (tags, data, globals):
// the binary module never has to agree with the text module byte-wise, only
// behave identically — the program-output oracle is the gate.

type St =
    { M : Mod
      Errors : Vec<string>
      CaseTag : Dict<string, int>
      CaseArity : Dict<string, int>
      EnumConst : Dict<string, int>
      GlobalOf : Dict<string * int, string>
      FnOf : Dict<string * int, string>
      ArityOf : Dict<string * int, int>
      Warnings : Vec<string>
      /// record name -> field order; (record, field) -> slot
      FieldsOf : Dict<string, string list>
      FieldIdx : Dict<string * string, int>
      /// field name -> owning record (last declaration wins, like the text)
      FieldOwner : Dict<string, string>
      /// each lifted lambda, keyed by its ELam NODE (reference identity):
      /// name + captured keys in slot order
      LamName : RefMap<Expr, string>
      LamFree : Dict<string, (string * int) list>
      LamBody : Vec<string * (VarId * Scheme) * Expr>
      /// let-bound mutables that a lambda mentions: capture copies the env
      /// BY VALUE, so these live in a one-field $cell and the copy that
      /// lands in the closure's env is a copy of the CELL REFERENCE
      CellVars : Dict<string * int, bool>
      /// curry wrappers requested for top-level functions used first-class:
      /// name -> arity, plus request order (bodies are emitted LAST, and
      /// their decls land last too, so decl order still equals body order)
      Wrappers : Dict<string, int>
      WrapperOrder : Vec<string>
      mutable DataN : int }

let private err (st : St) (msg : string) : unit = vecAdd st.Errors msg

/// dereference a $cell already on the stack
let private cellGet (f : Fn) : unit =
    gcT f "ref.cast" "$cell"
    gcTF f "struct.get" "$cell" 0

let private mangle (v : VarId) : string =
    "$b" + string (abs (strHash v.Path % 1000)) + "_" + string v.Offset + "_"
    + (v.Name |> String.map (fun c -> if isLetterOrDigit c then c else '_'))

/// intern a string literal as a data segment, return its name and length
let private internStr (st : St) (bytes : byte[]) : string * int =
    // named by the MODULE's segment count: the scratch pass and the real
    // pass then agree without shared mutable state of their own
    let name = "$bd" + string st.M.DataCount
    dataSeg st.M name bytes
    name, bytes.Length

// unescape for string literals — decimal/hex/named escapes, same rules as
// the text emitter's (shared logic would be better placed in Prelude later)
let private unescape (raw : string) : byte[] =
    let inner =
        if strLen raw >= 6 && charAt raw 0 = '"' && charAt raw 1 = '"' then substr raw 3 (strLen raw - 6)
        elif strLen raw >= 3 && charAt raw 0 = '@' then substr raw 2 (strLen raw - 3)
        elif strLen raw >= 2 then substr raw 1 (strLen raw - 2)
        else raw
    let out = vecNew<byte> ()
    let mutable i = 0
    while i < strLen inner do
        let c = charAt inner i
        if c = '\\' && i + 1 < strLen inner then
            let n = charAt inner (i + 1)
            let code, w =
                match n with
                | 'n' -> 10, 2 | 't' -> 9, 2 | 'r' -> 13, 2
                | '\\' -> 92, 2 | '"' -> 34, 2 | '\'' -> 39, 2
                | d when d >= '0' && d <= '9' && i + 3 < strLen inner
                         && isDigit (charAt inner (i + 2)) && isDigit (charAt inner (i + 3)) ->
                    ((int d - 48) * 100 + (int (charAt inner (i + 2)) - 48) * 10
                     + (int (charAt inner (i + 3)) - 48)) % 256, 4
                | o -> int o, 2
            vecAdd out (byte code)
            i <- i + w
        else
            vecAdd out (byte c)
            i <- i + 1
    vecToArray out

/// A local becomes a cell when it is let-bound, assigned somewhere, and
/// mentioned inside a lambda. The test is per BINDING, so every read and
/// write agrees on the representation. (Port of the text emitter's cellScan.)
let private cellScan (decls : Decl list) : Dict<string * int, bool> =
    let letBound = dictNew<string * int, bool> ()
    let assigned = dictNew<string * int, bool> ()
    let inLambda = dictNew<string * int, bool> ()
    let rec go (depth : int) (e : Expr) : unit =
        let g = go depth
        match e with
        | EVar (v, _) | EVarI (v, _, _) ->
            if depth > 0 then dictSet inLambda (v.Path, v.Offset) true
        | ELam (_, b) -> go (depth + 1) b
        | EAssign (v, x) ->
            dictSet assigned (v.Path, v.Offset) true
            if depth > 0 then dictSet inLambda (v.Path, v.Offset) true
            g x
        | ELet (_, v, _, r, b) ->
            dictSet letBound (v.Path, v.Offset) true
            g r
            g b
        | EApp (fn, args) -> g fn; List.iter g args
        | EIf (a, b, c) -> g a; g b; g c
        | EMatch (s, cs) ->
            g s
            for _, gd, b in cs do
                (match gd with Some gd -> g gd | None -> ())
                g b
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) ->
            List.iter g xs
        | ERecord (_, fs) -> for _, v in fs do g v
        | ERecordExt (_, b, fs) -> g b; (for _, v in fs do g v)
        | EField (r, _, _) -> g r
        | EFieldSet (r, _, _, v) -> g r; g v
        | EWhile (c, b) -> g c; g b
        | EIndex (_, a, i) -> g a; g i
        | EIndexSet (_, a, i, v) -> g a; g i; g v
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | ECast (_, a, _) | ETypeTest (_, a) -> g a
        | EArrayCreate (_, n, v) -> g n; g v
        | EIfaceCall (_, _, recv, args) -> g recv; List.iter g args
        | ETry (b, cs) ->
            g b
            for _, gd, x in cs do
                (match gd with Some gd -> g gd | None -> ())
                g x
        | _ -> ()
    // a top-level function's own parameter lambdas ARE the function, not a
    // capture boundary — its body compiles to a wasm function whose locals
    // are locals
    let rec skipParams (e : Expr) : Expr =
        match e with
        | ELam (_, b) -> skipParams b
        | _ -> e
    for d in decls do
        match d with
        | DLet (_, _, _, e) -> go 0 (skipParams e)
        | _ -> ()
    let cells = dictNew<string * int, bool> ()
    for k, _ in dictPairs assigned do
        if (dictTryFind letBound k).IsSome && (dictTryFind inLambda k).IsSome then
            dictSet cells k true
    cells

/// free variables of a body: referenced keys minus those bound inside
let rec private freeWalk (bound : Dict<string * int, bool>) (acc : Vec<string * int>) (seen : Dict<string * int, bool>) (e : Expr) : unit =
    let note (v : VarId) =
        let k = (v.Path, v.Offset)
        if not (dictTryFind bound k).IsSome && not (dictTryFind seen k).IsSome then
            dictSet seen k true
            vecAdd acc k
    let rec bindPat (p : Pat) =
        match p with
        | PVar (v, _) -> dictSet bound (v.Path, v.Offset) true
        | PAs (inner, v, _) -> dictSet bound (v.Path, v.Offset) true; bindPat inner
        | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.iter bindPat ps
        | PCons (h, t) -> bindPat h; bindPat t
        | _ -> ()
    match e with
    | EVar (v, _) | EVarI (v, _, _) -> note v
    | EAssign (v, x) -> note v; freeWalk bound acc seen x
    | ELam (ps, b) ->
        for pv, _ in ps do dictSet bound (pv.Path, pv.Offset) true
        freeWalk bound acc seen b
    | ELet (_, v, _, rhs, b) ->
        freeWalk bound acc seen rhs
        dictSet bound (v.Path, v.Offset) true
        freeWalk bound acc seen b
    | EMatch (sc, cs) ->
        freeWalk bound acc seen sc
        for pt, g, b in cs do
            bindPat pt
            (match g with Some x -> freeWalk bound acc seen x | None -> ())
            freeWalk bound acc seen b
    | EApp (g, args) -> freeWalk bound acc seen g; for a in args do freeWalk bound acc seen a
    | EIf (a, b, c) -> freeWalk bound acc seen a; freeWalk bound acc seen b; freeWalk bound acc seen c
    | ESeq xs | ETuple xs | EListLit xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) ->
        for x in xs do freeWalk bound acc seen x
    | ERecord (_, fs) -> for _, v in fs do freeWalk bound acc seen v
    | ERecordExt (_, b, fs) -> freeWalk bound acc seen b; (for _, v in fs do freeWalk bound acc seen v)
    | EField (r, _, _) -> freeWalk bound acc seen r
    | EFieldSet (r, _, _, v) -> freeWalk bound acc seen r; freeWalk bound acc seen v
    | EWhile (c, b) -> freeWalk bound acc seen c; freeWalk bound acc seen b
    | EIfaceCall (_, _, r, args) -> freeWalk bound acc seen r; for a in args do freeWalk bound acc seen a
    | ECast (_, x, _) | ETypeTest (_, x) | EArrayLen (_, x) -> freeWalk bound acc seen x
    | EIndex (_, a, i) -> freeWalk bound acc seen a; freeWalk bound acc seen i
    | EIndexSet (_, a, i, v) -> freeWalk bound acc seen a; freeWalk bound acc seen i; freeWalk bound acc seen v
    | EArrayCreate (_, a, b) -> freeWalk bound acc seen a; freeWalk bound acc seen b
    | ETry (b, cs) ->
        freeWalk bound acc seen b
        for pt, g, x in cs do
            bindPat pt
            (match g with Some gg -> freeWalk bound acc seen gg | None -> ())
            freeWalk bound acc seen x
    | _ -> ()

/// discover every lambda in DFS order: curry multi-param, name it, record
/// its free list (order = discovery order of the walk), queue its body
let rec private discoverLams (st : St) (outer : Dict<string * int, bool>) (e : Expr) : unit =
    match e with
    | ELam (ps, body) ->
        // curry to unary
        (match ps with
         | [ (pv, psch) ] ->
             let name = "$blam" + string (vecLen st.LamBody)
             refMapSet st.LamName e name
             let bound = dictNew<string * int, bool> ()
             dictSet bound (pv.Path, pv.Offset) true
             let acc = vecNew<string * int> ()
             freeWalk bound acc (dictNew ()) body
             // captures exclude globals and known functions: those resolve
             // directly wherever they are read. BOTH the build site and the
             // body index this same filtered list, so slots cannot drift.
             let captured =
                 vecToList acc
                 |> List.filter (fun k ->
                     not (dictTryFind st.GlobalOf k).IsSome
                     && not (dictTryFind st.FnOf k).IsSome)
             dictSet st.LamFree name captured
             vecAdd st.LamBody (name, (pv, psch), body)
             let inner = dictNew<string * int, bool> ()
             dictSet inner (pv.Path, pv.Offset) true
             discoverLams st inner body
         | (pv, psch) :: rest ->
             let curried = ELam ([ (pv, psch) ], ELam (rest, body))
             refMapSet st.LamName e (
                 // name the SOURCE node by its curried head so emitNode
                 // finds it: discover the curried form and alias
                 let nm = "$blam" + string (vecLen st.LamBody)
                 discoverLams st outer curried
                 (match refMapTryFind st.LamName curried with Some n -> n | None -> nm))
         | [] -> ())
    | ELet (_, _, _, rhs, b) -> discoverLams st outer rhs; discoverLams st outer b
    | EMatch (sc, cs) ->
        discoverLams st outer sc
        for _, g, b in cs do
            (match g with Some x -> discoverLams st outer x | None -> ())
            discoverLams st outer b
    | EApp (g, args) -> discoverLams st outer g; for a in args do discoverLams st outer a
    | EIf (a, b, c) -> discoverLams st outer a; discoverLams st outer b; discoverLams st outer c
    | ESeq xs | ETuple xs | EListLit xs | EPrim (_, xs) | ECtor (_, _, xs) ->
        for x in xs do discoverLams st outer x
    | ERecord (_, fs) -> for _, v in fs do discoverLams st outer v
    | EField (r, _, _) -> discoverLams st outer r
    | EFieldSet (r, _, _, v) -> discoverLams st outer r; discoverLams st outer v
    | EWhile (c, b) -> discoverLams st outer c; discoverLams st outer b
    | EAssign (_, x) -> discoverLams st outer x
    | EIfaceCall (_, _, r, args) -> discoverLams st outer r; for a in args do discoverLams st outer a
    | ECast (_, x, _) | ETypeTest (_, x) -> discoverLams st outer x
    | ETry (b, cs) ->
        discoverLams st outer b
        for _, g, x in cs do
            (match g with Some gg -> discoverLams st outer gg | None -> ())
            discoverLams st outer x
    | _ -> ()

/// a known top-level function used as a VALUE: declare its curried wrapper
/// chain once; the closure built at the use site enters at .w0
let private requestWrapper (st : St) (f : Fn) (fname : string) (arity : int) : unit =
    if not (dictTryFind st.Wrappers fname).IsSome then
        dictSet st.Wrappers fname arity
        vecAdd st.WrapperOrder fname
        for k in 0 .. arity - 1 do declFn f.M (fname + ".w" + string k) "$u1"

/// cast to (ref null eq) — ref.eq's operand type
let private castEq (f : Fn) : unit =
    gci f "ref.cast_null"
    emitS32 f.B (heapByte "eq" - 0x80)

/// the STATIC kind of an expression, where one is knowable without type
/// state: enough to pick the rail a kindless conversion reads from. Uniform
/// storage makes "u" safe everywhere else — the value carries its box.
let rec private kindOfLite (e : Expr) : string =
    match e with
    | ELit (LFloat t) ->
        if t.EndsWith "h" || t.EndsWith "H" then "u"
        elif t.EndsWith "f" || t.EndsWith "F" then "s"
        else "f"
    | ELit (LInt t) -> if t.EndsWith "L" then "l" else "i"
    | EPrim (op, _) when
        op.Length > 1 && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%" ] ->
        let k = op.Substring (op.Length - 1)
        if k = "f" || k = "s" || k = "l" then k else "u"
    | EPrim (("-" | "*" | "/" | "%" | "&&&" | "|||" | "^^^" | "<<<" | ">>>" | "u~~~"), _) -> "i"
    | EPrim ("u-f", _) -> "f"
    | EPrim ("u-s", _) -> "s"
    | EPrim ("u-l", _) -> "l"
    | ELet (_, _, _, _, body) -> kindOfLite body
    | ESeq xs -> (match List.tryLast xs with Some x -> kindOfLite x | None -> "u")
    | EIf (_, t, e2) ->
        let a, b = kindOfLite t, kindOfLite e2
        if a = b then a else "u"
    | EApp (EUnknown n, [ _ ]) when n.Contains "#" ->
        (match n.Substring (0, n.IndexOf "#") with
         | "float" -> "f" | "float32" -> "s" | "int64" -> "l" | _ -> "u")
    | EApp (EUnknown "int64", [ _ ]) -> "l"
    | EApp (EUnknown "float", [ _ ]) -> "f"
    | EApp (EUnknown "float32", [ _ ]) -> "s"
    | _ -> "u"

/// collect the run of `let rec ... = fun` bindings heading a let spine.
/// Grouping bindings that are NOT mutually recursive is harmless: their
/// markers are simply never captured, so patching finds nothing to do.
let rec private recGroupOf (e : Expr) : (VarId * Expr) list * Expr =
    match e with
    | ELet (true, v, _, (ELam (_, _) as lam), rest) ->
        let ms, body = recGroupOf rest
        (v, lam) :: ms, body
    | _ -> [], e

let rec private emitNode (st : St) (f : Fn) (lv : Dict<string * int, string>) (e : Expr) : unit =
    match e with
    | ELit (LInt s) when not (s.EndsWith "L") ->
        // an unsigned literal keeps its bit pattern: 4000000000u is the i32
        // whose unsigned reading is that value
        let isHex = s.StartsWith "0x" || s.StartsWith "0X"
        let isUnsigned = s.EndsWith "u" || s.EndsWith "U"
        let v =
            if isHex then parseUInt32In 16 (s.Substring(2).TrimEnd ([| 'u'; 'U' |]))
            else
                let digits = s |> String.filter (fun c -> isDigit c || c = '-')
                if digits = "" then 0
                elif isUnsigned then parseUInt32 digits
                else int digits
        ic f v
        callf f "$ofi"
    | ELit (LInt s) ->
        let isHex = s.StartsWith "0x" || s.StartsWith "0X"
        let v =
            if isHex then parseInt64In 16 (s.Substring(2).TrimEnd ([| 'L' |]))
            else
                let digits = s |> String.filter (fun c -> isDigit c || c = '-')
                if digits = "" then 0L else int64 digits
        lc f v
        callf f "$ofl"
    | ELit (LFloat s) ->
        // keep everything a float constant may contain, drop only the F++
        // width suffix; the writer speaks BITS, so the conversion is here
        let num = s |> String.filter (fun c -> isDigit c || c = '.' || c = '-' || c = '+' || c = 'e' || c = 'E')
        if s.EndsWith "h" || s.EndsWith "H" then
            // a half literal is rounded ONCE, here, into its i31 bit pattern
            ic f (halfBits (parseFloat num))
            refI31 f
        elif s.EndsWith "f" || s.EndsWith "F" then
            sc f (singleBits (float32 (parseFloat num)))
            gcT f "struct.new" "$boxs"
        else
            fc f (doubleBits (parseFloat num))
            gcT f "struct.new" "$boxf"
    | ELit (LChar raw) ->
        let bytes = unescape raw
        ic f (if bytes.Length > 0 then int bytes.[0] else 0)
        refI31 f
    | ELit (LBool b) ->
        ic f (if b then 1 else 0)
        refI31 f
    | ELit LUnit ->
        ic f 0
        refI31 f
    | ELit LNull -> refNull f "any"
    | ELit (LString raw) ->
        let bytes = unescape raw
        let dn, len = internStr st bytes
        ic f 0
        ic f len
        arrNewData f "$str" dn
    | ESeq xs ->
        (match List.rev xs with
         | [] ->
             ic f 0
             refI31 f
         | last :: initRev ->
             for x in List.rev initRev do
                 emitNode st f lv x
                 ins f "drop"
             emitNode st f lv last)
    | EVarI (v, sch, _) -> emitNode st f lv (EVar (v, sch))
    | EVar (v, _) ->
        let vk = (v.Path, v.Offset)
        (match dictTryFind lv vk with
         | Some l when l.StartsWith "@env:" ->
             lg f "$env"
             gcT f "ref.cast" "$arr"
             ic f (int (l.Substring 5))
             gcT f "array.get" "$arr"
             // the env slot holds the CELL, shared with the frame that owns
             // it — that sharing is the whole point; reading dereferences
             if (dictTryFind st.CellVars vk).IsSome then cellGet f
         | Some l ->
             lg f l
             if (dictTryFind st.CellVars vk).IsSome then cellGet f
         | None ->
         match dictTryFind st.GlobalOf vk with
         | Some g -> gg f g
         | None ->
         match dictTryFind st.FnOf vk, dictTryFind st.ArityOf vk with
         | Some fn, Some ar ->
             // function as a value: curried wrapper closure chain
             requestWrapper st f fn ar
             rf f (fn + ".w0")
             refNull f "any"
             gcT f "struct.new" "$clo"
         | _ ->
             err st ("binary: unbound variable " + v.Name)
             refNull f "any")
    | ELet (_, _, _, _, _) ->
        // the let spine, iteratively, exactly like the text emitter
        let mutable cur = e
        let mutable walking = true
        while walking do
            match cur with
            | ELet (true, _, _, ELam _, _) ->
                // recursive local functions: every member captures the
                // others, so no closure can be built until every name has a
                // slot. Bind each name to a fresh MARKER (distinct identity),
                // build every closure over the markers, install, then patch
                // each closure's env slots marker → closure. A single rec
                // binding is just a one-element group.
                let members, groupBody = recGroupOf cur
                let slots =
                    members
                    |> List.map (fun (v, lam) ->
                        v, lam,
                        freshLocal f "$bl" "anyref",
                        freshLocal f "$bmk" "anyref",
                        freshLocal f "$bcl" "anyref")
                for v, _, l, _, _ in slots do dictSet lv (v.Path, v.Offset) l
                for _, _, l, mk, _ in slots do
                    ic f -999
                    gcT f "struct.new" "$du0"
                    ls f mk
                    lg f mk
                    ls f l
                for _, lam, _, _, cl in slots do
                    emitNode st f lv lam
                    ls f cl
                for _, _, l, _, cl in slots do
                    lg f cl
                    ls f l
                for _, _, _, _, cl in slots do
                    for _, _, _, mk2, cl2 in slots do
                        lg f cl
                        lg f mk2
                        lg f cl2
                        callf f "$patchmark"
                cur <- groupBody
            | ELet (_, v, _, rhs, body) ->
                emitNode st f lv rhs
                // a captured mutable: the frame holds the CELL, not the value
                if (dictTryFind st.CellVars (v.Path, v.Offset)).IsSome then
                    gcT f "struct.new" "$cell"
                let l = freshLocal f "$bl" "anyref"
                dictSet lv (v.Path, v.Offset) l
                ls f l
                cur <- body
            | _ -> walking <- false
        emitNode st f lv cur
    | EIf (c, t, el) ->
        emitNode st f lv c
        callf f "$toi"
        ifA f
        emitNode st f lv t
        elseB f
        emitNode st f lv el
        endB f
    | EMatch (scrut, cases) ->
        let sl = freshLocal f "$bm" "anyref"
        let res = freshLocal f "$br" "anyref"
        emitNode st f lv scrut
        ls f sl
        blockE f "$mdone"
        let mutable ci = 0
        for pat, guard, body in cases do
            let lbl = "$mc" + string ci
            ci <- ci + 1
            blockE f lbl
            emitPat st f lv lbl sl pat
            (match guard with
             | Some g ->
                 emitNode st f lv g
                 callf f "$toi"
                 ins f "i32.eqz"
                 brIf f lbl
             | None -> ())
            emitNode st f lv body
            ls f res
            br f "$mdone"
            endB f
        ins f "unreachable"
        endB f
        lg f res
    | ECtor (name, _, args) ->
        (match dictTryFind st.CaseArity name with
         | Some 0 -> gg f ("$c_" + name)
         | Some _ when not (List.isEmpty args) ->
             ic f (dictTryFind st.CaseTag name).Value
             (match args with
              | [ one ] -> emitNode st f lv one
              | many ->
                  err st "binary: multi-payload ctor not ported"
                  refNull f "any")
             gcT f "struct.new" "$du1"
         | _ ->
             err st ("binary: ctor shape not ported: " + name)
             refNull f "any")
    | EApp (EUnknown "print", [ a ]) ->
        emitNode st f lv a
        callf f "$printval"
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EApp (EUnknown "$str.Substring", [ s; start ]) ->
        let sl = freshLocal f "$sbs" "i32"
        let sv = freshLocal f "$sbv" "anyref"
        emitNode st f lv s
        ls f sv
        emitNode st f lv start
        callf f "$toi"
        ls f sl
        lg f sv
        gcT f "ref.cast" "$str"
        lg f sl
        lg f sv
        gcT f "ref.cast" "$str"
        gci f "array.len"
        lg f sl
        ins f "i32.sub"
        callf f "$strsub"
    | EApp (EUnknown "$str.Substring#2", [ s; start; len ])
    | EApp (EUnknown "strsub", [ s; start; len ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv start
        callf f "$toi"
        emitNode st f lv len
        callf f "$toi"
        callf f "$strsub"
    | EApp (EUnknown "$str.StartsWith", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        callf f "$strStarts"
        refI31 f
    | EApp (EUnknown "$str.EndsWith", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        callf f "$strEnds"
        refI31 f
    | EApp (EUnknown "$str.Contains", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        ic f 0
        callf f "$strFind"
        ic f 0
        ins f "i32.ge_s"
        refI31 f
    | EApp (EUnknown "$str.IndexOf", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        ic f 0
        callf f "$strFind"
        callf f "$ofi"
    | EApp (EUnknown "$str.IndexOf#2", [ s; c ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv c
        callf f "$toi"
        callf f "$strFindChar"
        callf f "$ofi"
    | EApp (EUnknown "$str.IndexOf#3", [ s; p; from ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        emitNode st f lv from
        callf f "$toi"
        callf f "$strFind"
        callf f "$ofi"
    | EApp (EUnknown "$str.LastIndexOf", [ s; c ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv c
        callf f "$toi"
        callf f "$strLastFindChar"
        callf f "$ofi"
    | EApp (EUnknown "$str.Split", [ s; c ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv c
        callf f "$toi"
        callf f "$strSplitChar"
    | EApp (EUnknown "$str.Replace", [ s; a; b ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv b
        gcT f "ref.cast" "$str"
        callf f "$strReplace"
    | EApp (EUnknown "$str.Trim", [ s ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        callf f "$strTrim"
    | EApp (EUnknown "$str.TrimEnd", [ s; cs ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv cs
        callf f "$strTrimEndChars"
    | EApp (EUnknown "compare", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$cmpv"
        callf f "$ofi"
    | EApp (EUnknown "hash", [ a ]) ->
        emitNode st f lv a
        callf f "$hashv"
        callf f "$ofi"
    | EApp (EUnknown "refEq", [ a; b ]) ->
        emitNode st f lv a
        castEq f
        emitNode st f lv b
        castEq f
        ins f "ref.eq"
        refI31 f
    | EUnknown "$class:Ordered:compare:$ref" ->
        // `compare` at a UNIFORM reference: the runtime compares structurally
        requestWrapper st f "$cmpvBoxed" 2
        rf f "$cmpvBoxed.w0"
        refNull f "any"
        gcT f "struct.new" "$clo"
    | EApp (EUnknown n, [ a ]) when
        n.Contains "#" && not (n.EndsWith "#h")
        && not (n.StartsWith "float16#") && not (n.StartsWith "pad") ->
        // conversions whose source kind inference resolved: target#srckind
        let target = n.Substring (0, n.IndexOf "#")
        let src = n.Substring (n.IndexOf "#" + 1)
        let emitA () = emitNode st f lv a
        let strA () = emitA (); gcT f "ref.cast" "$str"
        let mask8 () = ic f 255; ins f "i32.and"
        let sext8 () = ic f 24; ins f "i32.shl"; ic f 24; ins f "i32.shr_s"
        (match target, src with
         | "string", "t" -> emitA ()
         | "int", "t" | "uint32", "t" -> strA (); callf f "$atoi"; callf f "$ofi"
         | "int64", "t" -> strA (); callf f "$atol"; callf f "$ofl"
         | "byte", "t" -> strA (); callf f "$atoi"; mask8 (); callf f "$ofi"
         | "sbyte", "t" -> strA (); callf f "$atoi"; sext8 (); callf f "$ofi"
         | "float", "t" -> strA (); callf f "$atof"; callf f "$off"
         | "float32", "t" -> strA (); callf f "$atof"; ins f "f32.demote_f64"; callf f "$oss"
         | "char", "t" ->
             // Char.Parse: the single (first) character of the string
             strA (); ic f 0; gcT f "array.get_u" "$str"; callf f "$ofi"
         | "string", "f" -> emitA (); callf f "$tof"; callf f "$ftoa"
         | "string", "s" -> emitA (); callf f "$tos"; ins f "f64.promote_f32"; callf f "$ftoa"
         | "string", "l" -> emitA (); callf f "$tol"; callf f "$ltoa"
         | "string", "w" -> emitA (); callf f "$toi"; ins f "i64.extend_i32_u"; callf f "$ultoa"
         | "string", "b" ->
             // Boolean.ToString: "True"/"False", capital first
             emitA (); callf f "$toi"; ins f "i32.eqz"
             ifA f
             for c in [ 70; 97; 108; 115; 101 ] do ic f c
             arrNewFixed f "$str" 5
             elseB f
             for c in [ 84; 114; 117; 101 ] do ic f c
             arrNewFixed f "$str" 4
             endB f
         | "byte", "f" -> emitA (); callf f "$tof"; ins f "i32.trunc_f64_s"; mask8 (); callf f "$ofi"
         | "byte", "s" -> emitA (); callf f "$tos"; ins f "i32.trunc_f32_s"; mask8 (); callf f "$ofi"
         | "byte", "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; mask8 (); callf f "$ofi"
         | "byte", _ -> emitA (); callf f "$toi"; mask8 (); callf f "$ofi"
         | "sbyte", "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; sext8 (); callf f "$ofi"
         | "sbyte", _ -> emitA (); callf f "$toi"; sext8 (); callf f "$ofi"
         | "string", "c" -> emitA (); callf f "$toi"; ic f 1; gcT f "array.new" "$str"
         | "string", _ -> emitA (); callf f "$toi"; callf f "$itoa"
         | "float", "f" -> emitA ()
         | "float", "s" -> emitA (); callf f "$tos"; ins f "f64.promote_f32"; callf f "$off"
         | "float", "l" -> emitA (); callf f "$tol"; ins f "f64.convert_i64_s"; callf f "$off"
         | "float", _ -> emitA (); callf f "$toi"; ins f "f64.convert_i32_s"; callf f "$off"
         | "float32", "s" -> emitA ()
         | "float32", "f" -> emitA (); callf f "$tof"; ins f "f32.demote_f64"; callf f "$oss"
         | "float32", "l" -> emitA (); callf f "$tol"; ins f "f32.convert_i64_s"; callf f "$oss"
         | "float32", _ -> emitA (); callf f "$toi"; ins f "f32.convert_i32_s"; callf f "$oss"
         | "int64", "l" -> emitA ()
         | "int64", "f" -> emitA (); callf f "$tof"; ins f "i64.trunc_f64_s"; callf f "$ofl"
         | "int64", "s" -> emitA (); callf f "$tos"; ins f "i64.trunc_f32_s"; callf f "$ofl"
         | "int64", _ -> emitA (); callf f "$toi"; ins f "i64.extend_i32_s"; callf f "$ofl"
         | _, "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; callf f "$ofi"
         | _, "f" -> emitA (); callf f "$tof"; ins f "i32.trunc_f64_s"; callf f "$ofi"
         | _, "s" -> emitA (); callf f "$tos"; ins f "i32.trunc_f32_s"; callf f "$ofi"
         | _, "t" ->
             err st ("binary: cannot convert a string to " + target)
             emitA ()
         | _, _ -> emitA ())
    | EApp (EUnknown "int64", [ a ]) ->
        (match kindOfLite a with
         | "l" -> emitNode st f lv a
         | "f" -> emitNode st f lv a; callf f "$tof"; ins f "i64.trunc_f64_s"; callf f "$ofl"
         | "s" -> emitNode st f lv a; callf f "$tos"; ins f "i64.trunc_f32_s"; callf f "$ofl"
         | _ -> emitNode st f lv a; callf f "$toi"; ins f "i64.extend_i32_s"; callf f "$ofl")
    | EApp (EUnknown ("uint32" | "int"), [ a ]) ->
        (match kindOfLite a with
         | "f" -> emitNode st f lv a; callf f "$tof"; ins f "i32.trunc_f64_s"; callf f "$ofi"
         | "s" -> emitNode st f lv a; callf f "$tos"; ins f "i32.trunc_f32_s"; callf f "$ofi"
         | "l" -> emitNode st f lv a; callf f "$tol"; ins f "i32.wrap_i64"; callf f "$ofi"
         | _ -> emitNode st f lv a)
    | EApp (EUnknown "string", [ a ]) ->
        (match kindOfLite a with
         | "f" -> emitNode st f lv a; callf f "$tof"; callf f "$ftoa"
         | "s" -> emitNode st f lv a; callf f "$tos"; ins f "f64.promote_f32"; callf f "$ftoa"
         | "l" -> emitNode st f lv a; callf f "$tol"; callf f "$ltoa"
         | _ -> emitNode st f lv a; callf f "$toi"; callf f "$itoa")
    | EApp (EUnknown "printc", [ a ]) ->
        // a char prints as the character, not its code
        emitNode st f lv a
        callf f "$toi"
        callf f "$putc"
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EApp (EUnknown "prints", [ a ]) ->
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        callf f "$prints"
        ic f 0
        refI31 f
    | EPrim ("+", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$addv"
    | EPrim ("=", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$equal"
    | EPrim (op, [ a; b ]) when List.contains op [ "-"; "*"; "/" ] ->
        let insn = match op with "-" -> "i32.sub" | "*" -> "i32.mul" | _ -> "i32.div_s"
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f insn
        callf f "$ofi"
    | EPrim (op, [ a; b ]) when List.contains op [ "<"; ">"; "<="; ">=" ] ->
        let insn = match op with "<" -> "i32.lt_s" | ">" -> "i32.gt_s" | "<=" -> "i32.le_s" | _ -> "i32.ge_s"
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f insn
        refI31 f
    | EPrim ("<>", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$equal"
        gcAbs f "ref.cast" "i31"
        i31get f
        ins f "i32.eqz"
        refI31 f
    | EPrim ("::", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        gcT f "struct.new" "$cons"
    | EPrim ("&&", [ a; b ]) -> emitNode st f lv (EIf (a, b, ELit (LBool false)))
    | EPrim ("||", [ a; b ]) -> emitNode st f lv (EIf (a, ELit (LBool true), b))
    | EPrim ("u-", [ a ]) ->
        ic f 0
        emitNode st f lv a
        callf f "$toi"
        ins f "i32.sub"
        callf f "$ofi"
    | EPrim ("unot", [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        ins f "i32.eqz"
        refI31 f
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "t"
        && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "<"; ">"; "<="; ">=" ] ->
        // `+` concatenates; ordering is byte-wise ordinal, like F#'s `<`
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv b
        gcT f "ref.cast" "$str"
        (match op.Substring (0, op.Length - 1) with
         | "+" -> callf f "$strcat"
         | baseOp ->
             callf f "$strcmp"
             ic f 0
             ins f (match baseOp with
                    | "<" -> "i32.lt_s" | ">" -> "i32.gt_s"
                    | "<=" -> "i32.le_s" | _ -> "i32.ge_s")
             refI31 f)
    | EPrim (op, [ a; b ]) when
        op.Length > 1
        && (op.EndsWith "f" || op.EndsWith "s" || op.EndsWith "l" || op.EndsWith "i")
        && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">=" ] ->
        let baseOp = op.Substring (0, op.Length - 1)
        let kind = op.Substring (op.Length - 1)
        let un, box_, ty, flt =
            match kind with
            | "f" -> "$tof", "$off", "f64", true
            | "s" -> "$tos", "$oss", "f32", true
            | "l" -> "$tol", "$ofl", "i64", false
            | _ -> "$toi", "$ofi", "i32", false
        if baseOp = "%" && flt then
            err st "binary: float remainder unsupported"
            refNull f "any"
        else
            emitNode st f lv a
            callf f un
            emitNode st f lv b
            callf f un
            let cmp = List.contains baseOp [ "<"; ">"; "<="; ">=" ]
            let insn =
                match baseOp with
                | "+" -> ty + ".add" | "-" -> ty + ".sub" | "*" -> ty + ".mul"
                | "/" -> if flt then ty + ".div" else ty + ".div_s"
                | "%" -> ty + ".rem_s"
                | "<" -> if flt then ty + ".lt" else ty + ".lt_s"
                | ">" -> if flt then ty + ".gt" else ty + ".gt_s"
                | "<=" -> if flt then ty + ".le" else ty + ".le_s"
                | _ -> if flt then ty + ".ge" else ty + ".ge_s"
            ins f insn
            if cmp then refI31 f else callf f box_
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "w"
        && List.contains (op.Substring (0, op.Length - 1))
            [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="; "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        // the UNSIGNED int family: uint32 semantics on the i32 rail
        let baseOp = op.Substring (0, op.Length - 1)
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        let cmp = List.contains baseOp [ "<"; ">"; "<="; ">=" ]
        let insn =
            match baseOp with
            | "+" -> "i32.add" | "-" -> "i32.sub" | "*" -> "i32.mul"
            | "/" -> "i32.div_u" | "%" -> "i32.rem_u"
            | "<" -> "i32.lt_u" | ">" -> "i32.gt_u" | "<=" -> "i32.le_u" | ">=" -> "i32.ge_u"
            | "&&&" -> "i32.and" | "|||" -> "i32.or" | "^^^" -> "i32.xor"
            | "<<<" -> "i32.shl" | _ -> "i32.shr_u"
        ins f insn
        if cmp then refI31 f else callf f "$ofi"
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "l"
        && List.contains (op.Substring (0, op.Length - 1)) [ "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        let baseOp = op.Substring (0, op.Length - 1)
        emitNode st f lv a
        callf f "$tol"
        emitNode st f lv b
        (match baseOp with
         | "<<<" | ">>>" ->
             // the shift count is an int
             callf f "$toi"
             ins f "i64.extend_i32_s"
         | _ -> callf f "$tol")
        ins f (match baseOp with
               | "&&&" -> "i64.and" | "|||" -> "i64.or" | "^^^" -> "i64.xor"
               | "<<<" -> "i64.shl" | _ -> "i64.shr_s")
        callf f "$ofl"
    | EPrim (op, [ a; b ]) when List.contains op [ "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f (match op with
               | "&&&" -> "i32.and" | "|||" -> "i32.or" | "^^^" -> "i32.xor"
               | "<<<" -> "i32.shl" | _ -> "i32.shr_u")
        callf f "$ofi"
    | EPrim ("u-f", [ a ]) ->
        emitNode st f lv a
        callf f "$tof"
        ins f "f64.neg"
        callf f "$off"
    | EPrim ("u-s", [ a ]) ->
        emitNode st f lv a
        callf f "$tos"
        ins f "f32.neg"
        callf f "$oss"
    | EPrim ("u-l", [ a ]) ->
        lc f 0L
        emitNode st f lv a
        callf f "$tol"
        ins f "i64.sub"
        callf f "$ofl"
    | EPrim ("u~~~", [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        ic f -1
        ins f "i32.xor"
        callf f "$ofi"
    | EPrim (("sqrtf" | "sqrts" | "absf" | "abss" | "truncatef" | "truncates") as op, [ a ]) ->
        // the INSTRUCTION rather than `if x < 0 then -x`: that form gets
        // -0.0 and NaN wrong
        let f32 = op.EndsWith "s"
        let ty = if f32 then "f32" else "f64"
        emitNode st f lv a
        callf f (if f32 then "$tos" else "$tof")
        ins f (if op.StartsWith "sqrt" then ty + ".sqrt"
               elif op.StartsWith "abs" then ty + ".abs"
               else ty + ".trunc")
        callf f (if f32 then "$oss" else "$off")
    | EPrim ("abs", [ a ]) ->
        let l = freshLocal f "$bn" "i32"
        emitNode st f lv a
        callf f "$toi"
        ls f l
        ic f 0
        lg f l
        ins f "i32.sub"
        lg f l
        lg f l
        ic f 0
        ins f "i32.lt_s"
        ins f "select"
        callf f "$ofi"
    | EPrim ("absl", [ a ]) ->
        let l = freshLocal f "$bnl" "i64"
        emitNode st f lv a
        callf f "$tol"
        ls f l
        lc f 0L
        lg f l
        ins f "i64.sub"
        lg f l
        lg f l
        lc f 0L
        ins f "i64.lt_s"
        ins f "select"
        callf f "$ofl"
    | ERecord (tyName, fields) ->
        let rn =
            if tyName <> "" && tyName <> "?" && (dictTryFind st.FieldsOf tyName).IsSome then tyName
            else
                match fields |> List.tryPick (fun (fn, _) -> dictTryFind st.FieldOwner fn) with
                | Some r -> r
                | None -> ""
        (match dictTryFind st.FieldsOf rn with
         | Some order ->
             for fname in order do
                 (match fields |> List.tryFind (fun (fn, _) -> fn = fname) with
                  | Some (_, v) -> emitNode st f lv v
                  | None ->
                      err st ("binary: missing field " + fname + " in " + rn)
                      refNull f "any")
             gcT f "struct.new" ("$r_" + rn)
         | None ->
             err st ("binary: record with unknown type " + tyName)
             refNull f "any")
    | EField (r, "Length", _) when not (dictTryFind st.FieldOwner "Length").IsSome ->
        // no record claims a Length field: this is the built-in one, across
        // strings and every array representation
        emitNode st f lv r
        callf f "$lenv"
    | EField (r, fname, owner) ->
        let rn =
            if owner <> "" && (dictTryFind st.FieldIdx (owner, fname)).IsSome then owner
            else (match dictTryFind st.FieldOwner fname with Some x -> x | None -> "")
        (match dictTryFind st.FieldIdx (rn, fname) with
         | Some idx ->
             emitNode st f lv r
             gcT f "ref.cast" ("$r_" + rn)
             gcTF f "struct.get" ("$r_" + rn) idx
         | None ->
             err st ("binary: unknown field " + fname)
             refNull f "any")
    | EFieldSet (r, fname, owner, v) ->
        let rn =
            if owner <> "" && (dictTryFind st.FieldIdx (owner, fname)).IsSome then owner
            else (match dictTryFind st.FieldOwner fname with Some x -> x | None -> "")
        (match dictTryFind st.FieldIdx (rn, fname) with
         | Some idx ->
             emitNode st f lv r
             gcT f "ref.cast" ("$r_" + rn)
             emitNode st f lv v
             gcTF f "struct.set" ("$r_" + rn) idx
             ic f 0
             refI31 f
         | None ->
             err st ("binary: unknown field " + fname)
             refNull f "any")
    | ETuple xs ->
        for x in xs do emitNode st f lv x
        gcT f "struct.new" ("$tup" + string (List.length xs))
    | EListLit xs ->
        for x in xs do emitNode st f lv x
        refNull f "any"
        for _ in xs do gcT f "struct.new" "$cons"
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when
          (dictTryFind st.ArityOf (v.Path, v.Offset)) = Some (List.length args) ->
        for a in args do emitNode st f lv a
        callf f (dictTryFind st.FnOf (v.Path, v.Offset)).Value
    | EAssign (v, rhs) when (dictTryFind st.CellVars (v.Path, v.Offset)).IsSome ->
        // the cell may live in this frame or in the closure's env; both reads
        // yield the SAME cell, and the write goes through it
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l when l.StartsWith "@env:" ->
             lg f "$env"
             gcT f "ref.cast" "$arr"
             ic f (int (l.Substring 5))
             gcT f "array.get" "$arr"
         | Some l -> lg f l
         | None ->
             err st ("binary: cell not in scope: " + v.Name)
             refNull f "any")
        gcT f "ref.cast" "$cell"
        emitNode st f lv rhs
        gcTF f "struct.set" "$cell" 0
        ic f 0
        refI31 f
    | EAssign (v, rhs) ->
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l when not (l.StartsWith "@env:") ->
             emitNode st f lv rhs
             ls f l
         | Some _ ->
             err st "binary: captured mutable (cells) not ported"
         | None ->
             match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g ->
                 emitNode st f lv rhs
                 gs f g
             | None -> err st ("binary: assignment to unknown " + v.Name))
        ic f 0
        refI31 f
    | EWhile (c, b) ->
        blockE f "$wbrk"
        loopE f "$wgo"
        emitNode st f lv c
        callf f "$toi"
        ins f "i32.eqz"
        brIf f "$wbrk"
        emitNode st f lv b
        ins f "drop"
        br f "$wgo"
        endB f
        endB f
        ic f 0
        refI31 f
    | EApp (EUnknown "failwith", [ a ]) ->
        emitNode st f lv a
        throwExn f
        ic f 0
        refI31 f
    | EApp (EUnknown "ignore", [ a ]) ->
        emitNode st f lv a
        ins f "drop"
        ic f 0
        refI31 f
    | EApp (EUnknown "isNull", [ a ]) ->
        emitNode st f lv a
        ins f "ref.is_null"
        refI31 f
    | EApp (EUnknown "$listLength", [ a ]) ->
        // inline: walk the cons chain counting (the runtime's $listLength
        // moves here once more programs demand it)
        let cl = freshLocal f "$ll" "anyref"
        let cn = freshLocal f "$lc" "anyref"
        emitNode st f lv a
        ls f cl
        ic f 0
        refI31 f
        ls f cn
        blockE f "$ldone"
        loopE f "$lgo"
        lg f cl
        ins f "ref.is_null"
        brIf f "$ldone"
        lg f cn
        callf f "$toi"
        ic f 1
        ins f "i32.add"
        callf f "$ofi"
        ls f cn
        lg f cl
        gcT f "ref.cast" "$cons"
        gcTF f "struct.get" "$cons" 1
        ls f cl
        br f "$lgo"
        endB f
        endB f
        lg f cn
    // ---- arrays: UNIFORM $arr (anyref elements) ---------------------------
    // The element-kind name is carried but ignored: the binary path stays
    // uniform until the oracle is green, and packed/POD parity is its own
    // pass afterwards. Every element is therefore a boxed anyref, exactly
    // like a closure env slot.
    | EArray (_, xs) ->
        for x in xs do emitNode st f lv x
        arrNewFixed f "$arr" (List.length xs)
    | EArrayCreate (nm, n, EUnknown "$zero") ->
        // Array.zeroCreate. `array.new_default` would give NULL in every
        // slot, which is right for a reference element and wrong for a
        // numeric one — uniform boxing means a zero int is `ref.i31 0`, not
        // null. So the zero is spelled per element kind and filled by
        // array.new.
        (match nm with
         | "float" | "float32" | "double" | "single" ->
             fc f 0L
             gcT f "struct.new" "$boxf"
         | "string" | "obj" | "" -> refNull f "any"
         | _ when strLen nm > 0 && charAt nm 0 = '\'' -> refNull f "any"
         | _ ->
             ic f 0
             refI31 f)
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new" "$arr"
    | EArrayCreate (_, n, v) ->
        // array.new takes the INIT VALUE first, then the length
        emitNode st f lv v
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new" "$arr"
    | EIndex ("$str", a, i) ->
        // char access on a STRING receiver (the "$str" sentinel)
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv i
        callf f "$toi"
        gcT f "array.get_u" "$str"
        refI31 f
    | EIndex (_, a, i) ->
        emitNode st f lv a
        gcT f "ref.cast" "$arr"
        emitNode st f lv i
        callf f "$toi"
        gcT f "array.get" "$arr"
    | EIndexSet (_, a, i, v) ->
        emitNode st f lv a
        gcT f "ref.cast" "$arr"
        emitNode st f lv i
        callf f "$toi"
        emitNode st f lv v
        gcT f "array.set" "$arr"
        ic f 0
        refI31 f
    | EArrayLen (_, a) ->
        // representation-dispatched: the receiver may be $arr OR $str (byte
        // strings and arrays share the length surface)
        emitNode st f lv a
        callf f "$lenv"
    | ELam (_, _) ->
        (match refMapTryFind st.LamName e with
         | Some name ->
             // (struct.new $clo (ref.func $lam) env) — env slots hold the
             // CURRENT values of the captured locals, read here at build
             let free = (dictTryFind st.LamFree name).Value
             rf f name
             if List.isEmpty free then refNull f "any"
             else
                 for k in free do
                     (match dictTryFind lv k with
                      | Some l when l.StartsWith "@env:" ->
                          lg f "$env"
                          gcT f "ref.cast" "$arr"
                          ic f (int (l.Substring 5))
                          gcT f "array.get" "$arr"
                      | Some l -> lg f l
                      | None ->
                          err st "binary: capture not in scope at build site"
                          refNull f "any")
                 arrNewFixed f "$arr" (List.length free)
             gcT f "struct.new" "$clo"
         | None ->
             err st "binary: undiscovered lambda"
             refNull f "any")
    | EApp (g, args) ->
        // generic application: the applyc chain
        emitNode st f lv g
        for a in args do
            emitNode st f lv a
            callf f "$applyc"
    | other ->
        let tag =
            match other with
            | ELam _ -> "ELam" | EApp (EUnknown n, _) -> "EApp $" + n
            | EApp _ -> "EApp" | EPrim (op, _) -> "EPrim " + op
            | EField _ -> "EField" | EFieldSet _ -> "EFieldSet"
            | ERecord _ -> "ERecord" | ERecordExt _ -> "ERecordExt"
            | EIndex _ -> "EIndex" | EIndexSet _ -> "EIndexSet"
            | EArray _ -> "EArray" | EArrayLen _ -> "EArrayLen"
            | EArrayCreate _ -> "EArrayCreate" | EWhile _ -> "EWhile"
            | EAssign _ -> "EAssign" | ETry _ -> "ETry"
            | EIfaceCall _ -> "EIfaceCall" | ECast _ -> "ECast"
            | ETypeTest _ -> "ETypeTest" | ETuple _ -> "ETuple"
            | EListLit _ -> "EListLit" | EUnknown n -> "EUnknown " + n
            | _ -> "?"
        err st ("binary: not ported: " + tag)
        refNull f "any"

and private emitPat (st : St) (f : Fn) (lv : Dict<string * int, string>)
                    (failLbl : string) (slot : string) (p : Pat) : unit =
    match p with
    | PWild -> ()
    | PVar (v, _) ->
        let l = freshLocal f "$bp" "anyref"
        dictSet lv (v.Path, v.Offset) l
        lg f slot
        ls f l
    | PLit (LInt sIn) ->
        let digits = sIn |> String.filter (fun c -> isDigit c || c = '-')
        lg f slot
        callf f "$toi"
        ic f (if digits = "" then 0 else int digits)
        ins f "i32.ne"
        brIf f failLbl
    | PLit (LBool b) ->
        lg f slot
        callf f "$toi"
        ic f (if b then 1 else 0)
        ins f "i32.ne"
        brIf f failLbl
    | PCtor (name, _, args) ->
        (match dictTryFind st.CaseArity name, dictTryFind st.CaseTag name with
         | Some 0, Some t ->
             lg f slot
             gcT f "ref.test" "$du0"
             ins f "i32.eqz"
             brIf f failLbl
             lg f slot
             gcT f "ref.cast" "$du0"
             gcTF f "struct.get" "$du0" 0
             ic f t
             ins f "i32.ne"
             brIf f failLbl
         | Some _, Some t ->
             lg f slot
             gcT f "ref.test" "$du1"
             ins f "i32.eqz"
             brIf f failLbl
             lg f slot
             gcT f "ref.cast" "$du1"
             gcTF f "struct.get" "$du1" 0
             ic f t
             ins f "i32.ne"
             brIf f failLbl
             (match args with
              | [] -> ()
              | [ sub ] ->
                  let pl = freshLocal f "$bq" "anyref"
                  lg f slot
                  gcT f "ref.cast" "$du1"
                  gcTF f "struct.get" "$du1" 1
                  ls f pl
                  emitPat st f lv failLbl pl sub
              | _ -> err st "binary: multi-arg ctor pattern not ported")
         | _ -> err st ("binary: unknown ctor in pattern " + name))
    | PTuple ps ->
        let t = "$tup" + string (List.length ps)
        let mutable i = 0
        for sub in ps do
            let pl = freshLocal f "$bq" "anyref"
            lg f slot
            gcT f "ref.cast" t
            gcTF f "struct.get" t i
            ls f pl
            emitPat st f lv failLbl pl sub
            i <- i + 1
    | PCons (h, tl) ->
        lg f slot
        gcT f "ref.test" "$cons"
        ins f "i32.eqz"
        brIf f failLbl
        let hl = freshLocal f "$bq" "anyref"
        lg f slot
        gcT f "ref.cast" "$cons"
        gcTF f "struct.get" "$cons" 0
        ls f hl
        emitPat st f lv failLbl hl h
        let tll = freshLocal f "$bq" "anyref"
        lg f slot
        gcT f "ref.cast" "$cons"
        gcTF f "struct.get" "$cons" 1
        ls f tll
        emitPat st f lv failLbl tll tl
    | PListLit [] ->
        lg f slot
        ins f "ref.is_null"
        ins f "i32.eqz"
        brIf f failLbl
    | _ -> err st "binary: pattern case not ported yet"

/// Emit a body whose locals are only discovered DURING emission: run the
/// emission once into a scratch buffer (locals allocate in a deterministic
/// order), then declare exactly those locals and splice the bytes. Local
/// indices agree because both passes allocate in the same order.
and private emitWithLocals (st : St) (f : Fn) (lv : Dict<string * int, string>)
                           (owner : string) (body : Expr) (needsResult : bool) : bool =
    let scratchB = bytesNew ()
    let scratch =
        { M = f.M; B = scratchB; LocalIdx = dictNew (); LocalTys = vecNew ()
          NParams = f.NParams; Labels = labelsNew (); PatchAt = 0; Replay = -1 }
    for k, v in dictPairs f.LocalIdx do
        if (dictTryFind scratch.LocalIdx k).IsNone then dictSet scratch.LocalIdx k v
    let lv0 = dictNew<string * int, string> ()
    for k, v in dictPairs lv do dictSet lv0 k v
    // the DRY RUN uses a throwaway error sink: a body that hits unported
    // cases becomes an UNREACHABLE STUB (bring-up mode: vtable-rooted
    // prelude members survive DCE but are never called by small programs).
    // Reaching a stub at runtime traps loudly rather than misbehaving.
    let probe = { st with Errors = vecNew () }
    emitNode probe scratch lv0 body
    if vecLen probe.Errors > 0 then
        vecAdd st.Warnings ("stubbed " + owner + " (" + vecGet probe.Errors 0 + ")")
        localsDone f
        ins f "unreachable"
        false
    else
        for t in vecToList scratch.LocalTys do
            let l = "$x" + string (vecLen f.LocalTys)
            local f l t
        localsDone f
        f.Replay <- 0
        let lv1 = dictNew<string * int, string> ()
        for k, v in dictPairs lv do dictSet lv1 k v
        emitNode st f lv1 body
        ignore needsResult
        true

/// the whole program: globals + per-decl init functions + _start
let emitBinary (decls : Decl list) : byte[] * string list * string list =
    let m = modNew ()
    let st =
        { M = m; Errors = vecNew (); CaseTag = dictNew (); CaseArity = dictNew ()
          EnumConst = dictNew (); GlobalOf = dictNew (); FnOf = dictNew ()
          ArityOf = dictNew (); Warnings = vecNew ()
          Wrappers = dictNew (); WrapperOrder = vecNew ()
          FieldsOf = dictNew (); FieldIdx = dictNew (); FieldOwner = dictNew (); DataN = 0
          LamName = refMapNew (fun (_ : Expr) -> 7)
          LamFree = dictNew (); LamBody = vecNew (); CellVars = cellScan decls }
    // tags in declaration order, like the text prepass
    let mutable tag = 0
    for d in decls do
        match d with
        | DUnion (_, _, cases) ->
            for cn, ar in cases do
                dictSet st.CaseTag cn tag
                dictSet st.CaseArity cn ar
                tag <- tag + 1
        | _ -> ()
    frame m [ 1; 2; 3 ] [ 2; 3 ]
    // record types: UNIFORM anyref fields (scalarization is a parity task,
    // not a bring-up task); names as declared, stamped clones included
    for d in decls do
        match d with
        | DRecord (rn, _, fs, _) ->
            let names = fs |> List.map fst
            dictSet st.FieldsOf rn names
            names |> List.iteri (fun i fn ->
                dictSet st.FieldIdx (rn, fn) i
                dictSet st.FieldOwner fn rn)
            tyStruct m ("$r_" + rn) (names |> List.map (fun _ -> fld true "anyref"))
        | _ -> ()
    rtTypes2 m
    rtTypes3 m
    rtTypes4 m
    rtTypes5 m
    rtTypes6 m
    rtTypes7 m
    rtTypes8 m
    tyFunc m "$init_t" [] []
    rtDecls m
    rtCoreDecls2 m
    rtDecls3 m
    rtDecls4 m
    rtDecls5 m
    rtDecls6 m
    rtDecls7 m
    rtDecls8 m
    // const globals for arity-0 DU cases
    for cn, _ in dictPairs st.CaseTag do
        if (dictTryFind st.CaseArity cn) = Some 0 then
            dictSet m.GlobalIdx ("$c_" + cn) m.GlobalCount
            m.GlobalCount <- m.GlobalCount + 1
            emitRefType m.GlobalBody false (tyIdx m "$du0")
            emitByte m.GlobalBody 0
            emitByte m.GlobalBody opI32Const
            emitS32 m.GlobalBody (dictTryFind st.CaseTag cn).Value
            emitByte m.GlobalBody opGcPrefix
            emitU32 m.GlobalBody (gcByte "struct.new")
            emitU32 m.GlobalBody (tyIdx m "$du0")
            emitByte m.GlobalBody opEnd
    globalVt m "$duEq" (List.init (max tag 1) (fun _ -> "$eq_du_default"))
    globalVt m "$duHash" (List.init (max tag 1) (fun _ -> "$hash_du_default"))
    // program globals + init function declarations
    let inits = vecNew<string> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) ->
            let fn = mangle v
            dictSet st.FnOf (v.Path, v.Offset) fn
            dictSet st.ArityOf (v.Path, v.Offset) (List.length ps)
            declFn m fn ("$v" + string (List.length ps))
        | DLet (_, v, _, _) ->
            let g = mangle v
            dictSet st.GlobalOf (v.Path, v.Offset) g
            globalAnyref m g
        | _ -> ()
    // lambdas discovered only AFTER globals/functions are registered, so
    // the capture filter (below) can exclude them — a global or a known
    // function resolves directly and is never an env slot
    for d in decls do
        match d with
        | DLet (_, _, _, body) -> discoverLams st (dictNew ()) body
        | _ -> ()
    for name, _, _ in vecToList st.LamBody do
        declFn m name "$u1"
    let mutable initN = 0
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, _) ->
            let fname = "$init" + string initN
            initN <- initN + 1
            vecAdd inits fname
            declFn m fname "$init_t"
        | _ -> ()
    declFn m "$_start" "$init_t"
    exportFn m "_start" "$_start"
    // bodies, in declaration order
    rtCore m
    rtCore2 m
    rtCore3 m [ 2; 3 ]
    rtCore4 m
    rtCore5 m
    rtCore6 m
    rtCore7 m [ 2; 3 ]
    rtCore8 m
    // bodies in DECLARATION order: all functions first, then all inits —
    // interleaving them put code into the wrong slots
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            let names = ps |> List.mapi (fun i _ -> "$a" + string i)
            let f = beginFn m names
            let lv = dictNew<string * int, string> ()
            List.iteri (fun i (pv : VarId, _) -> dictSet lv (pv.Path, pv.Offset) ("$a" + string i)) ps
            // locals must all exist before instructions: pre-scan the body
            // is avoided by DECLARING lazily... which binary cannot do — so
            // Fn allows locals before localsDone only. Pre-pass: count let/
            // match binders by walking? Simpler: emit into a scratch, then
            // splice. The scratch approach: emit body into a temp Bytes via
            // a temp Fn, then copy. Implemented as: body Fn writes into the
            // REAL code stream, and `local` is legal before localsDone —
            // so we must know locals first. We pre-walk the body and create
            // one anyref local per binder, keyed by the SAME naming scheme
            // emitNode/emitPat use (vecLen LocalTys order).
            emitWithLocals st f lv (mangle v) body true |> ignore
            endFn f
        | _ -> ()
    // lambda bodies: param + env; captured keys read from the env array.
    // The capture FILTER at each build site is "is it a local there", so the
    // body maps every free key optimistically; unreached slots never read.
    for name, (pv, _), body in vecToList st.LamBody do
        let f = beginFn m [ "$a"; "$env" ]
        let lv = dictNew<string * int, string> ()
        dictSet lv (pv.Path, pv.Offset) "$a"
        // env reads become locals loaded up front — one array.get per slot
        let free = (dictTryFind st.LamFree name).Value
        let scratchProbe = { st with Errors = vecNew () }
        // slot mapping mirrors the build-site filter only at RUN time; the
        // body binds each env slot to a fresh local before its code
        let envLocals = free |> List.mapi (fun i k -> k, i)
        let fB = f
        // first pass probes; handled inside emitWithLocals — here we bind
        // env slots as pseudo-locals via a prelude in the body: emit reads
        // after localsDone. To keep the two-pass scheme, the prelude is part
        // of a wrapper expression instead: read slots lazily at each use.
        // Simplest correct: lv marks env keys with a sentinel handled in
        // EVar; but two-pass naming needs stability — so bind ALL slots to
        // locals here, before emitWithLocals, via direct emission:
        // (locals must precede instructions, so this uses the scratch pass
        // machinery: slot binds are emitted as part of the body by wrapping)
        ignore envLocals
        ignore scratchProbe
        ignore fB
        // sentinel scheme: "@env:i" in lv, resolved in emitNode's EVar case
        free |> List.iteri (fun i k -> dictSet lv k ("@env:" + string i))
        emitWithLocals st f lv name body true |> ignore
        endFn f
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) ->
            let f = beginFn m []
            let lv = dictNew<string * int, string> ()
            if emitWithLocals st f lv (mangle v) rhs true then
                gs f (dictTryFind st.GlobalOf (v.Path, v.Offset)).Value
            endFn f
        | _ -> ()
    let f = beginFn m []
    localsDone f
    for i in vecToList inits do callf f i
    endFn f
    // curried wrapper bodies: requested lazily during body emission, so their
    // decls sit after $_start in the function section — bodies land here in
    // request order. Each .wk before the last conses its arg onto the env;
    // the last unspools the chain (latest arg first) and calls direct.
    for fname in vecToList st.WrapperOrder do
        let arity = (dictTryFind st.Wrappers fname).Value
        for k in 0 .. arity - 1 do
            let f = beginFn m [ "$a"; "$env" ]
            localsDone f
            if k = arity - 1 then
                for j in 0 .. arity - 1 do
                    if j = k then lg f "$a"
                    else
                        lg f "$env"
                        for _ in 1 .. (k - 1 - j) do
                            gcT f "ref.cast" "$cons"
                            gcTF f "struct.get" "$cons" 1
                        gcT f "ref.cast" "$cons"
                        gcTF f "struct.get" "$cons" 0
                callf f fname
            else
                rf f (fname + ".w" + string (k + 1))
                lg f "$a"
                lg f "$env"
                gcT f "struct.new" "$cons"
                gcT f "struct.new" "$clo"
            endFn f
    assemble m 17 true, vecToList st.Errors, vecToList st.Warnings

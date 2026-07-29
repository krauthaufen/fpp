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
      mutable DataN : int }

let private err (st : St) (msg : string) : unit = vecAdd st.Errors msg

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

let rec private emitNode (st : St) (f : Fn) (lv : Dict<string * int, string>) (e : Expr) : unit =
    match e with
    | ELit (LInt s) when not (s.EndsWith "L") ->
        let digits = s |> String.filter (fun c -> isDigit c || c = '-')
        ic f (if digits = "" then 0 else int digits)
        callf f "$ofi"
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
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l -> lg f l
         | None ->
         match dictTryFind st.GlobalOf (v.Path, v.Offset) with
         | Some g -> gg f g
         | None ->
             err st ("binary: unbound variable " + v.Name)
             refNull f "any")
    | ELet (_, _, _, _, _) ->
        // the let spine, iteratively, exactly like the text emitter
        let mutable cur = e
        let mutable walking = true
        while walking do
            match cur with
            | ELet (_, v, _, rhs, body) ->
                emitNode st f lv rhs
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
let emitBinary (decls : Decl list) : byte[] * string list =
    let m = modNew ()
    let st =
        { M = m; Errors = vecNew (); CaseTag = dictNew (); CaseArity = dictNew ()
          EnumConst = dictNew (); GlobalOf = dictNew (); FnOf = dictNew ()
          ArityOf = dictNew (); Warnings = vecNew (); DataN = 0 }
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
    rtTypes2 m
    rtTypes3 m
    rtTypes4 m
    tyFunc m "$init_t" [] []
    rtDecls m
    rtCoreDecls2 m
    rtDecls3 m
    rtDecls4 m
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
    assemble m 17 true, vecToList st.Errors

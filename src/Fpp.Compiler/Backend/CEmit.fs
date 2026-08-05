module Fpp.Backend.CEmit

// The C backend: the SAME post-Link declarations the wasm-GC backend
// consumes, emitted as one C file against the fpprt runtime (runtime/).
// One emitter, two targets — gcc for native, emcc for wasm-linear — and
// the wasm-GC backend is the ORACLE: every construct this learns is gated
// on printing exactly what that backend prints (tests/tooling/cback).
//
// Value model (PLAN-CBACK.md): V = uintptr_t. Tagged scalar when bit 0 is
// set ((x<<1)|1 — int, bool, char, unit); heap reference when bit 0 is
// clear and the value nonzero; null is 0. Floats and int64 box. The
// collector skips tagged slots, so a generic field holds either honestly.
//
// GC discipline: EVERY local and temp of compiled code lives in a shadow
// frame slot — tagged values cost nothing there (the tracer skips them),
// and no liveness analysis is needed for v0 soundness. The `semi`
// collector exists to punish anything this gets wrong.
//
// Gaps are RUNTIME traps (fpp_not_emitted), never compile errors: like
// the wasm backend's not-ported stubs, a dead prelude corner must not
// block a live program, and a reached gap must never be silent.

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir

// tid classes, mirrored in fpprt-lang.h (fpp_reg_struct)
let private clsRecord = 1
let private clsCase = 2

type CSt =
    { Out : Vec<string>
      Fwd : Vec<string>
      Globals : Vec<string>
      Inits : Vec<string>
      Reg : Vec<string>                      // type/meta registration in main
      Fns : Dict<string * int, int>          // top-level fn -> arity
      GlobalOf : Dict<string * int, string>
      RecTid : Dict<string, int>             // record name -> tid
      RecFields : Dict<string, string list>  // record name -> field order
      CaseTid : Dict<string, int>            // union case name -> tid
      CaseArity : Dict<string, int>
      EnumVal : Dict<string, int>            // enum case name -> value
      FnClo : Dict<string * int, string>     // fn used as value -> global clo
      CloInits : Vec<string>                 // closure singletons: BEFORE all global inits
      VSlot : Dict<string * string, int>     // (bare iface, member) -> slot
      VWrap : Dict<string * int, string>     // member fn -> uniform wrapper
      ClassBase : Dict<string, string>       // class -> base
      ClassImpls : Dict<string, (string * (string * VarId) list) list>
      mutable NVSlots : int
      mutable NextTid : int
      mutable NextLam : int }

let private isIdentChar (c : char) = isLetterOrDigit c || c = '_'
let private sane (n : string) = n |> String.map (fun c -> if isIdentChar c then c else '_')

let private cname (v : VarId) : string =
    "f_" + string (abs (strHash v.Path % 1000)) + "_" + string v.Offset + "_" + sane v.Name
let private gname (v : VarId) : string =
    "g_" + string (abs (strHash v.Path % 1000)) + "_" + string v.Offset + "_" + sane v.Name

let private cstr (s : string) : string =
    let out = vecNew<string> ()
    vecAdd out "\""
    for ch in s do
        if ch = '\\' then vecAdd out "\\\\"
        elif ch = '"' then vecAdd out "\\\""
        elif ch = '\n' then vecAdd out "\\n"
        elif ch = '\t' then vecAdd out "\\t"
        elif ch = '\r' then vecAdd out "\\r"
        elif int ch < 32 || int ch > 126 then
            // close and reopen the literal: a C hex escape is GREEDY
            vecAdd out ("\\x" + (let h = "0123456789abcdef" in
                                 string (charAt h ((int ch >>> 4) &&& 15))
                                 + string (charAt h (int ch &&& 15)))
                        + "\" \"")
        else vecAdd out (string ch)
    vecAdd out "\""
    String.concat "" (vecToList out)

let private freshTid (st : CSt) : int =
    let t = st.NextTid
    st.NextTid <- t + 1
    t

// ---- per-function state ---------------------------------------------------

type CFn =
    { Body : Vec<string>
      mutable NSlots : int
      Locals : Dict<string * int, int>
      Cells : Dict<string * int, bool> }    // locals boxed in cells

let private slot (f : CFn) : int =
    let i = f.NSlots
    f.NSlots <- i + 1
    i

let private stmt (f : CFn) (s : string) : unit = vecAdd f.Body ("  " + s)
let private sref (i : int) : string = "F[" + string i + "]"

// ---- free variables and captured-mutable discovery ------------------------

let rec private walkE (g : Expr -> unit) (e : Expr) : unit =
    g e
    match e with
    | ELam (_, b) -> walkE g b
    | EApp (h, args) -> walkE g h; for a in args do walkE g a
    | ELet (_, _, _, r, b) -> walkE g r; walkE g b
    | EIf (a, b, c) -> walkE g a; walkE g b; walkE g c
    | EMatch (s, cs) ->
        walkE g s
        for _, gd, b in cs do
            (match gd with Some x -> walkE g x | None -> ())
            walkE g b
    | ETry (b, cs) ->
        walkE g b
        for _, gd, x in cs do
            (match gd with Some y -> walkE g y | None -> ())
            walkE g x
    | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) ->
        for x in xs do walkE g x
    | ERecord (_, fs) -> for _, v in fs do walkE g v
    | ERecordExt (_, b, fs) -> walkE g b; (for _, v in fs do walkE g v)
    | EField (r, _, _) -> walkE g r
    | EFieldSet (r, _, _, v) -> walkE g r; walkE g v
    | EWhile (c, b) -> walkE g c; walkE g b
    | EAssign (_, x) -> walkE g x
    | EIndex (_, a, i) -> walkE g a; walkE g i
    | EIndexSet (_, a, i, v) -> walkE g a; walkE g i; walkE g v
    | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) ->
        walkE g a
    | EArrayCreate (_, a, b) -> walkE g a; walkE g b
    | EIfaceCall (_, _, r, args) -> walkE g r; for a in args do walkE g a
    | ECast (_, x, _) | ETypeTest (_, x) -> walkE g x
    | _ -> ()

let rec private patBinders (p : Pat) (acc : Vec<string * int>) : unit =
    match p with
    | PVar (v, _) -> vecAdd acc (v.Path, v.Offset)
    | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps ->
        for q in ps do patBinders q acc
    | PCons (a, b) -> patBinders a acc; patBinders b acc
    | PAs (q, v, _) -> patBinders q acc; vecAdd acc (v.Path, v.Offset)
    | _ -> ()

/// variables a lambda BODY references that are bound OUTSIDE it
let private freeVarsOf (ps : (VarId * Scheme) list) (body : Expr)
                       (isOutside : string * int -> bool) : (string * int) list =
    let bound = dictNew<string * int, bool> ()
    for pv, _ in ps do dictSet bound (pv.Path, pv.Offset) true
    let free = vecNew<string * int> ()
    let seen = dictNew<string * int, bool> ()
    let note (k : string * int) =
        if not (dictTryFind bound k).IsSome && isOutside k
           && not (dictTryFind seen k).IsSome then
            dictSet seen k true
            vecAdd free k
    let rec go (e : Expr) : unit =
        match e with
        | EVar (v, _) | EVarI (v, _, _) -> note (v.Path, v.Offset)
        | EAssign (v, x) ->
            note (v.Path, v.Offset)
            go x
        | ELam (ps2, b) ->
            for pv, _ in ps2 do dictSet bound (pv.Path, pv.Offset) true
            go b
        | ELet (_, v, _, r, b) ->
            go r
            dictSet bound (v.Path, v.Offset) true
            go b
        | EMatch (s, cs) ->
            go s
            for p, gd, b in cs do
                let acc = vecNew<string * int> ()
                patBinders p acc
                for k in vecToList acc do dictSet bound k true
                (match gd with Some x -> go x | None -> ())
                go b
        | ETry (b, cs) ->
            go b
            for p, gd, x in cs do
                let acc = vecNew<string * int> ()
                patBinders p acc
                for k in vecToList acc do dictSet bound k true
                (match gd with Some y -> go y | None -> ())
                go x
        | EApp (h, args) -> go h; for a in args do go a
        | EIf (a, b, c) -> go a; go b; go c
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) ->
            for x in xs do go x
        | ERecord (_, fs) -> for _, v in fs do go v
        | ERecordExt (_, b2, fs) -> go b2; (for _, v in fs do go v)
        | EField (r, _, _) -> go r
        | EFieldSet (r, _, _, v) -> go r; go v
        | EWhile (c, b) -> go c; go b
        | EIndex (_, a, i) -> go a; go i
        | EIndexSet (_, a, i, v) -> go a; go i; go v
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) -> go a
        | EArrayCreate (_, a, b) -> go a; go b
        | EIfaceCall (_, _, r, args) -> go r; for a in args do go a
        | ECast (_, x, _) | ETypeTest (_, x) -> go x
        | _ -> ()
    go body
    vecToList free

/// locals assigned somewhere AND referenced from an inner lambda: cells
let private cellLocals (body : Expr) : Dict<string * int, bool> =
    let assigned = dictNew<string * int, bool> ()
    let captured = dictNew<string * int, bool> ()
    walkE (fun e ->
        match e with
        | EAssign (v, _) -> dictSet assigned (v.Path, v.Offset) true
        | ELam (_, b) ->
            walkE (fun x ->
                match x with
                | EVar (v, _) | EVarI (v, _, _) -> dictSet captured (v.Path, v.Offset) true
                | EAssign (v, _) -> dictSet captured (v.Path, v.Offset) true
                | _ -> ()) b
        | _ -> ()) body
    let cells = dictNew<string * int, bool> ()
    for k, _ in dictPairs assigned do
        if (dictTryFind captured k).IsSome then dictSet cells k true
    cells

// ---- expression emission --------------------------------------------------

let private mathSet (b : string) : bool =
    b = "abs" || b = "sqrt" || b = "floor" || b = "ceil"
    || b = "truncate" || b = "round" || b = "sign" || b = "exp"
    || b = "log" || b = "log2" || b = "log10" || b = "sin" || b = "cos"
    || b = "tan" || b = "asin" || b = "acos" || b = "atan"
    || b = "sinh" || b = "cosh" || b = "tanh"

/// the FULL name wins before suffix stripping: "abs" must not lose its s
let private mathBase (op0 : string) : string option =
    if mathSet op0 then Some op0
    elif strLen op0 > 1 then
        let c = charAt op0 (strLen op0 - 1)
        if c = 'i' || c = 'f' || c = 'l' || c = 's' || c = 'h'
           || c = 'w' || c = 'v' || c = 'b' || c = 'c' then
            let b = op0.Substring (0, strLen op0 - 1)
            if mathSet b then Some b else None
        else None
    else None

let private opBase (op0 : string) : string * char =
    // "=i" -> ("=", 'i'); a bare op is int-kinded
    if strLen op0 >= 2 then
        let last = charAt op0 (strLen op0 - 1)
        let head = op0.Substring (0, strLen op0 - 1)
        let known =
            head = "+" || head = "-" || head = "*" || head = "/" || head = "%"
            || head = "=" || head = "<>" || head = "<" || head = ">"
            || head = "<=" || head = ">=" || head = "&&&" || head = "|||"
            || head = "^^^" || head = "<<<" || head = ">>>"
        if known && (last = 'i' || last = 'b' || last = 'c' || last = 'f'
                     || last = 'l' || last = 's' || last = 'u' || last = 't'
                     || last = 'o' || last = 'w' || last = 'v' || last = 'h') then head, last
        else op0, '?'
    else op0, '?'

let rec private emitE (st : CSt) (f : CFn) (e : Expr) : int =
    let trap (what : string) : int =
        let d = slot f
        stmt f (sref d + " = fpp_not_emitted(" + cstr what + ");")
        d
    let unitV () : int =
        let d = slot f
        stmt f (sref d + " = VUNIT;")
        d
    let fieldIdx (order : string list) (fname : string) : int =
        let rec find (i : int) (rest : string list) =
            match rest with
            | r :: more -> if r = fname then i else find (i + 1) more
            | [] -> -1
        find 0 order
    match e with
    | ELit (LInt s) ->
        // the literal keeps its SOURCE suffix (5L, 3uy, 7us, 0x1F);
        // int64/uint64 box, everything else tags
        let d = slot f
        let mutable cut = strLen s
        while cut > 0 && (let c = charAt s (cut - 1) in
                          c = 'L' || c = 'l' || c = 'u' || c = 'U'
                          || c = 'y' || c = 's' || c = 'n') && cut > 1
              && not (cut = strLen s && strLen s >= 2 && charAt s 0 = '0'
                      && (charAt s 1 = 'x' || charAt s 1 = 'X') && cut <= 2) do
            cut <- cut - 1
        let num = s.Substring (0, cut)
        let suffix = s.Substring cut
        if suffix.Contains "L" || suffix.Contains "l" then
            stmt f (sref d + " = fpp_box_i64(" + num + "LL);")
        else
            stmt f (sref d + " = TAGI(" + num + "L);")
        d
    | ELit (LBool b) ->
        let d = slot f
        stmt f (sref d + " = TAGI(" + (if b then "1" else "0") + ");")
        d
    | ELit (LChar s) ->
        let d = slot f
        stmt f (sref d + " = TAGI(" + string (Fpp.Backend.BinDriver.charCode s) + ");")
        d
    | ELit LUnit -> unitV ()
    | ELit LNull ->
        let d = slot f
        stmt f (sref d + " = 0;")
        d
    | ELit (LFloat s) ->
        let d = slot f
        let t0 = if s.EndsWith "f" then s.Substring (0, strLen s - 1) else s
        let txt = if t0.EndsWith "." then t0 + "0" else t0
        stmt f (sref d + " = fpp_box_f64(" + txt + ");")
        d
    | ELit (LString s) ->
        let d = slot f
        let bs = Fpp.Backend.BinDriver.unescape s
        let txt = bs |> Array.map (fun b -> string (char (int b))) |> Array.toList |> String.concat ""
        stmt f (sref d + " = fpp_str_c(" + cstr txt + ", " + string bs.Length + ");")
        d
    | EVar (v, _) | EVarI (v, _, _) ->
        (match dictTryFind f.Locals (v.Path, v.Offset) with
         | Some i ->
             if (dictTryFind f.Cells (v.Path, v.Offset)).IsSome then
                 let d = slot f
                 stmt f (sref d + " = fpp_cell_get(" + sref i + ");")
                 d
             else i
         | None ->
             match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g ->
                 let d = slot f
                 stmt f (sref d + " = " + g + ";")
                 d
             | None ->
                 match dictTryFind st.Fns (v.Path, v.Offset) with
                 | Some _ ->
                     let g = fnCloGlobal st v
                     let d = slot f
                     stmt f (sref d + " = " + g + ";")
                     d
                 | None ->
                     match dictTryFind st.EnumVal v.Name with
                     | Some ev ->
                         let d = slot f
                         stmt f (sref d + " = TAGI(" + string ev + ");")
                         d
                     | None -> trap ("free var " + v.Name))
    | EApp (EUnknown "print", [ a ]) ->
        // the GENERIC print: a string prints raw, anything else through the
        // value renderer — the oracle's $showv path
        let x = emitE st f a
        stmt f ("fpp_print_any(" + sref x + ");")
        unitV ()
    | EApp (EUnknown "prints", [ a ]) ->
        let x = emitE st f a
        stmt f ("fpp_print(" + sref x + ");")
        unitV ()
    | EApp (EUnknown "printb", [ a ]) ->
        let x = emitE st f a
        stmt f ("fpp_print(fpp_bool_to_string(" + sref x + "));")
        unitV ()
    | EApp (EUnknown "printc", [ a ]) ->
        let x = emitE st f a
        stmt f ("fpp_print(fpp_char_to_string(" + sref x + "));")
        unitV ()
    | EApp (EUnknown "printu", [ a ]) ->
        let x = emitE st f a
        stmt f ("fpp_print_u32(" + sref x + ");")
        unitV ()
    | EApp (EUnknown "showv", [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = fpp_showv(" + sref x + ");")
        d
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string" ->
        let x = emitE st f a
        let d = slot f
        let k = if strLen n > 6 then charAt n (strLen n - 1) else ' '
        (match k with
         | 'b' -> stmt f (sref d + " = fpp_bool_to_string(" + sref x + ");")
         | 'f' | 's' | 'h' -> stmt f (sref d + " = fpp_f64_to_string(" + sref x + ");")
         | 'c' -> stmt f (sref d + " = fpp_char_to_string(" + sref x + ");")
         | 'v' -> stmt f (sref d + " = fpp_u64_to_string(" + sref x + ");")
         | 'w' -> stmt f (sref d + " = fpp_u32_to_string(" + sref x + ");")
         | _ -> stmt f (sref d + " = fpp_to_string(" + sref x + ");"))
        d
    | EApp (EUnknown "$cellof", [ inner ]) ->
        // the CELL itself, not its content: a non-cell-marked local already
        // HOLDS the cell (class ctor `let n = $forcecell ...`), a cell-marked
        // one is the slot raw
        (match inner with
         | EVar (v, _) | EVarI (v, _, _) ->
             (match dictTryFind f.Locals (v.Path, v.Offset) with
              | Some i -> i
              | None -> emitE st f inner)
         | _ -> emitE st f inner)
    | EApp (EUnknown "$forcecell", [ r ]) ->
        let x = emitE st f r
        let d = slot f
        stmt f (sref d + " = fpp_cell_new(" + sref x + ");")
        d
    | EApp (EUnknown "$cellget", [ c ]) ->
        let x = emitE st f c
        let d = slot f
        stmt f (sref d + " = fpp_cell_get(" + sref x + ");")
        d
    | EApp (EUnknown "$cellset", [ c; v ]) ->
        let x = emitE st f c
        let y = emitE st f v
        stmt f ("fpp_cell_set(" + sref x + ", " + sref y + ");")
        unitV ()
    | EApp (EUnknown "refEq", [ a; b ]) ->
        let x = emitE st f a
        let y = emitE st f b
        let d = slot f
        stmt f (sref d + " = TAGI(" + sref x + " == " + sref y + ");")
        d
    | EApp (EUnknown "compare", [ a; b ]) ->
        let x = emitE st f a
        let y = emitE st f b
        let d = slot f
        stmt f (sref d + " = TAGI(fpp_cmpv(" + sref x + ", " + sref y + "));")
        d
    | EApp (EUnknown "hash", [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI(fpp_hashv(" + sref x + "));")
        d
    | EApp (EUnknown "ignore", [ a ]) ->
        emitE st f a |> ignore
        unitV ()
    | EApp (EUnknown ("failwith" | "raise"), [ a ]) ->
        let x = emitE st f a
        stmt f ("fpp_raise(" + sref x + ");")
        unitV ()
    | EApp (EUnknown n, [ a ]) when n.StartsWith "float" && not (n.StartsWith "float32") ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = fpp_to_f64(" + sref x + ");")
        d
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int64" || n.StartsWith "uint64" ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = fpp_to_i64(" + sref x + ");")
        d
    | EApp (EUnknown n, [ a ]) when n.StartsWith "byte" || n.StartsWith "sbyte"
                                    || n.StartsWith "int16" || n.StartsWith "uint16"
                                    || n.StartsWith "uint32" ->
        let x = emitE st f a
        let d = slot f
        let mask =
            if n.StartsWith "byte" then "(intptr_t)(uint8_t)"
            elif n.StartsWith "sbyte" then "(intptr_t)(int8_t)"
            elif n.StartsWith "int16" then "(intptr_t)(int16_t)"
            elif n.StartsWith "uint16" then "(intptr_t)(uint16_t)"
            else "(intptr_t)(uint32_t)"
        stmt f (sref d + " = TAGI(" + mask + "UNTAGI(fpp_to_int(" + sref x + ")));")
        d
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int" ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = fpp_to_int(" + sref x + ");")
        d
    | EApp (EUnknown ("char" | "char#"), [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = fpp_to_int(" + sref x + ");")
        d
    | EApp (EUnknown n, [ a ]) when (mathBase n).IsSome ->
        emitE st f (EPrim (n, [ a ]))
    | EApp (EUnknown n, recv :: args) when n.StartsWith "$str." ->
        let m = n.Substring 5
        let r = emitE st f recv
        let xs = args |> List.map (emitE st f)
        let first = f.NSlots
        for x in xs do
            let s2 = slot f
            stmt f (sref s2 + " = " + sref x + ";")
        let d = slot f
        stmt f (sref d + " = fpp_str_method(" + cstr m + ", " + sref r
                + ", &F[" + string first + "], " + string (List.length xs) + ");")
        d
    | EApp (EUnknown "isNull", [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI(" + sref x + " == 0);")
        d
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when
          (dictTryFind st.Fns (v.Path, v.Offset)) = Some (List.length args) ->
        let xs = args |> List.map (emitE st f)
        let d = slot f
        stmt f (sref d + " = " + cname v + "("
                + String.concat ", " (xs |> List.map sref) + ");")
        d
    | EApp (h, args) ->
        // the closure protocol: args in CONSECUTIVE slots, rooted during apply
        let c = emitE st f h
        let xs = args |> List.map (emitE st f)
        let first = f.NSlots
        for x in xs do
            let s2 = slot f
            stmt f (sref s2 + " = " + sref x + ";")
        let d = slot f
        stmt f (sref d + " = fpp_apply(" + sref c + ", &F[" + string first + "], "
                + string (List.length xs) + ");")
        d
    | ELam (ps, body) -> emitLam st f ps body
    | EPrim ("::", [ h; t ]) ->
        let x = emitE st f h
        let y = emitE st f t
        let d = slot f
        stmt f (sref d + " = fpp_cons(" + sref x + ", " + sref y + ");")
        d
    | EPrim (op0, [ a; b ]) when op0.Contains "@" ->
        // "op@Type": the operand type rides on the operator. Uniformly
        // represented values answer the whole family structurally.
        let baseOp = op0.Substring (0, op0.IndexOf "@")
        let x = emitE st f a
        let y = emitE st f b
        let d = slot f
        (match baseOp with
         | "=" -> stmt f (sref d + " = TAGI(fpp_eqv(" + sref x + ", " + sref y + "));")
         | "<>" -> stmt f (sref d + " = TAGI(!fpp_eqv(" + sref x + ", " + sref y + "));")
         | "<" -> stmt f (sref d + " = TAGI(fpp_cmpv(" + sref x + ", " + sref y + ") < 0);")
         | ">" -> stmt f (sref d + " = TAGI(fpp_cmpv(" + sref x + ", " + sref y + ") > 0);")
         | "<=" -> stmt f (sref d + " = TAGI(fpp_cmpv(" + sref x + ", " + sref y + ") <= 0);")
         | ">=" -> stmt f (sref d + " = TAGI(fpp_cmpv(" + sref x + ", " + sref y + ") >= 0);")
         | _ -> stmt f (sref d + " = fpp_not_emitted(" + cstr ("op " + op0) + ");"))
        d
    | EPrim (op0, [ a; b ]) ->
        let op, k = opBase op0
        let x = emitE st f a
        let y = emitE st f b
        let d = slot f
        let arith (cop : string) =
            if k = '?' then
                // int carries NO kind suffix, and neither does generic code:
                // dispatch at runtime, exactly as the oracle's $addv does
                let fn =
                    match cop with
                    | "+" -> "fpp_addv" | "-" -> "fpp_subv" | "*" -> "fpp_mulv"
                    | "/" -> "fpp_divv" | _ -> "fpp_modv"
                stmt f (sref d + " = " + fn + "(" + sref x + ", " + sref y + ");")
            elif k = 'f' then
                stmt f (sref d + " = fpp_box_f64(fpp_unbox_f64(" + sref x + ") " + cop
                        + " fpp_unbox_f64(" + sref y + "));")
            elif k = 's' || k = 'h' then
                // float32/float16 ride in f64 boxes; rounding through
                // (float) after every op keeps single precision semantics
                stmt f (sref d + " = fpp_box_f64((double)(float)((float)fpp_unbox_f64("
                        + sref x + ") " + cop + " (float)fpp_unbox_f64(" + sref y + ")));")
            elif k = 'l' then
                stmt f (sref d + " = fpp_box_i64(fpp_unbox_i64(" + sref x + ") " + cop
                        + " fpp_unbox_i64(" + sref y + "));")
            elif k = 'v' then
                stmt f (sref d + " = fpp_box_i64((int64_t)((uint64_t)fpp_unbox_i64("
                        + sref x + ") " + cop + " (uint64_t)fpp_unbox_i64(" + sref y + ")));")
            elif k = 'w' then
                stmt f (sref d + " = TAGI((intptr_t)(uint32_t)((uint32_t)UNTAGI("
                        + sref x + ") " + cop + " (uint32_t)UNTAGI(" + sref y + ")));")
            else
                stmt f (sref d + " = TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(" + sref x + ") " + cop
                        + " (int32_t)UNTAGI(" + sref y + ")));")
        let rel (cop : string) =
            if k = '?' || k = 't' || k = 'o' then
                stmt f (sref d + " = TAGI(fpp_cmpv(" + sref x + ", " + sref y + ") "
                        + cop + " 0);")
            elif k = 'f' || k = 's' || k = 'h' then
                stmt f (sref d + " = TAGI(fpp_unbox_f64(" + sref x + ") " + cop
                        + " fpp_unbox_f64(" + sref y + "));")
            elif k = 'l' then
                stmt f (sref d + " = TAGI(fpp_unbox_i64(" + sref x + ") " + cop
                        + " fpp_unbox_i64(" + sref y + "));")
            elif k = 'v' then
                stmt f (sref d + " = TAGI((uint64_t)fpp_unbox_i64(" + sref x + ") " + cop
                        + " (uint64_t)fpp_unbox_i64(" + sref y + "));")
            elif k = 'w' then
                stmt f (sref d + " = TAGI((uint32_t)UNTAGI(" + sref x + ") " + cop
                        + " (uint32_t)UNTAGI(" + sref y + "));")
            else
                stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") " + cop
                        + " UNTAGI(" + sref y + "));")
        (match op with
         | "+" when k = 's' || k = 't' ->
             stmt f (sref d + " = fpp_str_concat(" + sref x + ", " + sref y + ");")
         | "+" | "-" | "*" | "/" | "%" -> arith op
         | "<" | ">" | "<=" | ">=" -> rel op
         | "=" -> stmt f (sref d + " = TAGI(fpp_eqv(" + sref x + ", " + sref y + "));")
         | "<>" -> stmt f (sref d + " = TAGI(!fpp_eqv(" + sref x + ", " + sref y + "));")
         | "&&" -> stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") && UNTAGI(" + sref y + "));")
         | "||" -> stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") || UNTAGI(" + sref y + "));")
         | "&&&" | "|||" | "^^^" | "<<<" | ">>>" ->
             let cop =
                 match op with
                 | "&&&" -> "&" | "|||" -> "|" | "^^^" -> "^"
                 | "<<<" -> "<<" | _ -> ">>"
             if k = 'l' then
                 // int64: unbox; shift COUNTS are tagged ints
                 let rhs =
                     if op = "<<<" || op = ">>>" then "UNTAGI(" + sref y + ")"
                     else "fpp_unbox_i64(" + sref y + ")"
                 stmt f (sref d + " = fpp_box_i64(fpp_unbox_i64(" + sref x + ") "
                         + cop + " " + rhs + ");")
             elif k = 'v' then
                 let rhs =
                     if op = "<<<" || op = ">>>" then "UNTAGI(" + sref y + ")"
                     else "(uint64_t)fpp_unbox_i64(" + sref y + ")"
                 stmt f (sref d + " = fpp_box_i64((int64_t)((uint64_t)fpp_unbox_i64("
                         + sref x + ") " + cop + " " + rhs + "));")
             elif k = 'w' then
                 stmt f (sref d + " = TAGI((intptr_t)(uint32_t)((uint32_t)UNTAGI("
                         + sref x + ") " + cop + " (uint32_t)UNTAGI(" + sref y + ")));")
             elif op = ">>>" && k = '?' then
                 // bare shift right on int32 stays ARITHMETIC in .NET
                 stmt f (sref d + " = TAGI((intptr_t)((int32_t)UNTAGI(" + sref x
                         + ") >> UNTAGI(" + sref y + ")));")
             else
                 stmt f (sref d + " = TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(" + sref x + ") "
                         + cop + " UNTAGI(" + sref y + ")));")
         | _ -> stmt f (sref d + " = fpp_not_emitted(" + cstr ("op " + op0) + ");"))
        d
    | EPrim (("unot" | "unoti" | "unotb"), [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI(!UNTAGI(" + sref x + "));")
        d
    | EPrim ("not", [ a ]) | EApp (EUnknown "not", [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI(!UNTAGI(" + sref x + "));")
        d
    | EPrim (op0, [ a ]) when (mathBase op0).IsSome ->
        let bare = (mathBase op0).Value
        let x = emitE st f a
        let d = slot f
        (match bare with
         | "abs" -> stmt f (sref d + " = fpp_absv(" + sref x + ");")
         | "sign" -> stmt f (sref d + " = fpp_signv(" + sref x + ");")
         | "truncate" -> stmt f (sref d + " = fpp_box_f64(__builtin_trunc(fpp_unbox_f64(" + sref x + ")));")
         | "round" -> stmt f (sref d + " = fpp_box_f64(fpp_round_even(fpp_unbox_f64(" + sref x + ")));")
         | m ->
             let cfn =
                 match m with
                 | "ceil" -> "__builtin_ceil"
                 | "log" -> "__builtin_log"
                 | _ -> "__builtin_" + m
             stmt f (sref d + " = fpp_box_f64(" + cfn + "(fpp_unbox_f64(" + sref x + ")));"))
        d
    | EPrim (op0, [ a ]) when op0.StartsWith "u-" ->
        let x = emitE st f a
        let d = slot f
        let k = if strLen op0 > 2 then charAt op0 2 else '?'
        (match k with
         | 'f' | 's' | 'h' ->
             stmt f (sref d + " = fpp_box_f64(-fpp_unbox_f64(" + sref x + "));")
         | 'l' | 'v' ->
             stmt f (sref d + " = fpp_box_i64(-fpp_unbox_i64(" + sref x + "));")
         | 'i' | 'b' | 'c' | 'w' ->
             stmt f (sref d + " = TAGI(-UNTAGI(" + sref x + "));")
         | _ ->
             stmt f (sref d + " = fpp_negv(" + sref x + ");"))
        d
    | EPrim (("~-" | "~-i"), [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI(-UNTAGI(" + sref x + "));")
        d
    | EPrim ("~-f", [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = fpp_box_f64(-fpp_unbox_f64(" + sref x + "));")
        d
    | ELet (isRec, v, _, rhs, body) ->
        (match rhs with
         | ELam _ when isRec ->
             // a local recursive closure captures ITSELF: the knot ties
             // through a cell — capture the cell empty, then fill it
             dictSet f.Cells (v.Path, v.Offset) true
             let l = slot f
             stmt f (sref l + " = fpp_cell_new(0);")
             dictSet f.Locals (v.Path, v.Offset) l
             let x = emitE st f rhs
             stmt f ("fpp_cell_set(" + sref l + ", " + sref x + ");")
             emitE st f body
         | _ ->
             let x = emitE st f rhs
             let l = slot f
             if (dictTryFind f.Cells (v.Path, v.Offset)).IsSome then
                 stmt f (sref l + " = fpp_cell_new(" + sref x + ");")
             else
                 stmt f (sref l + " = " + sref x + ";")
             dictSet f.Locals (v.Path, v.Offset) l
             emitE st f body)
    | EAssign (v, rhs) ->
        let x = emitE st f rhs
        (match dictTryFind f.Locals (v.Path, v.Offset) with
         | Some l ->
             if (dictTryFind f.Cells (v.Path, v.Offset)).IsSome then
                 stmt f ("fpp_cell_set(" + sref l + ", " + sref x + ");")
             else
                 stmt f (sref l + " = " + sref x + ";")
         | None ->
             match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g -> stmt f (g + " = " + sref x + ";")
             | None -> stmt f ("fpp_not_emitted(" + cstr ("assign " + v.Name) + ");"))
        unitV ()
    | EIf (c, t, e2) ->
        let x = emitE st f c
        let d = slot f
        stmt f ("if (UNTAGI(" + sref x + ")) {")
        let tv = emitE st f t
        stmt f (sref d + " = " + sref tv + ";")
        stmt f ("} else {")
        let ev = emitE st f e2
        stmt f (sref d + " = " + sref ev + ";")
        stmt f ("}")
        d
    | EWhile (c, b) ->
        stmt f ("for (;;) {")
        let x = emitE st f c
        stmt f ("if (!UNTAGI(" + sref x + ")) break;")
        emitE st f b |> ignore
        stmt f ("}")
        unitV ()
    | ESeq xs ->
        (match xs with
         | [] -> unitV ()
         | _ ->
             let rec go (rest : Expr list) : int =
                 match rest with
                 | [ last ] -> emitE st f last
                 | x :: more ->
                     emitE st f x |> ignore
                     go more
                 | [] -> unitV ()
             go xs)
    | ETuple xs ->
        let vs = xs |> List.map (emitE st f)
        let d = slot f
        stmt f (sref d + " = fpp_tuple(" + string (List.length xs) + ");")
        vs |> List.iteri (fun i x ->
            stmt f ("fpp_tuple_set(" + sref d + ", " + string i + ", " + sref x + ");"))
        d
    | EListLit xs ->
        let vs = xs |> List.map (emitE st f)
        let d = slot f
        stmt f (sref d + " = 0;")
        for x in List.rev vs do
            stmt f (sref d + " = fpp_cons(" + sref x + ", " + sref d + ");")
        d
    | ERecord (name, fs) ->
        (match dictTryFind st.RecTid name with
         | Some tid ->
             let order = (dictTryFind st.RecFields name).Value
             let d = slot f
             stmt f (sref d + " = fpprt_alloc(" + string tid + ");")
             for fn2, v in fs do
                 let x = emitE st f v
                 let idx = fieldIdx order fn2
                 if idx < 0 then
                     stmt f ("fpp_not_emitted(" + cstr ("field " + name + "." + fn2) + ");")
                 else
                     stmt f ("fpprt_write_ref(" + sref d + ", "
                             + string ((idx + 1) * 8) + ", " + sref x + ");")
             d
         | None -> trap ("record " + name))
    | ERecordExt (name, b, fs) ->
        (match dictTryFind st.RecTid name with
         | Some tid ->
             let src = emitE st f b
             let order = (dictTryFind st.RecFields name).Value
             let n = List.length order
             let d = slot f
             stmt f (sref d + " = fpprt_alloc(" + string tid + ");")
             for i in 0 .. n - 1 do
                 stmt f ("fpprt_write_ref(" + sref d + ", " + string ((i + 1) * 8)
                         + ", fpprt_read_ref(" + sref src + ", " + string ((i + 1) * 8) + "));")
             for fn2, v in fs do
                 let x = emitE st f v
                 let idx = fieldIdx order fn2
                 if idx >= 0 then
                     stmt f ("fpprt_write_ref(" + sref d + ", "
                             + string ((idx + 1) * 8) + ", " + sref x + ");")
             d
         | None -> trap ("record " + name))
    | EField (r, fname, owner) ->
        (match dictTryFind st.RecFields owner with
         | Some order ->
             let x = emitE st f r
             let idx = fieldIdx order fname
             if idx < 0 then trap ("field " + owner + "." + fname)
             else
                 let d = slot f
                 stmt f (sref d + " = fpprt_read_ref(" + sref x + ", "
                         + string ((idx + 1) * 8) + ");")
                 d
         | None -> trap ("field of " + owner + "." + fname))
    | EFieldSet (r, fname, owner, v) ->
        (match dictTryFind st.RecFields owner with
         | Some order ->
             let x = emitE st f r
             let y = emitE st f v
             let idx = fieldIdx order fname
             if idx < 0 then trap ("fieldset " + owner + "." + fname)
             else
                 stmt f ("fpprt_write_ref(" + sref x + ", "
                         + string ((idx + 1) * 8) + ", " + sref y + ");")
                 unitV ()
         | None -> trap ("fieldset of " + owner))
    | ECtor (cn, _, args) ->
        (match dictTryFind st.CaseTid cn with
         | Some tid ->
             let vs = args |> List.map (emitE st f)
             let d = slot f
             stmt f (sref d + " = fpprt_alloc(" + string tid + ");")
             vs |> List.iteri (fun i x ->
                 stmt f ("fpprt_write_ref(" + sref d + ", " + string ((i + 1) * 8)
                         + ", " + sref x + ");"))
             d
         | None ->
             match dictTryFind st.EnumVal cn with
             | Some ev ->
                 let d = slot f
                 stmt f (sref d + " = TAGI(" + string ev + ");")
                 d
             | None -> trap ("ctor " + cn))
    | EMatch (scrut, clauses) ->
        let sv = emitE st f scrut
        let d = slot f
        let matched = slot f
        stmt f (sref matched + " = TAGI(0);")
        for p, guard, body in clauses do
            stmt f ("if (!UNTAGI(" + sref matched + ")) {")
            let ok = slot f
            stmt f (sref ok + " = TAGI(1);")
            emitPat st f p sv ok
            (match guard with
             | Some g ->
                 stmt f ("if (UNTAGI(" + sref ok + ")) {")
                 let gv = emitE st f g
                 stmt f (sref ok + " = " + sref gv + ";")
                 stmt f ("}")
             | None -> ())
            stmt f ("if (UNTAGI(" + sref ok + ")) {")
            let bv = emitE st f body
            stmt f (sref d + " = " + sref bv + ";")
            stmt f (sref matched + " = TAGI(1);")
            stmt f ("}")
            stmt f ("}")
        stmt f ("if (!UNTAGI(" + sref matched + ")) fpp_match_fail();")
        d
    | ETry (body, handlers) ->
        let d = slot f
        let ex = slot f
        stmt f ("{ struct fpp_handler H;")
        stmt f ("if (!fpp_try(&H)) {")
        let bv = emitE st f body
        stmt f (sref d + " = " + sref bv + ";")
        stmt f ("fpp_try_pop();")
        stmt f ("} else {")
        stmt f (sref ex + " = fpp_exn_value();")
        let matched = slot f
        stmt f (sref matched + " = TAGI(0);")
        for p, guard, hb in handlers do
            stmt f ("if (!UNTAGI(" + sref matched + ")) {")
            let ok = slot f
            stmt f (sref ok + " = TAGI(1);")
            emitPat st f p ex ok
            (match guard with
             | Some g ->
                 stmt f ("if (UNTAGI(" + sref ok + ")) {")
                 let gv = emitE st f g
                 stmt f (sref ok + " = " + sref gv + ";")
                 stmt f ("}")
             | None -> ())
            stmt f ("if (UNTAGI(" + sref ok + ")) {")
            let bv = emitE st f hb
            stmt f (sref d + " = " + sref bv + ";")
            stmt f (sref matched + " = TAGI(1);")
            stmt f ("}")
            stmt f ("}")
        stmt f ("if (!UNTAGI(" + sref matched + ")) fpp_reraise();")
        stmt f ("} }")
        d
    | EArray (_, xs) ->
        let vs = xs |> List.map (emitE st f)
        let d = slot f
        stmt f (sref d + " = fpp_arr_new(" + string (List.length xs) + ");")
        vs |> List.iteri (fun i x ->
            stmt f ("fpp_arr_set(" + sref d + ", " + string i + ", " + sref x + ");"))
        d
    | EArrayCreate (nm, n, v) ->
        let nv = emitE st f n
        let d = slot f
        (match v with
         | EUnknown "$zero" ->
             // .NET zeros by ELEMENT KIND: an int slot is tagged 0, never
             // null — generic code adds it without looking
             let zk =
                 match nm with
                 | "int" | "bool" | "char" | "byte" | "sbyte" | "int16"
                 | "uint16" | "uint32" | "enum" -> "1"
                 | "float" | "float32" | "double" | "single" -> "2"
                 | "int64" | "uint64" -> "3"
                 | _ -> "0"
             stmt f (sref d + " = fpp_arr_zeroed(" + zk + ", (size_t)UNTAGI("
                     + sref nv + "));")
         | _ ->
             stmt f (sref d + " = fpp_arr_new((size_t)UNTAGI(" + sref nv + "));")
             let x = emitE st f v
             stmt f ("{ size_t N = fpprt_array_len(" + sref d + ");")
             stmt f ("for (size_t I = 0; I < N; I++) fpp_arr_set(" + sref d
                     + ", I, " + sref x + "); }"))
        d
    | EIndex ("$str", a, i) ->
        let av = emitE st f a
        let iv = emitE st f i
        let d = slot f
        stmt f (sref d + " = TAGI(fpp_str_units(" + sref av + ")[UNTAGI(" + sref iv + ")]);")
        d
    | EIndex (_, a, i) ->
        let av = emitE st f a
        let iv = emitE st f i
        let d = slot f
        stmt f (sref d + " = fpp_arr_get(" + sref av + ", (size_t)UNTAGI(" + sref iv + "));")
        d
    | EIndexSet (_, a, i, v) ->
        let av = emitE st f a
        let iv = emitE st f i
        let xv = emitE st f v
        stmt f ("fpp_arr_set(" + sref av + ", (size_t)UNTAGI(" + sref iv + "), " + sref xv + ");")
        unitV ()
    | EIndexSet ("$str", a, i, v) ->
        let av = emitE st f a
        let iv = emitE st f i
        let xv = emitE st f v
        stmt f ("fpp_str_units(" + sref av + ")[UNTAGI(" + sref iv + ")] = (uint16_t)UNTAGI(" + sref xv + ");")
        unitV ()
    | EArrayLen (_, a) ->
        let av = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI((intptr_t)fpprt_array_len(" + sref av + "));")
        d
    | EIfaceCall (iface, memberName, recv, args) ->
        let bare =
            match iface.IndexOf "`" with
            | i when i > 0 -> iface.Substring (0, i)
            | _ -> iface
        (match dictTryFind st.VSlot (bare, memberName) with
         | Some vslot ->
             let r = emitE st f recv
             let xs = args |> List.map (emitE st f)
             let first = f.NSlots
             for x in xs do
                 let s2 = slot f
                 stmt f (sref s2 + " = " + sref x + ";")
             let d = slot f
             stmt f (sref d + " = fpp_vcall(" + sref r + ", " + string vslot
                     + ", &F[" + string first + "], " + string (List.length xs) + ");")
             d
         | None -> trap ("iface slot " + bare + "." + memberName))
    | ECast (_, x, _) ->
        // uniform representation: a cast is bit-identity; the CHECKED ones
        // learn to check with the class machinery (M5)
        emitE st f x
    | ETypeTest (tn, x) ->
        let xv = emitE st f x
        (match dictTryFind st.RecTid tn with
         | Some tid ->
             let d = slot f
             stmt f (sref d + " = TAGI(" + sref xv + " != 0 && !(" + sref xv
                     + " & 1) && fpprt_typeid(" + sref xv + ") == " + string tid + ");")
             d
         | None ->
             match dictTryFind st.CaseTid tn with
             | Some tid ->
                 let d = slot f
                 stmt f (sref d + " = TAGI(" + sref xv + " != 0 && !(" + sref xv
                         + " & 1) && fpprt_typeid(" + sref xv + ") == " + string tid + ");")
                 d
             | None -> trap ("typetest " + tn))
    | EUnknown "$zero" ->
        let d = slot f
        stmt f (sref d + " = 0;")
        d
    | EUnknown n -> trap ("builtin " + n)
    | other ->
        let p0 = printExpr other
        let p = if strLen p0 > 60 then p0.Substring (0, 60) else p0
        trap ("form " + p)

/// pattern TEST against value slot `sv`: leaves `ok` false on mismatch,
/// binds pattern variables on the tested path
and private emitPat (st : CSt) (f : CFn) (p : Pat) (sv : int) (ok : int) : unit =
    match p with
    | PWild -> ()
    | PVar (v, _) ->
        let l = slot f
        stmt f (sref l + " = " + sref sv + ";")
        dictSet f.Locals (v.Path, v.Offset) l
    | PAs (q, v, _) ->
        emitPat st f q sv ok
        let l = slot f
        stmt f (sref l + " = " + sref sv + ";")
        dictSet f.Locals (v.Path, v.Offset) l
    | PLit (LInt s) ->
        let mutable cut = strLen s
        while cut > 1 && (let c = charAt s (cut - 1) in
                          c = 'L' || c = 'l' || c = 'u' || c = 'U'
                          || c = 'y' || c = 's' || c = 'n') do
            cut <- cut - 1
        let num = s.Substring (0, cut)
        let suffix = s.Substring cut
        if suffix.Contains "L" || suffix.Contains "l" then
            let lit = slot f
            stmt f (sref lit + " = fpp_box_i64(" + num + "LL);")
            stmt f ("if (!fpp_eqv(" + sref sv + ", " + sref lit + ")) "
                    + sref ok + " = TAGI(0);")
        else
            stmt f ("if (" + sref sv + " != TAGI(" + num + "L)) "
                    + sref ok + " = TAGI(0);")
    | PLit (LBool b) ->
        stmt f ("if (" + sref sv + " != TAGI(" + (if b then "1" else "0") + ")) "
                + sref ok + " = TAGI(0);")
    | PLit (LChar s) ->
        stmt f ("if (" + sref sv + " != TAGI(" + string (Fpp.Backend.BinDriver.charCode s) + ")) "
                + sref ok + " = TAGI(0);")
    | PLit LUnit -> ()
    | PLit LNull ->
        stmt f ("if (" + sref sv + " != 0) " + sref ok + " = TAGI(0);")
    | PLit (LString s) ->
        let lit = slot f
        let bs = Fpp.Backend.BinDriver.unescape s
        let txt = bs |> Array.map (fun b -> string (char (int b))) |> Array.toList |> String.concat ""
        stmt f (sref lit + " = fpp_str_c(" + cstr txt + ", " + string bs.Length + ");")
        stmt f ("if (!fpp_eqv(" + sref sv + ", " + sref lit + ")) " + sref ok + " = TAGI(0);")
    | PLit (LFloat s) ->
        let t0 = if s.EndsWith "f" then s.Substring (0, strLen s - 1) else s
        stmt f ("if (!(" + sref sv + " && !(" + sref sv + " & 1) && fpp_unbox_f64("
                + sref sv + ") == " + t0 + ")) " + sref ok + " = TAGI(0);")
    | PTuple ps ->
        ps |> List.iteri (fun i q ->
            let el = slot f
            stmt f ("if (UNTAGI(" + sref ok + ")) " + sref el + " = fpp_tuple_get("
                    + sref sv + ", " + string i + ");")
            emitPat st f q el ok)
    | PCons (h, t) ->
        stmt f ("if (!fpp_is_tid(" + sref sv + ", FPP_TID_CONS)) " + sref ok + " = TAGI(0);")
        let hv = slot f
        let tv = slot f
        stmt f ("if (UNTAGI(" + sref ok + ")) { " + sref hv + " = fpprt_read_ref("
                + sref sv + ", 8); " + sref tv + " = fpprt_read_ref(" + sref sv + ", 16); }")
        emitPat st f h hv ok
        emitPat st f t tv ok
    | PListLit ps ->
        let cur = slot f
        stmt f (sref cur + " = " + sref sv + ";")
        for q in ps do
            stmt f ("if (!fpp_is_tid(" + sref cur + ", FPP_TID_CONS)) "
                    + sref ok + " = TAGI(0);")
            let hv = slot f
            stmt f ("if (UNTAGI(" + sref ok + ")) " + sref hv + " = fpprt_read_ref("
                    + sref cur + ", 8);")
            emitPat st f q hv ok
            stmt f ("if (UNTAGI(" + sref ok + ")) " + sref cur + " = fpprt_read_ref("
                    + sref cur + ", 16);")
        stmt f ("if (UNTAGI(" + sref ok + ") && " + sref cur + " != 0) "
                + sref ok + " = TAGI(0);")
    | PCtor (cn, _, ps) ->
        (match dictTryFind st.CaseTid cn with
         | Some tid ->
             stmt f ("if (!fpp_is_tid(" + sref sv + ", " + string tid + ")) "
                     + sref ok + " = TAGI(0);")
             ps |> List.iteri (fun i q ->
                 let el = slot f
                 stmt f ("if (UNTAGI(" + sref ok + ")) " + sref el + " = fpprt_read_ref("
                         + sref sv + ", " + string ((i + 1) * 8) + ");")
                 emitPat st f q el ok)
         | None ->
             match dictTryFind st.EnumVal cn with
             | Some ev ->
                 stmt f ("if (" + sref sv + " != TAGI(" + string ev + ")) "
                         + sref ok + " = TAGI(0);")
             | None ->
                 stmt f (sref ok + " = fpp_not_emitted(" + cstr ("pat ctor " + cn) + ");"))
    | PTypeTest tn ->
        (match dictTryFind st.RecTid tn with
         | Some tid ->
             stmt f ("if (!fpp_is_tid(" + sref sv + ", " + string tid + ")) "
                     + sref ok + " = TAGI(0);")
         | None ->
             match dictTryFind st.CaseTid tn with
             | Some tid ->
                 stmt f ("if (!fpp_is_tid(" + sref sv + ", " + string tid + ")) "
                         + sref ok + " = TAGI(0);")
             | None ->
                 stmt f (sref ok + " = fpp_not_emitted(" + cstr ("pat typetest " + tn) + ");"))
    | POr ps ->
        let any = slot f
        stmt f (sref any + " = TAGI(0);")
        for q in ps do
            stmt f ("if (!UNTAGI(" + sref any + ")) {")
            let sub = slot f
            stmt f (sref sub + " = TAGI(1);")
            emitPat st f q sv sub
            stmt f ("if (UNTAGI(" + sref sub + ")) " + sref any + " = TAGI(1);")
            stmt f ("}")
        stmt f ("if (!UNTAGI(" + sref any + ")) " + sref ok + " = TAGI(0);")

/// a lambda in expression position: lift to a code function, allocate the
/// closure capturing its free variables. Closure layout:
/// [tag][code][arity][env0..] — code and arity raw scalars off the map.
and private emitLam (st : CSt) (f : CFn) (ps : (VarId * Scheme) list) (body : Expr) : int =
    let lamId = st.NextLam
    st.NextLam <- lamId + 1
    let code = "lam_" + string lamId
    let isOutside (k : string * int) = (dictTryFind f.Locals k).IsSome
    let frees = freeVarsOf ps body isOutside
    let lf = { Body = vecNew<string> (); NSlots = 0
               Locals = dictNew<string * int, int> (); Cells = f.Cells }
    frees |> List.iteri (fun i k ->
        let l = slot lf
        stmt lf (sref l + " = fpprt_read_ref(self, " + string ((i + 3) * 8) + ");")
        dictSet lf.Locals k l)
    ps |> List.iteri (fun i (pv, _) ->
        let l = slot lf
        stmt lf (sref l + " = args[" + string i + "];")
        dictSet lf.Locals (pv.Path, pv.Offset) l)
    let r = emitE st lf body
    vecAdd st.Fwd ("static V " + code + "(V self, V *args);")
    let all = vecNew<string> ()
    vecAdd all ("static V " + code + "(V self, V *args) {")
    vecAdd all ("  (void)self; (void)args;")
    vecAdd all ("  FPPRT_FRAME(Fr, " + string (max lf.NSlots 1) + "); V *F = Fr_slots;")
    for line in vecToList lf.Body do vecAdd all line
    vecAdd all ("  FPPRT_LEAVE(Fr);")
    vecAdd all ("  return " + sref r + ";")
    vecAdd all "}"
    vecAdd st.Out (String.concat "\n" (vecToList all))
    let tid = freshTid st
    vecAdd st.Reg ("  fpp_reg_clo(" + string tid + ", " + string (List.length frees) + ");")
    let d = slot f
    stmt f (sref d + " = fpp_clo_new(" + string tid + ", (fpp_code_t)" + code + ", "
            + string (List.length ps) + ", " + string (List.length frees) + ");")
    frees |> List.iteri (fun i k ->
        match dictTryFind f.Locals k with
        | Some l ->
            stmt f ("fpprt_write_ref(" + sref d + ", " + string ((i + 3) * 8) + ", "
                    + sref l + ");")
        | None -> stmt f ("fpp_not_emitted(\"capture miss\");"))
    d

/// a uniform (self, args) wrapper around a member function, for vtables
and private vtWrapper (st : CSt) (mv : VarId) : string =
    match dictTryFind st.VWrap (mv.Path, mv.Offset) with
    | Some w -> w
    | None ->
        let fn = cname mv
        let w = "vt_" + fn
        dictSet st.VWrap (mv.Path, mv.Offset) w
        let arity =
            match dictTryFind st.Fns (mv.Path, mv.Offset) with
            | Some a -> a
            | None -> 1
        vecAdd st.Fwd ("static V " + w + "(V self, V *args);")
        let extra =
            if arity <= 1 then []
            else List.init (arity - 1) (fun i -> "args[" + string i + "]")
        vecAdd st.Out
            ("static V " + w + "(V self, V *args) {\n  (void)args;\n  return "
             + fn + "(" + String.concat ", " ("self" :: extra) + ");\n}")
        w

/// the singleton closure for a top-level function used as a value
and private fnCloGlobal (st : CSt) (v : VarId) : string =
    match dictTryFind st.FnClo (v.Path, v.Offset) with
    | Some g -> g
    | None ->
        let fn = cname v
        let arity = (dictTryFind st.Fns (v.Path, v.Offset)).Value
        let g = "clo_" + fn
        let code = "code_" + fn
        dictSet st.FnClo (v.Path, v.Offset) g
        vecAdd st.Globals ("static V " + g + ";")
        vecAdd st.Fwd ("static V " + code + "(V self, V *args);")
        let psx =
            if arity = 0 then []
            else List.init arity (fun i -> "args[" + string i + "]")
        vecAdd st.Out
            ("static V " + code + "(V self, V *args) {\n  (void)self; (void)args;\n  return "
             + fn + "(" + String.concat ", " psx + ");\n}")
        let tid = freshTid st
        vecAdd st.Reg ("  fpp_reg_clo(" + string tid + ", 0);")
        // a fn-closure singleton has no dependencies: it initializes before
        // EVERY global initializer, whatever order emission discovered it
        vecAdd st.CloInits ("  " + g + " = fpp_clo_new(" + string tid + ", (fpp_code_t)"
                            + code + ", " + string arity + ", 0);")
        g

/// one function body, wrapped in its shadow frame
and private emitFn (st : CSt) (name : string) (ps : (VarId * Scheme) list) (body : Expr) : unit =
    let f = { Body = vecNew<string> (); NSlots = 0
              Locals = dictNew<string * int, int> (); Cells = cellLocals body }
    let pnames = ps |> List.mapi (fun i (pv, _) -> "p" + string i, pv)
    for pn, pv in pnames do
        let l = slot f
        if (dictTryFind f.Cells (pv.Path, pv.Offset)).IsSome then
            stmt f (sref l + " = fpp_cell_new(" + pn + ");")
        else
            stmt f (sref l + " = " + pn + ";")
        dictSet f.Locals (pv.Path, pv.Offset) l
    let r = emitE st f body
    vecAdd st.Fwd
        ("static V " + name + "("
         + (if List.isEmpty pnames then "void"
            else String.concat ", " (pnames |> List.map (fun _ -> "V")))
         + ");")
    let all = vecNew<string> ()
    vecAdd all
        ("static V " + name + "("
         + (if List.isEmpty pnames then "void"
            else String.concat ", " (pnames |> List.map (fun (pn, _) -> "V " + pn)))
         + ") {")
    vecAdd all ("  FPPRT_FRAME(Fr, " + string (max f.NSlots 1) + "); V *F = Fr_slots;")
    for line in vecToList f.Body do vecAdd all line
    vecAdd all ("  FPPRT_LEAVE(Fr);")
    vecAdd all ("  return " + sref r + ";")
    vecAdd all "}"
    vecAdd st.Out (String.concat "\n" (vecToList all))

// ---- whole program --------------------------------------------------------

let emitC (decls : Decl list) : string * string list =
    let st =
        { Out = vecNew<string> (); Fwd = vecNew<string> ()
          Globals = vecNew<string> (); Inits = vecNew<string> ()
          Reg = vecNew<string> ()
          Fns = dictNew<string * int, int> ()
          GlobalOf = dictNew<string * int, string> ()
          RecTid = dictNew<string, int> ()
          RecFields = dictNew<string, string list> ()
          CaseTid = dictNew<string, int> ()
          CaseArity = dictNew<string, int> ()
          EnumVal = dictNew<string, int> ()
          FnClo = dictNew<string * int, string> ()
          CloInits = vecNew<string> ()
          VSlot = dictNew<string * string, int> ()
          VWrap = dictNew<string * int, string> ()
          ClassBase = dictNew<string, string> ()
          ClassImpls = dictNew<string, (string * (string * VarId) list) list> ()
          NVSlots = 0
          NextTid = 32                          // FPP_TID_USER in fpprt-lang.h
          NextLam = 0 }
    // pass 1: names, record layouts, union cases, enums
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) ->
            dictSet st.Fns (v.Path, v.Offset) (List.length ps)
        | DLet (_, v, _, _) ->
            dictSet st.GlobalOf (v.Path, v.Offset) (gname v)
        | DRecord (n, _, fields, _) ->
            if not (dictTryFind st.RecTid n).IsSome then
                let tid = freshTid st
                dictSet st.RecTid n tid
                dictSet st.RecFields n (fields |> List.map fst)
                vecAdd st.Reg ("  fpp_reg_struct(" + string tid + ", "
                               + string (List.length fields) + ", 1, " + cstr n + ");")
        | DUnion (_, _, cases) ->
            for cn, arity in cases do
                if not (dictTryFind st.CaseTid cn).IsSome then
                    let tid = freshTid st
                    dictSet st.CaseTid cn tid
                    dictSet st.CaseArity cn arity
                    vecAdd st.Reg ("  fpp_reg_struct(" + string tid + ", "
                                   + string arity + ", 2, " + cstr cn + ");")
        | DEnum (_, cases) ->
            for cn, v in cases do dictSet st.EnumVal cn v
        | DClass (n, b, _, impls) ->
            (match b with Some x -> dictSet st.ClassBase n x | None -> ())
            dictSet st.ClassImpls n impls
            for iface, ms in impls do
                let bare =
                    match iface.IndexOf "`" with
                    | i when i > 0 -> iface.Substring (0, i)
                    | _ -> iface
                for mn, _ in ms do
                    if not (dictTryFind st.VSlot (bare, mn)).IsSome then
                        dictSet st.VSlot (bare, mn) st.NVSlots
                        st.NVSlots <- st.NVSlots + 1
        | DInterface (n, ms) ->
            let bare =
                match n.IndexOf "`" with
                | i when i > 0 -> n.Substring (0, i)
                | _ -> n
            for mn, _ in ms do
                if not (dictTryFind st.VSlot (bare, mn)).IsSome then
                    dictSet st.VSlot (bare, mn) st.NVSlots
                    st.NVSlots <- st.NVSlots + 1
        | _ -> ()
    // stamped record clones ("ResizeArray$int") arrive with EMPTY field
    // lists — the layout is the base's, uniform representation makes every
    // stamp identical, so they simply inherit the base record's fields.
    // Registration must agree (dictPairs snapshots, so mutation is safe).
    for n, flds in dictPairs st.RecFields do
        if List.isEmpty flds && n.Contains "$" then
            let baseName = n.Substring (0, n.IndexOf "$")
            match dictTryFind st.RecFields baseName with
            | Some bf when not (List.isEmpty bf) ->
                dictSet st.RecFields n bf
                match dictTryFind st.RecTid n with
                | Some tid ->
                    vecAdd st.Reg ("  fpp_reg_struct(" + string tid + ", "
                                   + string (List.length bf) + ", 1, " + cstr n + ");")
                | None -> ()
            | _ -> ()
    // pass 1.5: vtables — every class registers its impl chain's members
    // (nearest declaration wins, walking the base chain)
    let vtReg = vecNew<string> ()
    for d in decls do
        match d with
        | DClass (n, _, _, _) ->
            (match dictTryFind st.RecTid n with
             | Some tid ->
                 let filled = dictNew<int, bool> ()
                 let mutable cur = n
                 let mutable steps = 0
                 let mutable go = true
                 while go && steps < 32 do
                     (match dictTryFind st.ClassImpls cur with
                      | Some impls ->
                          for iface, ms in impls do
                              let bare =
                                  match iface.IndexOf "`" with
                                  | i when i > 0 -> iface.Substring (0, i)
                                  | _ -> iface
                              for mn, mv in ms do
                                  match dictTryFind st.VSlot (bare, mn) with
                                  | Some sl when not (dictTryFind filled sl).IsSome
                                                 // a DCE'd member body has no
                                                 // function to point at; its
                                                 // slot stays empty and traps
                                                 // only if dispatch reaches it
                                                 && (dictTryFind st.Fns (mv.Path, mv.Offset)).IsSome ->
                                      dictSet filled sl true
                                      let w = vtWrapper st mv
                                      vecAdd vtReg ("  fpp_vt_set(" + string tid + ", "
                                                    + string sl + ", " + w + ");")
                                  | _ -> ()
                      | None -> ())
                     (match dictTryFind st.ClassBase cur with
                      | Some b ->
                          cur <- b
                          steps <- steps + 1
                      | None -> go <- false)
             | None -> ())
        | _ -> ()
    // builtin seq protocol: arrays, lists, strings and tuples answer
    // IEnumerable/IEnumerator through runtime enumerators, wired into THIS
    // program's slot numbers
    (match dictTryFind st.VSlot ("IEnumerable", "GetEnumerator") with
     | Some sl ->
         for tid in [ "FPP_TID_ARR"; "FPP_TID_CONS"; "FPP_TID_STR"; "FPP_TID_TUPLE" ] do
             vecAdd vtReg ("  fpp_vt_set(" + tid + ", " + string sl + ", fpp_seq_getenum);")
     | None -> ())
    (match dictTryFind st.VSlot ("IEnumerator", "MoveNext") with
     | Some sl -> vecAdd vtReg ("  fpp_vt_set(FPP_TID_ENUM, " + string sl + ", fpp_enum_movenext);")
     | None -> ())
    (match dictTryFind st.VSlot ("IEnumerator", "Current") with
     | Some sl -> vecAdd vtReg ("  fpp_vt_set(FPP_TID_ENUM, " + string sl + ", fpp_enum_current);")
     | None -> ())
    (match dictTryFind st.VSlot ("IEnumerator", "Dispose") with
     | Some sl -> vecAdd vtReg ("  fpp_vt_set(FPP_TID_ENUM, " + string sl + ", fpp_enum_dispose);")
     | None -> ())
    (match dictTryFind st.VSlot ("IDisposable", "Dispose") with
     | Some sl -> vecAdd vtReg ("  fpp_vt_set(FPP_TID_ENUM, " + string sl + ", fpp_enum_dispose);")
     | None -> ())
    // pass 2: emission
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) -> emitFn st (cname v) ps body
        | DLet (_, v, _, rhs) ->
            vecAdd st.Globals ("static V " + gname v + ";")
            let initName = "init_" + gname v
            emitFn st initName [] rhs
            vecAdd st.Inits ("  " + gname v + " = " + initName + "();")
        | _ -> ()
    let out = vecNew<string> ()
    vecAdd out "/* generated by fpp --target c */"
    // FPP_CBACK_DUMP=1: every declaration as a comment, for reading what
    // the backend actually receives
    if System.Environment.GetEnvironmentVariable "FPP_CBACK_DUMP" = "1" then
        for d in decls do
            match d with
            | DLet (r, v, _, body) ->
                let p0 = printExpr body
                let p = if strLen p0 > 400 then p0.Substring (0, 400) else p0
                vecAdd out ("/* DLET " + (if r then "rec " else "") + v.Name
                            + " @" + v.Path + ":" + string v.Offset + "
   "
                            + (p |> String.map (fun c -> if c = '*' then '#' else c)) + " */")
            | DClass (n, b, own, impls) ->
                vecAdd out ("/* DCLASS " + n
                            + (match b with Some x -> " : " + x | None -> "")
                            + " own=[" + String.concat ", " (own |> List.map (fun (m, mv) -> m + "@" + string mv.Offset)) + "]"
                            + " impls=[" + String.concat "; " (impls |> List.map (fun (i, ms) -> i + ":" + String.concat "," (ms |> List.map fst))) + "] */")
            | DRecord (n, _, fs, isS) ->
                vecAdd out ("/* DRECORD " + n + (if isS then " struct" else "")
                            + " [" + String.concat ", " (fs |> List.map fst) + "] */")
            | DInterface (n, ms) ->
                vecAdd out ("/* DIFACE " + n + " [" + String.concat ", " (ms |> List.map fst) + "] */")
            | DUnion (n, _, cs) ->
                vecAdd out ("/* DUNION " + n + " [" + String.concat ", " (cs |> List.map fst) + "] */")
            | DMembers (n, ms) ->
                vecAdd out ("/* DMEMBERS " + n + " [" + String.concat ", " (ms |> List.map (fun (m, mv) -> m + "@" + string mv.Offset)) + "] */")
            | DBaseInst (n, xs) ->
                vecAdd out ("/* DBASEINST " + n + " [" + String.concat ", " xs + "] */")
            | _ -> ()
    vecAdd out "#include \"fpprt-lang.h\""
    vecAdd out ""
    for g in vecToList st.Globals do vecAdd out g
    vecAdd out ""
    for fd in vecToList st.Fwd do vecAdd out fd
    vecAdd out ""
    for fn in vecToList st.Out do
        vecAdd out fn
        vecAdd out ""
    vecAdd out "int main(void) {"
    vecAdd out "  fpp_lang_init();"
    for g in vecToList st.Globals do
        let n = g.Substring (9, strLen g - 10)
        vecAdd out ("  fpprt_add_static_roots(&" + n + ", 1);")
    for t in vecToList st.Reg do vecAdd out t
    for t in vecToList vtReg do vecAdd out t
    for i in vecToList st.CloInits do vecAdd out i
    for i in vecToList st.Inits do vecAdd out i
    vecAdd out "  return 0;"
    vecAdd out "}"
    String.concat "" ((vecToList out) |> List.map (fun l -> l + "\n")), []

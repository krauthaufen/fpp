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
      FnName : Dict<string * int, string>    // DECLARED C name: a call site
                                             // may use another Name for the
                                             // same (path,offset) — instance
                                             // members do ("compare" vs
                                             // "CompareTo")
      GlobalOf : Dict<string * int, string>
      RecTid : Dict<string, int>             // record name -> tid
      RecFields : Dict<string, string list>  // record name -> field order
      CaseTid : Dict<string, int>            // union case name -> tid
      CaseArity : Dict<string, int>
      EnumVal : Dict<string, int>            // enum case name -> value
      FnClo : Dict<string * int, string>     // fn used as value -> global clo
      CloInits : Vec<string>                 // closure singletons: BEFORE all global inits
      VSlot : Dict<string * string, int>     // (bare iface, member) -> slot
      IfaceRep : Dict<string, int>           // bare iface -> representative slot
      VWrap : Dict<string * int, string>     // member fn -> uniform wrapper
      ClassBase : Dict<string, string>       // class -> base
      ClassImpls : Dict<string, (string * (string * VarId) list) list>
      ClassOwn : Dict<string, (string * VarId) list>
      Intrin : Dict<string * int, string>    // member fn -> runtime intrinsic:
                                             // WeakReference / CWT members get
                                             // REAL weak semantics on fpprt
      mutable NVSlots : int
      mutable NextTid : int
      mutable NextLam : int
      Checked : bool }

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
      Locals : Dict<string * int, int>       // >= 0: V slot; < 0: raw local
                                             // at RawVars.[-(v)-1]
      Cells : Dict<string * int, bool>       // locals boxed in cells
      RawVars : Vec<char * string>           // rawified locals: kind, C name
      mutable NRaw : int
      RawDecls : Vec<string> }               // C declarations for raw locals

let private slot (f : CFn) : int =
    let i = f.NSlots
    f.NSlots <- i + 1
    i

let private stmt (f : CFn) (s : string) : unit = vecAdd f.Body ("  " + s)
let private sref (i : int) : string = "F[" + string i + "]"

// ---- raw (unboxed) values -------------------------------------------------
// Kinds: 'i' int32_t (also uint32/bool/char storage), 'l' int64_t (also
// uint64), 'f' double, 's' float. 'v' marks the uniform V fallback. Raw
// locals are plain C locals — never GC refs, so the tracer ignores them.

let private rawTy (k : char) : string =
    if k = 'l' then "int64_t"
    elif k = 'v' then "uint64_t"
    elif k = 'w' then "uint32_t"
    elif k = 'f' then "double"
    elif k = 's' then "float"
    else "int32_t"

let private rawNew (f : CFn) (k : char) : string =
    let i = f.NRaw
    f.NRaw <- i + 1
    let n = "R" + string i
    vecAdd f.RawDecls (rawTy k + " " + n + " = 0;")
    n

/// box a raw value into a fresh V slot ('V' atoms are already uniform)
let private boxRaw (f : CFn) (k : char) (atom : string) : int =
    let d = slot f
    if k = 'V' then stmt f (sref d + " = " + atom + ";")
    elif k = 'l' then stmt f (sref d + " = fpp_box_i64(" + atom + ");")
    elif k = 'v' then stmt f (sref d + " = fpp_box_i64((int64_t)" + atom + ");")
    elif k = 'f' then stmt f (sref d + " = fpp_box_f64(" + atom + ");")
    elif k = 's' then stmt f (sref d + " = fpp_box_f64((double)" + atom + ");")
    else stmt f (sref d + " = TAGI((intptr_t)" + atom + ");")
    d

/// a C expression converting a V atom to raw kind k
let private unboxExpr (k : char) (vatom : string) : string =
    if k = 'l' then "fpp_unbox_i64(" + vatom + ")"
    elif k = 'v' then "(uint64_t)fpp_unbox_i64(" + vatom + ")"
    elif k = 'w' then "(uint32_t)UNTAGI(" + vatom + ")"
    elif k = 'f' then "fpp_unbox_f64(" + vatom + ")"
    elif k = 's' then "(float)fpp_unbox_f64(" + vatom + ")"
    else "(int32_t)UNTAGI(" + vatom + ")"

/// numeric conversion between raw kinds as a C expression
let private convExpr (kFrom : char) (kTo : char) (atom : string) : string =
    if kFrom = kTo then atom
    else "(" + rawTy kTo + ")" + atom

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

let private mathSet (b : string) : bool =
    b = "abs" || b = "sqrt" || b = "floor" || b = "ceil"
    || b = "truncate" || b = "round" || b = "sign" || b = "exp"
    || b = "log" || b = "log2" || b = "log10" || b = "sin" || b = "cos"
    || b = "tan" || b = "asin" || b = "acos" || b = "atan"
    || b = "sinh" || b = "cosh" || b = "tanh"

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

/// scalar-array info for a CONCRETE element type name: the runtime tid
/// macro, the typed-accessor suffix, and the element's raw kind. int16 and
/// sbyte stay in ref arrays — unsigned storage would lose their sign.
let private elemInfo (nm : string) : (string * string * char) option =
    match nm with
    | "float" | "double" -> Some ("FPP_TID_AF64", "f64", 'f')
    | "float32" | "single" -> Some ("FPP_TID_AF32", "f32", 's')
    | "int64" | "uint64" -> Some ("FPP_TID_AI64", "i64", 'l')
    | "int" | "enum" | "uint32" -> Some ("FPP_TID_AI32", "i32", 'i')
    | "char" | "uint16" -> Some ("FPP_TID_AU16", "u16", 'i')
    | "byte" | "bool" -> Some ("FPP_TID_AU8", "u8", 'i')
    | _ -> None

/// the raw kind a CONCRETE monomorphized type stores at, or None (uniform)
let private schemeRawKind (sc : Scheme) : char option =
    match prune sc.Body with
    | TCon ("int", []) | TCon ("bool", []) | TCon ("char", [])
    | TCon ("byte", []) | TCon ("sbyte", [])
    | TCon ("int16", []) | TCon ("uint16", []) -> Some 'i'
    | TCon ("uint32", []) -> Some 'w'
    | TCon ("int64", []) -> Some 'l'
    | TCon ("uint64", []) -> Some 'v'
    | TCon ("float", []) -> Some 'f'
    | TCon ("float32", []) -> Some 's'
    | _ -> None

/// an int literal's (digits, suffix) — the same trimming the V emitter does
let private intLitParts (s : string) : string * string =
    let mutable cut = strLen s
    while cut > 0 && (let c = charAt s (cut - 1) in
                      c = 'L' || c = 'l' || c = 'u' || c = 'U'
                      || c = 'y' || c = 's' || c = 'n') && cut > 1
          && not (cut = strLen s && strLen s >= 2 && charAt s 0 = '0'
                  && (charAt s 1 = 'x' || charAt s 1 = 'X') && cut <= 2) do
        cut <- cut - 1
    s.Substring (0, cut), s.Substring cut

/// the raw kind an expression can be computed at WITHOUT boxing, or None.
/// PURE — must not emit; emitRaw relies on this to decide before writing.
let rec private rawKindOf (f : CFn) (e : Expr) : char option =
    match e with
    | ELit (LInt s) ->
        let _, suf = intLitParts s
        if suf.Contains "L" || suf.Contains "l" then Some 'l' else Some 'i'
    | ELit (LFloat s) -> Some (if s.EndsWith "f" then 's' else 'f')
    | ELit (LBool _) -> Some 'i'
    | ELit (LChar _) -> Some 'i'
    | EVar (v, _) | EVarI (v, _, _) ->
        (match dictTryFind f.Locals (v.Path, v.Offset) with
         | Some i when i < 0 ->
             let k, _ = vecGet f.RawVars (-i - 1)
             Some k
         | _ -> None)
    | EPrim (op0, [ a; b ]) ->
        let op, k = opBase op0
        let numk =
            if k = 'f' then Some 'f'
            elif k = 's' || k = 'h' then Some 's'
            elif k = 'l' then Some 'l'
            elif k = 'v' then Some 'v'
            elif k = 'w' then Some 'w'
            elif k = 'i' || k = 'b' || k = 'c' then Some 'i'
            else None
        (match op with
         | "+" when k = 's' || k = 't' -> None       // string concat
         | "%" when k = 'f' || k = 's' || k = 'h' -> None
         | "+" | "-" | "*" | "/" | "%" ->
             (match numk with
              | Some x -> Some x
              | None ->
                  if k = '?' then
                      match rawKindOf f a, rawKindOf f b with
                      | Some 'i', Some 'i' -> Some 'i'
                      | _ -> None
                  else None)
         | "<" | ">" | "<=" | ">=" | "=" | "<>" ->
             (match numk with
              | Some _ -> Some 'i'
              | None ->
                  if k = '?' then
                      match rawKindOf f a, rawKindOf f b with
                      | Some ka, Some kb when ka = kb -> Some 'i'
                      | _ -> None
                  else None)
         | "&&&" | "|||" | "^^^" | "<<<" | ">>>" ->
             if k = 'l' then Some 'l'
             elif k = 'v' then Some 'v'
             elif k = 'w' then Some 'w'
             elif k = 'i' || k = 'b' then Some 'i'
             elif k = '?' && not (op = "<<<" || op = ">>>") then
                 (match rawKindOf f a, rawKindOf f b with
                  | Some 'i', Some 'i' -> Some 'i'
                  | _ -> None)
             else None
         | "&&" | "||" ->
             (match rawKindOf f a, rawKindOf f b with
              | Some 'i', Some 'i' -> Some 'i'
              | _ -> None)
         | _ -> None)
    | EPrim (op0, [ a ]) when op0.StartsWith "u-" && strLen op0 <= 3 ->
        let k = if strLen op0 > 2 then charAt op0 2 else '?'
        if k = 'f' then Some 'f'
        elif k = 's' || k = 'h' then Some 's'
        elif k = 'l' || k = 'v' then Some 'l'
        elif k = 'i' || k = 'b' || k = 'c' || k = 'w' then Some 'i'
        elif k = '?' then
            (match rawKindOf f a with Some 'i' -> Some 'i' | _ -> None)
        else None
    | EPrim (("~-" | "~-i"), [ _ ]) -> Some 'i'
    | EPrim ("~-f", [ _ ]) -> Some 'f'
    | EPrim (op0, [ _ ]) when op0.StartsWith "u~~~" ->
        let k = if strLen op0 > 4 then charAt op0 4 else '?'
        if k = 'l' then Some 'l'
        elif k = 'v' then Some 'v'
        elif k = 'w' then Some 'w'
        elif k = 'i' || k = 'b' then Some 'i'
        else None
    | EPrim (op0, [ _ ]) when (mathBase op0).IsSome ->
        // only FLOAT math goes raw ("sqrtf" etc); abs/sign stay dynamic
        let b = (mathBase op0).Value
        if b <> "abs" && b <> "sign" && strLen op0 = strLen b + 1
           && charAt op0 (strLen op0 - 1) = 'f' then Some 'f'
        else None
    | EIndex (nm, _, _) when nm <> "$str" ->
        (match elemInfo nm with
         | Some (_, _, k) -> Some k
         | None -> None)
    | EIf (_, t, e2) ->
        (match rawKindOf f t, rawKindOf f e2 with
         | Some ka, Some kb when ka = kb -> Some ka
         | _ -> None)
    | ESeq xs ->
        (match List.tryLast xs with
         | Some x -> rawKindOf f x
         | None -> None)
    | EApp (EUnknown n, [ _ ]) when n.StartsWith "float32" -> Some 's'
    | EApp (EUnknown n, [ _ ]) when n.StartsWith "float" -> Some 'f'
    | EApp (EUnknown n, [ _ ]) when n.StartsWith "int64" || n.StartsWith "uint64" ->
        Some 'l'
    | _ -> None

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

/// the FULL name wins before suffix stripping: "abs" must not lose its s
/// record lookups fall back to the BASE name: uniform representation makes
/// every stamp of a record identical, so "AdaptiveReduction$<#37983...>"
/// (a name the stamper never grounded) simply IS "AdaptiveReduction"
let private recBase (name : string) : string =
    match name.IndexOf "$" with
    | i when i > 0 -> name.Substring (0, i)
    | _ -> name

/// "StructTuple7" -> 7; the synthetic struct-tuple types are declared
/// nowhere — they register on first sight, fields Item1..ItemN
let private structTupleArity (name : string) : int option =
    let b = recBase name
    if b.StartsWith "StructTuple" && strLen b > 11 then
        let digits = b.Substring 11
        let mutable ok = strLen digits > 0
        for ch in digits do
            if not (isDigit ch) then ok <- false
        if ok then Some (int digits) else None
    else None

let private ensureStructTuple (st : CSt) (name : string) : unit =
    if not (dictTryFind st.RecTid name).IsSome then
        match structTupleArity name with
        | Some n ->
            let tid = freshTid st
            dictSet st.RecTid name tid
            dictSet st.RecFields name (List.init n (fun i -> "Item" + string (i + 1)))
            vecAdd st.Reg ("  fpp_reg_struct(" + string tid + ", " + string n
                           + ", 1, " + cstr name + ");")
        | None -> ()

let private recTidOf (st : CSt) (name : string) : int option =
    match dictTryFind st.RecTid name with
    | Some t -> Some t
    | None -> dictTryFind st.RecTid (recBase name)

/// the tid a TYPE TEST checks: stamps share their base's uniform repr, so
/// `:? Foo$<int>` collapses to Foo — instances may carry the base tid or a
/// SIBLING stamp's, and fpp_isa only walks upward
let private testTidOf (st : CSt) (name : string) : int option =
    match dictTryFind st.RecTid (recBase name) with
    | Some t -> Some t
    | None -> recTidOf st name

let private recFieldsOf (st : CSt) (name : string) : string list option =
    match dictTryFind st.RecFields name with
    | Some fs when not (List.isEmpty fs) -> Some fs
    | _ ->
        match dictTryFind st.RecFields (recBase name) with
        | Some fs when not (List.isEmpty fs) -> Some fs
        | other -> other

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
    // raw-able computation chains: compute UNBOXED, box once at this
    // uniform boundary (consumers wanting raw call emitRaw and skip it)
    | EPrim (_, [ _; _ ]) when (rawKindOf f e).IsSome ->
        let k, a = emitRaw st f e
        boxRaw f k a
    | EPrim (_, [ _ ]) when (rawKindOf f e).IsSome ->
        let k, a = emitRaw st f e
        boxRaw f k a
    | EApp (EUnknown _, [ _ ]) when (rawKindOf f e).IsSome ->
        let k, a = emitRaw st f e
        boxRaw f k a
    | EIndex _ when (rawKindOf f e).IsSome ->
        let k, a = emitRaw st f e
        boxRaw f k a
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
         | Some i when i < 0 ->
             // a RAW local read in uniform context: box at the use
             let k, n = vecGet f.RawVars (-i - 1)
             boxRaw f k n
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
        // RAW string out, no newline — printfn's format carries its own
        let x = emitE st f a
        stmt f ("fpp_prints(" + sref x + ");")
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
              | Some i when i >= 0 -> i
              | _ -> emitE st f inner)
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
    | EApp (EUnknown "$idhash", [ a ]) ->
        // object.GetHashCode with no override: the IDENTITY hash
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI((intptr_t)fpprt_idhash(" + sref x + "));")
        d
    | EApp (EUnknown "ignore", [ a ]) ->
        emitE st f a |> ignore
        unitV ()
    | EApp (EUnknown "failwith", [ a ]) ->
        // the payload is Failure(msg), exactly as the oracle wraps it — so
        // `with Failure msg -> ...` matches
        let x = emitE st f a
        (match dictTryFind st.CaseTid "Failure" with
         | Some tid ->
             let w = slot f
             stmt f (sref w + " = fpprt_alloc(" + string tid + ");")
             stmt f ("fpprt_write_ref(" + sref w + ", FPPOFF(1), " + sref x + ");")
             stmt f ("fpp_raise(" + sref w + ");")
         | None ->
             stmt f ("fpp_raise(" + sref x + ");"))
        unitV ()
    | EApp (EUnknown "raise", [ a ]) ->
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
    | EApp (EUnknown "$hasflag", [ a; b ]) ->
        let x = emitE st f a
        let y = emitE st f b
        let d = slot f
        stmt f (sref d + " = TAGI((UNTAGI(" + sref x + ") & UNTAGI(" + sref y
                + ")) == UNTAGI(" + sref y + "));")
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
        stmt f (sref d + " = " + (dictTryFind st.FnName (v.Path, v.Offset)).Value + "("
                + String.concat ", " (xs |> List.map sref) + ");")
        d
    | EApp (ECtor (cn, cs, []), args) when
          (dictTryFind st.CaseArity cn) = Some (List.length args)
          && not (List.isEmpty args) ->
        // a curried constructor applied: build the case directly
        emitE st f (ECtor (cn, cs, args))
    | EApp (h, []) ->
        // an empty application is its head — `Ctor (null)` lowers this way
        emitE st f h
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
    | EPrim (("&&" | "&&b" | "&&i"), [ a; b ]) ->
        // SHORT-CIRCUIT: the right side must not evaluate when the left
        // decides — `isNull x || x.f ...` depends on it
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = " + sref x + ";")
        stmt f ("if (UNTAGI(" + sref d + ")) {")
        let y = emitE st f b
        stmt f (sref d + " = " + sref y + ";")
        stmt f ("}")
        d
    | EPrim (("||" | "||b" | "||i"), [ a; b ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = " + sref x + ";")
        stmt f ("if (!UNTAGI(" + sref d + ")) {")
        let y = emitE st f b
        stmt f (sref d + " = " + sref y + ";")
        stmt f ("}")
        d
    | EPrim ("::", [ h; t ]) ->
        let x = emitE st f h
        let y = emitE st f t
        let d = slot f
        stmt f (sref d + " = fpp_cons(" + sref x + ", " + sref y + ");")
        d
    | EPrim ("@", [ a; b ]) ->
        // list append
        let x = emitE st f a
        let y = emitE st f b
        let d = slot f
        stmt f (sref d + " = fpp_append(" + sref x + ", " + sref y + ");")
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
         | "@" -> stmt f (sref d + " = fpp_append(" + sref x + ", " + sref y + ");")
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
    | EPrim (op0, [ a ]) when op0.StartsWith "u~~~" ->
        let x = emitE st f a
        let d = slot f
        let k = if strLen op0 > 4 then charAt op0 4 else '?'
        (match k with
         | 'l' -> stmt f (sref d + " = fpp_box_i64(~fpp_unbox_i64(" + sref x + "));")
         | 'v' -> stmt f (sref d + " = fpp_box_i64((int64_t)~(uint64_t)fpp_unbox_i64(" + sref x + "));")
         | 'w' -> stmt f (sref d + " = TAGI((intptr_t)(uint32_t)~(uint32_t)UNTAGI(" + sref x + "));")
         | _ -> stmt f (sref d + " = TAGI((intptr_t)(int32_t)~(int32_t)UNTAGI(" + sref x + "));"))
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
         | EApp (EUnknown "$forcecell", [ inner ]) ->
             // a class-level `let mutable`: the binding IS a cell, and
             // every read must deref — the oracle's cellScan marks exactly
             // this shape
             let x = emitE st f inner
             let l = slot f
             stmt f (sref l + " = fpp_cell_new(" + sref x + ");")
             dictSet f.Cells (v.Path, v.Offset) true
             dictSet f.Locals (v.Path, v.Offset) l
             emitE st f body
         | _ ->
             let isCell = (dictTryFind f.Cells (v.Path, v.Offset)).IsSome
             let rk, atom = emitRaw st f rhs
             if rk <> 'V' && not isCell then
                 // a local of KNOWN primitive kind lives in a raw C local;
                 // mutation stays raw, uniform uses box at the use site
                 let n = rawNew f rk
                 stmt f (n + " = " + atom + ";")
                 vecAdd f.RawVars (rk, n)
                 dictSet f.Locals (v.Path, v.Offset) (-(vecLen f.RawVars))
                 emitE st f body
             else
                 let x = if rk = 'V' then atom else sref (boxRaw f rk atom)
                 let l = slot f
                 if isCell then
                     stmt f (sref l + " = fpp_cell_new(" + x + ");")
                 else
                     stmt f (sref l + " = " + x + ";")
                 dictSet f.Locals (v.Path, v.Offset) l
                 emitE st f body)
    | EAssign (v, rhs) ->
        (match dictTryFind f.Locals (v.Path, v.Offset) with
         | Some l when l < 0 ->
             let k, n = vecGet f.RawVars (-l - 1)
             let atom = emitRawAs st f k rhs
             stmt f (n + " = " + atom + ";")
         | Some l ->
             let x = emitE st f rhs
             if (dictTryFind f.Cells (v.Path, v.Offset)).IsSome then
                 stmt f ("fpp_cell_set(" + sref l + ", " + sref x + ");")
             else
                 stmt f (sref l + " = " + sref x + ";")
         | None ->
             let x = emitE st f rhs
             match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g -> stmt f (g + " = " + sref x + ";")
             | None -> stmt f ("fpp_not_emitted(" + cstr ("assign " + v.Name) + ");"))
        unitV ()
    | EIf (c, t, e2) ->
        let ck, ca = emitRaw st f c
        let d = slot f
        if ck = 'V' then stmt f ("if (UNTAGI(" + ca + ")) {")
        else stmt f ("if (" + ca + ") {")
        let tv = emitE st f t
        stmt f (sref d + " = " + sref tv + ";")
        stmt f ("} else {")
        let ev = emitE st f e2
        stmt f (sref d + " = " + sref ev + ";")
        stmt f ("}")
        d
    | EWhile (c, b) ->
        stmt f ("for (;;) {")
        let ck, ca = emitRaw st f c
        if ck = 'V' then stmt f ("if (!UNTAGI(" + ca + ")) break;")
        else stmt f ("if (!(" + ca + ")) break;")
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
        ensureStructTuple st name
        (match recTidOf st name with
         | Some tid ->
             let order = (recFieldsOf st name).Value
             let d = slot f
             stmt f (sref d + " = fpprt_alloc(" + string tid + ");")
             // WeakReference holds its target through a REAL weak ref on
             // fpprt (the prelude body is strong — a wasm-GC limitation)
             let weakWrap = recBase name = "WeakReference"
             for fn2, v in fs do
                 if weakWrap && fn2 = "value" then
                     let x = emitE st f v
                     let w = slot f
                     stmt f (sref w + " = fpprt_weak_new(" + sref x + ");")
                     let idx = fieldIdx order fn2
                     stmt f ("fpprt_write_ref(" + sref d + ", "
                             + ("FPPOFF(" + string (idx + 1) + ")") + ", " + sref w + ");")
                 elif fn2 = "base" then
                     // the base constructor built a BASE instance; its
                     // fields are this layout's shared prefix — copy them
                     let b = emitE st f v
                     stmt f ("{ uint32_t NB = fpp_tfields_[fpprt_typeid(" + sref b + ")];")
                     stmt f ("for (uint32_t I = 0; I < NB; I++)")
                     stmt f ("  fpprt_write_ref(" + sref d + ", FPPOFF(I + 1), fpprt_read_ref("
                             + sref b + ", FPPOFF(I + 1))); }")
                 else
                     let x = emitE st f v
                     let idx = fieldIdx order fn2
                     if idx < 0 then
                         stmt f ("fpp_not_emitted(" + cstr ("field " + name + "." + fn2) + ");")
                     else
                         stmt f ("fpprt_write_ref(" + sref d + ", "
                                 + ("FPPOFF(" + string (idx + 1) + ")") + ", " + sref x + ");")
             // ConditionalWeakTable: field 0 becomes the ephemeron table —
             // its members are runtime intrinsics, the other fields unused
             if recBase name = "ConditionalWeakTable" then
                 stmt f ("fpp_cwt_init(" + sref d + ");")
             d
         | None -> trap ("record " + name))
    | ERecordExt (name, b, fs) ->
        (match recTidOf st name with
         | Some tid ->
             let src = emitE st f b
             let order = (recFieldsOf st name).Value
             let n = List.length order
             let d = slot f
             stmt f (sref d + " = fpprt_alloc(" + string tid + ");")
             // the source can be a BASE-class instance (a class ctor lowers as
             // an extension over the base ctor's result) — copy only the
             // fields the source OBJECT has, never the derived layout's count
             stmt f ("{ uint32_t NB = fpp_tfields_[fpprt_typeid(" + sref src + ")];")
             stmt f ("if (NB > " + string n + "u) NB = " + string n + "u;")
             stmt f ("for (uint32_t I = 0; I < NB; I++)")
             stmt f ("  fpprt_write_ref(" + sref d + ", FPPOFF(I + 1), fpprt_read_ref("
                     + sref src + ", FPPOFF(I + 1))); }")
             for fn2, v in fs do
                 let x = emitE st f v
                 let idx = fieldIdx order fn2
                 if idx >= 0 then
                     stmt f ("fpprt_write_ref(" + sref d + ", "
                             + ("FPPOFF(" + string (idx + 1) + ")") + ", " + sref x + ");")
             d
         | None -> trap ("record " + name))
    | EField (r, fname, owner) ->
        ensureStructTuple st owner
        (match recFieldsOf st owner with
         | Some order ->
             let x = emitE st f r
             let idx = fieldIdx order fname
             if idx < 0 then trap ("field " + owner + "." + fname)
             else
                 let d = slot f
                 if st.Checked then
                     stmt f ("fpp_chk(" + sref x + ", " + string idx + ", "
                             + cstr (owner + "." + fname) + ");")
                 stmt f (sref d + " = fpprt_read_ref(" + sref x + ", "
                         + ("FPPOFF(" + string (idx + 1) + ")") + ");")
                 d
         | None -> trap ("field of " + owner + "." + fname))
    | EFieldSet (r, fname, owner, v) ->
        ensureStructTuple st owner
        (match recFieldsOf st owner with
         | Some order ->
             let x = emitE st f r
             let y = emitE st f v
             let idx = fieldIdx order fname
             if idx < 0 then trap ("fieldset " + owner + "." + fname)
             else
                 if st.Checked then
                     stmt f ("fpp_chk(" + sref x + ", " + string idx + ", "
                             + cstr (owner + "." + fname) + ");")
                 stmt f ("fpprt_write_ref(" + sref x + ", "
                         + ("FPPOFF(" + string (idx + 1) + ")") + ", " + sref y + ");")
                 unitV ()
         | None -> trap ("fieldset of " + owner))
    | ECtor (cn, _, []) when
          (match dictTryFind st.CaseArity cn with Some a -> a > 0 | None -> false) ->
        // a payload-carrying constructor as a VALUE: its singleton closure
        let g = ctorCloGlobal st cn
        let d = slot f
        stmt f (sref d + " = " + g + ";")
        d
    | ECtor (cn, _, args) ->
        (match dictTryFind st.CaseTid cn with
         | Some tid ->
             let vs = args |> List.map (emitE st f)
             let d = slot f
             stmt f (sref d + " = fpprt_alloc(" + string tid + ");")
             vs |> List.iteri (fun i x ->
                 stmt f ("fpprt_write_ref(" + sref d + ", " + ("FPPOFF(" + string (i + 1) + ")")
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
        stmt f ("fpp_handler_push_(&H, __func__);")
        stmt f ("if (!setjmp(H.jb)) {")
        let bv = emitE st f body
        stmt f (sref d + " = " + sref bv + ";")
        stmt f ("fpp_try_pop2(&H);")
        stmt f ("} else {")
        stmt f ("fpp_hlog_('H', __func__, (void *)&H);")
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
    | EArray (nm, xs) ->
        (match elemInfo nm with
         | Some (tid, suffix, k) ->
             // typed literal: scalar array, elements stored RAW
             let atoms = xs |> List.map (emitRawAs st f k)
             let d = slot f
             stmt f (sref d + " = fpprt_alloc_array(" + tid + ", "
                     + string (List.length xs) + ");")
             atoms |> List.iteri (fun i a ->
                 stmt f ("fpp_arr_set_" + suffix + "(" + sref d + ", "
                         + string i + ", " + a + ");"))
             d
         | None ->
             let vs = xs |> List.map (emitE st f)
             let d = slot f
             stmt f (sref d + " = fpp_arr_new(" + string (List.length xs) + ");")
             vs |> List.iteri (fun i x ->
                 stmt f ("fpp_arr_set(" + sref d + ", " + string i + ", " + sref x + ");"))
             d)
    | EArrayCreate (nm, n, v) ->
        let nv = emitE st f n
        let d = slot f
        (match v, elemInfo nm with
         | EUnknown "$zero", Some (tid, _, _) ->
             // typed zeroCreate: a SCALAR array — the allocator zeroes
             stmt f (sref d + " = fpprt_alloc_array(" + tid + ", (size_t)UNTAGI("
                     + sref nv + "));")
         | EUnknown "$zero", None ->
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
         | _, Some (tid, suffix, k) ->
             stmt f (sref d + " = fpprt_alloc_array(" + tid + ", (size_t)UNTAGI("
                     + sref nv + "));")
             let a = emitRawAs st f k v
             stmt f ("{ size_t N = fpprt_array_len(" + sref d + ");")
             stmt f ("for (size_t I = 0; I < N; I++) fpp_arr_set_" + suffix
                     + "(" + sref d + ", I, " + a + "); }")
         | _, None ->
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
    | EIndexSet (nm, a, i, v) when nm <> "$str" && (elemInfo nm).IsSome ->
        let _, suffix, k = (elemInfo nm).Value
        let av = emitE st f a
        let ia = emitRawAs st f 'i' i
        let xa = emitRawAs st f k v
        stmt f ("fpp_arr_set_" + suffix + "(" + sref av + ", (size_t)" + ia
                + ", " + xa + ");")
        unitV ()
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
        let bareI =
            match tn.IndexOf "`" with
            | i when i > 0 -> tn.Substring (0, i)
            | _ -> tn
        (match dictTryFind st.IfaceRep bareI with
         | Some rep ->
             let d = slot f
             stmt f (sref d + " = TAGI(fpp_vt_has(" + sref xv + ", " + string rep + "));")
             d
         | None ->
             match testTidOf st tn with
             | Some tid ->
                 // classes: accept DERIVED and STAMPED tids via the chain
                 let d = slot f
                 stmt f (sref d + " = TAGI(fpp_isa(" + sref xv + ", " + string tid + "));")
                 d
             | None ->
                 match dictTryFind st.CaseTid tn with
                 | Some tid ->
                     let d = slot f
                     stmt f (sref d + " = TAGI(" + sref xv + " != 0 && !(" + sref xv
                             + " & 1) && fpprt_typeid(" + sref xv + ") == " + string tid + ");")
                     d
                 | None -> trap ("typetest " + tn))
    | EUnknown n when n.StartsWith "$class:Ordered:compare:" ->
        // a still-symbolic Ordered dictionary member: uniform values answer
        // it STRUCTURALLY, which is what the wasm backend's $cmpv does
        let d = slot f
        stmt f (sref d + " = fpp_cmpv_clo_;")
        d
    | EUnknown n when n.StartsWith "$zero:" ->
        // defaultof at the named type; a still-symbolic one gets the
        // reference zero, which is what canonical code means by it
        let tn = n.Substring 6
        let d = slot f
        (match tn with
         | "int" | "bool" | "char" | "byte" | "sbyte" | "int16"
         | "uint16" | "uint32" -> stmt f (sref d + " = TAGI(0);")
         | "float" | "float32" | "float16" -> stmt f (sref d + " = fpp_box_f64(0.0);")
         | "int64" | "uint64" -> stmt f (sref d + " = fpp_box_i64(0);")
         | _ -> stmt f (sref d + " = 0;"))
        d
    | EUnknown n when n.StartsWith "$sizeof:" ->
        // primitives at their widths, anything else at pointer width — the
        // oracle's own table and fallback
        let tn = n.Substring 8
        let size =
            match tn with
            | "byte" | "sbyte" | "bool" -> 1
            | "char" | "int16" | "uint16" | "float16" -> 2
            | "int" | "uint32" | "float32" -> 4
            | _ -> 8
        let d = slot f
        stmt f (sref d + " = TAGI(" + string size + ");")
        d
    | EUnknown "$zero" ->
        let d = slot f
        stmt f (sref d + " = 0;")
        d
    | EUnknown n when n.StartsWith "$class:Ordered:compare:" ->
        // a still-symbolic Ordered dictionary member: uniform values answer
        // it STRUCTURALLY, which is what the wasm backend's $cmpv does
        let d = slot f
        stmt f (sref d + " = fpp_cmpv_clo_;")
        d
    | EUnknown n when n.StartsWith "$zero:" ->
        // defaultof at the named type; a still-symbolic one gets the
        // reference zero, which is what canonical code means by it
        let tn = n.Substring 6
        let d = slot f
        (match tn with
         | "int" | "bool" | "char" | "byte" | "sbyte" | "int16"
         | "uint16" | "uint32" -> stmt f (sref d + " = TAGI(0);")
         | "float" | "float32" | "float16" -> stmt f (sref d + " = fpp_box_f64(0.0);")
         | "int64" | "uint64" -> stmt f (sref d + " = fpp_box_i64(0);")
         | _ -> stmt f (sref d + " = 0;"))
        d
    | EUnknown n when n.StartsWith "$sizeof:" ->
        // primitives at their widths, anything else at pointer width — the
        // oracle's own table and fallback
        let tn = n.Substring 8
        let size =
            match tn with
            | "byte" | "sbyte" | "bool" -> 1
            | "char" | "int16" | "uint16" | "float16" -> 2
            | "int" | "uint32" | "float32" -> 4
            | _ -> 8
        let d = slot f
        stmt f (sref d + " = TAGI(" + string size + ");")
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
                + sref sv + ", FPPOFF(1)); " + sref tv + " = fpprt_read_ref(" + sref sv + ", FPPOFF(2)); }")
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
                    + sref cur + ", FPPOFF(1));")
            emitPat st f q hv ok
            stmt f ("if (UNTAGI(" + sref ok + ")) " + sref cur + " = fpprt_read_ref("
                    + sref cur + ", FPPOFF(2));")
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
                         + sref sv + ", " + ("FPPOFF(" + string (i + 1) + ")") + ");")
                 emitPat st f q el ok)
         | None ->
             match dictTryFind st.EnumVal cn with
             | Some ev ->
                 stmt f ("if (" + sref sv + " != TAGI(" + string ev + ")) "
                         + sref ok + " = TAGI(0);")
             | None ->
                 stmt f (sref ok + " = fpp_not_emitted(" + cstr ("pat ctor " + cn) + ");"))
    | PTypeTest tn ->
        let bare =
            match tn.IndexOf "`" with
            | i when i > 0 -> tn.Substring (0, i)
            | _ -> tn
        (match dictTryFind st.IfaceRep bare with
         | Some rep ->
             stmt f ("if (!fpp_vt_has(" + sref sv + ", " + string rep + ")) "
                     + sref ok + " = TAGI(0);")
         | None ->
             match testTidOf st tn with
             | Some tid ->
                 // classes: accept DERIVED and STAMPED tids via the chain
                 stmt f ("if (!fpp_isa(" + sref sv + ", " + string tid + ")) "
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
               Locals = dictNew<string * int, int> (); Cells = f.Cells
               RawVars = vecNew<char * string> (); NRaw = 0
               RawDecls = vecNew<string> () }
    frees |> List.iteri (fun i k ->
        let l = slot lf
        stmt lf (sref l + " = fpprt_read_ref(self, " + ("FPPOFF(" + string (i + 3) + ")") + ");")
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
    for line in vecToList lf.RawDecls do vecAdd all ("  " + line)
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
        | Some l when l < 0 ->
            // captured RAW local: box the current value into the env
            let kk, n = vecGet f.RawVars (-l - 1)
            let b = boxRaw f kk n
            stmt f ("fpprt_write_ref(" + sref d + ", " + ("FPPOFF(" + string (i + 3) + ")") + ", "
                    + sref b + ");")
        | Some l ->
            stmt f ("fpprt_write_ref(" + sref d + ", " + ("FPPOFF(" + string (i + 3) + ")") + ", "
                    + sref l + ");")
        | None -> stmt f ("fpp_not_emitted(\"capture miss\");"))
    d

/// a uniform (self, args) wrapper around a member function, for vtables
and private vtWrapper (st : CSt) (mv : VarId) : string =
    match dictTryFind st.VWrap (mv.Path, mv.Offset) with
    | Some w -> w
    | None ->
        let fn =
            match dictTryFind st.FnName (mv.Path, mv.Offset) with
            | Some x -> x
            | None -> cname mv
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

/// the singleton closure for a payload-carrying constructor as a value
and private ctorCloGlobal (st : CSt) (cn : string) : string =
    let key = ("$ctor", strHash cn)
    match dictTryFind st.FnClo key with
    | Some g -> g
    | None ->
        let tid = (dictTryFind st.CaseTid cn).Value
        let arity = (dictTryFind st.CaseArity cn).Value
        let g = "clo_ctor_" + sane cn + "_" + string tid
        let code = "code_ctor_" + sane cn + "_" + string tid
        dictSet st.FnClo key g
        vecAdd st.Globals ("static V " + g + ";")
        vecAdd st.Fwd ("static V " + code + "(V self, V *args);")
        let body = vecNew<string> ()
        vecAdd body ("static V " + code + "(V self, V *args) {")
        vecAdd body "  (void)self;"
        vecAdd body ("  V r = fpprt_alloc(" + string tid + ");")
        for i in 0 .. arity - 1 do
            vecAdd body ("  fpprt_write_ref(r, " + ("FPPOFF(" + string (i + 1) + ")")
                         + ", args[" + string i + "]);")
        vecAdd body "  return r;"
        vecAdd body "}"
        vecAdd st.Out (String.concat "\n" (vecToList body))
        let ctid = freshTid st
        vecAdd st.Reg ("  fpp_reg_clo(" + string ctid + ", 0);")
        vecAdd st.CloInits ("  " + g + " = fpp_clo_new(" + string ctid
                            + ", (fpp_code_t)" + code + ", " + string arity + ", 0);")
        g

/// the singleton closure for a top-level function used as a value
and private fnCloGlobal (st : CSt) (v : VarId) : string =
    match dictTryFind st.FnClo (v.Path, v.Offset) with
    | Some g -> g
    | None ->
        let fn =
            match dictTryFind st.FnName (v.Path, v.Offset) with
            | Some x -> x
            | None -> cname v
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
              Locals = dictNew<string * int, int> (); Cells = cellLocals body
              RawVars = vecNew<char * string> (); NRaw = 0
              RawDecls = vecNew<string> () }
    let pnames = ps |> List.mapi (fun i (pv, _) -> "p" + string i, pv)
    List.iter2 (fun (pn, pv) ((_ : VarId), sc) ->
        let isCell = (dictTryFind f.Cells (pv.Path, pv.Offset)).IsSome
        match (if isCell then None else schemeRawKind sc) with
        | Some k ->
            // a param of PROVEN primitive type unboxes once at entry
            let n = rawNew f k
            stmt f (n + " = " + unboxExpr k pn + ";")
            vecAdd f.RawVars (k, n)
            dictSet f.Locals (pv.Path, pv.Offset) (-(vecLen f.RawVars))
        | None ->
            let l = slot f
            if isCell then
                stmt f (sref l + " = fpp_cell_new(" + pn + ");")
            else
                stmt f (sref l + " = " + pn + ";")
            dictSet f.Locals (pv.Path, pv.Offset) l) pnames ps
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
    for line in vecToList f.RawDecls do vecAdd all ("  " + line)
    for line in vecToList f.Body do vecAdd all line
    vecAdd all ("  FPPRT_LEAVE(Fr);")
    vecAdd all ("  return " + sref r + ";")
    vecAdd all "}"
    vecAdd st.Out (String.concat "\n" (vecToList all))

/// a member whose body is a runtime intrinsic: WeakReference and
/// ConditionalWeakTable get REAL weak semantics over fpprt's ephemerons —
/// the prelude bodies are strong because wasm-GC has no weak refs. The
/// receiver's payload sits in FIELD 0 (offset 8); out-params are cells.
and private emitIntrinFn (st : CSt) (name : string) (nps : int) (tag : string) : unit =
    let decl =
        "static V " + name + "("
        + String.concat ", " (List.init nps (fun i -> "V p" + string i)) + ")"
    vecAdd st.Fwd
        ("static V " + name + "("
         + String.concat ", " (List.init nps (fun _ -> "V")) + ");")
    let body =
        if tag = "weak.TryGetTarget" then
            "  V w = fpprt_read_ref(p0, FPPOFF(1));\n  V t = w ? fpprt_weak_get(w) : 0;\n  if (!t) return TAGI(0);\n  fpprt_write_ref(p1, FPPOFF(1), t);\n  return TAGI(1);"
        elif tag = "weak.Target" then
            "  V w = fpprt_read_ref(p0, FPPOFF(1));\n  return w ? fpprt_weak_get(w) : 0;"
        elif tag = "weak.IsAlive" then
            "  V w = fpprt_read_ref(p0, FPPOFF(1));\n  return TAGI((w && fpprt_weak_get(w)) ? 1 : 0);"
        elif tag = "cwt.TryGetValue" then
            // two source args arrive TUPLED in p1 unless the decl untuples
            (if nps >= 3
             then "  V t = fpp_cwt_tryget(p0, p1);\n  if (!t) return TAGI(0);\n  fpprt_write_ref(p2, FPPOFF(1), t);\n  return TAGI(1);"
             else "  V k = fpp_tuple_get(p1, 0);\n  V o = fpp_tuple_get(p1, 1);\n  V t = fpp_cwt_tryget(p0, k);\n  if (!t) return TAGI(0);\n  fpprt_write_ref(o, FPPOFF(1), t);\n  return TAGI(1);")
        elif tag = "cwt.Add" then
            (if nps >= 3
             then "  fpp_cwt_add(p0, p1, p2);\n  return VUNIT;"
             else "  fpp_cwt_add(p0, fpp_tuple_get(p1, 0), fpp_tuple_get(p1, 1));\n  return VUNIT;")
        elif tag = "cwt.Remove" then
            "  return fpp_cwt_remove(p0, p1);"
        elif tag = "cwt.Count" then
            "  return fpp_cwt_count(p0);"
        elif tag = "cwt.IndexOf" then
            "  return fpp_cwt_indexof(p0, p1);"
        else
            "  fpp_not_emitted(" + cstr ("intrinsic " + tag) + ");\n  return 0;"
    vecAdd st.Out (decl + " {\n" + body + "\n}")

/// emit e as a RAW value when rawKindOf admits it; ('V', "F[i]") otherwise.
/// Atoms are pure (locals, literals, casts of those) — all computation goes
/// through statements, so sequencing matches the V emitter exactly.
and private emitRaw (st : CSt) (f : CFn) (e : Expr) : char * string =
    match rawKindOf f e with
    | None -> 'V', sref (emitE st f e)
    | Some rk ->
        match e with
        | ELit (LInt s) ->
            let num, _ = intLitParts s
            rk, (if rk = 'l' then num + "LL" else num)
        | ELit (LFloat s) ->
            let t0 = if s.EndsWith "f" then s.Substring (0, strLen s - 1) else s
            let txt = if t0.EndsWith "." then t0 + "0" else t0
            rk, (if rk = 's' then "(float)" + txt else txt)
        | ELit (LBool b) -> 'i', (if b then "1" else "0")
        | ELit (LChar s) -> 'i', string (Fpp.Backend.BinDriver.charCode s)
        | EVar (v, _) | EVarI (v, _, _) ->
            let i = (dictTryFind f.Locals (v.Path, v.Offset)).Value
            let k, n = vecGet f.RawVars (-i - 1)
            k, n
        | EPrim (op0, [ a; b ]) ->
            let op, k0 = opBase op0
            (match op with
             | "+" | "-" | "*" | "/" | "%" ->
                 let aa = emitRawAs st f rk a
                 let ab = emitRawAs st f rk b
                 let n = rawNew f rk
                 if rk = 'i' then
                     // int32 wraparound, the shape the V emitter uses
                     stmt f (n + " = (int32_t)(" + aa + " " + op + " " + ab + ");")
                 else
                     stmt f (n + " = " + aa + " " + op + " " + ab + ";")
                 rk, n
             | "<" | ">" | "<=" | ">=" | "=" | "<>" ->
                 let cop = if op = "=" then "==" elif op = "<>" then "!=" else op
                 let okind =
                     if k0 = 'f' then 'f'
                     elif k0 = 's' || k0 = 'h' then 's'
                     elif k0 = 'l' then 'l'
                     elif k0 = 'v' then 'v'
                     elif k0 = 'w' then 'w'
                     elif k0 = 'i' || k0 = 'b' || k0 = 'c' then 'i'
                     else (match rawKindOf f a with Some x -> x | None -> 'i')
                 let aa = emitRawAs st f okind a
                 let ab = emitRawAs st f okind b
                 let n = rawNew f 'i'
                 stmt f (n + " = " + aa + " " + cop + " " + ab + ";")
                 'i', n
             | "&&&" | "|||" | "^^^" | "<<<" | ">>>" ->
                 let cop =
                     if op = "&&&" then "&" elif op = "|||" then "|"
                     elif op = "^^^" then "^"
                     elif op = "<<<" then "<<" else ">>"
                 let shift = op = "<<<" || op = ">>>"
                 let aa = emitRawAs st f rk a
                 let ab = emitRawAs st f (if shift then 'i' else rk) b
                 let n = rawNew f rk
                 if rk = 'i' && op = ">>>" then
                     // bare/int32 shift right stays ARITHMETIC in .NET
                     stmt f (n + " = " + aa + " >> " + ab + ";")
                 else
                     stmt f (n + " = " + aa + " " + cop + " " + ab + ";")
                 rk, n
             | "&&" | "||" ->
                 let aa = emitRawAs st f 'i' a
                 let ab = emitRawAs st f 'i' b
                 let n = rawNew f 'i'
                 stmt f (n + " = " + aa + " " + op + " " + ab + ";")
                 'i', n
             | _ -> 'V', sref (emitE st f e))
        | EPrim (op0, [ a ]) when op0.StartsWith "u~~~" ->
            let aa = emitRawAs st f rk a
            let n = rawNew f rk
            stmt f (n + " = ~" + aa + ";")
            rk, n
        | EPrim (op0, [ a ]) when op0.StartsWith "u-" || op0.StartsWith "~-" ->
            let aa = emitRawAs st f rk a
            let n = rawNew f rk
            stmt f (n + " = -" + aa + ";")
            rk, n
        | EPrim (op0, [ a ]) when (mathBase op0).IsSome ->
            let b = (mathBase op0).Value
            let cfn =
                if b = "truncate" then "__builtin_trunc"
                elif b = "round" then "fpp_round_even"
                else "__builtin_" + b
            let aa = emitRawAs st f 'f' a
            let n = rawNew f 'f'
            stmt f (n + " = " + cfn + "(" + aa + ");")
            'f', n
        | EIndex (nm, a, i) ->
            let acc = (elemInfo nm).Value
            let _, suffix, _ = acc
            let av = emitE st f a
            let ia = emitRawAs st f 'i' i
            let n = rawNew f rk
            stmt f (n + " = fpp_arr_get_" + suffix + "(" + sref av
                    + ", (size_t)" + ia + ");")
            rk, n
        | EIf (c, t, e2) ->
            let ck, ca = emitRaw st f c
            let n = rawNew f rk
            if ck = 'V' then stmt f ("if (UNTAGI(" + ca + ")) {")
            else stmt f ("if (" + ca + ") {")
            let ta = emitRawAs st f rk t
            stmt f (n + " = " + ta + ";")
            stmt f ("} else {")
            let ea = emitRawAs st f rk e2
            stmt f (n + " = " + ea + ";")
            stmt f ("}")
            rk, n
        | ESeq xs ->
            let rec go (rest : Expr list) : char * string =
                match rest with
                | [ last ] -> emitRaw st f last
                | x :: more ->
                    emitE st f x |> ignore
                    go more
                | [] -> 'V', sref (emitE st f e)
            go xs
        | EApp (EUnknown _, [ a ]) ->
            // a conversion rawKindOf admitted: float / float32 / int64 / uint64
            let k1, a1 = emitRaw st f a
            if k1 = 'V' then
                // dynamic conversion on a uniform value, then unbox
                let d = slot f
                if rk = 'f' || rk = 's' then
                    stmt f (sref d + " = fpp_to_f64(" + a1 + ");")
                else
                    stmt f (sref d + " = fpp_to_i64(" + a1 + ");")
                let n = rawNew f rk
                stmt f (n + " = " + unboxExpr rk (sref d) + ";")
                rk, n
            else
                rk, convExpr k1 rk a1
        | _ -> 'V', sref (emitE st f e)

/// emit e as raw kind k, coercing as needed
and private emitRawAs (st : CSt) (f : CFn) (k : char) (e : Expr) : string =
    let k1, a1 = emitRaw st f e
    if k1 = k then a1
    elif k1 = 'V' then
        let n = rawNew f k
        stmt f (n + " = " + unboxExpr k a1 + ";")
        n
    else convExpr k1 k a1

// ---- whole program --------------------------------------------------------

let emitC (decls : Decl list) : string * string list =
    let st =
        { Out = vecNew<string> (); Fwd = vecNew<string> ()
          Globals = vecNew<string> (); Inits = vecNew<string> ()
          Reg = vecNew<string> ()
          Fns = dictNew<string * int, int> ()
          FnName = dictNew<string * int, string> ()
          GlobalOf = dictNew<string * int, string> ()
          RecTid = dictNew<string, int> ()
          RecFields = dictNew<string, string list> ()
          CaseTid = dictNew<string, int> ()
          CaseArity = dictNew<string, int> ()
          EnumVal = dictNew<string, int> ()
          FnClo = dictNew<string * int, string> ()
          CloInits = vecNew<string> ()
          VSlot = dictNew<string * string, int> ()
          IfaceRep = dictNew<string, int> ()
          VWrap = dictNew<string * int, string> ()
          ClassBase = dictNew<string, string> ()
          ClassImpls = dictNew<string, (string * (string * VarId) list) list> ()
          ClassOwn = dictNew<string, (string * VarId) list> ()
          Intrin = dictNew<string * int, string> ()
          NVSlots = 0
          NextTid = 32                          // FPP_TID_USER in fpprt-lang.h
          NextLam = 0
          // FPP_CBACK_CHECK=1: every field access validates its receiver
          // and index against the runtime type table before touching memory
          Checked = System.Environment.GetEnvironmentVariable "FPP_CBACK_CHECK" = "1" }
    // pass 1: names, record layouts, union cases, enums
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) ->
            dictSet st.Fns (v.Path, v.Offset) (List.length ps)
            dictSet st.FnName (v.Path, v.Offset) (cname v)
        | DLet (_, v, _, _) ->
            dictSet st.GlobalOf (v.Path, v.Offset) (gname v)
        | DRecord (n, _, fields, _) ->
            if not (dictTryFind st.RecTid n).IsSome then
                let tid = freshTid st
                dictSet st.RecTid n tid
                dictSet st.RecFields n (fields |> List.map fst)
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
        | DClass (n, b, own, impls) ->
            (match b with Some x -> dictSet st.ClassBase n x | None -> ())
            dictSet st.ClassImpls n impls
            dictSet st.ClassOwn n own
            // WeakReference / ConditionalWeakTable: the prelude bodies are
            // STRONG (wasm-GC has no weak refs); fpprt has real ephemerons,
            // so their members route to runtime intrinsics here
            let cbase = recBase n
            if cbase = "WeakReference" then
                for mn, mv in own do
                    if mn = "TryGetTarget" || mn = "Target" || mn = "IsAlive" then
                        dictSet st.Intrin (mv.Path, mv.Offset) ("weak." + mn)
            if cbase = "ConditionalWeakTable" then
                for mn, mv in own do
                    if mn = "TryGetValue" || mn = "Add" || mn = "Remove"
                       || mn = "Count" || mn = "IndexOf" then
                        dictSet st.Intrin (mv.Path, mv.Offset) ("cwt." + mn)
            for iface, ms in impls do
                let bare =
                    match iface.IndexOf "`" with
                    | i when i > 0 -> iface.Substring (0, i)
                    | _ -> iface
                for mn, _ in ms do
                    if not (dictTryFind st.VSlot (bare, mn)).IsSome then
                        dictSet st.VSlot (bare, mn) st.NVSlots
                        st.NVSlots <- st.NVSlots + 1
        | DMembers (n, ms) ->
            // abstract/overridable members dispatched through the class:
            // the slot keys by the DECLARING class's bare name
            let bare = recBase n
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
                if not (dictTryFind st.IfaceRep bare).IsSome then
                    dictSet st.IfaceRep bare (dictTryFind st.VSlot (bare, mn)).Value
        | DMembers (n, ms) ->
            // abstract/overridable members dispatched through the CLASS:
            // slots key by the declaring class's bare name
            let bare = recBase n
            for mn, _ in ms do
                if not (dictTryFind st.VSlot (bare, mn)).IsSome then
                    dictSet st.VSlot (bare, mn) st.NVSlots
                    st.NVSlots <- st.NVSlots + 1
        | _ -> ()
    // FINAL LAYOUTS. Three rules, applied in order:
    //   1. a stamped clone with an empty field list inherits its base
    //      name's OWN fields (uniform repr: every stamp is identical);
    //   2. a CLASS lays out as its chain root-first — base fields form a
    //      shared prefix, so a field index computed against any ancestor
    //      is valid on every descendant instance;
    //   3. registration carries the final count.
    let ownFieldsOf (n : string) : string list =
        match dictTryFind st.RecFields n with
        | Some fs when not (List.isEmpty fs) -> fs
        | _ ->
            match dictTryFind st.RecFields (recBase n) with
            | Some fs -> fs
            | None -> []
    let chainRootFirst (n0 : string) : string list =
        let out = vecNew<string> ()
        let seen = dictNew<string, bool> ()
        let mutable cur = n0
        let mutable go = true
        let mutable steps = 0
        while go && steps < 64 do
            if (dictTryFind seen cur).IsSome then go <- false
            else
                dictSet seen cur true
                vecAdd out cur
                steps <- steps + 1
                match dictTryFind st.ClassBase cur with
                | Some b -> cur <- b
                | None ->
                    let bb = recBase cur
                    if bb <> cur && ((dictTryFind st.ClassBase bb).IsSome
                                     || (dictTryFind st.ClassOwn bb).IsSome) then cur <- bb
                    else go <- false
        List.rev (vecToList out)
    let full = dictNew<string, string list> ()
    for n, _ in dictPairs st.RecTid do
        let isClass =
            (dictTryFind st.ClassOwn n).IsSome || (dictTryFind st.ClassBase n).IsSome
            || (dictTryFind st.ClassOwn (recBase n)).IsSome
            || (dictTryFind st.ClassBase (recBase n)).IsSome
        let layout =
            if isClass then
                chainRootFirst n |> List.collect ownFieldsOf
            else ownFieldsOf n
        dictSet full n layout
    for n, layout in dictPairs full do
        dictSet st.RecFields n layout
        let isClass =
            (dictTryFind st.ClassOwn n).IsSome || (dictTryFind st.ClassBase n).IsSome
            || (dictTryFind st.ClassOwn (recBase n)).IsSome
            || (dictTryFind st.ClassBase (recBase n)).IsSome
        // records compare STRUCTURALLY, classes by IDENTITY — a cyclic
        // object graph (the adaptive one) must never be walked by eqv
        let tclass = if isClass then 4 else 1
        match dictTryFind st.RecTid n with
        | Some tid ->
            vecAdd st.Reg ("  fpp_reg_struct(" + string tid + ", "
                           + string (List.length layout) + ", " + string tclass
                           + ", " + cstr n + ");")
            // the tid's PARENT: a stamped clone's parent is its canonical
            // base, a plain class's is its declared base — `:? Base`
            // accepts the whole chain through fpp_isa
            if isClass then
                let pname =
                    if recBase n <> n then recBase n
                    else
                        match dictTryFind st.ClassBase n with
                        | Some b -> b
                        | None -> n
                if pname <> n then
                    match dictTryFind st.RecTid pname with
                    | Some ptid when ptid <> tid ->
                        vecAdd st.Reg ("  fpp_reg_parent(" + string tid + ", "
                                       + string ptid + ");")
                    | _ -> ()
        | None -> ()
    // pass 1.5: vtables — every class registers its impl chain's members
    // (nearest declaration wins, walking the base chain)
    let vtReg = vecNew<string> ()
    // the full ancestor chain of a class name: bases, and each stamped
    // name's canonical base (a stamped decl lists only what stamping saw)
    let chainOf (n0 : string) : string list =
        let out = vecNew<string> ()
        let seen = dictNew<string, bool> ()
        let mutable cur = n0
        let mutable steps = 0
        let mutable go = true
        while go && steps < 64 do
            if (dictTryFind seen cur).IsSome then go <- false
            else
                dictSet seen cur true
                vecAdd out cur
                steps <- steps + 1
                match dictTryFind st.ClassBase cur with
                | Some b -> cur <- b
                | None ->
                    let bb = recBase cur
                    if bb <> cur then cur <- bb else go <- false
        vecToList out
    for d in decls do
        match d with
        | DClass (n, _, _, _) ->
            (match dictTryFind st.RecTid n with
             | Some tid ->
                 let filled = dictNew<int, bool> ()
                 let chain = chainOf n
                 let bareChain = chain |> List.map recBase |> List.distinct
                 // the NEAREST override of a member name anywhere in the
                 // chain: an interface slot recorded against a BASE class's
                 // implementation still dispatches to the subclass override
                 let nearestOwn = dictNew<string, VarId> ()
                 for cur in chain do
                     match dictTryFind st.ClassOwn cur with
                     | Some own ->
                         for mn, mv in own do
                             if not (dictTryFind nearestOwn mn).IsSome
                                && (dictTryFind st.Fns (mv.Path, mv.Offset)).IsSome then
                                 dictSet nearestOwn mn mv
                     | None -> ()
                 // a class defining CompareTo gets a dispatch slot even when
                 // no interface asked: `compare` on the class must use ITS
                 // ordering, never identity order
                 (match dictTryFind nearestOwn "CompareTo" with
                  | Some mv when (dictTryFind st.Fns (mv.Path, mv.Offset)) = Some 2 ->
                      let key = (recBase n, "CompareTo")
                      let sl =
                          match dictTryFind st.VSlot key with
                          | Some x -> x
                          | None ->
                              let x = st.NVSlots
                              st.NVSlots <- x + 1
                              dictSet st.VSlot key x
                              x
                      let w = vtWrapper st mv
                      vecAdd vtReg ("  fpp_vt_set(" + string tid + ", " + string sl
                                    + ", " + w + ");")
                      vecAdd vtReg ("  fpp_reg_cmp(" + string tid + ", " + string sl + ");")
                  | _ -> ())
                 // same for Equals / GetHashCode: a class overriding them
                 // is VALUE-keyed in dictionaries, the way the oracle keys
                 // it — identity hashing loses logically-equal instances
                 let regDisp (mn : string) (arity : int) (reg : string) =
                     match dictTryFind nearestOwn mn with
                     | Some mv when
                         (let a = dictTryFind st.Fns (mv.Path, mv.Offset)
                          // a nullary member may carry a UNIT param
                          a = Some arity || (arity = 1 && a = Some 2)) ->
                         let key = (recBase n, mn)
                         let sl =
                             match dictTryFind st.VSlot key with
                             | Some x -> x
                             | None ->
                                 let x = st.NVSlots
                                 st.NVSlots <- x + 1
                                 dictSet st.VSlot key x
                                 x
                         let w = vtWrapper st mv
                         vecAdd vtReg ("  fpp_vt_set(" + string tid + ", " + string sl
                                       + ", " + w + ");")
                         vecAdd vtReg ("  " + reg + "(" + string tid + ", " + string sl + ");")
                     | _ -> ()
                 regDisp "Equals" 2 "fpp_reg_eq"
                 regDisp "GetHashCode" 1 "fpp_reg_hash"
                 let fill (sl : int) (mv : VarId) =
                     if not (dictTryFind filled sl).IsSome
                        // a DCE'd member body has no function to point at;
                        // its slot stays empty and traps only if reached
                        && (dictTryFind st.Fns (mv.Path, mv.Offset)).IsSome then
                         dictSet filled sl true
                         let w = vtWrapper st mv
                         vecAdd vtReg ("  fpp_vt_set(" + string tid + ", "
                                       + string sl + ", " + w + ");")
                 for cur in chain do
                     // interface implementations: keyed by the iface
                     (match dictTryFind st.ClassImpls cur with
                      | Some impls ->
                          for iface, ms in impls do
                              let bare =
                                  match iface.IndexOf "`" with
                                  | i when i > 0 -> iface.Substring (0, i)
                                  | _ -> iface
                              for mn, mv in ms do
                                  let target =
                                      match dictTryFind nearestOwn mn with
                                      | Some ov -> ov
                                      | None -> mv
                                  match dictTryFind st.VSlot (bare, mn) with
                                  | Some sl -> fill sl target
                                  | None -> ()
                      | None -> ())
                     // OWN members answer abstract dispatch keyed by ANY
                     // ancestor class that declares the member's slot
                     (match dictTryFind st.ClassOwn cur with
                      | Some own ->
                          for mn, mv in own do
                              for a in bareChain do
                                  match dictTryFind st.VSlot (a, mn) with
                                  | Some sl -> fill sl mv
                                  | None -> ()
                      | None -> ())
                 // DUCK-TYPED seq protocol: F# accepts any class with
                 // MoveNext/Current as an enumerator and GetEnumerator as a
                 // seq, no interface required — but GENERIC consumption
                 // dispatches through the IEnumerator/IEnumerable slots, so
                 // a duck class answers those too (explicit impls, filled
                 // above, win)
                 for mn, iface in [ "MoveNext", "IEnumerator"
                                    "Current", "IEnumerator"
                                    "Dispose", "IEnumerator"
                                    "Dispose", "IDisposable"
                                    "GetEnumerator", "IEnumerable" ] do
                     match dictTryFind nearestOwn mn with
                     | Some mv ->
                         (match dictTryFind st.VSlot (iface, mn) with
                          | Some sl -> fill sl mv
                          | None -> ())
                     | None -> ()
             | None -> ())
        | _ -> ()
    // builtin seq protocol: arrays, lists, strings and tuples answer
    // IEnumerable/IEnumerator through runtime enumerators, wired into THIS
    // program's slot numbers
    (match dictTryFind st.VSlot ("IEnumerable", "GetEnumerator") with
     | Some sl ->
         for tid in [ "FPP_TID_ARR"; "FPP_TID_CONS"; "FPP_TID_STR"; "FPP_TID_TUPLE"
                      "FPP_TID_AF64"; "FPP_TID_AF32"; "FPP_TID_AI64"
                      "FPP_TID_AI32"; "FPP_TID_AU16"; "FPP_TID_AU8" ] do
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
    // a NULL receiver on these slots is the EMPTY SEQUENCE (null is the
    // empty list) — fpp_vcall needs the program's slot numbers to know
    let slotOr (k : string * string) : string =
        match dictTryFind st.VSlot k with
        | Some s -> string s
        | None -> "-1"
    vecAdd vtReg ("  fpp_seq_slots(" + slotOr ("IEnumerable", "GetEnumerator")
                  + ", " + slotOr ("IEnumerator", "MoveNext")
                  + ", " + slotOr ("IEnumerator", "Dispose") + ");")
    // pass 2: emission
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            (match dictTryFind st.Intrin (v.Path, v.Offset) with
             | Some tag -> emitIntrinFn st (cname v) (List.length ps) tag
             | None -> emitFn st (cname v) ps body)
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
    (match dictTryFind st.CaseTid "Failure" with
     | Some tid -> vecAdd out ("  fpp_failure_tid_ = " + string tid + ";")
     | None -> ())
    for g in vecToList st.Globals do
        let n = g.Substring (9, strLen g - 10)
        vecAdd out ("  fpprt_add_static_roots(&" + n + ", 1);")
    // the slot map as comments: which (iface, member) each number means
    for k, sl in dictPairs st.VSlot do
        let iface, mem = k
        vecAdd out ("  /* slot " + string sl + " = " + iface + "." + mem + " */")
    for t in vecToList st.Reg do vecAdd out t
    for t in vecToList vtReg do vecAdd out t
    for i in vecToList st.CloInits do vecAdd out i
    for i in vecToList st.Inits do vecAdd out i
    vecAdd out "  return 0;"
    vecAdd out "}"
    String.concat "" ((vecToList out) |> List.map (fun l -> l + "\n")), []

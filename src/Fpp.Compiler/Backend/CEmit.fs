module Fpp.Backend.CEmit

// The C backend: the SAME post-Link declarations the wasm-GC backend
// consumes, emitted as one C file against the fpprt runtime (runtime/).
// One emitter, two targets — gcc for native, emcc for wasm-linear — and
// the wasm-GC backend is the ORACLE: every construct this learns is gated
// on printing exactly what that backend prints.
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

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir

type CSt =
    { Out : Vec<string>                    // completed function definitions
      Fwd : Vec<string>                    // forward declarations
      Globals : Vec<string>                // global V slots
      Inits : Vec<string>                  // statements for fpp_main, in order
      TypeReg : Vec<string>                // fpprt_register_type calls
      Errors : Vec<string>
      Fns : Dict<string * int, int>        // (path,offset) -> arity of top-level fn
      GlobalOf : Dict<string * int, string>  // (path,offset) -> C global name
      mutable NextTid : int }

let private isIdentChar (c : char) = isLetterOrDigit c || c = '_'

let private cname (v : VarId) : string =
    "f_" + string (abs (strHash v.Path % 1000)) + "_" + string v.Offset + "_"
    + (v.Name |> String.map (fun c -> if isIdentChar c then c else '_'))

let private gname (v : VarId) : string =
    "g_" + string (abs (strHash v.Path % 1000)) + "_" + string v.Offset + "_"
    + (v.Name |> String.map (fun c -> if isIdentChar c then c else '_'))

/// a C string literal from source-text bytes
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
            // close and reopen the literal: a C hex escape is GREEDY, and
            // "\xbb" followed by 'r' would read as the escape \xbbr
            vecAdd out ("\\x" + (let h = "0123456789abcdef" in
                                 string (charAt h ((int ch >>> 4) &&& 15)) + string (charAt h (int ch &&& 15)))
                        + "\" \"")
        else vecAdd out (string ch)
    vecAdd out "\""
    String.concat "" (vecToList out)

// ---- per-function emission ------------------------------------------------
// Statements accumulate in `body`; every expression's value lands in a
// frame SLOT (S(i)), so the emitter returns slot indices, not C
// expressions. Slots double as GC roots.

type CFn =
    { Body : Vec<string>
      mutable NSlots : int
      Locals : Dict<string * int, int> }   // VarId key -> slot

let private slot (f : CFn) : int =
    let i = f.NSlots
    f.NSlots <- i + 1
    i

let private stmt (f : CFn) (s : string) : unit = vecAdd f.Body ("  " + s)

let private sref (i : int) : string = "F[" + string i + "]"

let rec private emitE (st : CSt) (f : CFn) (e : Expr) : int =
    match e with
    | ELit (LInt s) ->
        let d = slot f
        stmt f (sref d + " = TAGI(" + s + "L);")
        d
    | ELit (LBool b) ->
        let d = slot f
        stmt f (sref d + " = TAGI(" + (if b then "1" else "0") + ");")
        d
    | ELit (LChar s) ->
        let d = slot f
        stmt f (sref d + " = TAGI(" + string (int (charAt s 0)) + ");")
        d
    | ELit LUnit ->
        let d = slot f
        stmt f (sref d + " = VUNIT;")
        d
    | ELit LNull ->
        let d = slot f
        stmt f (sref d + " = 0;")
        d
    | ELit (LFloat s) ->
        let d = slot f
        let txt = if s.EndsWith "f" then s.Substring (0, strLen s - 1) else s
        stmt f (sref d + " = fpp_box_f64(" + txt + ");")
        d
    | ELit (LString s) ->
        let d = slot f
        stmt f (sref d + " = fpp_str_c(" + cstr s + ", " + string (strLen s) + ");")
        d
    | EVar (v, _) | EVarI (v, _, _) ->
        (match dictTryFind f.Locals (v.Path, v.Offset) with
         | Some i -> i
         | None ->
             match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g ->
                 let d = slot f
                 stmt f (sref d + " = " + g + ";")
                 d
             | None ->
                 // a top-level FUNCTION used as a value — M4 (closures)
                 let d = slot f
                 stmt f (sref d + " = fpp_not_emitted(" + cstr ("fn value " + v.Name) + ");")
                 d)
    | EApp (EUnknown "print", [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f ("fpp_print(" + sref x + ");")
        stmt f (sref d + " = VUNIT;")
        d
    | EApp (EUnknown ("string" | "string#"), [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = fpp_to_string(" + sref x + ");")
        d
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when (dictTryFind st.Fns (v.Path, v.Offset)).IsSome ->
        let arity = (dictTryFind st.Fns (v.Path, v.Offset)).Value
        if List.length args <> arity then
            let d = slot f
            stmt f (sref d + " = fpp_not_emitted(" + cstr ("partial app " + v.Name) + ");")
            d
        else
            let xs = args |> List.map (emitE st f)
            let d = slot f
            stmt f (sref d + " = " + cname v + "("
                    + String.concat ", " (xs |> List.map sref) + ");")
            d
    | EPrim (op0, [ a; b ]) ->
        // operators arrive KIND-SUFFIXED from lowering ("=i", "+f", "<l");
        // the tagged-int forms strip the suffix, boxed kinds join later
        let op =
            if strLen op0 >= 2 then
                let last = charAt op0 (strLen op0 - 1)
                let head = op0.Substring (0, strLen op0 - 1)
                if (last = 'i' || last = 'b' || last = 'c')
                   && (head = "+" || head = "-" || head = "*" || head = "/" || head = "%"
                       || head = "=" || head = "<>" || head = "<" || head = ">"
                       || head = "<=" || head = ">=") then head
                else op0
            else op0
        let x = emitE st f a
        let y = emitE st f b
        let d = slot f
        (match op with
         | "+" | "-" | "*" ->
             stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") " + op + " UNTAGI(" + sref y + "));")
         | "/" | "%" ->
             stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") " + op + " UNTAGI(" + sref y + "));")
         | "<" | ">" | "<=" | ">=" ->
             stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") " + op + " UNTAGI(" + sref y + "));")
         | "=" ->
             stmt f (sref d + " = TAGI(" + sref x + " == " + sref y + ");")
         | "<>" ->
             stmt f (sref d + " = TAGI(" + sref x + " != " + sref y + ");")
         | "&&" ->
             stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") && UNTAGI(" + sref y + "));")
         | "||" ->
             stmt f (sref d + " = TAGI(UNTAGI(" + sref x + ") || UNTAGI(" + sref y + "));")
         | _ ->
             stmt f (sref d + " = fpp_not_emitted(" + cstr ("op " + op) + ");"))
        d
    | EPrim ("not", [ a ]) | EApp (EUnknown "not", [ a ]) ->
        let x = emitE st f a
        let d = slot f
        stmt f (sref d + " = TAGI(!UNTAGI(" + sref x + "));")
        d
    | ELet (_, v, _, rhs, body) ->
        let x = emitE st f rhs
        // the binding OWNS a slot: later reassignment must not clobber the
        // rhs temp another expression still reads
        let l = slot f
        stmt f (sref l + " = " + sref x + ";")
        dictSet f.Locals (v.Path, v.Offset) l
        emitE st f body
    | EAssign (v, rhs) ->
        let x = emitE st f rhs
        (match dictTryFind f.Locals (v.Path, v.Offset) with
         | Some l -> stmt f (sref l + " = " + sref x + ";")
         | None ->
             match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g -> stmt f (g + " = " + sref x + ";")
             | None -> stmt f ("fpp_not_emitted(" + cstr ("assign " + v.Name) + ");"))
        let d = slot f
        stmt f (sref d + " = VUNIT;")
        d
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
        let d = slot f
        stmt f (sref d + " = VUNIT;")
        d
    | ESeq xs ->
        (match xs with
         | [] ->
             let d = slot f
             stmt f (sref d + " = VUNIT;")
             d
         | _ ->
             let rec go (rest : Expr list) : int =
                 match rest with
                 | [ last ] -> emitE st f last
                 | x :: more ->
                     emitE st f x |> ignore
                     go more
                 | [] -> 0
             go xs)
    | EApp (EUnknown "ignore", [ a ]) ->
        emitE st f a |> ignore
        let d = slot f
        stmt f (sref d + " = VUNIT;")
        d
    | EUnknown n ->
        let d = slot f
        stmt f (sref d + " = fpp_not_emitted(" + cstr ("builtin " + n) + ");")
        d
    | other ->
        // NOT an error: like the wasm backend's not-ported stubs, the gap
        // traps only if the program actually reaches it — dead prelude
        // corners must not block a live program
        let d = slot f
        let p0 = printExpr other
        let p = if strLen p0 > 60 then p0.Substring (0, 60) else p0
        stmt f (sref d + " = fpp_not_emitted(" + cstr p + ");")
        d

/// one function body, wrapped in its shadow frame
let private emitFn (st : CSt) (name : string) (ps : (VarId * Scheme) list) (body : Expr) : unit =
    let f = { Body = vecNew<string> (); NSlots = 0; Locals = dictNew<string * int, int> () }
    // parameters copy into frame slots: they are roots too
    let pnames = ps |> List.mapi (fun i (pv, _) -> "p" + string i, pv)
    for pn, pv in pnames do
        let l = slot f
        stmt f (sref l + " = " + pn + ";")
        dictSet f.Locals (pv.Path, pv.Offset) l
    let r = emitE st f body
    let head =
        "static V " + name + "("
        + (if List.isEmpty pnames then "void"
           else String.concat ", " (pnames |> List.map (fun (pn, _) -> "V " + pn)))
        + ") {"
    vecAdd st.Fwd
        ("static V " + name + "("
         + (if List.isEmpty pnames then "void"
            else String.concat ", " (pnames |> List.map (fun _ -> "V")))
         + ");")
    let all = vecNew<string> ()
    vecAdd all head
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
          TypeReg = vecNew<string> (); Errors = vecNew<string> ()
          Fns = dictNew<string * int, int> ()
          GlobalOf = dictNew<string * int, string> ()
          NextTid = 0 }
    // pass 1: names — every top-level fn's arity, every global's C name
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) ->
            dictSet st.Fns (v.Path, v.Offset) (List.length ps)
        | DLet (_, v, _, _) ->
            dictSet st.GlobalOf (v.Path, v.Offset) (gname v)
        | _ -> ()
    // pass 2: emission
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            emitFn st (cname v) ps body
        | DLet (_, v, _, rhs) ->
            vecAdd st.Globals ("static V " + gname v + ";")
            // the init runs inside fpp_main's frame: emit as a function so
            // its temps have their own slots, called in decl order
            let initName = "init_" + gname v
            emitFn st initName [] rhs
            vecAdd st.Inits ("  " + gname v + " = " + initName + "();")
        | DExtern _ | DExport _ | DUnion _ | DRecord _ | DInterface _
        | DClass _ | DEnum _ | DMembers _ | DBaseInst _ -> ()
    let out = vecNew<string> ()
    vecAdd out "/* generated by fpp --target c */"
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
    let nglobals = vecLen st.Globals
    if nglobals > 0 then
        // globals are contiguous? NO — separate statics. Register each as a
        // one-slot range: correct, and the count is small.
        ()
    for g in vecToList st.Globals do
        // "static V g_x;" -> g_x
        let n = g.Substring (9, strLen g - 10)
        vecAdd out ("  fpprt_add_static_roots(&" + n + ", 1);")
    for t in vecToList st.TypeReg do vecAdd out t
    for i in vecToList st.Inits do vecAdd out i
    vecAdd out "  return 0;"
    vecAdd out "}"
    String.concat "\n" (vecToList out), vecToList st.Errors

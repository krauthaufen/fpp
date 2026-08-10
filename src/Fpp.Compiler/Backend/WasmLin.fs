module Fpp.Backend.WasmLin

// The DIRECT wasm-linear backend: Core IR straight to a wasm module over
// LINEAR MEMORY, with no C compiler and no emscripten in the path. The
// value model is fpprt's, at 32 bits — a tagged i32 where the low bit set
// means a 31-bit int and an even value is a byte address into the module's
// own memory. It reuses EmitBin's wasm assembly (the byte encoders, the
// function/code sections, the instruction emitters); only the LOWERING is
// new, the linear-memory counterpart of BinDriver's wasm-GC lowering.
//
// SLICE 1 (this file's current reach): integers, the arithmetic and
// comparison operators, let-bindings and top-level mutable globals,
// top-level functions and direct calls, if / while / assignment /
// sequencing, string literals, int-to-string, string concat, and
// `printfn`. Enough to run recursion, loops and formatted output under
// wasmtime with NOTHING but a wasm runtime. No GC yet: allocation bumps a
// pointer and never frees — honest for short-lived programs, and the seam
// a real collector drops into later. Anything outside the slice is
// reported, not silently mis-emitted.

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir
open Fpp.Core.LowIR
open Fpp.Backend.WasmBinary
open Fpp.Backend.EmitBin

// ---- the linear value model -----------------------------------------------
// static memory map (bytes): the fd_write iovec and scratch live low, then
// string constants, then the bump heap.
let private IOV_PTR = 0        // i32: the write buffer's address
let private IOV_LEN = 4        // i32: its length
let private NWRITTEN = 8       // i32: fd_write's out-param
let private PRINTBUF = 16      // utf-8 staging for one prints
let private PRINTCAP = 262144
let private FMTBUF = PRINTBUF + PRINTCAP   // u16 staging for float formatting
let private FMTCAP = 512
let private CONST_BASE = FMTBUF + FMTCAP

type private St =
    { M : Mod
      Errors : Vec<string>
      /// top-level function names (their DLet is an ELam): reached by call
      Funcs : Dict<string, int>          // "path:offset" -> arity
      /// top-level non-lambda bindings: a mutable global each
      Globals : Dict<string, bool>       // "path:offset" -> unit
      /// per-function: a Core VarId -> its wasm local name
      mutable Locals : Dict<string, string>
      /// interned string literals -> their constant address
      Consts : Dict<string, int>
      mutable ConstNext : int
      ConstData : Bytes
      /// a NESTED lambda node -> the lifted function name it became
      LamName : RefMap<Expr, string>
      /// every lifted lambda, in emission order: (name, param, body, captures)
      Lams : Vec<string * (VarId * Scheme) * Expr * (string * int) list>
      /// while emitting a lambda body: captured key -> its env slot
      mutable Captures : Dict<string, int>
      /// while emitting a lambda body: the environment parameter's local name
      mutable EnvName : string
      /// closure-apply temporaries, indexed by nesting depth (pre-declared)
      mutable ClosDepth : int
      /// record name -> its field names in DECLARED order (an offset each)
      RecFields : Dict<string, string list>
      /// union case name -> its tag (index) and its payload arity
      UnionTag : Dict<string, int>
      UnionArity : Dict<string, int>
      /// match temporaries, indexed by nesting depth (pre-declared)
      mutable MatchDepth : int
      /// allocation-nesting depth: indexes the base/value scratch pools
      mutable AllocDepth : int }

let private CLO_KIND = 2

let private key (v : VarId) : string = v.Path + ":" + string v.Offset
let private fn (v : VarId) : string = "$f" + string (abs (strHash (key v)))
let private gl (v : VarId) : string = "$g" + string (abs (strHash (key v)))

let private err (st : St) (m : string) : unit = vecAdd st.Errors m

// a UTF-16 string constant, baked into the active data segment; its address
// is stable and even (a heap pointer). Layout: [i32 kind=1][i32 nunits][u16..]
let private internStr (st : St) (s : string) : int =
    match dictTryFind st.Consts s with
    | Some a -> a
    | None ->
        let addr = st.ConstNext
        // the literal is the RAW source token (quotes, escapes and all) —
        // unescape it to little-endian UTF-16 unit bytes, the same routine
        // the wasm-GC backend uses
        let ub = Fpp.Backend.BinDriver.unescape s
        let n = ub.Length / 2
        // kind = 1 (string)
        emitByte st.ConstData 1; emitByte st.ConstData 0; emitByte st.ConstData 0; emitByte st.ConstData 0
        emitByte st.ConstData (n &&& 0xFF); emitByte st.ConstData ((n >>> 8) &&& 0xFF)
        emitByte st.ConstData ((n >>> 16) &&& 0xFF); emitByte st.ConstData ((n >>> 24) &&& 0xFF)
        for b in ub do emitByte st.ConstData (int b)
        // 4-align the next constant
        let total = 8 + 2 * n
        let pad = (4 - (total &&& 3)) &&& 3
        for _ in 1 .. pad do emitByte st.ConstData 0
        st.ConstNext <- st.ConstNext + total + pad
        dictSet st.Consts s addr
        addr

// ---- tag helpers (operate on the wasm stack) ------------------------------
let private tagi (f : Fn) : unit =           // i32 int -> tagged
    ic f 1; ins f "i32.shl"; ic f 1; ins f "i32.or"
let private untagi (f : Fn) : unit =         // tagged -> i32 int
    ic f 1; ins f "i32.shr_s"
let private constInt (f : Fn) (n : int) : unit =
    ic f ((n <<< 1) ||| 1)

// ---- the runtime, emitted as wasm -----------------------------------------
let private rtTypesLin (m : Mod) : unit =
    tyFunc m "$lt_i2i" [ "i32" ] [ "i32" ]
    tyFunc m "$lt_ii2i" [ "i32"; "i32" ] [ "i32" ]
    tyFunc m "$lt_i2v" [ "i32" ] []
    tyFunc m "$lt_v2v" [] []
    tyFunc m "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    // the closure calling convention: (environment, argument) -> result
    tyFunc m "$lclo" [ "i32"; "i32" ] [ "i32" ]

// closure-apply temporaries (indexed by nesting depth) and the closure-build
// scratch — declared in every function body, before any instruction
let private declTemps (f : Fn) : unit =
    local f "$cbuild" "i32"
    for i in 0 .. 15 do local f ("$ct" + string i) "i32"
    // per-match scrutinee and result, indexed by match-nesting depth
    for i in 0 .. 7 do local f ("$ms" + string i) "i32"; local f ("$mr" + string i) "i32"
    for i in 0 .. 15 do local f ("$pt" + string i) "i32"
    for i in 0 .. 7 do local f ("$ab" + string i) "i32"; local f ("$av" + string i) "i32"
    for i in 0 .. 7 do local f ("$ai" + string i) "i32"; local f ("$an" + string i) "i32"
    for i in 0 .. 7 do local f ("$fd" + string i) "f64"; local f ("$ld" + string i) "i64"
    local f "$obj" "i32"

let private rtDeclsLin (m : Mod) : unit =
    importFn m "wasi_snapshot_preview1" "fd_write" "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    exportMem m "memory"
    declFn m "$lalloc" "$lt_i2i"
    declFn m "$str_of_int" "$lt_i2i"
    declFn m "$str_cat" "$lt_ii2i"
    declFn m "$prints" "$lt_i2v"
    declFn m "$ftoa6" "$lt_i2i"

// %f: .NET's fixed-six-decimals form, ported to the linear string layout.
// Takes a boxed f64 pointer, returns a string pointer. Handles NaN, sign,
// rounding at the sixth decimal, an i64 integer part and six fractionals.
// A store16 helper writes one UTF-16 unit and advances $w.
let private emitFtoa6 (m : Mod) : unit =
    let f = beginFn m [ "$x" ]
    local f "$v" "f64"; local f "$w" "i32"; local f "$ip" "f64"; local f "$frac" "f64"
    local f "$ipi" "i64"; local f "$tmp" "i64"; local f "$d" "i32"; local f "$k" "i32"
    local f "$cur" "i32"; local f "$p" "i32"; local f "$len" "i32"; local f "$i" "i32"
    localsDone f
    let put (code : unit -> unit) =
        lg f "$w"; code (); mem f "i32.store16"; lg f "$w"; ic f 2; ins f "i32.add"; ls f "$w"
    lg f "$x"; mem f "f64.load"; ls f "$v"
    ic f FMTBUF; ls f "$w"
    blockE f "$fin"
    // NaN
    lg f "$v"; lg f "$v"; ins f "f64.ne"
    ifE f
    for c in [ 78; 97; 78 ] do put (fun () -> ic f c)
    br f "$fin"
    endB f
    // sign
    lg f "$v"; fc f 0L; ins f "f64.lt"
    ifE f
    put (fun () -> ic f 45)
    lg f "$v"; ins f "f64.neg"; ls f "$v"
    endB f
    // round at the sixth decimal (add 5e-7)
    lg f "$v"; fc f 4512825593480736141L; ins f "f64.add"; ls f "$v"
    lg f "$v"; ins f "f64.floor"; ls f "$ip"
    lg f "$ip"; ins f "i64.trunc_f64_s"; ls f "$ipi"
    // integer part: count digits (d), then write back-to-front from $w
    ic f 1; ls f "$d"
    lg f "$ipi"; ls f "$tmp"
    blockE f "$dc"; loopE f "$dl"
    lg f "$tmp"; lc f 10L; ins f "i64.lt_u"; brIf f "$dc"
    lg f "$tmp"; lc f 10L; ins f "i64.div_u"; ls f "$tmp"
    lg f "$d"; ic f 1; ins f "i32.add"; ls f "$d"
    br f "$dl"; endB f; endB f
    // write digits into [$w .. $w+2*d), MSB first via back-to-front
    lg f "$w"; lg f "$d"; ic f 1; ins f "i32.sub"; ic f 1; ins f "i32.shl"; ins f "i32.add"; ls f "$cur"
    lg f "$ipi"; ls f "$tmp"
    blockE f "$wc"; loopE f "$wl"
    lg f "$cur"
    lg f "$tmp"; lc f 10L; ins f "i64.rem_u"; ins f "i32.wrap_i64"; ic f 48; ins f "i32.add"
    mem f "i32.store16"
    lg f "$cur"; ic f 2; ins f "i32.sub"; ls f "$cur"
    lg f "$tmp"; lc f 10L; ins f "i64.div_u"; ls f "$tmp"
    lg f "$tmp"; lc f 0L; ins f "i64.eq"; brIf f "$wc"
    br f "$wl"; endB f; endB f
    lg f "$w"; lg f "$d"; ic f 1; ins f "i32.shl"; ins f "i32.add"; ls f "$w"
    // decimal point
    put (fun () -> ic f 46)
    // six fractional digits
    lg f "$v"; lg f "$ip"; ins f "f64.sub"; ls f "$frac"
    ic f 0; ls f "$k"
    blockE f "$fc2"; loopE f "$fl2"
    lg f "$k"; ic f 6; ins f "i32.ge_s"; brIf f "$fc2"
    lg f "$frac"; fc f 4621819117588971520L; ins f "f64.mul"; ls f "$frac"
    lg f "$frac"; ins f "f64.floor"; ins f "i32.trunc_f64_s"; ls f "$d"
    put (fun () -> ic f 48; lg f "$d"; ins f "i32.add")
    lg f "$frac"; lg f "$frac"; ins f "f64.floor"; ins f "f64.sub"; ls f "$frac"
    lg f "$k"; ic f 1; ins f "i32.add"; ls f "$k"
    br f "$fl2"; endB f; endB f
    endB f  // $fin
    // build the string [kind=1][len][units] from FMTBUF
    lg f "$w"; ic f FMTBUF; ins f "i32.sub"; ic f 1; ins f "i32.shr_u"; ls f "$len"
    ic f 8; lg f "$len"; ic f 1; ins f "i32.shl"; ins f "i32.add"; callf f "$lalloc"; ls f "$p"
    lg f "$p"; ic f 1; mem f "i32.store"
    lg f "$p"; ic f 4; ins f "i32.add"; lg f "$len"; mem f "i32.store"
    ic f 0; ls f "$i"
    blockE f "$cc"; loopE f "$cl"
    lg f "$i"; lg f "$len"; ins f "i32.ge_u"; brIf f "$cc"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    ic f FMTBUF; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$cl"; endB f; endB f
    lg f "$p"
    endFn f

// $lalloc(n): 4-align the bump pointer, reserve n bytes, grow memory as
// needed, return the aligned start.
let private emitLalloc (m : Mod) : unit =
    let f = beginFn m [ "$n" ]
    local f "$p" "i32"
    localsDone f
    gg f "$hp"
    ic f 3; ins f "i32.add"; ic f -4; ins f "i32.and"
    ls f "$p"
    // grow if $p + n exceeds current memory
    lg f "$p"; lg f "$n"; ins f "i32.add"
    memSizeIns f; ic f 16; ins f "i32.shl"
    ins f "i32.gt_u"
    ifE f
    ic f 64; memGrowIns f; ins f "drop"
    endB f
    lg f "$p"; lg f "$n"; ins f "i32.add"; gs f "$hp"
    lg f "$p"
    endFn f

// $str_of_int(tagged): decimal, with a leading '-' for negatives.
let private emitStrOfInt (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    local f "$n" "i32"; local f "$neg" "i32"; local f "$d" "i32"
    local f "$p" "i32"; local f "$w" "i32"; local f "$t" "i32"
    localsDone f
    lg f "$v"; untagi f; ls f "$n"
    // neg = n < 0 ; if so n = -n
    ic f 0; ls f "$neg"
    lg f "$n"; ic f 0; ins f "i32.lt_s"
    ifE f
    ic f 1; ls f "$neg"
    ic f 0; lg f "$n"; ins f "i32.sub"; ls f "$n"
    endB f
    // count digits (t = n, d = count; at least 1)
    ic f 1; ls f "$d"
    lg f "$n"; ls f "$t"
    blockE f "$dc"; loopE f "$dl"
    lg f "$t"; ic f 10; ins f "i32.lt_u"; brIf f "$dc"
    lg f "$t"; ic f 10; ins f "i32.div_u"; ls f "$t"
    lg f "$d"; ic f 1; ins f "i32.add"; ls f "$d"
    br f "$dl"; endB f; endB f
    // total units = d + neg ; alloc 8 + 2*units (align inside lalloc)
    ic f 8
    lg f "$d"; lg f "$neg"; ins f "i32.add"; ic f 1; ins f "i32.shl"
    ins f "i32.add"
    callf f "$lalloc"; ls f "$p"
    // header: kind=1, len = d+neg
    lg f "$p"; ic f 1; mem f "i32.store"
    lg f "$p"; ic f 4; ins f "i32.add"
    lg f "$d"; lg f "$neg"; ins f "i32.add"; mem f "i32.store"
    // write digits back to front into [p+8 .. )
    // w = p + 8 + 2*(neg + d - 1)  (last digit slot)
    lg f "$p"; ic f 8; ins f "i32.add"
    lg f "$neg"; lg f "$d"; ins f "i32.add"; ic f 1; ins f "i32.sub"
    ic f 1; ins f "i32.shl"; ins f "i32.add"; ls f "$w"
    blockE f "$wc"; loopE f "$wl"
    lg f "$w"
    lg f "$n"; ic f 10; ins f "i32.rem_u"; ic f 48; ins f "i32.add"
    mem f "i32.store16"
    lg f "$w"; ic f 2; ins f "i32.sub"; ls f "$w"
    lg f "$n"; ic f 10; ins f "i32.div_u"; ls f "$n"
    lg f "$n"; ic f 0; ins f "i32.eq"; brIf f "$wc"
    br f "$wl"; endB f; endB f
    // leading '-' at [p+8]
    lg f "$neg"
    ifE f
    lg f "$p"; ic f 8; ins f "i32.add"; ic f 45; mem f "i32.store16"
    endB f
    lg f "$p"
    endFn f

// $str_cat(a, b): a fresh string of a's units then b's.
let private emitStrCat (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    local f "$la" "i32"; local f "$lb" "i32"; local f "$p" "i32"
    local f "$i" "i32"
    localsDone f
    lg f "$a"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$la"
    lg f "$b"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$lb"
    ic f 8
    lg f "$la"; lg f "$lb"; ins f "i32.add"; ic f 1; ins f "i32.shl"
    ins f "i32.add"
    callf f "$lalloc"; ls f "$p"
    lg f "$p"; ic f 1; mem f "i32.store"
    lg f "$p"; ic f 4; ins f "i32.add"
    lg f "$la"; lg f "$lb"; ins f "i32.add"; mem f "i32.store"
    // copy a
    ic f 0; ls f "$i"
    blockE f "$ac"; loopE f "$al"
    lg f "$i"; lg f "$la"; ins f "i32.ge_u"; brIf f "$ac"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$a"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$al"; endB f; endB f
    // copy b after a
    ic f 0; ls f "$i"
    blockE f "$bc"; loopE f "$bl"
    lg f "$i"; lg f "$lb"; ins f "i32.ge_u"; brIf f "$bc"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$la"; lg f "$i"; ins f "i32.add"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$b"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$bl"; endB f; endB f
    lg f "$p"
    endFn f

// $prints(s): UTF-16 -> UTF-8 into PRINTBUF, then fd_write(1). Handles the
// BMP (1/2/3-byte forms); surrogate pairs are written as their raw units
// (adequate for slice 1's ASCII-and-Latin output).
let private emitPrints (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$len" "i32"; local f "$i" "i32"; local f "$w" "i32"; local f "$u" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    ic f PRINTBUF; ls f "$w"
    ic f 0; ls f "$i"
    blockE f "$pc"; loopE f "$pl"
    lg f "$i"; lg f "$len"; ins f "i32.ge_u"; brIf f "$pc"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ls f "$u"
    // 1-byte: u < 0x80
    lg f "$u"; ic f 0x80; ins f "i32.lt_u"
    ifE f
    lg f "$w"; lg f "$u"; mem f "i32.store8"
    lg f "$w"; ic f 1; ins f "i32.add"; ls f "$w"
    elseB f
    lg f "$u"; ic f 0x800; ins f "i32.lt_u"
    ifE f
    // 2-byte
    lg f "$w"; lg f "$u"; ic f 6; ins f "i32.shr_u"; ic f 0xC0; ins f "i32.or"; mem f "i32.store8"
    lg f "$w"; ic f 1; ins f "i32.add"; lg f "$u"; ic f 0x3F; ins f "i32.and"; ic f 0x80; ins f "i32.or"; mem f "i32.store8"
    lg f "$w"; ic f 2; ins f "i32.add"; ls f "$w"
    elseB f
    // 3-byte
    lg f "$w"; lg f "$u"; ic f 12; ins f "i32.shr_u"; ic f 0xE0; ins f "i32.or"; mem f "i32.store8"
    lg f "$w"; ic f 1; ins f "i32.add"; lg f "$u"; ic f 6; ins f "i32.shr_u"; ic f 0x3F; ins f "i32.and"; ic f 0x80; ins f "i32.or"; mem f "i32.store8"
    lg f "$w"; ic f 2; ins f "i32.add"; lg f "$u"; ic f 0x3F; ins f "i32.and"; ic f 0x80; ins f "i32.or"; mem f "i32.store8"
    lg f "$w"; ic f 3; ins f "i32.add"; ls f "$w"
    endB f
    endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$pl"; endB f; endB f
    // iovec = (PRINTBUF, w - PRINTBUF); fd_write(1, IOV, 1, NWRITTEN)
    ic f IOV_PTR; ic f PRINTBUF; mem f "i32.store"
    ic f IOV_LEN; lg f "$w"; ic f PRINTBUF; ins f "i32.sub"; mem f "i32.store"
    ic f 1; ic f IOV_PTR; ic f 1; ic f NWRITTEN
    callf f "$fd_write"; ins f "drop"
    endFn f

// operators arrive with a type-kind suffix (`+i`, `<>i`, `=l`); slice 1 is
// int-only, so strip a trailing kind letter to recover the base operator
let private baseOp (op : string) : string =
    if strLen op >= 2 then
        let last = charAt op (strLen op - 1)
        if (last = 'i' || last = 'l' || last = 'f' || last = 's' || last = 'h'
            || last = 'w' || last = 'v' || last = 'p')
           && List.contains (substr op 0 (strLen op - 1)) [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="; "="; "<>" ]
        then substr op 0 (strLen op - 1)
        else op
    else op

// ---- lambda lifting -------------------------------------------------------
// the free (path,offset) VarIds a lambda body reads, EXCLUDING its own
// bound param, globals and top-level functions — those resolve directly.
let private freeVars (st : St) (bound : Dict<string, bool>) (body : Expr) : (string * int) list =
    let acc = vecNew<string * int> ()
    let seen = dictNew<string, bool> ()
    let rec go (bnd : Dict<string, bool>) (e : Expr) : unit =
        match e with
        | EVar (v, _) | EVarI (v, _, _) ->
            let k = key v
            if (dictTryFind bnd k).IsNone
               && (dictTryFind st.Globals k).IsNone
               && (dictTryFind st.Funcs k).IsNone
               && (dictTryFind seen k).IsNone then
                dictSet seen k true
                vecAdd acc (v.Path, v.Offset)
        | ELam (ps, b) ->
            let bnd2 = dictNew<string, bool> ()
            for kv in dictPairs bnd do dictSet bnd2 (fst kv) (snd kv)
            for pv, _ in ps do dictSet bnd2 (key pv) true
            go bnd2 b
        | ELet (_, v, _, rhs, b) ->
            go bnd rhs
            let bnd2 = dictNew<string, bool> ()
            for kv in dictPairs bnd do dictSet bnd2 (fst kv) (snd kv)
            dictSet bnd2 (key v) true
            go bnd2 b
        | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) -> for x in xs do go bnd x
        | EApp (g, xs) -> go bnd g; for x in xs do go bnd x
        | EIf (a, b, c) -> go bnd a; go bnd b; go bnd c
        | EWhile (a, b) -> go bnd a; go bnd b
        | EAssign (_, x) -> go bnd x
        | _ -> ()
    go bound body
    vecToList acc

// discover every nested lambda, curry to unary, name it, record its
// captures — the same lifting the wasm-GC backend does.
let rec private discover (st : St) (e : Expr) : unit =
    match e with
    | ELam ([ (pv, psch) ], body) ->
        let name = "$blam" + string (vecLen st.Lams)
        refMapSet st.LamName e name
        let bnd = dictNew<string, bool> ()
        dictSet bnd (key pv) true
        let caps = freeVars st bnd body
        vecAdd st.Lams (name, (pv, psch), body, caps)
        discover st body
    | ELam ((pv, psch) :: rest, body) ->
        let curried = ELam ([ (pv, psch) ], ELam (rest, body))
        discover st curried
        (match refMapTryFind st.LamName curried with
         | Some n -> refMapSet st.LamName e n
         | None -> ())
    | ELet (_, _, _, a, b) | EWhile (a, b) -> discover st a; discover st b
    | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) -> for x in xs do discover st x
    | EApp (g, xs) -> discover st g; for x in xs do discover st x
    | EIf (a, b, c) -> discover st a; discover st b; discover st c
    | EAssign (_, x) -> discover st x
    | _ -> ()

// ---- lowering -------------------------------------------------------------
// every expression emitter leaves ONE i32 (a tagged value) on the stack.
let rec private lower (st : St) (f : Fn) (e : Expr) : unit =
    match e with
    | ELit (LInt s) when s.EndsWith "L" || s.EndsWith "l" ->
        // a 64-bit literal: boxed i64
        (match System.Int64.TryParse (s.Substring (0, s.Length - 1)) with
         | true, n -> lc f n; boxI64 st f
         | _ -> constInt f 0; err st ("wasm-linear slice: bad int64 literal " + s))
    | ELit (LInt s) ->
        (match System.Int32.TryParse s with
         | true, n -> constInt f n
         | _ -> constInt f 0; err st ("wasm-linear slice: integer literal out of 31-bit range: " + s))
    | ELit (LBool b) -> constInt f (if b then 1 else 0)
    | ELit LUnit -> constInt f 0
    | ELit LNull -> constInt f 0
    | ELit (LString s) -> ic f (internStr st s)
    | EVar (v, _) | EVarI (v, _, _) ->
        (match dictTryFind st.Locals (key v) with
         | Some ln -> lg f ln
         | None ->
             match dictTryFind st.Captures (key v) with
             | Some slot ->
                 // a captured free variable: env[8 + 4*slot]
                 lg f st.EnvName; ic f (8 + 4 * slot); ins f "i32.add"; mem f "i32.load"
             | None ->
                 if (dictTryFind st.Globals (key v)).IsSome then gg f (gl v)
                 else (constInt f 0; err st ("wasm-linear slice: unbound value " + v.Name)))
    | ELet (_, v, _, rhs, body) ->
        lower st f rhs
        (match dictTryFind st.Locals (key v) with
         | Some ln -> ls f ln
         | None -> ins f "drop"; err st "wasm-linear slice: let local not pre-declared")
        lower st f body
    | ESeq xs ->
        (match xs with
         | [] -> constInt f 0
         | _ ->
             xs |> List.iteri (fun i x ->
                 lower st f x
                 if i < List.length xs - 1 then ins f "drop"))
    | EIf (c, a, b) ->
        lower st f c; untagi f
        ifV f "i32"
        lower st f a
        elseB f
        lower st f b
        endB f
    | EWhile (c, body) ->
        blockE f "$wb"; loopE f "$wl"
        lower st f c; untagi f; ins f "i32.eqz"; brIf f "$wb"
        lower st f body; ins f "drop"
        br f "$wl"; endB f; endB f
        constInt f 0
    | EAssign (v, rhs) ->
        lower st f rhs
        (match dictTryFind st.Locals (key v) with
         | Some ln -> ls f ln
         | None -> if (dictTryFind st.Globals (key v)).IsSome then gs f (gl v)
                   else err st ("wasm-linear slice: assignment to unbound " + v.Name))
        constInt f 0
    | ELit (LFloat s) ->
        // a boxed f64 [f64 bits]; box at the use site (no GC yet)
        (match System.Double.TryParse (s, System.Globalization.CultureInfo.InvariantCulture) with
         | true, d -> fc f (System.BitConverter.DoubleToInt64Bits d); boxF64 st f
         | _ -> constInt f 0; err st ("wasm-linear slice: bad float literal " + s))
    | EPrim (op, [ a; b ]) when op.EndsWith "f" && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/" ] ->
        lower st f a; unboxF64 st f
        lower st f b; unboxF64 st f
        ins f (match op.Substring (0, op.Length - 1) with "+" -> "f64.add" | "-" -> "f64.sub" | "*" -> "f64.mul" | _ -> "f64.div")
        boxF64 st f
    | EPrim (op, [ a; b ]) when op.EndsWith "f" && List.contains (op.Substring (0, op.Length - 1)) [ "<"; ">"; "<="; ">="; "="; "<>" ] ->
        lower st f a; unboxF64 st f
        lower st f b; unboxF64 st f
        ins f (match op.Substring (0, op.Length - 1) with "<" -> "f64.lt" | ">" -> "f64.gt" | "<=" -> "f64.le" | ">=" -> "f64.ge" | "=" -> "f64.eq" | _ -> "f64.ne")
        tagi f
    | EPrim ("u-f", [ a ]) ->
        lower st f a; unboxF64 st f; ins f "f64.neg"; boxF64 st f
    | EPrim (op, [ a; b ]) when op.EndsWith "l" && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%" ] ->
        lower st f a; unboxI64 st f
        lower st f b; unboxI64 st f
        ins f (match op.Substring (0, op.Length - 1) with "+" -> "i64.add" | "-" -> "i64.sub" | "*" -> "i64.mul" | "/" -> "i64.div_s" | _ -> "i64.rem_s")
        boxI64 st f
    | EPrim (op, [ a; b ]) when op.EndsWith "l" && List.contains (op.Substring (0, op.Length - 1)) [ "<"; ">"; "<="; ">="; "="; "<>" ] ->
        lower st f a; unboxI64 st f
        lower st f b; unboxI64 st f
        ins f (match op.Substring (0, op.Length - 1) with "<" -> "i64.lt_s" | ">" -> "i64.gt_s" | "<=" -> "i64.le_s" | ">=" -> "i64.ge_s" | "=" -> "i64.eq" | _ -> "i64.ne")
        tagi f
    | EApp (EUnknown "fixed6", [ a ]) ->
        lower st f a; callf f "$ftoa6"
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#l" || n = "int#l" ->
        // int64 -> int: unbox, wrap to i32, tag
        lower st f a; unboxI64 st f; ins f "i32.wrap_i64"; tagi f
    | EApp (EUnknown n, [ a ]) when n = "int64#" || n.StartsWith "int64#" ->
        // int -> int64: untag i32, widen, box
        lower st f a; untagi f; ins f "i64.extend_i32_s"; boxI64 st f
    | EApp (EUnknown n, [ a ]) when (n = "float#" || n.StartsWith "float#") && not (n.StartsWith "float32") ->
        // int -> float: untag, convert, box
        lower st f a; untagi f; ins f "f64.convert_i32_s"; boxF64 st f
    | EPrim (op0, [ a; b ]) when (List.contains (baseOp op0) [ "+"; "-"; "*"; "/"; "%" ]) ->
        lower st f a; untagi f
        lower st f b; untagi f
        ins f (match baseOp op0 with "+" -> "i32.add" | "-" -> "i32.sub" | "*" -> "i32.mul" | "/" -> "i32.div_s" | _ -> "i32.rem_s")
        tagi f
    | EPrim (op0, [ a; b ]) when (List.contains (baseOp op0) [ "<"; ">"; "<="; ">="; "="; "<>" ]) ->
        lower st f a; untagi f
        lower st f b; untagi f
        ins f (match baseOp op0 with "<" -> "i32.lt_s" | ">" -> "i32.gt_s" | "<=" -> "i32.le_s" | ">=" -> "i32.ge_s" | "=" -> "i32.eq" | _ -> "i32.ne")
        tagi f
    | EPrim ("::", [ h; t ]) ->
        // a cons cell [head][tail]; the empty list is the null pointer 0
        buildObj st f 2 [ 0, (fun () -> lower st f h); 1, (fun () -> lower st f t) ]
    | EApp (EUnknown "isNull", [ e ]) ->
        lower st f e; ic f 0; ins f "i32.eq"; tagi f
    | EApp (EUnknown ("failwith" | "raise" | "invalidArg" | "invalidOp" | "nullArg"), args) ->
        // no exception machinery yet: evaluate the argument for its effects,
        // then trap. `unreachable` is stack-polymorphic, so it satisfies any
        // result type the call site expects. A program that stays off this
        // path never reaches it.
        for a in args do lower st f a; ins f "drop"
        ins f "unreachable"
    | EPrim ("+t", [ a; b ]) ->
        lower st f a; lower st f b; callf f "$str_cat"
    | EApp (EUnknown "prints", [ a ]) ->
        lower st f a; callf f "$prints"; constInt f 0
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string" ->
        // slice 1: only int-to-string; other formatters await later slices
        lower st f a; callf f "$str_of_int"
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args)
        when (dictTryFind st.Funcs (key v)) = Some (List.length args) ->
        // a direct call to a top-level function at its exact arity
        for a in args do lower st f a
        callf f (fn v)
    | ELam (_, _) ->
        (match refMapTryFind st.LamName e with
         | Some name -> buildClosure st f name
         | None -> constInt f 0; err st "wasm-linear slice: lambda not discovered")
    | EApp (g, args) ->
        // an indirect application: g evaluates to a closure. Curry — apply
        // one argument at a time through the closure's code slot.
        lower st f g
        for a in args do applyClosure st f a
    | ETuple xs ->
        // a heap object of the elements, in order (no header — the pattern
        // that reads it knows the arity)
        buildObj st f (List.length xs) (xs |> List.mapi (fun i x -> i, (fun () -> lower st f x)))
    | ERecord (name, fields) ->
        // fields stored in DECLARED order, whatever order they are written
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst fields
        buildObj st f (List.length order)
            (order |> List.mapi (fun i fn ->
                i, (fun () ->
                    match fields |> List.tryPick (fun (fn2, e2) -> if fn2 = fn then Some e2 else None) with
                    | Some e2 -> lower st f e2
                    | None -> constInt f 0)))
    | ERecordExt (name, baseE, updates) ->
        // copy the base record, overwrite the named fields
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst updates
        let d = st.AllocDepth
        let bs = "$ab" + string d       // base reserved at depth d
        st.AllocDepth <- d + 1          // base-eval and buildObj live above it
        lower st f baseE; ls f bs
        buildObj st f (List.length order)
            (order |> List.mapi (fun i fn ->
                i, (fun () ->
                    match updates |> List.tryPick (fun (fn2, e2) -> if fn2 = fn then Some e2 else None) with
                    | Some e2 -> lower st f e2
                    | None -> lg f bs; ic f (4 * i); ins f "i32.add"; mem f "i32.load")))
        st.AllocDepth <- d
    | EField (r, fname, owner) ->
        let idx =
            match dictTryFind st.RecFields owner with
            | Some order -> (match List.tryFindIndex (fun x -> x = fname) order with Some i -> i | None -> 0)
            | None -> 0
        lower st f r
        ic f (4 * idx); ins f "i32.add"; mem f "i32.load"
    | EFieldSet (r, fname, owner, v) ->
        let idx =
            match dictTryFind st.RecFields owner with
            | Some order -> (match List.tryFindIndex (fun x -> x = fname) order with Some i -> i | None -> 0)
            | None -> 0
        lower st f r
        ic f (4 * idx); ins f "i32.add"
        lower st f v
        mem f "i32.store"
        constInt f 0
    | EListLit xs ->
        // a chain of cons cells ending in the null pointer; [] is 0
        emitList st f xs
    | EArray (_, xs) ->
        // [len][elem0..] — len is a RAW i32 at slot 0, elements are tagged
        buildObj st f (List.length xs + 1)
            ((0, (fun () -> ic f (List.length xs)))
             :: (xs |> List.mapi (fun i x -> i + 1, (fun () -> lower st f x))))
    | EIndex (_, arr, i) ->
        // element k is at slot (k+1): address = base + 4*(untag i + 1)
        lower st f arr
        lower st f i; untagi f; ic f 1; ins f "i32.add"; ic f 4; ins f "i32.mul"
        ins f "i32.add"; mem f "i32.load"
    | EIndexSet (_, arr, i, v) ->
        lower st f arr
        lower st f i; untagi f; ic f 1; ins f "i32.add"; ic f 4; ins f "i32.mul"
        ins f "i32.add"
        lower st f v; mem f "i32.store"
        constInt f 0
    | EArrayLen (_, arr) ->
        lower st f arr; mem f "i32.load"; tagi f
    | EArrayCreate (_, n, init) ->
        // [len][init x count] — count and fill value are dynamic, so a loop;
        // all scratch is depth-indexed for nesting safety
        let d = st.AllocDepth
        let bs = "$ab" + string d
        let cnt = "$av" + string d
        let iv = "$ai" + string d
        let it = "$an" + string d
        st.AllocDepth <- d + 1
        lower st f n; untagi f; ls f cnt
        lower st f init; ls f iv
        ic f 4; lg f cnt; ic f 4; ins f "i32.mul"; ins f "i32.add"; callf f "$lalloc"; ls f bs
        lg f bs; lg f cnt; mem f "i32.store"
        ic f 0; ls f it
        blockE f "$acc"; loopE f "$acl"
        lg f it; lg f cnt; ins f "i32.ge_u"; brIf f "$acc"
        lg f bs; lg f it; ic f 1; ins f "i32.add"; ic f 4; ins f "i32.mul"; ins f "i32.add"; lg f iv; mem f "i32.store"
        lg f it; ic f 1; ins f "i32.add"; ls f it
        br f "$acl"; endB f; endB f
        st.AllocDepth <- d
        lg f bs
    | EApp (EUnknown n, _) when n.StartsWith "$zero" -> constInt f 0
    | EUnknown n when n.StartsWith "$zero" -> constInt f 0
    | ECtor (case, _, args) ->
        // [tag][payload0..] — the tag (a RAW i32, not a tagged value) is the
        // case's index in its union; payloads are ordinary tagged values
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        buildObj st f (List.length args + 1)
            ((0, (fun () -> ic f tag))
             :: (args |> List.mapi (fun i a -> i + 1, (fun () -> lower st f a))))
    | EMatch (scrut, clauses) ->
        let d = st.MatchDepth
        let sc = "$ms" + string d
        let mr = "$mr" + string d
        st.MatchDepth <- d + 1
        lower st f scrut; ls f sc
        blockE f "$mdone"
        for pat, guard, body in clauses do
            blockE f "$mnext"
            emitPatTest st f sc "$mnext" 0 pat
            (match guard with
             | Some g -> lower st f g; untagi f; ins f "i32.eqz"; brIf f "$mnext"
             | None -> ())
            lower st f body; ls f mr
            br f "$mdone"
            endB f
        ins f "unreachable"
        endB f
        st.MatchDepth <- d
        lg f mr
    | _ ->
        constInt f 0
        err st ("wasm-linear slice: unsupported expression: "
                + (match e with
                   | ECtor (n, _, _) -> "constructor " + n
                   | ERecord (n, _) -> "record " + n
                   | EMatch _ -> "match" | ETuple _ -> "tuple"
                   | EArray _ -> "array" | EField _ -> "field access"
                   | ELam _ -> "nested lambda"
                   | EPrim (op, _) -> "operator " + op
                   | _ -> "node"))

// a list literal as a chain of [head][tail] cons cells ending in null (0)
and private emitList (st : St) (f : Fn) (xs : Expr list) : unit =
    match xs with
    | [] -> ic f 0
    | x :: rest -> buildObj st f 2 [ 0, (fun () -> lower st f x); 1, (fun () -> emitList st f rest) ]

// build a heap object of `nslots` 4-byte words, filling slot `i` with the
// thunk that emits its value; leaves the pointer on the stack. Base and
// value scratch are indexed by allocation-nesting depth, so a field whose
// value is itself an allocation cannot clobber the enclosing one.
and private buildObj (st : St) (f : Fn) (nslots : int) (fills : (int * (unit -> unit)) list) : unit =
    let d = st.AllocDepth
    let ab = "$ab" + string d
    let av = "$av" + string d
    st.AllocDepth <- d + 1
    ic f (4 * nslots); callf f "$lalloc"; ls f ab
    for i, emit in fills do
        emit ()            // may recurse at depth d+1
        ls f av
        lg f ab; ic f (4 * i); ins f "i32.add"; lg f av; mem f "i32.store"
    st.AllocDepth <- d
    lg f ab

// test `pat` against the value in local `scrutLocal`; branch to `fail` on
// mismatch, and bind any pattern variables on the matching path. `depth`
// indexes the pattern-scratch pool for sub-value loads.
and private emitPatTest (st : St) (f : Fn) (scrutLocal : string) (fail : string) (depth : int) (pat : Pat) : unit =
    match pat with
    | PWild -> ()
    | PVar (v, _) ->
        (match dictTryFind st.Locals (key v) with
         | Some ln -> lg f scrutLocal; ls f ln
         | None -> err st "wasm-linear slice: pattern binder not pre-declared")
    | PAs (p, v, _) ->
        (match dictTryFind st.Locals (key v) with Some ln -> lg f scrutLocal; ls f ln | None -> ())
        emitPatTest st f scrutLocal fail depth p
    | PLit (LInt s) ->
        (match System.Int32.TryParse s with
         | true, n -> lg f scrutLocal; untagi f; ic f n; ins f "i32.ne"; brIf f fail
         | _ -> err st "wasm-linear slice: integer pattern out of range")
    | PLit (LBool b) ->
        lg f scrutLocal; untagi f; ic f (if b then 1 else 0); ins f "i32.ne"; brIf f fail
    | PLit LUnit -> ()
    | PCtor (case, _, subs) ->
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        // the tag is a RAW i32 at slot 0
        lg f scrutLocal; mem f "i32.load"; ic f tag; ins f "i32.ne"; brIf f fail
        subs |> List.iteri (fun i sub ->
            let t = "$pt" + string (depth &&& 15)
            lg f scrutLocal; ic f (4 * (i + 1)); ins f "i32.add"; mem f "i32.load"; ls f t
            emitPatTest st f t fail (depth + 1) sub)
    | PTuple subs ->
        subs |> List.iteri (fun i sub ->
            let t = "$pt" + string (depth &&& 15)
            lg f scrutLocal; ic f (4 * i); ins f "i32.add"; mem f "i32.load"; ls f t
            emitPatTest st f t fail (depth + 1) sub)
    | PCons (h, t) ->
        // a non-empty list: the scrutinee is a [head][tail] cell (not null)
        lg f scrutLocal; ins f "i32.eqz"; brIf f fail
        let th = "$pt" + string (depth &&& 15)
        lg f scrutLocal; mem f "i32.load"; ls f th
        emitPatTest st f th fail (depth + 1) h
        let tt = "$pt" + string (depth &&& 15)
        lg f scrutLocal; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f tt
        emitPatTest st f tt fail (depth + 1) t
    | PListLit [] ->
        // the empty list: a null pointer
        lg f scrutLocal; brIf f fail
    | _ ->
        err st "wasm-linear slice: unsupported pattern (non-empty list literals / or-patterns / type tests await a later slice)"

// box/unbox the 64-bit payloads — a boxed value is a pointer to 8 bytes;
// scratch is depth-indexed so a nested box cannot clobber this one
and private boxF64 (st : St) (f : Fn) : unit =
    let d = st.AllocDepth
    st.AllocDepth <- d + 1
    ls f ("$fd" + string d)
    ic f 8; callf f "$lalloc"; ls f ("$ab" + string d)
    lg f ("$ab" + string d); lg f ("$fd" + string d); mem f "f64.store"
    st.AllocDepth <- d
    lg f ("$ab" + string d)
and private unboxF64 (st : St) (f : Fn) : unit = mem f "f64.load"
and private boxI64 (st : St) (f : Fn) : unit =
    let d = st.AllocDepth
    st.AllocDepth <- d + 1
    ls f ("$ld" + string d)
    ic f 8; callf f "$lalloc"; ls f ("$ab" + string d)
    lg f ("$ab" + string d); lg f ("$ld" + string d); mem f "i64.store"
    st.AllocDepth <- d
    lg f ("$ab" + string d)
and private unboxI64 (st : St) (f : Fn) : unit = mem f "i64.load"

// resolve a captured/local/global reference known only by its (path,offset)
and private emitVarByKey (st : St) (f : Fn) (k : string) : unit =
    match dictTryFind st.Locals k with
    | Some ln -> lg f ln
    | None ->
        match dictTryFind st.Captures k with
        | Some slot -> lg f st.EnvName; ic f (8 + 4 * slot); ins f "i32.add"; mem f "i32.load"
        | None ->
            match st.Globals |> dictPairs |> List.tryFind (fun (gk, _) -> gk = k) with
            | Some _ -> gg f ("$g" + string (abs (strHash k)))
            | None -> constInt f 0; err st "wasm-linear slice: unresolved captured variable"

// build a closure object [kind=2][code-table-idx][cap0..] and leave its
// pointer on the stack
and private buildClosure (st : St) (f : Fn) (name : string) : unit =
    let caps =
        st.Lams |> vecToList |> List.tryPick (fun (n, _, _, c) -> if n = name then Some c else None)
        |> Option.defaultValue []
    let nc = List.length caps
    ic f (8 + 4 * nc); callf f "$lalloc"
    ls f "$cbuild"
    lg f "$cbuild"; ic f CLO_KIND; mem f "i32.store"
    lg f "$cbuild"; ic f 4; ins f "i32.add"; ic f (tblIdx st.M name); mem f "i32.store"
    caps |> List.iteri (fun i (p, o) ->
        lg f "$cbuild"; ic f (8 + 4 * i); ins f "i32.add"
        emitVarByKey st f (p + ":" + string o)
        mem f "i32.store")
    lg f "$cbuild"

// apply the closure currently on the stack to argument `a` (unary)
and private applyClosure (st : St) (f : Fn) (a : Expr) : unit =
    let t = "$ct" + string st.ClosDepth
    ls f t                              // stash the closure ptr
    lg f t                              // env (operand 0)
    st.ClosDepth <- st.ClosDepth + 1
    lower st f a                         // arg (operand 1)
    st.ClosDepth <- st.ClosDepth - 1
    lg f t; ic f 4; ins f "i32.add"; mem f "i32.load"   // code index (table slot)
    callIndirect f "$lclo"

// pre-declare every let-bound local in a function body (locals must be
// declared before any instruction is emitted)
and private scanLets (st : St) (f : Fn) (e : Expr) : unit =
    match e with
    | ELet (_, v, _, rhs, body) ->
        (dictTryFind st.Locals (key v) |> ignore)
        if (dictTryFind st.Locals (key v)).IsNone then
            let ln = "$l" + string (List.length (dictPairs st.Locals))
            local f ln "i32"
            dictSet st.Locals (key v) ln
        scanLets st f rhs; scanLets st f body
    | ESeq xs | EApp (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) -> for x in xs do scanLets st f x
    | EIf (c, a, b) -> scanLets st f c; scanLets st f a; scanLets st f b
    | EWhile (c, b) -> scanLets st f c; scanLets st f b
    | EAssign (_, r) -> scanLets st f r
    | EPrim (_, xs) -> for x in xs do scanLets st f x
    | ERecord (_, fs) -> for _, v in fs do scanLets st f v
    | ERecordExt (_, b, fs) -> scanLets st f b; for _, v in fs do scanLets st f v
    | EField (r, _, _) -> scanLets st f r
    | EFieldSet (r, _, _, v) -> scanLets st f r; scanLets st f v
    | EArray (_, xs) -> for x in xs do scanLets st f x
    | EIndex (_, a, i) -> scanLets st f a; scanLets st f i
    | EIndexSet (_, a, i, v) -> scanLets st f a; scanLets st f i; scanLets st f v
    | EArrayLen (_, a) -> scanLets st f a
    | EArrayCreate (_, n, ini) -> scanLets st f n; scanLets st f ini
    | ELam (_, _) -> ()   // a nested lambda's OWN body scans in its own pass
    | EMatch (scrut, clauses) ->
        scanLets st f scrut
        for pat, guard, body in clauses do
            declarePatVars st f pat
            (match guard with Some g -> scanLets st f g | None -> ())
            scanLets st f body
    | _ -> ()

// declare a local for every variable a pattern binds
and private declarePatVars (st : St) (f : Fn) (p : Pat) : unit =
    match p with
    | PVar (v, _) | PAs (_, v, _) ->
        if (dictTryFind st.Locals (key v)).IsNone then
            let ln = "$l" + string (List.length (dictPairs st.Locals))
            local f ln "i32"
            dictSet st.Locals (key v) ln
        (match p with PAs (inner, _, _) -> declarePatVars st f inner | _ -> ())
    | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> for x in ps do declarePatVars st f x
    | PCons (a, b) -> declarePatVars st f a; declarePatVars st f b
    | _ -> ()

// intern every string literal up front, so the heap pointer's start (after
// the constant region) is known before any global is declared
// intern EVERY string literal reachable in a body — a literal missed here
// is baked at an address the heap pointer already claimed, so $hp must
// only settle once every constant is counted
let rec private scanConsts (st : St) (e : Expr) : unit =
    match e with
    | ELit (LString s) -> internStr st s |> ignore
    | ELet (_, _, _, a, b) | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> scanConsts st a; scanConsts st b
    | EIf (a, b, c) | EIndexSet (_, a, b, c) -> scanConsts st a; scanConsts st b; scanConsts st c
    | ESeq xs | EPrim (_, xs) | EApp (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> for x in xs do scanConsts st x
    | EAssign (_, r) | EField (r, _, _) | EArrayLen (_, r) | ECast (_, r, _) | ETypeTest (_, r) -> scanConsts st r
    | EFieldSet (r, _, _, v) -> scanConsts st r; scanConsts st v
    | ELam (_, b) -> scanConsts st b
    | EMatch (s, cs) -> scanConsts st s; for _, g, b in cs do (match g with Some x -> scanConsts st x | None -> ()); scanConsts st b
    | ERecord (_, fs) -> for _, v in fs do scanConsts st v
    | ERecordExt (_, b, fs) -> scanConsts st b; for _, v in fs do scanConsts st v
    | EIfaceCall (_, _, r, xs) -> scanConsts st r; for x in xs do scanConsts st x
    | ETry (b, cs) -> scanConsts st b; for _, g, x in cs do (match g with Some y -> scanConsts st y | None -> ()); scanConsts st x
    | _ -> ()

let private paramNm (v : VarId) : string = "$p" + string (abs (strHash (key v)))

// a reference-map hash over lambda nodes, keyed by the bound param's offset
let private shallowLamHash (e : Expr) : int =
    match e with
    | ELam ((pv, _) :: _, _) -> 31 * pv.Offset + 7
    | _ -> 7

// ---- LowIR: Core -> a shared machine IR, then IR -> wasm ------------------
// The migration seam off the hand-lowering above. A function whose body lies
// in the supported subset is lowered to LowIR (Core/LowIR.fs) and emitted
// from there; everything else still goes through `lower`. Tag/box arithmetic
// is EXPANDED here into plain machine ops, so LowIR carries no tag primitive
// of its own — the property that lets one IR serve the C backend and an
// eventual native backend the same way it serves this one. As coverage grows,
// `lowSupported` widens until `lower` is dead and the IR is the only path.

type private LowCtx =
    { LSt : St
      // a Core VarId (param or let) -> its dense LowIR register id
      Regs : Dict<string, int>
      // when lowering a lifted lambda body: the register holding the env
      // pointer (-1 elsewhere). Captured vars load from env+8+4*slot.
      mutable EnvReg : int
      mutable NReg : int }

let private freshReg (ctx : LowCtx) (k : string) : int =
    match dictTryFind ctx.Regs k with
    | Some id -> id
    | None ->
        let id = ctx.NReg
        dictSet ctx.Regs k id
        ctx.NReg <- id + 1
        id

let private freshTmp (ctx : LowCtx) : int =
    let id = ctx.NReg
    ctx.NReg <- id + 1
    id

let private wReg (id : int) : LReg = { Id = id; RTy = W }
let private regNm (r : LReg) : string = "$r" + string r.Id
let private lowInt (n : int) : LExpr = LConstW ((n <<< 1) ||| 1)
let private lowUntag (e : LExpr) : LExpr = LPrim (ShrSW, [ e; LConstW 1 ])
let private lowTag (e : LExpr) : LExpr = LPrim (OrW, [ LPrim (ShlW, [ e; LConstW 1 ]); LConstW 1 ])

let private intArithOp (b : string) : LOp =
    match b with
    | "+" -> AddW
    | "-" -> SubW
    | "*" -> MulW
    | "/" -> DivSW
    | _ -> RemSW

let private intCmpOp (b : string) : LOp =
    match b with
    | "<" -> LtSW
    | ">" -> GtSW
    | "<=" -> LeSW
    | ">=" -> GeSW
    | "=" -> EqW
    | _ -> NeW

// can this pattern be compiled by lowPatTest?
let rec private patSupported (p : Pat) : bool =
    match p with
    | PWild | PVar _ -> true
    | PLit (LInt _) | PLit (LBool _) | PLit LUnit -> true
    | PAs (inner, _, _) -> patSupported inner
    | PCtor (_, _, subs) -> List.forall patSupported subs
    | PTuple subs -> List.forall patSupported subs
    | PCons (a, b) -> patSupported a && patSupported b
    | PListLit [] -> true
    // non-empty list literals, or-patterns, `:?` type tests, string/float/char
    // literal patterns still fall back
    | _ -> false

// is this whole expression inside the LowIR subset? (called on a function body
// before choosing the IR path; a false anywhere falls the function back to the
// hand-lowering). Nested lambda BODIES are not walked — they lower on the
// lifted path — but constructing a lambda (the closure) here is supported.
let rec private lowSupported (st : St) (e : Expr) : bool =
    let allS (xs : Expr list) : bool = List.forall (lowSupported st) xs
    match e with
    | ELit (LInt _) | ELit (LFloat _) | ELit (LBool _) | ELit LUnit | ELit LNull | ELit (LString _) -> true
    | EVar (v, _) | EVarI (v, _, _) ->
        // params, lets and globals are fine; a bare top-level function used as
        // a first-class value is not (only direct calls are supported)
        (dictTryFind st.Funcs (key v)).IsNone
    | ELet (_, _, _, a, b) -> lowSupported st a && lowSupported st b
    | ESeq xs -> allS xs
    | EIf (a, b, c) -> lowSupported st a && lowSupported st b && lowSupported st c
    | EWhile (a, b) -> lowSupported st a && lowSupported st b
    | EAssign (_, x) -> lowSupported st x
    | ETuple xs | EListLit xs -> allS xs
    | ERecord (_, fs) -> List.forall (fun (_, v) -> lowSupported st v) fs
    | ERecordExt (_, b, fs) -> lowSupported st b && List.forall (fun (_, v) -> lowSupported st v) fs
    | ECtor (_, _, args) -> allS args
    | EField (r, _, _) | EArrayLen (_, r) -> lowSupported st r
    | EFieldSet (r, _, _, v) -> lowSupported st r && lowSupported st v
    | EArray (_, xs) -> allS xs
    | EIndex (_, a, b) -> lowSupported st a && lowSupported st b
    | EIndexSet (_, a, b, c) -> lowSupported st a && lowSupported st b && lowSupported st c
    | EArrayCreate (_, a, b) -> lowSupported st a && lowSupported st b
    | EMatch (scrut, clauses) ->
        lowSupported st scrut
        && List.forall (fun (p, g, b) ->
            patSupported p
            && (match g with Some x -> lowSupported st x | None -> true)
            && lowSupported st b) clauses
    | ELam (_, _) -> true
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args)
        when (dictTryFind st.Funcs (key v)) = Some (List.length args) -> allS args
    | EPrim ("u-f", [ a ]) -> lowSupported st a
    | EPrim (op, [ a; b ]) ->
        (op = "+t" || op = "::"
         || List.contains (baseOp op) [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="; "="; "<>" ])
        && lowSupported st a && lowSupported st b
    | EPrim (_, _) -> false
    | EApp (EUnknown "prints", [ a ]) -> lowSupported st a
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string" -> lowSupported st a
    | EApp (EUnknown "fixed6", [ a ]) -> lowSupported st a
    | EApp (EUnknown "isNull", [ a ]) -> lowSupported st a
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#l" || n = "int64#" || n.StartsWith "int64#"
                                    || ((n = "float#" || n.StartsWith "float#") && not (n.StartsWith "float32")) -> lowSupported st a
    | EApp (EUnknown ("failwith" | "raise" | "invalidArg" | "invalidOp" | "nullArg"), args) -> allS args
    | EApp (EUnknown n, _) when n.StartsWith "$zero" -> true
    | EUnknown n when n.StartsWith "$zero" -> true
    | EApp (EUnknown _, _) -> false
    | EApp (g, args) -> lowSupported st g && allS args
    | _ -> false

// for --lowir stats: the tag of the first node that keeps a body off the LowIR
// path, so the remaining fallbacks are legible
let rec private unsupReason (st : St) (e : Expr) : string =
    let firstBad (xs : Expr list) : string =
        match xs |> List.filter (fun x -> not (lowSupported st x)) with
        | b :: _ -> unsupReason st b
        | [] -> ""
    let orSelf (self : string) (xs : Expr list) : string =
        let r = firstBad xs in if r = "" then self else r
    if lowSupported st e then "" else
    match e with
    | EIfaceCall (i, mn, r, xs) -> orSelf ("ifacecall " + i + "." + mn) (r :: xs)
    | ECast (_, r, _) -> orSelf "cast" [ r ]
    | ETypeTest (_, r) -> orSelf "typetest" [ r ]
    | ETry _ -> "try"
    | EArrayPin (_, r) -> orSelf "arraypin" [ r ]
    | EArrayUnpin (_, r) -> orSelf "arrayunpin" [ r ]
    | EArrayBytes (_, r) -> orSelf "arraybytes" [ r ]
    | EApp (EUnknown n, xs) -> orSelf ("unknown " + n) xs
    | EVar (v, _) | EVarI (v, _, _) -> "func-as-value " + v.Name
    | EMatch (s, cs) ->
        if not (lowSupported st s) then unsupReason st s
        else match cs |> List.filter (fun (p, _, _) -> not (patSupported p)) with
             | (p, _, _) :: _ -> "pattern " + printPat p
             | [] -> (match cs |> List.filter (fun (_, _, b) -> not (lowSupported st b)) with (_, _, b) :: _ -> unsupReason st b | [] -> "match")
    | ELet (_, _, _, a, b) | EWhile (a, b) -> firstBad [ a; b ]
    | EIf (a, b, c) -> firstBad [ a; b; c ]
    | EFieldSet (r, _, _, v) -> firstBad [ r; v ]
    | EField (r, _, _) | EArrayLen (_, r) -> firstBad [ r ]
    | ERecord (_, fs) -> orSelf "record" (List.map snd fs)
    | ERecordExt (_, b, fs) -> orSelf "recordext" (b :: List.map snd fs)
    | EPrim (op, xs) -> orSelf ("prim " + op) xs
    | EApp (g, xs) -> orSelf "app" (g :: xs)
    | ESeq xs | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> orSelf "app" xs
    | _ -> "node"

let rec private coreToLowE (ctx : LowCtx) (e : Expr) : LExpr =
    let st = ctx.LSt
    match e with
    | ELit (LInt s) when s.EndsWith "L" || s.EndsWith "l" ->
        (match System.Int64.TryParse (s.Substring (0, s.Length - 1)) with
         | true, n -> lowBoxI ctx (LConstL n)
         | _ -> lowInt 0)
    | ELit (LInt s) -> (match System.Int32.TryParse s with | true, n -> lowInt n | _ -> lowInt 0)
    | ELit (LFloat s) ->
        (match System.Double.TryParse (s, System.Globalization.CultureInfo.InvariantCulture) with
         | true, d -> lowBoxF ctx (LConstF d)
         | _ -> lowInt 0)
    | ELit (LBool b) -> lowInt (if b then 1 else 0)
    | ELit LUnit | ELit LNull -> lowInt 0
    | ELit (LString s) -> LConstW (internStr st s)
    | EVar (v, _) | EVarI (v, _, _) -> lowVarByKey ctx (key v)
    | ELet (_, v, _, rhs, body) ->
        let id = freshReg ctx (key v)
        LDo ([ LSet (wReg id, coreToLowE ctx rhs) ], coreToLowE ctx body)
    | ESeq xs ->
        let rec go (xs : Expr list) : LExpr =
            match xs with
            | [] -> lowInt 0
            | [ x ] -> coreToLowE ctx x
            | x :: rest -> LDo (coreToLowS ctx x, go rest)
        go xs
    | EIf (c, a, b) ->
        let r = freshTmp ctx
        LDo ([ LIf (lowUntag (coreToLowE ctx c),
                    [ LSet (wReg r, coreToLowE ctx a) ],
                    [ LSet (wReg r, coreToLowE ctx b) ]) ],
             LGet (wReg r))
    | EWhile (_, _) | EAssign (_, _) -> LDo (coreToLowS ctx e, lowInt 0)
    | EPrim ("+t", [ a; b ]) -> LCall ("$str_cat", [ coreToLowE ctx a; coreToLowE ctx b ])
    | EPrim (op, [ a; b ]) when op.EndsWith "f" && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/" ] ->
        let fa = lowUnboxF (coreToLowE ctx a)
        let fb = lowUnboxF (coreToLowE ctx b)
        let fop = match op.Substring (0, op.Length - 1) with | "+" -> AddF | "-" -> SubF | "*" -> MulF | _ -> DivF
        lowBoxF ctx (LPrim (fop, [ fa; fb ]))
    | EPrim (op, [ a; b ]) when op.EndsWith "f" && List.contains (op.Substring (0, op.Length - 1)) [ "<"; ">"; "<="; ">="; "="; "<>" ] ->
        let fa = lowUnboxF (coreToLowE ctx a)
        let fb = lowUnboxF (coreToLowE ctx b)
        let fop = match op.Substring (0, op.Length - 1) with | "<" -> LtF | ">" -> GtF | "<=" -> LeF | ">=" -> GeF | "=" -> EqF | _ -> NeF
        lowTag (LPrim (fop, [ fa; fb ]))
    | EPrim ("u-f", [ a ]) -> lowBoxF ctx (LPrim (NegF, [ lowUnboxF (coreToLowE ctx a) ]))
    | EPrim (op, [ a; b ]) when op.EndsWith "l" && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%" ] ->
        let ia = lowUnboxI (coreToLowE ctx a)
        let ib = lowUnboxI (coreToLowE ctx b)
        let iop = match op.Substring (0, op.Length - 1) with | "+" -> AddL | "-" -> SubL | "*" -> MulL | "/" -> DivSL | _ -> RemSL
        lowBoxI ctx (LPrim (iop, [ ia; ib ]))
    | EPrim (op, [ a; b ]) when op.EndsWith "l" && List.contains (op.Substring (0, op.Length - 1)) [ "<"; ">"; "<="; ">="; "="; "<>" ] ->
        let ia = lowUnboxI (coreToLowE ctx a)
        let ib = lowUnboxI (coreToLowE ctx b)
        let iop = match op.Substring (0, op.Length - 1) with | "<" -> LtSL | ">" -> GtSL | "<=" -> LeSL | ">=" -> GeSL | "=" -> EqL | _ -> NeL
        lowTag (LPrim (iop, [ ia; ib ]))
    | EPrim ("::", [ h; t ]) -> lowObj ctx [ coreToLowE ctx h; coreToLowE ctx t ]
    | EPrim (op, [ a; b ]) ->
        let bop = baseOp op
        let la = lowUntag (coreToLowE ctx a)
        let lb = lowUntag (coreToLowE ctx b)
        if List.contains bop [ "+"; "-"; "*"; "/"; "%" ]
        then lowTag (LPrim (intArithOp bop, [ la; lb ]))
        else lowTag (LPrim (intCmpOp bop, [ la; lb ]))
    | ETuple xs -> lowObj ctx (List.map (coreToLowE ctx) xs)
    | EListLit xs -> lowList ctx xs
    | ERecord (name, fields) ->
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst fields
        lowObj ctx (order |> List.map (fun fnm ->
            match fields |> List.tryPick (fun (fn2, e2) -> if fn2 = fnm then Some e2 else None) with
            | Some e2 -> coreToLowE ctx e2
            | None -> lowInt 0))
    | ERecordExt (name, baseE, updates) ->
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst updates
        let b = freshTmp ctx
        let slots =
            order |> List.mapi (fun i fnm ->
                match updates |> List.tryPick (fun (fn2, e2) -> if fn2 = fnm then Some e2 else None) with
                | Some e2 -> coreToLowE ctx e2
                | None -> LLoad (W, LGet (wReg b), 4 * i))
        LDo ([ LSet (wReg b, coreToLowE ctx baseE) ], lowObj ctx slots)
    | ECtor (case, _, args) ->
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        lowObj ctx (LConstW tag :: List.map (coreToLowE ctx) args)
    | EField (r, fname, owner) ->
        let idx =
            match dictTryFind st.RecFields owner with
            | Some order -> (match List.tryFindIndex (fun x -> x = fname) order with Some i -> i | None -> 0)
            | None -> 0
        LLoad (W, coreToLowE ctx r, 4 * idx)
    | EFieldSet (r, fname, owner, v) ->
        let idx =
            match dictTryFind st.RecFields owner with
            | Some order -> (match List.tryFindIndex (fun x -> x = fname) order with Some i -> i | None -> 0)
            | None -> 0
        LDo ([ LStore (W, coreToLowE ctx r, 4 * idx, coreToLowE ctx v) ], lowInt 0)
    | EArray (_, xs) -> lowObj ctx (LConstW (List.length xs) :: List.map (coreToLowE ctx) xs)
    | EIndex (_, arr, i) ->
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ lowUntag (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LLoad (W, addr, 0)
    | EIndexSet (_, arr, i, v) ->
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ lowUntag (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LDo ([ LStore (W, addr, 0, coreToLowE ctx v) ], lowInt 0)
    | EArrayLen (_, arr) -> lowTag (LLoad (W, coreToLowE ctx arr, 0))
    | EArrayCreate (_, n, init) ->
        let cnt = freshTmp ctx
        let iv = freshTmp ctx
        let bs = freshTmp ctx
        let it = freshTmp ctx
        let stmts =
            [ LSet (wReg cnt, lowUntag (coreToLowE ctx n))
              LSet (wReg iv, coreToLowE ctx init)
              LSet (wReg bs, LAlloc (LPrim (AddW, [ LConstW 4; LPrim (MulW, [ LGet (wReg cnt); LConstW 4 ]) ])))
              LStore (W, LGet (wReg bs), 0, LGet (wReg cnt))
              LSet (wReg it, LConstW 0)
              LWhile (LPrim (LtUW, [ LGet (wReg it); LGet (wReg cnt) ]),
                      [ LStore (W, LPrim (AddW, [ LGet (wReg bs); LPrim (MulW, [ LPrim (AddW, [ LGet (wReg it); LConstW 1 ]); LConstW 4 ]) ]), 0, LGet (wReg iv))
                        LSet (wReg it, LPrim (AddW, [ LGet (wReg it); LConstW 1 ])) ]) ]
        LDo (stmts, LGet (wReg bs))
    | EApp (EUnknown n, _) when n.StartsWith "$zero" -> lowInt 0
    | EUnknown n when n.StartsWith "$zero" -> lowInt 0
    | EApp (EUnknown "fixed6", [ a ]) -> LCall ("$ftoa6", [ coreToLowE ctx a ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#l" || n = "int#l" ->
        lowTag (LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ]))
    | EApp (EUnknown n, [ a ]) when n = "int64#" || n.StartsWith "int64#" ->
        lowBoxI ctx (LPrim (WToL, [ lowUntag (coreToLowE ctx a) ]))
    | EApp (EUnknown n, [ a ]) when (n = "float#" || n.StartsWith "float#") && not (n.StartsWith "float32") ->
        lowBoxF ctx (LPrim (WToF, [ lowUntag (coreToLowE ctx a) ]))
    | EApp (EUnknown "isNull", [ x ]) -> lowTag (LPrim (EqW, [ coreToLowE ctx x; LConstW 0 ]))
    | EApp (EUnknown ("failwith" | "raise" | "invalidArg" | "invalidOp" | "nullArg"), args) ->
        LDo ((args |> List.map (fun a -> LEval (coreToLowE ctx a))) @ [ LTrap ], lowInt 0)
    | EApp (EUnknown "prints", [ a ]) -> LDo ([ LCallVoidS ("$prints", [ coreToLowE ctx a ]) ], lowInt 0)
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string" -> LCall ("$str_of_int", [ coreToLowE ctx a ])
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args)
        when (dictTryFind st.Funcs (key v)) = Some (List.length args) ->
        LCall (fn v, List.map (coreToLowE ctx) args)
    | ELam (_, _) ->
        (match refMapTryFind st.LamName e with
         | Some name -> lowClosure ctx name
         | None -> err st "wasm-linear LowIR: lambda not discovered"; lowInt 0)
    | EApp (g, args) -> lowApply ctx (coreToLowE ctx g) args
    | EMatch (scrut, clauses) ->
        let sc = freshTmp ctx
        let mr = freshTmp ctx
        let clauseStmts =
            clauses |> List.map (fun (pat, guard, body) ->
                let tests = lowPatTest ctx sc "$mnext" pat
                let guardStmt =
                    match guard with
                    | Some g -> [ LBreakIf ("$mnext", LPrim (EqW, [ lowUntag (coreToLowE ctx g); LConstW 0 ])) ]
                    | None -> []
                LBlock ("$mnext", tests @ guardStmt @ [ LSet (wReg mr, coreToLowE ctx body); LBreak "$mdone" ]))
        LDo ([ LSet (wReg sc, coreToLowE ctx scrut)
               LBlock ("$mdone", clauseStmts @ [ LTrap ]) ], LGet (wReg mr))
    | _ -> err st "wasm-linear LowIR: node outside subset reached emission"; lowInt 0

and private coreToLowS (ctx : LowCtx) (e : Expr) : LStmt list =
    match e with
    | ESeq xs -> List.collect (coreToLowS ctx) xs
    | ELet (_, v, _, rhs, body) ->
        let id = freshReg ctx (key v)
        LSet (wReg id, coreToLowE ctx rhs) :: coreToLowS ctx body
    | EAssign (v, rhs) ->
        (match dictTryFind ctx.Regs (key v) with
         | Some id -> [ LSet (wReg id, coreToLowE ctx rhs) ]
         | None -> [ LSetGlobal (gl v, coreToLowE ctx rhs) ])
    | EIf (c, a, b) -> [ LIf (lowUntag (coreToLowE ctx c), coreToLowS ctx a, coreToLowS ctx b) ]
    | EWhile (c, b) -> [ LWhile (lowUntag (coreToLowE ctx c), coreToLowS ctx b) ]
    | ELit LUnit -> []
    | EApp (EUnknown "prints", [ a ]) -> [ LCallVoidS ("$prints", [ coreToLowE ctx a ]) ]
    | _ -> [ LEval (coreToLowE ctx e) ]

// allocate an n-word object and fill each slot; a fresh register holds the
// base, so nesting is safe with NO scratch pool (the depth-indexed pools the
// hand path needs fall away — the IR gives every allocation its own register)
and private lowObj (ctx : LowCtx) (slots : LExpr list) : LExpr =
    let n = List.length slots
    let b = freshTmp ctx
    let stores = slots |> List.mapi (fun i v -> LStore (W, LGet (wReg b), 4 * i, v))
    LDo (LSet (wReg b, LAlloc (LConstW (4 * n))) :: stores, LGet (wReg b))

and private lowList (ctx : LowCtx) (xs : Expr list) : LExpr =
    match xs with
    | [] -> LConstW 0
    | x :: rest -> lowObj ctx [ coreToLowE ctx x; lowList ctx rest ]

// a boxed 64-bit payload is a pointer to 8 bytes; box/unbox are alloc+store /
// load, with the wide type carried on the LStore/LLoad so the backend picks
// f64/i64 access
and private lowBoxF (ctx : LowCtx) (fv : LExpr) : LExpr =
    let b = freshTmp ctx
    LDo ([ LSet (wReg b, LAlloc (LConstW 8)); LStore (F64, LGet (wReg b), 0, fv) ], LGet (wReg b))

and private lowUnboxF (p : LExpr) : LExpr = LLoad (F64, p, 0)

and private lowBoxI (ctx : LowCtx) (iv : LExpr) : LExpr =
    let b = freshTmp ctx
    LDo ([ LSet (wReg b, LAlloc (LConstW 8)); LStore (I64, LGet (wReg b), 0, iv) ], LGet (wReg b))

and private lowUnboxI (p : LExpr) : LExpr = LLoad (I64, p, 0)

// test `pat` against the value in register `scrutReg`; produce statements that
// LBreak to `fail` on mismatch and bind pattern variables on the matching
// path. Sub-values load into fresh registers — again no scratch pool.
and private lowPatTest (ctx : LowCtx) (scrutReg : int) (fail : string) (pat : Pat) : LStmt list =
    let st = ctx.LSt
    let sc = LGet (wReg scrutReg)
    match pat with
    | PWild -> []
    | PVar (v, _) -> [ LSet (wReg (freshReg ctx (key v)), sc) ]
    | PAs (p, v, _) -> LSet (wReg (freshReg ctx (key v)), sc) :: lowPatTest ctx scrutReg fail p
    | PLit (LInt s) ->
        (match System.Int32.TryParse s with
         | true, n -> [ LBreakIf (fail, LPrim (NeW, [ lowUntag sc; LConstW n ])) ]
         | _ -> [])
    | PLit (LBool b) -> [ LBreakIf (fail, LPrim (NeW, [ lowUntag sc; LConstW (if b then 1 else 0) ])) ]
    | PLit LUnit -> []
    | PCtor (case, _, subs) ->
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        let tagTest = LBreakIf (fail, LPrim (NeW, [ LLoad (W, sc, 0); LConstW tag ]))
        tagTest :: List.concat (subs |> List.mapi (fun i sub ->
            let t = freshTmp ctx
            LSet (wReg t, LLoad (W, sc, 4 * (i + 1))) :: lowPatTest ctx t fail sub))
    | PTuple subs ->
        List.concat (subs |> List.mapi (fun i sub ->
            let t = freshTmp ctx
            LSet (wReg t, LLoad (W, sc, 4 * i)) :: lowPatTest ctx t fail sub))
    | PCons (h, tl) ->
        let th = freshTmp ctx
        let tt = freshTmp ctx
        LBreakIf (fail, LPrim (EqW, [ sc; LConstW 0 ]))
        :: (LSet (wReg th, LLoad (W, sc, 0)) :: lowPatTest ctx th fail h)
        @ (LSet (wReg tt, LLoad (W, sc, 4)) :: lowPatTest ctx tt fail tl)
    | PListLit [] -> [ LBreakIf (fail, LPrim (NeW, [ sc; LConstW 0 ])) ]
    | _ -> [ LTrap ]

// resolve a variable by its (path:offset) key: a local/param register, a
// captured free variable read from the env (when lowering a lifted lambda
// body), or a module global — the LowIR counterpart of emitVarByKey
and private lowVarByKey (ctx : LowCtx) (k : string) : LExpr =
    let st = ctx.LSt
    match dictTryFind ctx.Regs k with
    | Some id -> LGet (wReg id)
    | None ->
        match dictTryFind st.Captures k with
        | Some slot when ctx.EnvReg >= 0 -> LLoad (W, LGet (wReg ctx.EnvReg), 8 + 4 * slot)
        | _ ->
            match st.Globals |> dictPairs |> List.tryFind (fun (gk, _) -> gk = k) with
            | Some _ -> LGetGlobal ("$g" + string (abs (strHash k)))
            | None -> err st "wasm-linear LowIR: unresolved variable"; lowInt 0

// build a closure object [kind=2][code-index][captures…]; its layout and the
// (env, arg) calling convention match the hand path, so a LowIR-built closure
// interoperates with a lifted body emitted by `lower` and vice versa
and private lowClosure (ctx : LowCtx) (name : string) : LExpr =
    let st = ctx.LSt
    let caps =
        st.Lams |> vecToList |> List.tryPick (fun (n, _, _, c) -> if n = name then Some c else None)
        |> Option.defaultValue []
    LConstW CLO_KIND
    :: LConstW (tblIdx st.M name)
    :: (caps |> List.map (fun (p, o) -> lowVarByKey ctx (p + ":" + string o)))
    |> lowObj ctx

and private lowApply (ctx : LowCtx) (cloE : LExpr) (args : Expr list) : LExpr =
    match args with
    | [] -> cloE
    | a :: rest ->
        // bind the closure to a register so LCallIndirect can read it twice
        // (as env and to load the code index) without re-evaluating it
        let tclo = freshTmp ctx
        let step = LDo ([ LSet (wReg tclo, cloE) ], LCallIndirect ([ W ], LGet (wReg tclo), [ coreToLowE ctx a ]))
        lowApply ctx step rest

let private lowOpIns (op : LOp) : string =
    match op with
    | AddW -> "i32.add"
    | SubW -> "i32.sub"
    | MulW -> "i32.mul"
    | DivSW -> "i32.div_s"
    | RemSW -> "i32.rem_s"
    | AndW -> "i32.and"
    | OrW -> "i32.or"
    | XorW -> "i32.xor"
    | ShlW -> "i32.shl"
    | ShrSW -> "i32.shr_s"
    | ShrUW -> "i32.shr_u"
    | EqW -> "i32.eq"
    | NeW -> "i32.ne"
    | LtSW -> "i32.lt_s"
    | GtSW -> "i32.gt_s"
    | LeSW -> "i32.le_s"
    | GeSW -> "i32.ge_s"
    | LtUW -> "i32.lt_u"
    | GeUW -> "i32.ge_u"
    | AddL -> "i64.add"
    | SubL -> "i64.sub"
    | MulL -> "i64.mul"
    | DivSL -> "i64.div_s"
    | RemSL -> "i64.rem_s"
    | EqL -> "i64.eq"
    | NeL -> "i64.ne"
    | LtSL -> "i64.lt_s"
    | GtSL -> "i64.gt_s"
    | LeSL -> "i64.le_s"
    | GeSL -> "i64.ge_s"
    | AddF -> "f64.add"
    | SubF -> "f64.sub"
    | MulF -> "f64.mul"
    | DivF -> "f64.div"
    | NegF -> "f64.neg"
    | EqF -> "f64.eq"
    | NeF -> "f64.ne"
    | LtF -> "f64.lt"
    | GtF -> "f64.gt"
    | LeF -> "f64.le"
    | GeF -> "f64.ge"
    | WToL -> "i64.extend_i32_s"
    | LToW -> "i32.wrap_i64"
    | WToF -> "f64.convert_i32_s"
    | FToW -> "i32.trunc_f64_s"
    | LToF -> "f64.convert_i64_s"
    | FToL -> "i64.trunc_f64_s"

let private loadIns (ty : LTy) : string =
    match ty with
    | F64 -> "f64.load"
    | I64 -> "i64.load"
    | I8 -> "i32.load8_u"
    | I16 -> "i32.load16_u"
    | _ -> "i32.load"

let private storeIns (ty : LTy) : string =
    match ty with
    | F64 -> "f64.store"
    | I64 -> "i64.store"
    | I8 -> "i32.store8"
    | I16 -> "i32.store16"
    | _ -> "i32.store"

let rec private emitLowE (f : Fn) (e : LExpr) : unit =
    match e with
    | LConstW n -> ic f n
    | LConstL n -> lc f n
    | LConstF x -> fc f (System.BitConverter.DoubleToInt64Bits x)
    | LGet r -> lg f (regNm r)
    | LGetGlobal g -> gg f g
    | LLoad (ty, a, off) ->
        emitLowE f a
        (if off <> 0 then (ic f off; ins f "i32.add"))
        mem f (loadIns ty)
    | LPrim (op, args) ->
        for a in args do emitLowE f a
        ins f (lowOpIns op)
    | LAlloc n -> emitLowE f n; callf f "$lalloc"
    | LCall (sym, args) ->
        for a in args do emitLowE f a
        callf f sym
    | LCallIndirect (_, fp, args) ->
        // (env, arg) -> result through table 0: the closure IS the env, and
        // the code index is the word at closure+4. `fp` must be a pure LGet
        // (Core->LowIR binds the closure into a register first), so emitting
        // it twice — once as env, once for the index load — is side-effect
        // free. Stack: env, arg, table-index, then call_indirect.
        emitLowE f fp
        for a in args do emitLowE f a
        emitLowE f (LLoad (W, fp, 4))
        callIndirect f "$lclo"
    | LDo (ss, v) ->
        for s in ss do emitLowS f s
        emitLowE f v

and private emitLowS (f : Fn) (s : LStmt) : unit =
    match s with
    | LStore (ty, a, off, v) ->
        emitLowE f a
        (if off <> 0 then (ic f off; ins f "i32.add"))
        emitLowE f v
        mem f (storeIns ty)
    | LSet (r, e) -> emitLowE f e; ls f (regNm r)
    | LSetGlobal (g, e) -> emitLowE f e; gs f g
    | LEval e -> emitLowE f e; ins f "drop"
    | LCallVoidS (sym, args) ->
        for a in args do emitLowE f a
        callf f sym
    | LIf (c, t, el) ->
        emitLowE f c; ifE f
        for s in t do emitLowS f s
        elseB f
        for s in el do emitLowS f s
        endB f
    | LWhile (c, body) ->
        blockE f "$wb"; loopE f "$wl"
        emitLowE f c; ins f "i32.eqz"; brIf f "$wb"
        for s in body do emitLowS f s
        br f "$wl"; endB f; endB f
    | LBlock (lbl, body) ->
        blockE f lbl
        for s in body do emitLowS f s
        endB f
    | LBreakIf (lbl, c) -> emitLowE f c; brIf f lbl
    | LBreak lbl -> br f lbl
    | LTrap -> ins f "unreachable"
    | LReturn e -> emitLowE f e; ins f "return"

// emit one function (or init) through LowIR: allocate a register per param and
// per let, declare the wasm locals for them, then the body. `finish` stores a
// global for an init and does nothing for an ordinary function.
let private emitFuncLow (st : St) (m : Mod) (ps : VarId list) (body : Expr) (finish : Fn -> unit) : unit =
    let ctx = { LSt = st; Regs = dictNew (); EnvReg = -1; NReg = 0 }
    let pnames = ps |> List.map (fun pv -> regNm (wReg (freshReg ctx (key pv))))
    let bodyLow = coreToLowE ctx body
    let f = beginFn m pnames
    let np = List.length ps
    for id in np .. ctx.NReg - 1 do local f (regNm (wReg id)) "i32"
    localsDone f
    emitLowE f bodyLow
    finish f
    endFn f

// a lifted lambda body: params are (env, arg); captured free variables read
// from the env at 8+4*slot (st.Captures is set by the driver). Register 0 is
// the env, register 1 the argument.
let private emitLambdaLow (st : St) (m : Mod) (pv : VarId) (body : Expr) : unit =
    let ctx = { LSt = st; Regs = dictNew (); EnvReg = 0; NReg = 0 }
    let envId = freshTmp ctx
    let argId = freshReg ctx (key pv)
    let bodyLow = coreToLowE ctx body
    let f = beginFn m [ regNm (wReg envId); regNm (wReg argId) ]
    for id in 2 .. ctx.NReg - 1 do local f (regNm (wReg id)) "i32"
    localsDone f
    emitLowE f bodyLow
    endFn f

// ---- driver ---------------------------------------------------------------
let private emitLinearImpl (useLow : bool) (decls0 : Decl list) : byte[] * string list =
    // emit the REACHABLE program: the user's declarations plus every
    // prelude function or global a chain of references reaches from them.
    // Unreachable prelude machinery (most of it) is dropped, so a program
    // pays only for what it uses — and one that reaches a still-unsupported
    // node gets a reported gap, never a bad module.
    let allDlets =
        decls0 |> List.choose (fun d -> match d with DLet (_, v, _, e) -> Some (v.Path + ":" + string v.Offset, e) | _ -> None)
    let bodyOf = dictNew<string, Expr> ()
    for k, e in allDlets do dictSet bodyOf k e
    let reachable = dictNew<string, bool> ()
    let rec refsOf (e : Expr) (acc : Vec<string>) : unit =
        match e with
        | EVar (v, _) | EVarI (v, _, _) -> vecAdd acc (v.Path + ":" + string v.Offset)
        | ELam (_, b) -> refsOf b acc
        | ELet (_, _, _, a, b) | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> refsOf a acc; refsOf b acc
        | EIf (a, b, c) | EIndexSet (_, a, b, c) -> refsOf a acc; refsOf b acc; refsOf c acc
        | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> for x in xs do refsOf x acc
        | EApp (g, xs) -> refsOf g acc; for x in xs do refsOf x acc
        | EMatch (s, cs) -> refsOf s acc; for _, g, b in cs do (match g with Some x -> refsOf x acc | None -> ()); refsOf b acc
        | ERecord (_, fs) -> for _, v in fs do refsOf v acc
        | ERecordExt (_, b, fs) -> refsOf b acc; for _, v in fs do refsOf v acc
        | EField (r, _, _) | EArrayLen (_, r) | ECast (_, r, _) | ETypeTest (_, r) | EArrayPin (_, r) | EArrayUnpin (_, r) | EArrayBytes (_, r) -> refsOf r acc
        | EFieldSet (r, _, _, v) -> refsOf r acc; refsOf v acc
        | EAssign (_, x) -> refsOf x acc
        | EIfaceCall (_, _, r, xs) -> refsOf r acc; for x in xs do refsOf x acc
        | ETry (b, cs) -> refsOf b acc; for _, g, x in cs do (match g with Some y -> refsOf y acc | None -> ()); refsOf x acc
        | _ -> ()
    let rec visit (k : string) : unit =
        if (dictTryFind reachable k).IsNone then
            dictSet reachable k true
            match dictTryFind bodyOf k with
            | Some e -> let a = vecNew<string> () in refsOf e a; for r in vecToList a do visit r
            | None -> ()
    for d in decls0 do
        match d with
        | DLet (_, v, _, e) when v.Path <> Fpp.Analysis.Classes.builtinPath ->
            dictSet reachable (v.Path + ":" + string v.Offset) true
            let a = vecNew<string> () in refsOf e a; for r in vecToList a do visit r
        | _ -> ()
    // keep decls0 order (prelude before user — inits sequence correctly),
    // filtered to what is reachable
    let decls =
        decls0 |> List.filter (fun d ->
            match d with
            | DLet (_, v, _, _) -> (dictTryFind reachable (v.Path + ":" + string v.Offset)).IsSome
            | _ -> false)
    let m = modNew ()
    let st =
        { M = m; Errors = vecNew (); Funcs = dictNew (); Globals = dictNew ()
          Locals = dictNew (); Consts = dictNew (); ConstNext = CONST_BASE; ConstData = bytesNew ()
          LamName = refMapNew shallowLamHash; Lams = vecNew ()
          Captures = dictNew (); EnvName = ""; ClosDepth = 0
          RecFields = dictNew (); UnionTag = dictNew (); UnionArity = dictNew (); MatchDepth = 0; AllocDepth = 0 }
    // record layouts and union case tags — needed everywhere below
    for d in decls0 do
        match d with
        | DRecord (n, _, fs, _) -> dictSet st.RecFields n (fs |> List.map fst)
        | DUnion (_, _, cs) ->
            cs |> List.iteri (fun i (cn, ar) ->
                dictSet st.UnionTag cn i
                dictSet st.UnionArity cn ar)
        | _ -> ()
    rtTypesLin m
    // classify top-level bindings
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) -> dictSet st.Funcs (key v) (List.length ps)
        | DLet (_, v, _, _) -> dictSet st.Globals (key v) true
        | _ -> ()
    // function type per arity used, and the function declarations
    let arities = st.Funcs |> dictPairs |> List.map snd |> List.distinct
    for a in arities do
        tyFunc m ("$lfn" + string a) (List.replicate a "i32") [ "i32" ]
    rtDeclsLin m
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) -> declFn m (fn v) ("$lfn" + string (List.length ps))
        | _ -> ()
    // one init function per top-level global, plus _start
    let inits = vecNew<string> ()
    let mutable initN = 0
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, _) ->
            globalI32Mut m (gl v) 0
            let nm = "$linit" + string initN
            initN <- initN + 1
            vecAdd inits nm
            declFn m nm "$lt_v2v"
        | _ -> ()
    declFn m "$_start" "$lt_v2v"
    // discover every NESTED lambda (the top-level ELams ARE the functions,
    // so walk their bodies, not the whole binding) and give each a lifted
    // function and a code-table slot
    for d in decls do
        match d with
        | DLet (_, _, _, ELam (_, body)) -> discover st body
        | DLet (_, _, _, e) -> discover st e
        | _ -> ()
    for name, _, _, _ in vecToList st.Lams do
        declFn m name "$lclo"
        tblIdx m name |> ignore
    // intern all string constants FIRST, so the heap starts after them
    for d in decls do
        match d with DLet (_, _, _, e) -> scanConsts st e | _ -> ()
    globalI32Mut m "$hp" st.ConstNext
    exportFn m "_start" "$_start"
    // runtime bodies
    emitLalloc m; emitStrOfInt m; emitStrCat m; emitPrints m; emitFtoa6 m
    // top-level function bodies
    let mutable nLow = 0
    let mutable nHand = 0
    let reasons = vecNew<string> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            if useLow && lowSupported st body then
                nLow <- nLow + 1
                emitFuncLow st m (ps |> List.map fst) body (fun _ -> ())
            else
                st.Locals <- dictNew (); st.Captures <- dictNew (); st.EnvName <- ""; st.ClosDepth <- 0
                let f = beginFn m (ps |> List.map (fun (pv, _) -> paramNm pv))
                for pv, _ in ps do dictSet st.Locals (key pv) (paramNm pv)
                scanLets st f body
                declTemps f
                localsDone f
                lower st f body
                endFn f
                if useLow then (nHand <- nHand + 1; vecAdd reasons (unsupReason st body))
        | _ -> ()
    // init bodies — DECLARED before _start and the lambdas, so emitted here
    // too (the function and code sections are positional and must agree)
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) ->
            if useLow && lowSupported st rhs then
                nLow <- nLow + 1
                emitFuncLow st m [] rhs (fun f -> gs f (gl v))
            else
                st.Locals <- dictNew (); st.Captures <- dictNew (); st.EnvName <- ""; st.ClosDepth <- 0
                let f = beginFn m []
                scanLets st f rhs
                declTemps f
                localsDone f
                lower st f rhs
                gs f (gl v)
                endFn f
                if useLow then (nHand <- nHand + 1; vecAdd reasons (unsupReason st rhs))
        | _ -> ()
    // _start: run every init in order
    let f = beginFn m []
    localsDone f
    for nm in vecToList inits do callf f nm
    endFn f
    // lifted lambda bodies: (environment, argument) -> result — declared LAST
    for name, (pv, _), body, caps in vecToList st.Lams do
        st.Locals <- dictNew (); st.Captures <- dictNew (); st.ClosDepth <- 0
        caps |> List.iteri (fun i (p, o) -> dictSet st.Captures (p + ":" + string o) i)
        if useLow && lowSupported st body then
            nLow <- nLow + 1
            emitLambdaLow st m pv body
        else
            let f = beginFn m [ "$env"; paramNm pv ]
            st.EnvName <- "$env"
            dictSet st.Locals (key pv) (paramNm pv)
            scanLets st f body
            declTemps f
            localsDone f
            lower st f body
            endFn f
            if useLow then (nHand <- nHand + 1; vecAdd reasons (unsupReason st body))
    // bake the constant data at CONST_BASE; $hp already starts after it
    activeData m CONST_BASE (bytesToArray st.ConstData)
    let pages = (st.ConstNext / 65536) + 64
    let bytes = assembleWith m pages false ""
    if useLow && System.Environment.GetEnvironmentVariable "FPP_LOWIR_STATS" <> null then
        eprintfn "LOWIR: %d functions via LowIR, %d fell back to hand-lowering" nLow nHand
        for r in reasons |> vecToList |> List.distinct do
            let c = reasons |> vecToList |> List.filter (fun x -> x = r) |> List.length
            eprintfn "  fallback: %s (x%d)" r c
    bytes, vecToList st.Errors

// the hand-lowered path (default) and the LowIR path (`--linear` with the
// shared IR). Both share the whole driver; they differ only in whether a
// function's body is emitted by `lower` or through Core/LowIR.fs.
let emitLinear (decls0 : Decl list) : byte[] * string list = emitLinearImpl false decls0
let emitLinearLow (decls0 : Decl list) : byte[] * string list = emitLinearImpl true decls0

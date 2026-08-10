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
    | _ ->
        err st "wasm-linear slice: unsupported pattern (lists / or-patterns / type tests await a later slice)"

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
let rec private scanConsts (st : St) (e : Expr) : unit =
    match e with
    | ELit (LString s) -> internStr st s |> ignore
    | ELet (_, _, _, a, b) | EWhile (a, b) -> scanConsts st a; scanConsts st b
    | ESeq xs | EPrim (_, xs) | EApp (_, xs) | ETuple xs | EListLit xs -> for x in xs do scanConsts st x
    | EIf (a, b, c) -> scanConsts st a; scanConsts st b; scanConsts st c
    | EAssign (_, r) -> scanConsts st r
    | ELam (_, b) -> scanConsts st b
    | ECtor (_, _, xs) -> for x in xs do scanConsts st x
    | _ -> ()

let private paramNm (v : VarId) : string = "$p" + string (abs (strHash (key v)))

// a reference-map hash over lambda nodes, keyed by the bound param's offset
let private shallowLamHash (e : Expr) : int =
    match e with
    | ELam ((pv, _) :: _, _) -> 31 * pv.Offset + 7
    | _ -> 7

// ---- driver ---------------------------------------------------------------
let emitLinear (decls0 : Decl list) : byte[] * string list =
    // slice 1 emits the USER program only: the prelude's own declarations
    // and startup initializers are outside the slice, and a program that
    // stays within it never needs them. A user call into an unemitted
    // prelude function surfaces as a reported gap, not a bad module.
    let decls =
        decls0 |> List.filter (fun d ->
            match d with
            | DLet (_, v, _, _) -> v.Path <> Fpp.Analysis.Classes.builtinPath
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
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            st.Locals <- dictNew (); st.Captures <- dictNew (); st.EnvName <- ""; st.ClosDepth <- 0
            let f = beginFn m (ps |> List.map (fun (pv, _) -> paramNm pv))
            for pv, _ in ps do dictSet st.Locals (key pv) (paramNm pv)
            scanLets st f body
            declTemps f
            localsDone f
            lower st f body
            endFn f
        | _ -> ()
    // init bodies — DECLARED before _start and the lambdas, so emitted here
    // too (the function and code sections are positional and must agree)
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) ->
            st.Locals <- dictNew (); st.Captures <- dictNew (); st.EnvName <- ""; st.ClosDepth <- 0
            let f = beginFn m []
            scanLets st f rhs
            declTemps f
            localsDone f
            lower st f rhs
            gs f (gl v)
            endFn f
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
        let f = beginFn m [ "$env"; paramNm pv ]
        st.EnvName <- "$env"
        dictSet st.Locals (key pv) (paramNm pv)
        scanLets st f body
        declTemps f
        localsDone f
        lower st f body
        endFn f
    // bake the constant data at CONST_BASE; $hp already starts after it
    activeData m CONST_BASE (bytesToArray st.ConstData)
    let pages = (st.ConstNext / 65536) + 64
    let bytes = assembleWith m pages false ""
    bytes, vecToList st.Errors

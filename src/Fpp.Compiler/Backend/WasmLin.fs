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
let private CONST_BASE = PRINTBUF + PRINTCAP

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
      ConstData : Bytes }

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

let private rtDeclsLin (m : Mod) : unit =
    importFn m "wasi_snapshot_preview1" "fd_write" "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    exportMem m "memory"
    declFn m "$lalloc" "$lt_i2i"
    declFn m "$str_of_int" "$lt_i2i"
    declFn m "$str_cat" "$lt_ii2i"
    declFn m "$prints" "$lt_i2v"

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

// ---- lowering -------------------------------------------------------------
// every expression emitter leaves ONE i32 (a tagged value) on the stack.
let rec private lower (st : St) (f : Fn) (e : Expr) : unit =
    match e with
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
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when (dictTryFind st.Funcs (key v)).IsSome ->
        for a in args do lower st f a
        callf f (fn v)
    | EApp (g, args) ->
        // no closures in slice 1
        lower st f g
        for a in args do lower st f a |> ignore
        err st "wasm-linear slice: indirect / closure application not supported yet"
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
    | ESeq xs | EApp (_, xs) -> for x in xs do scanLets st f x
    | EIf (c, a, b) -> scanLets st f c; scanLets st f a; scanLets st f b
    | EWhile (c, b) -> scanLets st f c; scanLets st f b
    | EAssign (_, r) -> scanLets st f r
    | EPrim (_, xs) -> for x in xs do scanLets st f x
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
          Locals = dictNew (); Consts = dictNew (); ConstNext = CONST_BASE; ConstData = bytesNew () }
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
    // intern all string constants FIRST, so the heap starts after them
    for d in decls do
        match d with DLet (_, _, _, e) -> scanConsts st e | _ -> ()
    globalI32Mut m "$hp" st.ConstNext
    exportFn m "_start" "$_start"
    // runtime bodies
    emitLalloc m; emitStrOfInt m; emitStrCat m; emitPrints m
    // function bodies
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            st.Locals <- dictNew ()
            let f = beginFn m (ps |> List.map (fun (pv, _) -> paramNm pv))
            // params are locals 0..: record them by their Core key
            for pv, _ in ps do dictSet st.Locals (key pv) (paramNm pv)
            scanLets st f body
            localsDone f
            lower st f body
            endFn f
        | _ -> ()
    // init bodies
    let mutable ii = 0
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) ->
            st.Locals <- dictNew ()
            let f = beginFn m []
            scanLets st f rhs
            localsDone f
            lower st f rhs
            gs f (gl v)
            endFn f
            ii <- ii + 1
        | _ -> ()
    // _start: run every init in order
    let f = beginFn m []
    localsDone f
    for nm in vecToList inits do callf f nm
    endFn f
    // bake the constant data at CONST_BASE; $hp already starts after it
    activeData m CONST_BASE (bytesToArray st.ConstData)
    let pages = (st.ConstNext / 65536) + 64
    let bytes = assembleWith m pages false ""
    bytes, vecToList st.Errors

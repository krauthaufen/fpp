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
// Every heap object carries a DESCRIPTOR pointer at offset 0 — a static
// structure baked into the data segment holding the type's class-id (and,
// later, its vtable). Linear memory has no runtime type information, so this
// word IS the type of a value: `x :? T` and interface dispatch read it. The
// object's own content (fields, tag, elements, payload) begins after it.
let private HDR = 4           // bytes: the descriptor-pointer header
// static memory map (bytes): the fd_write iovec and scratch live low, then
// string constants and descriptors, then the bump heap.
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
      /// interned string literals -> their constant address
      Consts : Dict<string, int>
      mutable ConstNext : int
      ConstData : Bytes
      /// a NESTED lambda node -> the lifted function name it became
      LamName : RefMap<Expr, string>
      /// every lifted lambda, in emission order: (name, param, body, captures)
      Lams : Vec<string * (VarId * Scheme) * Expr * (string * int) list>
      /// while emitting a lifted lambda body: captured key -> its env slot
      mutable Captures : Dict<string, int>
      /// record name -> its field names in DECLARED order (an offset each)
      RecFields : Dict<string, string list>
      /// union case name -> its tag (index) and its payload arity
      UnionTag : Dict<string, int>
      UnionArity : Dict<string, int>
      /// the descriptor word stored at every object's offset 0: a type's
      /// class-id. type name -> class-id, and a union CASE -> its union's id
      ClassId : Dict<string, int>
      CaseClass : Dict<string, int>
      /// interface dispatch: "bareIface|method" -> vtable slot; the row width;
      /// the base address of the flat [class-id][slot] vtable in linear memory;
      /// and, for hierarchy type tests, a class/interface name -> the set of
      /// class-ids it accepts (itself + subclasses, or its implementors)
      SlotOf : Dict<string, int>
      mutable NSlots : int
      mutable VtBase : int
      TestIds : Dict<string, int list>
      /// set when the program throws or catches, so the module declares the
      /// exception tag and asks the assembler for the tag section
      mutable UsesExn : bool
      /// keys of let-bound mutables that a closure captures: they live in a
      /// heap CELL (a 1-word box) so the capture shares the mutation. Reads
      /// dereference, writes store, the capture passes the pointer.
      CellVars : Dict<string, bool> }

// reserved class-ids for the built-in shapes that have no declared type name;
// declared records and unions are numbered above these
let private CID_TUPLE = 0
let private CID_ARRAY = 1
let private CID_LIST = 2
let private CID_CLOSURE = 3
let private CID_FLOAT = 4
let private CID_INT64 = 5
let private CID_STRING = 6
let private CID_FIRST_USER = 7

let private CLO_KIND = 2

// the slot key for an interface method uses the interface's BARE name: the
// declaration, an impl clause and a dispatch site spell its arity and type
// arguments differently, but all mean one slot
let private bareIfaceOf (n : string) : string =
    let n = if n.Contains "$<" then n.Substring (0, n.IndexOf "$<") else n
    match n.IndexOf '`' with i when i > 0 -> n.Substring (0, i) | _ -> n

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
        // header = the string class-id (nunits @4 and units @8 unchanged, so
        // the string runtime functions need no adjustment)
        emitByte st.ConstData (CID_STRING &&& 0xFF); emitByte st.ConstData ((CID_STRING >>> 8) &&& 0xFF)
        emitByte st.ConstData ((CID_STRING >>> 16) &&& 0xFF); emitByte st.ConstData ((CID_STRING >>> 24) &&& 0xFF)
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
    tyFunc m "$lt_iii2i" [ "i32"; "i32"; "i32" ] [ "i32" ]
    tyFunc m "$lt_i2v" [ "i32" ] []
    tyFunc m "$lt_v2v" [] []
    tyFunc m "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    // the closure calling convention: (environment, argument) -> result
    tyFunc m "$lclo" [ "i32"; "i32" ] [ "i32" ]
    // the exception tag carries the thrown value (a tagged i32)
    tyFunc m "$exntag" [ "i32" ] []


let private rtDeclsLin (m : Mod) : unit =
    importFn m "wasi_snapshot_preview1" "fd_write" "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    exportMem m "memory"
    declFn m "$lalloc" "$lt_i2i"
    declFn m "$str_of_int" "$lt_i2i"
    declFn m "$str_cat" "$lt_ii2i"
    declFn m "$prints" "$lt_i2v"
    declFn m "$ftoa6" "$lt_i2i"
    declFn m "$streq" "$lt_ii2i"
    declFn m "$str_starts" "$lt_ii2i"
    declFn m "$str_ends" "$lt_ii2i"
    declFn m "$str_find" "$lt_iii2i"
    declFn m "$strsub" "$lt_iii2i"
    declFn m "$str_trim" "$lt_i2i"

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
    lg f "$x"; ic f HDR; ins f "i32.add"; mem f "f64.load"; ls f "$v"
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

// $streq(a, b): value equality of two strings. 1 when equal, 0 otherwise —
// same pointer short-circuits, then length, then unit-by-unit. String
// PATTERNS (`match name with "i32.add" -> …`) compile to this.
let private emitStreq (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    local f "$la" "i32"; local f "$i" "i32"
    localsDone f
    lg f "$a"; lg f "$b"; ins f "i32.eq"
    ifE f; ic f 1; ins f "return"; endB f
    lg f "$a"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$la"
    lg f "$la"; lg f "$b"; ic f 4; ins f "i32.add"; mem f "i32.load"; ins f "i32.ne"
    ifE f; ic f 0; ins f "return"; endB f
    ic f 0; ls f "$i"
    blockE f "$sc"; loopE f "$sl"
    lg f "$i"; lg f "$la"; ins f "i32.ge_u"; brIf f "$sc"
    lg f "$a"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$b"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    ins f "i32.ne"
    ifE f; ic f 0; ins f "return"; endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$sl"; endB f; endB f
    ic f 1
    endFn f

// string-method runtime, over the [cid][nunits@4][u16 units@8] layout. u16 unit
// i of string x is at x + 8 + 2*i; its length is the word at x + 4.

// $str_starts(s, p): 1 if s begins with p
let private emitStrStarts (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$p" ]
    local f "$pl" "i32"; local f "$sl" "i32"; local f "$i" "i32"
    localsDone f
    lg f "$p"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$pl"
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$sl"
    lg f "$pl"; lg f "$sl"; ins f "i32.gt_s"
    ifE f; ic f 0; ins f "return"; endB f
    ic f 0; ls f "$i"
    blockE f "$c"; loopE f "$l"
    lg f "$i"; lg f "$pl"; ins f "i32.ge_s"; brIf f "$c"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    ins f "i32.ne"
    ifE f; ic f 0; ins f "return"; endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$l"; endB f; endB f
    ic f 1
    endFn f

// $str_ends(s, p): 1 if s ends with p (compare p against s from offset sl-pl)
let private emitStrEnds (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$p" ]
    local f "$pl" "i32"; local f "$sl" "i32"; local f "$i" "i32"; local f "$off" "i32"
    localsDone f
    lg f "$p"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$pl"
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$sl"
    lg f "$pl"; lg f "$sl"; ins f "i32.gt_s"
    ifE f; ic f 0; ins f "return"; endB f
    lg f "$sl"; lg f "$pl"; ins f "i32.sub"; ls f "$off"
    ic f 0; ls f "$i"
    blockE f "$c"; loopE f "$l"
    lg f "$i"; lg f "$pl"; ins f "i32.ge_s"; brIf f "$c"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$off"; lg f "$i"; ins f "i32.add"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    ins f "i32.ne"
    ifE f; ic f 0; ins f "return"; endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$l"; endB f; endB f
    ic f 1
    endFn f

// $str_find(s, p, from): index of the first occurrence of p in s at or after
// `from`, or -1. An empty pattern matches at `from`.
let private emitStrFind (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$p"; "$from" ]
    local f "$pl" "i32"; local f "$sl" "i32"; local f "$j" "i32"; local f "$k" "i32"; local f "$mm" "i32"
    localsDone f
    lg f "$p"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$pl"
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$sl"
    lg f "$pl"; ins f "i32.eqz"
    ifE f; lg f "$from"; ins f "return"; endB f
    lg f "$from"; ls f "$j"
    blockE f "$jc"; loopE f "$jl"
    lg f "$j"; lg f "$sl"; lg f "$pl"; ins f "i32.sub"; ins f "i32.gt_s"; brIf f "$jc"
    ic f 1; ls f "$mm"; ic f 0; ls f "$k"
    blockE f "$kc"; loopE f "$kl"
    lg f "$k"; lg f "$pl"; ins f "i32.ge_s"; brIf f "$kc"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$j"; lg f "$k"; ins f "i32.add"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$k"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    ins f "i32.ne"
    ifE f; ic f 0; ls f "$mm"; br f "$kc"; endB f
    lg f "$k"; ic f 1; ins f "i32.add"; ls f "$k"
    br f "$kl"; endB f; endB f
    lg f "$mm"; ifE f; lg f "$j"; ins f "return"; endB f
    lg f "$j"; ic f 1; ins f "i32.add"; ls f "$j"
    br f "$jl"; endB f; endB f
    ic f -1
    endFn f

// $strsub(s, start, len): a fresh string of s' units [start, start+len)
let private emitStrsub (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$start"; "$len" ]
    local f "$p" "i32"; local f "$i" "i32"
    localsDone f
    ic f 8; lg f "$len"; ic f 1; ins f "i32.shl"; ins f "i32.add"; callf f "$lalloc"; ls f "$p"
    lg f "$p"; ic f CID_STRING; mem f "i32.store"
    lg f "$p"; ic f 4; ins f "i32.add"; lg f "$len"; mem f "i32.store"
    ic f 0; ls f "$i"
    blockE f "$c"; loopE f "$l"
    lg f "$i"; lg f "$len"; ins f "i32.ge_s"; brIf f "$c"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$start"; lg f "$i"; ins f "i32.add"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$l"; endB f; endB f
    lg f "$p"
    endFn f

// $str_trim(s): s with leading and trailing ASCII whitespace removed. Finds
// the first and last non-space unit, then reuses $strsub for the copy.
let private emitStrTrim (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$sl" "i32"; local f "$i" "i32"; local f "$j" "i32"; local f "$u" "i32"
    localsDone f
    let isWs () =
        lg f "$u"; ic f 0x20; ins f "i32.eq"
        lg f "$u"; ic f 0x09; ins f "i32.eq"; ins f "i32.or"
        lg f "$u"; ic f 0x0A; ins f "i32.eq"; ins f "i32.or"
        lg f "$u"; ic f 0x0D; ins f "i32.eq"; ins f "i32.or"
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$sl"
    ic f 0; ls f "$i"
    blockE f "$sc"; loopE f "$sl2"
    lg f "$i"; lg f "$sl"; ins f "i32.ge_s"; brIf f "$sc"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ls f "$u"
    isWs (); ins f "i32.eqz"; brIf f "$sc"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$sl2"; endB f; endB f
    lg f "$sl"; ls f "$j"
    blockE f "$ec"; loopE f "$el"
    lg f "$j"; lg f "$i"; ins f "i32.le_s"; brIf f "$ec"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$j"; ic f 1; ins f "i32.sub"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ls f "$u"
    isWs (); ins f "i32.eqz"; brIf f "$ec"
    lg f "$j"; ic f 1; ins f "i32.sub"; ls f "$j"
    br f "$el"; endB f; endB f
    lg f "$s"; lg f "$i"; lg f "$j"; lg f "$i"; ins f "i32.sub"; callf f "$strsub"
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

// which let-bound mutables need a heap cell: those that are ASSIGNED and also
// referenced INSIDE a lambda (captured). A top-level function's outermost
// lambda IS the function, not a capture boundary, so its params are skipped.
let private cellScan (decls : Decl list) : Dict<string, bool> =
    let letBound = dictNew<string, bool> ()
    let assigned = dictNew<string, bool> ()
    let inLambda = dictNew<string, bool> ()
    let rec go (depth : int) (e : Expr) : unit =
        let g = go depth
        match e with
        | EVar (v, _) | EVarI (v, _, _) -> if depth > 0 then dictSet inLambda (key v) true
        | ELam (_, b) -> go (depth + 1) b
        | EAssign (v, x) ->
            dictSet assigned (key v) true
            (if depth > 0 then dictSet inLambda (key v) true)
            g x
        | ELet (_, v, _, EApp (EUnknown "$forcecell", [ r ]), b) ->
            dictSet letBound (key v) true; dictSet assigned (key v) true; dictSet inLambda (key v) true; g r; g b
        | ELet (_, v, _, r, b) -> dictSet letBound (key v) true; g r; g b
        | EApp (fn, args) -> g fn; List.iter g args
        | EIf (a, b, c) -> g a; g b; g c
        | EMatch (s, cs) | ETry (s, cs) ->
            g s
            for _, gd, b in cs do (match gd with Some gd -> g gd | None -> ()); g b
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) -> List.iter g xs
        | ERecord (_, fs) -> for _, v in fs do g v
        | ERecordExt (_, b, fs) -> g b; (for _, v in fs do g v)
        | EField (r, _, _) -> g r
        | EFieldSet (r, _, _, v) -> g r; g v
        | EWhile (c, b) -> g c; g b
        | EIndex (_, a, i) -> g a; g i
        | EIndexSet (_, a, i, v) -> g a; g i; g v
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) | ECast (_, a, _) | ETypeTest (_, a) -> g a
        | EArrayCreate (_, n, v) -> g n; g v
        | EIfaceCall (_, _, recv, args) -> g recv; List.iter g args
        | _ -> ()
    let skipParams (e : Expr) : Expr = match e with ELam (_, b) -> b | _ -> e
    for d in decls do match d with DLet (_, _, _, e) -> go 0 (skipParams e) | _ -> ()
    let cells = dictNew<string, bool> ()
    for k, _ in dictPairs assigned do
        if (dictTryFind letBound k).IsSome && (dictTryFind inLambda k).IsSome then dictSet cells k true
    cells

// ---- lambda lifting -------------------------------------------------------
// the variables a pattern binds (so a match/try arm's binders shadow the
// captured set); mirrors the shape lowPatTest binds
let rec private patBinders (p : Pat) : VarId list =
    match p with
    | PVar (v, _) -> [ v ]
    | PAs (inner, v, _) -> v :: patBinders inner
    | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.collect patBinders ps
    | PCons (a, b) -> patBinders a @ patBinders b
    | _ -> []

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
        | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> for x in xs do go bnd x
        | EApp (g, xs) -> go bnd g; for x in xs do go bnd x
        | EIf (a, b, c) | EIndexSet (_, a, b, c) -> go bnd a; go bnd b; go bnd c
        | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> go bnd a; go bnd b
        | EAssign (_, x) -> go bnd x
        | EField (r, _, _) | EArrayLen (_, r) | ECast (_, r, _) | ETypeTest (_, r) | EArrayPin (_, r) | EArrayUnpin (_, r) | EArrayBytes (_, r) -> go bnd r
        | EFieldSet (r, _, _, x) -> go bnd r; go bnd x
        | ERecord (_, fs) -> for _, x in fs do go bnd x
        | ERecordExt (_, b, fs) -> go bnd b; for _, x in fs do go bnd x
        | EIfaceCall (_, _, r, xs) -> go bnd r; for x in xs do go bnd x
        | EMatch (s, cs) | ETry (s, cs) ->
            go bnd s
            for pat, guard, body2 in cs do
                let bnd2 = dictNew<string, bool> ()
                for kv in dictPairs bnd do dictSet bnd2 (fst kv) (snd kv)
                for v in patBinders pat do dictSet bnd2 (key v) true
                (match guard with Some g -> go bnd2 g | None -> ())
                go bnd2 body2
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
    | ELet (_, _, _, a, b) | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> discover st a; discover st b
    | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> for x in xs do discover st x
    | EApp (g, xs) -> discover st g; for x in xs do discover st x
    | EIf (a, b, c) | EIndexSet (_, a, b, c) -> discover st a; discover st b; discover st c
    | EAssign (_, x) -> discover st x
    | EField (r, _, _) | EArrayLen (_, r) | ECast (_, r, _) | ETypeTest (_, r) | EArrayPin (_, r) | EArrayUnpin (_, r) | EArrayBytes (_, r) -> discover st r
    | EFieldSet (r, _, _, x) -> discover st r; discover st x
    | ERecord (_, fs) -> for _, x in fs do discover st x
    | ERecordExt (_, b, fs) -> discover st b; for _, x in fs do discover st x
    | EIfaceCall (_, _, r, xs) -> discover st r; for x in xs do discover st x
    | EMatch (s, cs) | ETry (s, cs) ->
        discover st s
        for _, guard, body2 in cs do
            (match guard with Some g -> discover st g | None -> ())
            discover st body2
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
    | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> for x in xs do scanConsts st x
    // the function position matters: an eta-expansion lambda lives there and
    // may hold string literals (a missed one is interned late, past $hp, and
    // the first allocation overwrites it)
    | EApp (g, xs) -> scanConsts st g; for x in xs do scanConsts st x
    | EAssign (_, r) | EField (r, _, _) | EArrayLen (_, r) | ECast (_, r, _) | ETypeTest (_, r) -> scanConsts st r
    | EFieldSet (r, _, _, v) -> scanConsts st r; scanConsts st v
    | ELam (_, b) -> scanConsts st b
    | EMatch (s, cs) -> scanConsts st s; for _, g, b in cs do (match g with Some x -> scanConsts st x | None -> ()); scanConsts st b
    | ERecord (_, fs) -> for _, v in fs do scanConsts st v
    | ERecordExt (_, b, fs) -> scanConsts st b; for _, v in fs do scanConsts st v
    | EIfaceCall (_, _, r, xs) -> scanConsts st r; for x in xs do scanConsts st x
    | ETry (b, cs) -> scanConsts st b; for _, g, x in cs do (match g with Some y -> scanConsts st y | None -> ()); scanConsts st x
    | _ -> ()

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
// the class-id descriptor for a record type / a union case's union; -1 for an
// undeclared name (a value no type test looks for)
let private cidRec (st : St) (name : string) : int = match dictTryFind st.ClassId name with Some c -> c | None -> 0 - 1
let private cidCase (st : St) (case : string) : int = match dictTryFind st.CaseClass case with Some c -> c | None -> 0 - 1
// the class-id a `:? T` / `:?>` looks for. An instantiated name tests its
// erased head (the header carries no type arguments); an unknown name yields
// -1, which no object header holds, so the test is a safe false.
let private typeTestCid (st : St) (tn0 : string) : int =
    let tn = if tn0.Contains "$<" then tn0.Substring (0, tn0.IndexOf "$<") else tn0
    match dictTryFind st.ClassId tn with Some c -> c | None -> 0 - 1
// the SET of class-ids `:? T` accepts: a class' own id plus its subclasses',
// an interface's implementors', or a record/union's single id
let private typeTestIds (st : St) (tn0 : string) : int list =
    let tn = if tn0.Contains "$<" then tn0.Substring (0, tn0.IndexOf "$<") else tn0
    match dictTryFind st.TestIds tn with
    | Some xs -> xs
    | None ->
        match dictTryFind st.TestIds (bareIfaceOf tn) with
        | Some xs -> xs
        | None -> match dictTryFind st.ClassId tn with Some c -> [ c ] | None -> []
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
    | ELit (LChar raw) -> lowInt (Fpp.Backend.BinDriver.charCode raw)
    | ELit LUnit | ELit LNull -> lowInt 0
    | ELit (LString s) -> LConstW (internStr st s)
    | EVar (v, _) | EVarI (v, _, _) -> lowVarByKey ctx (key v)
    | ELet (_, v, _, rhs, body) ->
        let id = freshReg ctx (key v)
        let init = if (dictTryFind st.CellVars (key v)).IsSome then lowMkCell ctx (coreToLowE ctx rhs) else coreToLowE ctx rhs
        LDo ([ LSet (wReg id, init) ], coreToLowE ctx body)
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
    | EPrim ("u-l", [ a ]) -> lowBoxI ctx (LPrim (SubL, [ LConstL 0L; lowUnboxI (coreToLowE ctx a) ]))
    | EPrim (("u-" | "u-i"), [ a ]) -> lowTag (LPrim (SubW, [ LConstW 0; lowUntag (coreToLowE ctx a) ]))
    | EPrim (("unot" | "not"), [ a ]) -> lowTag (LPrim (EqW, [ lowUntag (coreToLowE ctx a); LConstW 0 ]))
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
    | EPrim ("::", [ h; t ]) -> lowObj ctx CID_LIST [ coreToLowE ctx h; coreToLowE ctx t ]
    | EPrim (op, [ a; b ]) ->
        let bop = baseOp op
        let la = lowUntag (coreToLowE ctx a)
        let lb = lowUntag (coreToLowE ctx b)
        if List.contains bop [ "+"; "-"; "*"; "/"; "%" ]
        then lowTag (LPrim (intArithOp bop, [ la; lb ]))
        else lowTag (LPrim (intCmpOp bop, [ la; lb ]))
    | ETuple xs -> lowObj ctx CID_TUPLE (List.map (coreToLowE ctx) xs)
    | EListLit xs -> lowList ctx xs
    | ERecord (name, fields) ->
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst fields
        lowObj ctx (cidRec st name) (order |> List.map (fun fnm ->
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
                | None -> LLoad (W, LGet (wReg b), HDR + 4 * i))
        LDo ([ LSet (wReg b, coreToLowE ctx baseE) ], lowObj ctx (cidRec st name) slots)
    | ECtor (case, _, args) ->
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        lowObj ctx (cidCase st case) (LConstW tag :: List.map (coreToLowE ctx) args)
    | EField (r, fname, owner) ->
        let idx =
            match dictTryFind st.RecFields owner with
            | Some order -> (match List.tryFindIndex (fun x -> x = fname) order with Some i -> i | None -> 0)
            | None -> 0
        LLoad (W, coreToLowE ctx r, HDR + 4 * idx)
    | EFieldSet (r, fname, owner, v) ->
        let idx =
            match dictTryFind st.RecFields owner with
            | Some order -> (match List.tryFindIndex (fun x -> x = fname) order with Some i -> i | None -> 0)
            | None -> 0
        LDo ([ LStore (W, coreToLowE ctx r, HDR + 4 * idx, coreToLowE ctx v) ], lowInt 0)
    | EArray (_, xs) -> lowObj ctx CID_ARRAY (LConstW (List.length xs) :: List.map (coreToLowE ctx) xs)
    | EIndex (_, arr, i) ->
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ lowUntag (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LLoad (W, addr, HDR)
    | EIndexSet (_, arr, i, v) ->
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ lowUntag (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LDo ([ LStore (W, addr, HDR, coreToLowE ctx v) ], lowInt 0)
    | EArrayLen (_, arr) -> lowTag (LLoad (W, coreToLowE ctx arr, HDR))
    | EArrayCreate (_, n, init) ->
        let cnt = freshTmp ctx
        let iv = freshTmp ctx
        let bs = freshTmp ctx
        let it = freshTmp ctx
        let stmts =
            [ LSet (wReg cnt, lowUntag (coreToLowE ctx n))
              LSet (wReg iv, coreToLowE ctx init)
              LSet (wReg bs, LAlloc (LPrim (AddW, [ LConstW (HDR + 4); LPrim (MulW, [ LGet (wReg cnt); LConstW 4 ]) ])))
              LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY)
              LStore (W, LGet (wReg bs), HDR, LGet (wReg cnt))
              LSet (wReg it, LConstW 0)
              LWhile (LPrim (LtUW, [ LGet (wReg it); LGet (wReg cnt) ]),
                      [ LStore (W, LPrim (AddW, [ LGet (wReg bs); LPrim (MulW, [ LPrim (AddW, [ LGet (wReg it); LConstW 1 ]); LConstW 4 ]) ]), HDR, LGet (wReg iv))
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
    // char and int share the tagged-int representation, so `int c` / `char i`
    // are the identity
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#c" || n.StartsWith "char" -> coreToLowE ctx a
    // int from float: unbox, truncate, tag
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#f" -> lowTag (LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ]))
    | EApp (EUnknown "isNull", [ x ]) -> lowTag (LPrim (EqW, [ coreToLowE ctx x; LConstW 0 ]))
    | EApp (EUnknown ("refEq" | "$refeq"), [ a; b ]) -> lowTag (LPrim (EqW, [ coreToLowE ctx a; coreToLowE ctx b ]))
    // cells: $cellof yields the cell POINTER (its storage, no deref); $cellget
    // reads through it; $cellset writes; $forcecell is a marker
    | EApp (EUnknown "$cellof", [ (EVar (v, _) | EVarI (v, _, _)) ]) -> lowVarStore ctx (key v)
    | EApp (EUnknown "$cellget", [ c ]) -> LLoad (W, coreToLowE ctx c, 0)
    | EApp (EUnknown "$cellset", [ c; v ]) -> LDo ([ LStore (W, coreToLowE ctx c, 0, coreToLowE ctx v) ], lowInt 0)
    | EApp (EUnknown "$forcecell", [ r ]) -> coreToLowE ctx r
    | EApp (EUnknown "$str.StartsWith", [ s; p ]) -> lowTag (LCall ("$str_starts", [ coreToLowE ctx s; coreToLowE ctx p ]))
    | EApp (EUnknown "$str.EndsWith", [ s; p ]) -> lowTag (LCall ("$str_ends", [ coreToLowE ctx s; coreToLowE ctx p ]))
    | EApp (EUnknown "$str.Contains", [ s; p ]) ->
        lowTag (LPrim (GeSW, [ LCall ("$str_find", [ coreToLowE ctx s; coreToLowE ctx p; LConstW 0 ]); LConstW 0 ]))
    | EApp (EUnknown "$str.IndexOf", [ s; p ]) ->
        lowTag (LCall ("$str_find", [ coreToLowE ctx s; coreToLowE ctx p; LConstW 0 ]))
    | EApp (EUnknown "$str.Trim", [ s ]) -> LCall ("$str_trim", [ coreToLowE ctx s ])
    | EApp (EUnknown ("$str.Substring#2" | "strsub"), [ s; start; len ]) ->
        LCall ("$strsub", [ coreToLowE ctx s; lowUntag (coreToLowE ctx start); lowUntag (coreToLowE ctx len) ])
    | EApp (EUnknown "$str.Substring", [ s; start ]) ->
        // one-arg Substring runs to the end: len = s.Length - start
        let ts = freshTmp ctx
        let ti = freshTmp ctx
        LDo ([ LSet (wReg ts, coreToLowE ctx s); LSet (wReg ti, lowUntag (coreToLowE ctx start)) ],
             LCall ("$strsub", [ LGet (wReg ts); LGet (wReg ti); LPrim (SubW, [ LLoad (W, LGet (wReg ts), 4); LGet (wReg ti) ]) ]))
    | EApp (EUnknown "$listLength", [ l ]) ->
        // walk the cons cells ([cid][head][tail], null = 0) counting nodes
        let p = freshTmp ctx
        let n = freshTmp ctx
        LDo ([ LSet (wReg p, coreToLowE ctx l)
               LSet (wReg n, LConstW 0)
               LWhile (LPrim (NeW, [ LGet (wReg p); LConstW 0 ]),
                       [ LSet (wReg n, LPrim (AddW, [ LGet (wReg n); LConstW 1 ]))
                         LSet (wReg p, LLoad (W, LGet (wReg p), HDR + 4)) ]) ],
             lowTag (LGet (wReg n)))
    | EApp (EUnknown "failwith", [ msg ]) ->
        LDo ([ LThrow (lowFailure ctx (coreToLowE ctx msg)) ], lowInt 0)
    | EApp (EUnknown "raise", [ ex ]) ->
        st.UsesExn <- true
        LDo ([ LThrow (coreToLowE ctx ex) ], lowInt 0)
    | EApp (EUnknown ("invalidArg" | "invalidOp" | "nullArg"), args) ->
        // approximate as Failure(message): the last argument is the message
        let msg = match List.rev args with m :: _ -> coreToLowE ctx m | [] -> LConstW 0
        LDo ([ LThrow (lowFailure ctx msg) ], lowInt 0)
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
    | ETypeTest (tn, e2) -> lowTag (lowTypeTest ctx tn (coreToLowE ctx e2))
    | ECast (tn, e2, true) when not (List.isEmpty (typeTestIds st tn)) ->
        // `:?>` downcast to a type we carry a class-id for: check the header
        // and trap on a mismatch, then yield the value unchanged
        let t = freshTmp ctx
        LDo ([ LSet (wReg t, coreToLowE ctx e2)
               LIf (LPrim (EqW, [ lowTypeTest ctx tn (LGet (wReg t)); LConstW 0 ]), [ LTrap ], []) ],
             LGet (wReg t))
    | ECast (_, e2, _) ->
        // `:>` widening, and `:?>` to a type without a class-id: the identity —
        // the representation does not change under a cast in the tagged model
        coreToLowE ctx e2
    | EIfaceCall (iface, method, recv, args) ->
        // dispatch through the vtable: the receiver's class-id header indexes a
        // row, the slot the column; the word there is the impl's table index
        let slot = match dictTryFind st.SlotOf (bareIfaceOf iface + "|" + method) with Some s -> s | None -> 0
        let t = freshTmp ctx
        let cid = LLoad (W, LGet (wReg t), 0)
        let idxAddr =
            LPrim (AddW, [ LConstW st.VtBase
                           LPrim (MulW, [ LPrim (AddW, [ LPrim (MulW, [ cid; LConstW st.NSlots ]); LConstW slot ]); LConstW 4 ]) ])
        let callArgs = LGet (wReg t) :: List.map (coreToLowE ctx) args
        LDo ([ LSet (wReg t, coreToLowE ctx recv) ],
             LCallIdx (1 + List.length args, LLoad (W, idxAddr, 0), callArgs))
    | ETry (body, clauses) ->
        // run body; a throw is caught into `exn` and matched against the
        // clauses (each a block that binds and breaks to $tdone on a match);
        // no match re-throws. Same clause shape as a match, over the exn value.
        st.UsesExn <- true
        let res = freshTmp ctx
        let exn = freshTmp ctx
        let catchStmts =
            clauses |> List.map (fun (pat, guard, handler) ->
                let tests = lowPatTest ctx exn "$cnext" pat
                let guardStmt =
                    match guard with
                    | Some g -> [ LBreakIf ("$cnext", LPrim (EqW, [ lowUntag (coreToLowE ctx g); LConstW 0 ])) ]
                    | None -> []
                LBlock ("$cnext", tests @ guardStmt @ [ LSet (wReg res, coreToLowE ctx handler); LBreak "$tdone" ]))
        LDo ([ LTryStmt (coreToLowE ctx body, wReg res, wReg exn, catchStmts) ], LGet (wReg res))
    | _ ->
        let what =
            match e with
            | EUnknown n -> "unknown " + n
            | EApp (EUnknown n, _) -> "apply-unknown " + n
            | EPrim (op, _) -> "prim " + op
            | EArrayPin _ -> "arraypin" | EArrayUnpin _ -> "arrayunpin" | EArrayBytes _ -> "arraybytes"
            | ELit _ -> "lit" | _ -> "node"
        err st ("wasm-linear LowIR: unsupported " + what); lowInt 0

and private coreToLowS (ctx : LowCtx) (e : Expr) : LStmt list =
    match e with
    | ESeq xs -> List.collect (coreToLowS ctx) xs
    | ELet (_, v, _, rhs, body) ->
        let id = freshReg ctx (key v)
        let init = if (dictTryFind ctx.LSt.CellVars (key v)).IsSome then lowMkCell ctx (coreToLowE ctx rhs) else coreToLowE ctx rhs
        LSet (wReg id, init) :: coreToLowS ctx body
    | EAssign (v, rhs) when (dictTryFind ctx.LSt.CellVars (key v)).IsSome ->
        // a captured mutable: store into its cell (shared with the closure)
        [ LStore (W, lowVarStore ctx (key v), 0, coreToLowE ctx rhs) ]
    | EAssign (v, rhs) ->
        (match dictTryFind ctx.Regs (key v) with
         | Some id -> [ LSet (wReg id, coreToLowE ctx rhs) ]
         | None when (dictTryFind ctx.LSt.Globals (key v)).IsSome -> [ LSetGlobal (gl v, coreToLowE ctx rhs) ]
         | None -> err ctx.LSt ("wasm-linear LowIR: assignment to unbound " + v.Name); [ LEval (coreToLowE ctx rhs) ])
    | EIf (c, a, b) -> [ LIf (lowUntag (coreToLowE ctx c), coreToLowS ctx a, coreToLowS ctx b) ]
    | EWhile (c, b) -> [ LWhile (lowUntag (coreToLowE ctx c), coreToLowS ctx b) ]
    | ELit LUnit -> []
    | EApp (EUnknown "prints", [ a ]) -> [ LCallVoidS ("$prints", [ coreToLowE ctx a ]) ]
    | _ -> [ LEval (coreToLowE ctx e) ]

// allocate an object: the class-id descriptor at offset 0, then each slot at
// HDR + 4*i. A fresh register holds the base, so nesting is safe with no
// scratch pool — the IR gives every allocation its own register.
and private lowObj (ctx : LowCtx) (cid : int) (slots : LExpr list) : LExpr =
    let n = List.length slots
    let b = freshTmp ctx
    let stores =
        LStore (W, LGet (wReg b), 0, LConstW cid)
        :: (slots |> List.mapi (fun i v -> LStore (W, LGet (wReg b), HDR + 4 * i, v)))
    LDo (LSet (wReg b, LAlloc (LConstW (HDR + 4 * n))) :: stores, LGet (wReg b))

and private lowList (ctx : LowCtx) (xs : Expr list) : LExpr =
    match xs with
    | [] -> LConstW 0
    | x :: rest -> lowObj ctx CID_LIST [ coreToLowE ctx x; lowList ctx rest ]

// a boxed 64-bit payload: the class-id header then an 8-byte payload at HDR;
// the wide type on the LStore/LLoad picks f64/i64 access
and private lowBoxF (ctx : LowCtx) (fv : LExpr) : LExpr =
    let b = freshTmp ctx
    LDo ([ LSet (wReg b, LAlloc (LConstW (HDR + 8))); LStore (W, LGet (wReg b), 0, LConstW CID_FLOAT); LStore (F64, LGet (wReg b), HDR, fv) ], LGet (wReg b))

and private lowUnboxF (p : LExpr) : LExpr = LLoad (F64, p, HDR)

and private lowBoxI (ctx : LowCtx) (iv : LExpr) : LExpr =
    let b = freshTmp ctx
    LDo ([ LSet (wReg b, LAlloc (LConstW (HDR + 8))); LStore (W, LGet (wReg b), 0, LConstW CID_INT64); LStore (I64, LGet (wReg b), HDR, iv) ], LGet (wReg b))

and private lowUnboxI (p : LExpr) : LExpr = LLoad (I64, p, HDR)

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
        // a union case is [cid][tag][payload…]; the tag distinguishes cases
        let tagTest = LBreakIf (fail, LPrim (NeW, [ LLoad (W, sc, HDR); LConstW tag ]))
        tagTest :: List.concat (subs |> List.mapi (fun i sub ->
            let t = freshTmp ctx
            LSet (wReg t, LLoad (W, sc, HDR + 4 * (i + 1))) :: lowPatTest ctx t fail sub))
    | PTuple subs ->
        List.concat (subs |> List.mapi (fun i sub ->
            let t = freshTmp ctx
            LSet (wReg t, LLoad (W, sc, HDR + 4 * i)) :: lowPatTest ctx t fail sub))
    | PCons (h, tl) ->
        let th = freshTmp ctx
        let tt = freshTmp ctx
        LBreakIf (fail, LPrim (EqW, [ sc; LConstW 0 ]))
        :: (LSet (wReg th, LLoad (W, sc, HDR)) :: lowPatTest ctx th fail h)
        @ (LSet (wReg tt, LLoad (W, sc, HDR + 4)) :: lowPatTest ctx tt fail tl)
    | PListLit [] -> [ LBreakIf (fail, LPrim (NeW, [ sc; LConstW 0 ])) ]
    | PListLit (x :: rest) ->
        // an exact list literal [a; b; …] is a :: b :: … :: []
        lowPatTest ctx scrutReg fail (PCons (x, PListLit rest))
    | PLit (LChar raw) -> [ LBreakIf (fail, LPrim (NeW, [ lowUntag sc; LConstW (Fpp.Backend.BinDriver.charCode raw) ])) ]
    | PLit LNull -> [ LBreakIf (fail, LPrim (NeW, [ sc; LConstW 0 ])) ]
    | PLit (LFloat s) ->
        (match System.Double.TryParse (s, System.Globalization.CultureInfo.InvariantCulture) with
         | true, d -> [ LBreakIf (fail, LPrim (NeF, [ lowUnboxF sc; LConstF d ])) ]
         | _ -> [])
    | PLit (LString raw) ->
        // a string pattern is a value compare: $streq returns 1 when equal
        [ LBreakIf (fail, LPrim (EqW, [ LCall ("$streq", [ sc; LConstW (internStr st raw) ]); LConstW 0 ])) ]
    | POr alts ->
        // try each alternative in its own block; a match breaks past the rest
        // to $por, a mismatch falls to the next. All alternatives bind the same
        // identities, and freshReg's per-VarId reuse makes their slots agree.
        let n = List.length alts
        let nonLast =
            alts |> List.mapi (fun j alt -> j, alt) |> List.filter (fun (j, _) -> j < n - 1)
            |> List.map (fun (_, alt) -> LBlock ("$palt", lowPatTest ctx scrutReg "$palt" alt @ [ LBreak "$por" ]))
        let last = match List.rev alts with a :: _ -> lowPatTest ctx scrutReg fail a | [] -> []
        [ LBlock ("$por", nonLast @ last) ]
    | PTypeTest tn -> [ LBreakIf (fail, LPrim (EqW, [ lowTypeTest ctx tn sc; LConstW 0 ])) ]
    | _ -> [ LTrap ]

// the raw STORAGE a variable occupies: a local/param register, an env slot (in
// a lifted lambda body), or a module global. For a cell var this content is the
// CELL POINTER; for an ordinary var it is the value itself.
and private lowVarStore (ctx : LowCtx) (k : string) : LExpr =
    let st = ctx.LSt
    match dictTryFind ctx.Regs k with
    | Some id -> LGet (wReg id)
    | None ->
        match dictTryFind st.Captures k with
        | Some slot when ctx.EnvReg >= 0 -> LLoad (W, LGet (wReg ctx.EnvReg), HDR + 8 + 4 * slot)
        | _ ->
            match st.Globals |> dictPairs |> List.tryFind (fun (gk, _) -> gk = k) with
            | Some _ -> LGetGlobal ("$g" + string (abs (strHash k)))
            | None -> err st ("wasm-linear LowIR: unresolved variable " + k); lowInt 0

// read a variable: dereference the cell for a captured mutable, else the
// storage content directly
and private lowVarByKey (ctx : LowCtx) (k : string) : LExpr =
    let store = lowVarStore ctx k
    if (dictTryFind ctx.LSt.CellVars k).IsSome then LLoad (W, store, 0) else store

// a fresh 1-word cell holding `v` (headerless — cells are internal, never
// type-tested or dispatched on)
and private lowMkCell (ctx : LowCtx) (v : LExpr) : LExpr =
    let b = freshTmp ctx
    LDo ([ LSet (wReg b, LAlloc (LConstW 4)); LStore (W, LGet (wReg b), 0, v) ], LGet (wReg b))

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
    // capture the STORAGE, not the dereferenced value: for a cell var that is
    // the shared pointer, so mutation is visible on both sides
    :: (caps |> List.map (fun (p, o) -> lowVarStore ctx (p + ":" + string o)))
    |> lowObj ctx CID_CLOSURE

and private lowApply (ctx : LowCtx) (cloE : LExpr) (args : Expr list) : LExpr =
    match args with
    | [] -> cloE
    | a :: rest ->
        // bind the closure to a register so LCallIndirect can read it twice
        // (as env and to load the code index) without re-evaluating it
        let tclo = freshTmp ctx
        let step = LDo ([ LSet (wReg tclo, cloE) ], LCallIndirect ([ W ], LGet (wReg tclo), [ coreToLowE ctx a ]))
        lowApply ctx step rest

// `failwith msg` raises Failure(msg) so `with Failure m` catches it; if the
// prelude's Failure case is not in scope, throw the bare message instead
and private lowFailure (ctx : LowCtx) (msg : LExpr) : LExpr =
    ctx.LSt.UsesExn <- true
    match dictTryFind ctx.LSt.UnionTag "Failure" with
    | Some tag -> lowObj ctx (cidCase ctx.LSt "Failure") [ LConstW tag; msg ]
    | None -> msg

// a RAW i32 (0/1): is `v` a heap object whose class-id header is one of those
// `tn` accepts (its own, a subclass', an implementor')? Guards the header load
// behind an even-and-nonzero pointer test, so a tagged int or a null answers 0
// without dereferencing.
and private lowTypeTest (ctx : LowCtx) (tn : string) (v : LExpr) : LExpr =
    let ids = typeTestIds ctx.LSt tn
    let t = freshTmp ctx
    let r = freshTmp ctx
    let h = freshTmp ctx
    let isPtr =
        LPrim (AndW, [ LPrim (EqW, [ LPrim (AndW, [ LGet (wReg t); LConstW 1 ]); LConstW 0 ])
                       LPrim (NeW, [ LGet (wReg t); LConstW 0 ]) ])
    let matchAny = ids |> List.fold (fun acc id -> LPrim (OrW, [ acc; LPrim (EqW, [ LGet (wReg h); LConstW id ]) ])) (LConstW 0)
    LDo ([ LSet (wReg t, v)
           LIf (isPtr,
                [ LSet (wReg h, LLoad (W, LGet (wReg t), 0)); LSet (wReg r, matchAny) ],
                [ LSet (wReg r, LConstW 0) ]) ],
         LGet (wReg r))

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
        // the code index is the word at closure + HDR + 4 (after the class-id
        // header and the kind word). `fp` must be a pure LGet (Core->LowIR
        // binds the closure into a register first), so emitting it twice — once
        // as env, once for the index load — is side-effect free. Stack: env,
        // arg, table-index, then call_indirect.
        emitLowE f fp
        for a in args do emitLowE f a
        emitLowE f (LLoad (W, fp, HDR + 4))
        callIndirect f "$lclo"
    | LCallIdx (nparams, fnidx, args) ->
        // interface dispatch: the args (receiver first), then the table index,
        // then call_indirect with the arity's signature
        for a in args do emitLowE f a
        emitLowE f fnidx
        callIndirect f ("$lfn" + string nparams)
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
    | LThrow e -> emitLowE f e; throwExn f
    | LTryStmt (body, res, exn, catchStmts) ->
        // block $tdone { block $tcatch (i32) { try_table (i32) (catch → $tcatch)
        //   <body:i32> } res := ·; br $tdone } exn := ·; <handler>; rethrow }
        blockE f "$tdone"
        blockI f "$tcatch"
        tryTableI f "$tcatch"
        emitLowE f body
        endB f                       // end try_table — body value on stack
        ls f (regNm res)
        br f "$tdone"
        endB f                       // end $tcatch — caught value on stack
        ls f (regNm exn)
        for s in catchStmts do emitLowS f s
        lg f (regNm exn); throwExn f  // no handler matched: re-throw outward
        endB f                       // end $tdone

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
let private emitLinearImpl (decls0 : Decl list) : byte[] * string list =
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
    // a class' interface-method implementations are reached only through a
    // vtable at run time, never by a static reference — so seed them as roots,
    // or the reachability filter would drop the very functions dispatch calls.
    // Restricted to user impls: prelude class dispatch (and the prelude methods
    // it would pull in, some not yet lowerable) is a later concern.
    for d in decls0 do
        match d with
        | DClass (_, _, _, impls) ->
            for _, ms in impls do
                for _, v in ms do
                    if v.Path <> Fpp.Analysis.Classes.builtinPath then visit (v.Path + ":" + string v.Offset)
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
          Consts = dictNew (); ConstNext = CONST_BASE; ConstData = bytesNew ()
          LamName = refMapNew shallowLamHash; Lams = vecNew ()
          Captures = dictNew ()
          RecFields = dictNew (); UnionTag = dictNew (); UnionArity = dictNew ()
          ClassId = dictNew (); CaseClass = dictNew ()
          SlotOf = dictNew (); NSlots = 0; VtBase = 0; TestIds = dictNew (); UsesExn = false
          CellVars = cellScan decls0 }
    // record layouts, union case tags, and a class-id per declared type (the
    // descriptor word every object of that type carries at offset 0). Records
    // and unions are numbered from CID_FIRST_USER; a union's cases all share
    // its id and are told apart by their tag.
    let mutable nextCid = CID_FIRST_USER
    for d in decls0 do
        match d with
        | DRecord (n, _, fs, _) ->
            dictSet st.RecFields n (fs |> List.map fst)
            if (dictTryFind st.ClassId n).IsNone then (dictSet st.ClassId n nextCid; nextCid <- nextCid + 1)
        | DUnion (uname, _, cs) ->
            let cid = match dictTryFind st.ClassId uname with Some c -> c | None -> (let c = nextCid in dictSet st.ClassId uname c; nextCid <- nextCid + 1; c)
            cs |> List.iteri (fun i (cn, ar) ->
                dictSet st.UnionTag cn i
                dictSet st.UnionArity cn ar
                dictSet st.CaseClass cn cid)
        | _ -> ()
    let nCid = nextCid
    // interface dispatch tables. A method slot is keyed by the BARE interface
    // name and the method (the impl clause, the dispatch site and the decl
    // spell the arity differently, but all mean one slot). slotImpl walks the
    // inheritance chain to the function implementing a slot for a class.
    let classDecls = decls0 |> List.choose (fun d -> match d with DClass (n, b, own, impls) -> Some (n, b, own, impls) | _ -> None)
    let interfaceDecls = decls0 |> List.choose (fun d -> match d with DInterface (n, ms) -> Some (n, ms) | _ -> None)
    let bareIface = bareIfaceOf
    let baseOf (n : string) = classDecls |> List.tryPick (fun (cn, b, _, _) -> if cn = n then b else None)
    let rec chainOf (n : string) : string list =
        match baseOf n with Some b when b <> n -> n :: chainOf b | _ -> [ n ]
    let subclassesOf (n : string) =
        let derived = classDecls |> List.filter (fun (cn, _, _, _) -> List.contains n (chainOf cn)) |> List.map (fun (cn, _, _, _) -> cn)
        if List.isEmpty derived then [ n ] else derived
    let slotImpl (cn : string) (owner : string) (mn : string) : VarId option =
        chainOf cn
        |> List.tryPick (fun c ->
            classDecls
            |> List.tryPick (fun (n2, _, _, impls) ->
                if n2 <> c then None
                else impls |> List.tryPick (fun (i, ms) -> if bareIface i = owner then ms |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None) else None)))
    let vtableSlots =
        ((interfaceDecls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> bareIface i, mn)))
         @ (classDecls |> List.collect (fun (_, _, _, impls) -> impls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> bareIface i, mn)))))
        |> List.distinct |> List.sort
    st.NSlots <- List.length vtableSlots
    vtableSlots |> List.iteri (fun i (ifn, mn) -> dictSet st.SlotOf (ifn + "|" + mn) i)
    // the class-id set a `:? T` accepts: a class matches itself and its
    // subclasses; an interface matches its implementors; anything else is exact
    let cidsOf (names : string list) = names |> List.choose (fun n -> dictTryFind st.ClassId n)
    for cn, _, _, _ in classDecls do dictSet st.TestIds cn (cidsOf (subclassesOf cn))
    for ifn, _ in interfaceDecls do
        let impls = classDecls |> List.filter (fun (_, _, _, impls) -> impls |> List.exists (fun (i, _) -> bareIface i = bareIface ifn)) |> List.collect (fun (cn, _, _, _) -> subclassesOf cn) |> List.distinct
        dictSet st.TestIds ifn (cidsOf impls)
        dictSet st.TestIds (bareIface ifn) (cidsOf impls)
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
    // the vtable: a flat [class-id][slot] array of function TABLE indices, so
    // dispatch is `table[cid*NSlots + slot]`. Fill each class' row from
    // slotImpl (walking its inheritance chain); every impl function joins the
    // call table here. Rows for types with no impls stay 0.
    let vtRows = Array.zeroCreate (nCid * st.NSlots)
    for cn, _, _, _ in classDecls do
        match dictTryFind st.ClassId cn with
        | Some cid ->
            vtableSlots |> List.iteri (fun slot (ifn, mn) ->
                match slotImpl cn ifn mn with
                // only a declared top-level function can go in the table; an
                // impl that never became one (not reachable / not a plain
                // function) leaves the slot 0
                | Some v when (dictTryFind st.Funcs (key v)).IsSome ->
                    vtRows.[cid * st.NSlots + slot] <- tblIdx m (fn v)
                | _ -> ())
        | None -> ()
    // intern all string constants FIRST, so the heap starts after them
    for d in decls do
        match d with DLet (_, _, _, e) -> scanConsts st e | _ -> ()
    // bake the vtable right after the string constants; $hp starts after it
    st.VtBase <- st.ConstNext
    for w in vtRows do
        emitByte st.ConstData (w &&& 0xFF); emitByte st.ConstData ((w >>> 8) &&& 0xFF)
        emitByte st.ConstData ((w >>> 16) &&& 0xFF); emitByte st.ConstData ((w >>> 24) &&& 0xFF)
    st.ConstNext <- st.ConstNext + 4 * (nCid * st.NSlots)
    globalI32Mut m "$hp" st.ConstNext
    exportFn m "_start" "$_start"
    // runtime bodies
    emitLalloc m; emitStrOfInt m; emitStrCat m; emitPrints m; emitFtoa6 m; emitStreq m
    emitStrStarts m; emitStrEnds m; emitStrFind m; emitStrsub m; emitStrTrim m
    // top-level function bodies — all through LowIR (Core/LowIR.fs); an
    // unsupported node reports a gap through coreToLowE, never a bad module
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) -> emitFuncLow st m (ps |> List.map fst) body (fun _ -> ())
        | _ -> ()
    // init bodies — DECLARED before _start and the lambdas, so emitted here
    // too (the function and code sections are positional and must agree)
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) -> emitFuncLow st m [] rhs (fun f -> gs f (gl v))
        | _ -> ()
    // _start: run every init in order
    let f = beginFn m []
    localsDone f
    for nm in vecToList inits do callf f nm
    endFn f
    // lifted lambda bodies: (environment, argument) -> result — declared LAST.
    // st.Captures maps each captured (path:offset) to its env slot; the LowIR
    // lowering reads them from the env register.
    for name, (pv, _), body, caps in vecToList st.Lams do
        st.Captures <- dictNew ()
        caps |> List.iteri (fun i (p, o) -> dictSet st.Captures (p + ":" + string o) i)
        emitLambdaLow st m pv body
    // bake the constant data at CONST_BASE; $hp already starts after it
    activeData m CONST_BASE (bytesToArray st.ConstData)
    let pages = (st.ConstNext / 65536) + 64
    let bytes = assembleWith m pages st.UsesExn ""
    bytes, vecToList st.Errors

// the wasm-linear backend: Core straight to a linear-memory module through the
// shared LowIR. `--lowir` is a retained alias for the same path.
let emitLinear (decls0 : Decl list) : byte[] * string list = emitLinearImpl decls0
let emitLinearLow (decls0 : Decl list) : byte[] * string list = emitLinearImpl decls0

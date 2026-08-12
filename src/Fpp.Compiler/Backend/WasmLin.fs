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
      /// per-function gap redirect (mirrors the wasm-GC driver's probe): while
      /// lowering one function body, gaps go HERE instead of Errors, so the
      /// driver can turn a body with any gap into an unreachable STUB + warning
      /// rather than a hard error. None -> gaps are real errors.
      mutable GapSink : Vec<string> option
      /// functions stubbed because their body hit an unported node — the gap
      /// text, one per stub (dead prelude/backend members that survive DCE but
      /// are never called during self-host)
      Warnings : Vec<string>
      /// top-level function names (their DLet is an ELam): reached by call
      Funcs : Dict<string, int>          // "path:offset" -> arity
      /// unboxed ABI of a top-level function whose signature has any scalar
      /// param/return: (param wasm types, return wasm type). Only present for
      /// SPECIALIZED functions; a direct caller unboxes scalar args and re-boxes
      /// a scalar result. Safe because a top-level fn is only ever direct-called
      /// (first-class uses eta-expand to a lambda that itself does a direct call).
      FuncSig : Dict<string, LTy list * LTy>
      /// top-level non-lambda bindings: a mutable global each
      Globals : Dict<string, bool>       // "path:offset" -> unit
      /// `extern` host imports (readTextRaw, preludeSourceRaw, …). WasmLin has
      /// no host env yet, so a call to one lowers to a null default rather than
      /// stubbing its callers — enough for the compiler to RUN the pipeline
      /// (readTextRaw null → None; a real host env is the self-host follow-up).
      Externs : Dict<string, bool>
      /// arities `(1 + argc)` used by interface dispatches (`EIfaceCall`). Each
      /// needs its `$lfn<n>` call_indirect type declared — and a dispatch can
      /// need an arity NO top-level function has (a 0-arg member like `Current`
      /// gives arity 1), so these are collected separately from `Funcs` or the
      /// type is missing and `callIndirect` emits a negative type index.
      IfaceArities : Dict<int, bool>
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
      /// inline value-type layout (repr step 1): a record/struct with >=1 scalar
      /// field stores its fields RAW inline. Fields are ordered SCALARS-FIRST,
      /// REFS-LAST; a scalar rides raw (`f64`/`i64`/packed), a ref/generic field
      /// is a word (pointer or tagged). Registered FK_TAGGED with start = the
      /// first ref word, so the GC scans ONLY the ref suffix (skipping raw scalar
      /// bytes that could look like pointers) and $cmpv compares the scalar prefix
      /// raw and recurses only the refs. Maps name -> (field -> (byte offset,
      /// type string)), the total size, and that first-ref word index (= size/4
      /// when all-scalar). A one-field record still collapses (newtype) first.
      RecPod : Dict<string, Dict<string, int * string> * int * int>
      /// repr(T) single-field collapse: a record with EXACTLY one field, never
      /// mutated (no EFieldSet), travels AS that field — no heap object. Maps the
      /// record name -> its sole field name. This is the general "any one-field
      /// struct is a newtype" rule; construction/access on such a record become
      /// the identity on the field value.
      Collapse : Dict<string, string>
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
      CellVars : Dict<string, bool>
      /// GC mode only: a shape key ("rec:7", "tup:3", "case:9", "clo:2",
      /// "list", "arr", "str", "f64", "i64", "cell") -> its fpprt type-id, and
      /// the registrations to emit at startup as (tid, size-bytes, kind,
      /// first-payload-word-index). tids are numbered from TID_FIRST.
      Tids : Dict<string, int>
      TidRegs : Vec<int * int * int * int>
      mutable TidNext : int
      /// GC mode: each string constant as (root-slot, UTF-16 bytes). `Consts`
      /// maps the source literal to its slot. Constants are allocated through
      /// fpprt at startup and their pointers kept in the shim's root table.
      GcConstData : Vec<int * byte[]>
      /// GC mode: a top-level global's key ("path:offset") -> its root-table
      /// slot. Top-level bindings hold tagged values or heap pointers, so they
      /// live in the scanned root table, not in unscanned wasm globals.
      GlobalSlot : Dict<string, int>
      /// next free root-table slot (0 = scratch buffer; then globals, then
      /// string constants; the shadow stack for in-flight roots follows)
      mutable RootNext : int
      /// GC mode: (fpprt type-id, language class-id) for every type-testable
      /// shape (records, union cases), filled into the tid->cid table so `:?`
      /// and vtable dispatch recover the class-id from the tagged header
      TidCid : Vec<int * int>
      /// GC mode: the root-table slot holding the vtable array pointer (the
      /// vtable can't live in a data segment — that would land in fpprt's heap)
      mutable VtSlot : int
      /// GC mode: root slot holding the tid->shape-info array the generic $cmpv
      /// uses to structurally compare ANY shape at runtime (kind/start/nwords
      /// packed per tid). Standalone reads the same info from static memory.
      mutable CmpTblSlot : int }

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

// GC mode: allocation, the header and roots go through fpprt (the F++ runtime
// over Whippet), linked as an imported reactor module and fused with a
// wasm-merge pass. Off = the standalone bump-allocator path (no collection).
// Set by the CLI (`--gc`) before emission.
let mutable gc = false

// GC: the fpprt type-ids for a heap STRING (SCALAR_ARRAY, 2 bytes/unit) and a
// raw SCALAR byte buffer, resolved by the driver before the runtime string and
// print helpers are emitted (they bake the string tid as an immediate).
let mutable private nameOf : Dict<string, string> = dictNew ()
let mutable private gcStrTid = 0
let mutable private gcByteTid = 0
let mutable private gcIntTid = 0
// a ref-array tid baked for the hand-emitted $str_split_char helper (which has
// no LowCtx to call gcTid); registered eagerly beside the string/byte tids
let mutable private gcArrTid = 0
// reserved-shape tids the hand-emitted $cmpv matches: under GC an object's
// word-0 is (tid<<1)|1, NOT the class-id, so $cmpv compares those headers.
// Interned eagerly with the SAME shape keys lowObj/lowBox64 use (shared tids).
let mutable private gcFloatTid = 0
let mutable private gcInt64Tid = 0
let mutable private gcListTid = 0
let mutable private gcCmpTblSlot = 0
// GC: wasm global name ("$g<hash>" of a top-level binding) -> its root-table
// slot, so emitLowE can turn a global read/write into a root-table load/store.
// Set by the driver per compile.
let mutable private gcGlobalSlots : Dict<string, int> = dictNew ()

// fpprt's reserved type-ids; the compiler numbers its own from here (mirrors
// FPPRT_TID_FIRST in fpprt.h)
let private TID_FIRST = 3
// fpprt type kinds (enum fpprt_type_kind)
let private FK_STRUCT = 0
let private FK_REF_ARRAY = 1
let private FK_SCALAR_ARRAY = 2
let private FK_TAGGED = 5    // uniform tagged-word objects (see fpprt-embedder.h)

// import fpprt's memory and the allocator/GC/root API a GC-mode module needs.
// Declared among the imports so the shared memory is index 0 and every fpprt
// function keeps a stable index below the module's own functions.
let private importFpprt (m : Mod) : unit =
    importFn m "fpprt" "_initialize" "$fpinit" [] []
    importFn m "fpprt" "fpprt_init" "$fpheap" [ "i32" ] []
    importFn m "fpprt" "fpprt_alloc" "$fpalloc" [ "i32" ] [ "i32" ]
    importFn m "fpprt" "fpprt_alloc_array" "$fpallocn" [ "i32"; "i32" ] [ "i32" ]
    importFn m "fpprt" "fpprt_register_type_s" "$fpreg" [ "i32"; "i32"; "i32"; "i32"; "i32"; "i32" ] []
    importFn m "fpprt" "fpprt_add_static_roots" "$fproots" [ "i32"; "i32" ] []
    importFn m "fpprt" "fpprt_frame_push" "$fppush" [ "i32" ] []
    importFn m "fpprt" "fpprt_frame_pop" "$fppop" [ "i32" ] []
    importFn m "fpprt" "fpprt_write_ref" "$fpwr" [ "i32"; "i32"; "i32" ] []
    importFn m "fpprt" "fpprt_wasm_roots_base" "$rootsbase" [] [ "i32" ]
    importFn m "fpprt" "fpprt_wasm_roots_register" "$rootsreg" [ "i32" ] []
    importFn m "fpprt" "fpprt_tid2cid_base" "$t2cbase" [] [ "i32" ]
    importMem m "fpprt" "memory" 258 32768

// the slot key for an interface method uses the interface's BARE name: the
// declaration, an impl clause and a dispatch site spell its arity and type
// arguments differently, but all mean one slot
let private bareIfaceOf (n : string) : string =
    let n = if n.Contains "$<" then n.Substring (0, n.IndexOf "$<") else n
    match n.IndexOf '`' with i when i > 0 -> n.Substring (0, i) | _ -> n

// GC mode: intern an fpprt type-id for a shape and queue its registration.
// `sizeBytes` is the total object size (header included) for TAGGED/STRUCT, or
// the element size for arrays; `start` is the first-payload word index a
// TAGGED tracer scans from (skipping the header and any raw metadata words).
let private gcTid (st : St) (shapeKey : string) (sizeBytes : int) (kind : int) (start : int) : int =
    match dictTryFind st.Tids shapeKey with
    | Some t -> t
    | None ->
        let t = st.TidNext
        st.TidNext <- t + 1
        dictSet st.Tids shapeKey t
        vecAdd st.TidRegs (t, sizeBytes, kind, start)
        t

// where a captured-mutable cell keeps its value: at offset 0 in the standalone
// headerless cell, or after the fpprt header in GC mode (a cell is a TAGGED
// object so its value is scanned)
let private cellOff () : int = if gc then HDR else 0

let private key (v : VarId) : string = v.Path + ":" + string v.Offset
let private fn (v : VarId) : string = "$f" + string (abs (strHash (key v)))
let private gl (v : VarId) : string = "$g" + string (abs (strHash (key v)))

let private err (st : St) (m : string) : unit =
    match st.GapSink with
    | Some v -> vecAdd v m
    | None -> vecAdd st.Errors m

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

// GC: assign a string constant its root-table slot (1-based; slot 0 is the
// scratch buffer) and record its UTF-16 bytes for startup allocation. No data
// segment — constants become fpprt objects kept alive by the root table.
let private internStrGc (st : St) (s : string) : int =
    match dictTryFind st.Consts s with
    | Some slot -> slot
    | None ->
        let slot = st.RootNext
        st.RootNext <- slot + 1
        vecAdd st.GcConstData (slot, Fpp.Backend.BinDriver.unescape s)
        dictSet st.Consts s slot
        slot

// a string constant as a value: standalone bakes it at a fixed address; GC
// loads its (possibly relocated) pointer from the root table
let private lowStrConst (st : St) (s : string) : LExpr =
    if gc then LLoad (W, LGetGlobal "$roots", 4 * internStrGc st s)
    else LConstW (internStr st s)

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
    tyFunc m "$lt_iiii2i" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    tyFunc m "$lt_i2v" [ "i32" ] []
    tyFunc m "$lt_v2v" [] []
    tyFunc m "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    // the closure calling convention: (environment, argument) -> result
    tyFunc m "$lclo" [ "i32"; "i32" ] [ "i32" ]
    // the exception tag carries the thrown value (a tagged i32)
    tyFunc m "$exntag" [ "i32" ] []
    // GC shadow stack: push a value (i32->void), pop one (void->i32)
    tyFunc m "$lt_v2i" [] [ "i32" ]


let private rtDeclsLin (m : Mod) : unit =
    importFn m "wasi_snapshot_preview1" "fd_write" "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    // GC mode imports fpprt's memory + API (all imports must precede declared
    // functions in the index space); the standalone path defines+exports its own
    if gc then importFpprt m else exportMem m "memory"
    // GC shadow-stack push/pop for in-flight roots (declared before the string
    // helpers so declaration order matches body-emission order)
    if gc then (declFn m "$spush" "$lt_i2v"; declFn m "$spop" "$lt_v2i")
    declFn m "$lalloc" "$lt_i2i"
    declFn m "$str_of_int" "$lt_i2i"
    declFn m "$str_of_char" "$lt_i2i"
    declFn m "$str_cat" "$lt_ii2i"
    declFn m "$prints" "$lt_i2v"
    declFn m "$ftoa6" "$lt_i2i"
    declFn m "$streq" "$lt_ii2i"
    declFn m "$str_starts" "$lt_ii2i"
    declFn m "$str_ends" "$lt_ii2i"
    declFn m "$str_find" "$lt_iii2i"
    declFn m "$strsub" "$lt_iii2i"
    declFn m "$str_trim" "$lt_i2i"
    declFn m "$str_replace" "$lt_iii2i"
    declFn m "$str_find_char" "$lt_ii2i"
    declFn m "$str_last_find_char" "$lt_ii2i"
    declFn m "$str_split_char" "$lt_ii2i"
    declFn m "$str_upper" "$lt_i2i"
    declFn m "$str_lower" "$lt_i2i"
    declFn m "$str_chars" "$lt_i2i"
    declFn m "$str_pad" "$lt_iiii2i"
    declFn m "$str_trim_start_chars" "$lt_ii2i"
    declFn m "$str_trim_end_chars" "$lt_ii2i"
    declFn m "$str_insert" "$lt_iii2i"
    declFn m "$str_remove2" "$lt_iii2i"
    declFn m "$str_cmp" "$lt_ii2i"
    declFn m "$cmpv" "$lt_ii2i"
    declFn m "$hashv" "$lt_i2i"
    declFn m "$lappend" "$lt_ii2i"

// %f: .NET's fixed-six-decimals form, ported to the linear string layout.
// Takes a boxed f64 pointer, returns a string pointer. Handles NaN, sign,
// rounding at the sixth decimal, an i64 integer part and six fractionals.
// A store16 helper writes one UTF-16 unit and advances $w.
// allocate a fresh string of `pushLen` UTF-16 units, leaving its pointer in the
// caller's `$p` local. Standalone bump-allocs and writes the [kind][len] header;
// GC calls fpprt_alloc_array (which writes the tag and length). `pushLen` emits
// code leaving the unit count on the stack, and is invoked up to twice.
let private strAllocN (f : Fn) (pushLen : unit -> unit) : unit =
    if gc then
        ic f gcStrTid; pushLen (); callf f "$fpallocn"; ls f "$p"
    else
        ic f 8; pushLen (); ic f 1; ins f "i32.shl"; ins f "i32.add"; callf f "$lalloc"; ls f "$p"
        lg f "$p"; ic f CID_STRING; mem f "i32.store"
        lg f "$p"; ic f 4; ins f "i32.add"; pushLen (); mem f "i32.store"

// push/pop a source string pointer across a string allocation (GC only): the
// allocation may collect and relocate the source we are about to copy from
let private strGuard (f : Fn) (locals : string list) : (unit -> unit) =
    if gc then
        for v in locals do lg f v; callf f "$spush"
        fun () -> for v in List.rev locals do callf f "$spop"; ls f v
    else fun () -> ()

// GC: reload $sbuf from the (rooted) scratch buffer's current address — after a
// safepoint the collector may have relocated it
let private emitSbufRefresh (f : Fn) : unit =
    if gc then (gg f "$roots"; mem f "i32.load"; ic f 8; ins f "i32.add"; gs f "$sbuf")

// a scratch address: a fixed low offset in the standalone path, or `$sbuf`
// (the fpprt-allocated scratch buffer) plus that offset in GC mode, where no
// fixed low memory is ours.
let private saddr (f : Fn) (n : int) : unit =
    if gc then
        gg f "$sbuf"
        if n <> 0 then (ic f n; ins f "i32.add")
    else ic f n

let private emitFtoa6 (m : Mod) : unit =
    let f = beginFn m [ "$x" ]
    local f "$v" "f64"; local f "$w" "i32"; local f "$ip" "f64"; local f "$frac" "f64"
    local f "$ipi" "i64"; local f "$tmp" "i64"; local f "$d" "i32"; local f "$k" "i32"
    local f "$cur" "i32"; local f "$p" "i32"; local f "$len" "i32"; local f "$i" "i32"
    localsDone f
    let put (code : unit -> unit) =
        lg f "$w"; code (); mem f "i32.store16"; lg f "$w"; ic f 2; ins f "i32.add"; ls f "$w"
    emitSbufRefresh f
    lg f "$x"; ic f HDR; ins f "i32.add"; mem f "f64.load"; ls f "$v"
    saddr f FMTBUF; ls f "$w"
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
    lg f "$w"; saddr f FMTBUF; ins f "i32.sub"; ic f 1; ins f "i32.shr_u"; ls f "$len"
    strAllocN f (fun () -> lg f "$len")
    // the result allocation may have moved the scratch buffer we copy from
    emitSbufRefresh f
    ic f 0; ls f "$i"
    blockE f "$cc"; loopE f "$cl"
    lg f "$i"; lg f "$len"; ins f "i32.ge_u"; brIf f "$cc"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    saddr f FMTBUF; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
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

// GC shadow stack (in-flight roots): a LIFO of live heap pointers in the
// scanned root table, above the scratch/global/constant slots. A value pushed
// before an allocation survives the collection it might trigger, and pop reads
// its (possibly relocated) address back. $sp is a byte offset into $roots.
let private emitSpush (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    localsDone f
    gg f "$roots"; gg f "$sp"; ins f "i32.add"; lg f "$v"; mem f "i32.store"
    gg f "$sp"; ic f 4; ins f "i32.add"; gs f "$sp"
    endFn f

let private emitSpop (m : Mod) : unit =
    let f = beginFn m []
    local f "$a" "i32"; local f "$r" "i32"
    localsDone f
    gg f "$sp"; ic f 4; ins f "i32.sub"; gs f "$sp"
    gg f "$roots"; gg f "$sp"; ins f "i32.add"; ls f "$a"
    lg f "$a"; mem f "i32.load"; ls f "$r"
    lg f "$a"; ic f 0; mem f "i32.store"      // clear the popped slot (no stale scan)
    lg f "$r"
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
    // total units = d + neg. GC: fpprt_alloc_array writes the tag and length;
    // standalone: bump-alloc 8 + 2*units and write the header + length here.
    if gc then
        ic f gcStrTid
        lg f "$d"; lg f "$neg"; ins f "i32.add"
        callf f "$fpallocn"; ls f "$p"
    else
        ic f 8
        lg f "$d"; lg f "$neg"; ins f "i32.add"; ic f 1; ins f "i32.shl"
        ins f "i32.add"
        callf f "$lalloc"; ls f "$p"
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

// $str_of_char(c): a fresh one-unit string holding the raw char code c.
let private emitStrOfChar (m : Mod) : unit =
    let f = beginFn m [ "$c" ]
    local f "$p" "i32"
    localsDone f
    strAllocN f (fun () -> ic f 1)
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$c"; mem f "i32.store16"
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
    let unpin = strGuard f [ "$a"; "$b" ]
    strAllocN f (fun () -> lg f "$la"; lg f "$lb"; ins f "i32.add")
    unpin ()
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

// $lappend(a, b): rebuild list a's spine onto b (`a @ b`). Recursive like the GC
// backend's $append; a tagged/linear cons is [cid-or-tid][head][tail] and nil is
// 0. GC mode roots the head across the recursive call and the head+result across
// the allocation (both are safepoints); standalone bump-allocs and writes the cid.
let private emitLappend (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    local f "$h" "i32"; local f "$rec" "i32"; local f "$cell" "i32"
    localsDone f
    // nil ++ b = b
    lg f "$a"; ins f "i32.eqz"; ifE f; lg f "$b"; ins f "return"; endB f
    // head, then recurse on the tail; the recursion allocates, so root the head
    lg f "$a"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ls f "$h"
    if gc then (lg f "$h"; callf f "$spush")
    lg f "$a"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"
    lg f "$b"
    callf f "$lappend"; ls f "$rec"
    if gc then (callf f "$spop"; ls f "$h")
    // cons the head onto the result: allocate a cell, rooting head+result across it
    if gc then
        lg f "$h"; callf f "$spush"; lg f "$rec"; callf f "$spush"
        ic f gcListTid; callf f "$fpalloc"; ls f "$cell"
        callf f "$spop"; ls f "$rec"; callf f "$spop"; ls f "$h"
    else
        ic f (HDR + 8); callf f "$lalloc"; ls f "$cell"
        lg f "$cell"; ic f CID_LIST; mem f "i32.store"
    lg f "$cell"; ic f HDR; ins f "i32.add"; lg f "$h"; mem f "i32.store"
    lg f "$cell"; ic f (HDR + 4); ins f "i32.add"; lg f "$rec"; mem f "i32.store"
    lg f "$cell"
    endFn f

// $prints(s): UTF-16 -> UTF-8 into PRINTBUF, then fd_write(1). Handles the
// BMP (1/2/3-byte forms); surrogate pairs are written as their raw units
// (adequate for slice 1's ASCII-and-Latin output).
let private emitPrints (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$len" "i32"; local f "$i" "i32"; local f "$w" "i32"; local f "$u" "i32"
    localsDone f
    // GC: the scratch buffer may have moved since the last print — reload its
    // current address from the root table
    if gc then (gg f "$roots"; mem f "i32.load"; ic f 8; ins f "i32.add"; gs f "$sbuf")
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    saddr f PRINTBUF; ls f "$w"
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
    saddr f IOV_PTR; saddr f PRINTBUF; mem f "i32.store"
    saddr f IOV_LEN; lg f "$w"; saddr f PRINTBUF; ins f "i32.sub"; mem f "i32.store"
    ic f 1; saddr f IOV_PTR; ic f 1; saddr f NWRITTEN
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
    let unpin = strGuard f [ "$s" ]
    strAllocN f (fun () -> lg f "$len")
    unpin ()
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

// $str_replace(s, a, b): s with every occurrence of a replaced by b. Two
// passes: count occurrences (via $str_find) to size the result, then build it.
let private emitStrReplace (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$a"; "$b" ]
    local f "$sl" "i32"; local f "$al" "i32"; local f "$bl" "i32"
    local f "$cnt" "i32"; local f "$pos" "i32"; local f "$idx" "i32"
    local f "$p" "i32"; local f "$w" "i32"; local f "$i" "i32"; local f "$k" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$sl"
    lg f "$a"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$al"
    lg f "$b"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$bl"
    // empty pattern: return s unchanged
    lg f "$al"; ins f "i32.eqz"; ifE f; lg f "$s"; ins f "return"; endB f
    // count occurrences
    ic f 0; ls f "$cnt"; ic f 0; ls f "$pos"
    blockE f "$cc"; loopE f "$cl"
    lg f "$s"; lg f "$a"; lg f "$pos"; callf f "$str_find"; ls f "$idx"
    lg f "$idx"; ic f 0; ins f "i32.lt_s"; brIf f "$cc"
    lg f "$cnt"; ic f 1; ins f "i32.add"; ls f "$cnt"
    lg f "$idx"; lg f "$al"; ins f "i32.add"; ls f "$pos"
    br f "$cl"; endB f; endB f
    // resultLen = sl + cnt*(bl - al); alloc
    lg f "$sl"; lg f "$cnt"; lg f "$bl"; lg f "$al"; ins f "i32.sub"; ins f "i32.mul"; ins f "i32.add"; ls f "$k"
    let unpin = strGuard f [ "$s"; "$b" ]
    strAllocN f (fun () -> lg f "$k")
    unpin ()
    // build
    ic f 0; ls f "$w"; ic f 0; ls f "$i"
    blockE f "$bc"; loopE f "$bl2"
    lg f "$i"; lg f "$sl"; ins f "i32.ge_s"; brIf f "$bc"
    lg f "$s"; lg f "$a"; lg f "$i"; callf f "$str_find"; ls f "$idx"
    lg f "$idx"; lg f "$i"; ins f "i32.eq"
    ifE f
    // copy b (bl units) into p[w..]
    ic f 0; ls f "$k"
    blockE f "$bkc"; loopE f "$bkl"
    lg f "$k"; lg f "$bl"; ins f "i32.ge_s"; brIf f "$bkc"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$w"; lg f "$k"; ins f "i32.add"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$b"; ic f 8; ins f "i32.add"; lg f "$k"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$k"; ic f 1; ins f "i32.add"; ls f "$k"
    br f "$bkl"; endB f; endB f
    lg f "$w"; lg f "$bl"; ins f "i32.add"; ls f "$w"
    lg f "$i"; lg f "$al"; ins f "i32.add"; ls f "$i"
    elseB f
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$w"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$w"; ic f 1; ins f "i32.add"; ls f "$w"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    endB f
    br f "$bl2"; endB f; endB f
    lg f "$p"
    endFn f

// $str_find_char(s, c): index of the first unit equal to c, or -1.
let private emitStrFindChar (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$c" ]
    local f "$sl" "i32"; local f "$i" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$sl"
    ic f 0; ls f "$i"
    blockE f "$c0"; loopE f "$l"
    lg f "$i"; lg f "$sl"; ins f "i32.ge_s"; brIf f "$c0"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$c"; ins f "i32.eq"
    ifE f; lg f "$i"; ins f "return"; endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$l"; endB f; endB f
    ic f -1
    endFn f

// $str_last_find_char(s, c): index of the last unit equal to c, or -1.
let private emitStrLastFindChar (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$c" ]
    local f "$i" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ic f 1; ins f "i32.sub"; ls f "$i"
    blockE f "$c0"; loopE f "$l"
    lg f "$i"; ic f 0; ins f "i32.lt_s"; brIf f "$c0"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$c"; ins f "i32.eq"
    ifE f; lg f "$i"; ins f "return"; endB f
    lg f "$i"; ic f 1; ins f "i32.sub"; ls f "$i"
    br f "$l"; endB f; endB f
    ic f -1
    endFn f

// $str_split_char(s, c): split s on unit c into a fresh string array of n+1
// pieces (n = separator count). Two passes: count, then cut each [start, i)
// slice via $strsub. Under GC the source `$s` and the growing result `$r` are
// rooted across every $strsub allocation (a safepoint may relocate them).
// Array layout matches EArrayCreate: [cid@0][len@4][elem0@8][elem i@8+4i].
let private emitStrSplitChar (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$c" ]
    local f "$sl" "i32"; local f "$n" "i32"; local f "$i" "i32"
    local f "$start" "i32"; local f "$k" "i32"; local f "$r" "i32"; local f "$sub" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$sl"
    // pass 1: n = 1 + count(c)
    ic f 1; ls f "$n"
    ic f 0; ls f "$i"
    blockE f "$c1"; loopE f "$l1"
    lg f "$i"; lg f "$sl"; ins f "i32.ge_s"; brIf f "$c1"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$c"; ins f "i32.eq"
    ifE f; lg f "$n"; ic f 1; ins f "i32.add"; ls f "$n"; endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$l1"; endB f; endB f
    // allocate the result array (root $s across the alloc)
    let unpinA = strGuard f [ "$s" ]
    if gc then (ic f gcArrTid; lg f "$n"; callf f "$fpallocn"; ls f "$r")
    else
        ic f 8; lg f "$n"; ic f 2; ins f "i32.shl"; ins f "i32.add"; callf f "$lalloc"; ls f "$r"
        lg f "$r"; ic f CID_ARRAY; mem f "i32.store"
        lg f "$r"; ic f 4; ins f "i32.add"; lg f "$n"; mem f "i32.store"
    unpinA ()
    // pass 2: cut a piece at each separator
    ic f 0; ls f "$i"; ic f 0; ls f "$start"; ic f 0; ls f "$k"
    blockE f "$c2"; loopE f "$l2"
    lg f "$i"; lg f "$sl"; ins f "i32.ge_s"; brIf f "$c2"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    lg f "$c"; ins f "i32.eq"
    ifE f
    let unpin = strGuard f [ "$s"; "$r" ]
    lg f "$s"; lg f "$start"; lg f "$i"; lg f "$start"; ins f "i32.sub"; callf f "$strsub"; ls f "$sub"
    unpin ()
    lg f "$r"; ic f 8; ins f "i32.add"; lg f "$k"; ic f 2; ins f "i32.shl"; ins f "i32.add"; lg f "$sub"; mem f "i32.store"
    lg f "$k"; ic f 1; ins f "i32.add"; ls f "$k"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$start"
    endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$l2"; endB f; endB f
    // the final piece: [start, sl)
    let unpin2 = strGuard f [ "$s"; "$r" ]
    lg f "$s"; lg f "$start"; lg f "$sl"; lg f "$start"; ins f "i32.sub"; callf f "$strsub"; ls f "$sub"
    unpin2 ()
    lg f "$r"; ic f 8; ins f "i32.add"; lg f "$k"; ic f 2; ins f "i32.shl"; ins f "i32.add"; lg f "$sub"; mem f "i32.store"
    lg f "$r"
    endFn f

// $str_upper / $str_lower: ASCII case mapping, unit for unit. `lower=false`
// emits $str_upper (a..z -> A..Z), `lower=true` emits $str_lower — declared and
// emitted in that order. The mapped unit is chosen branchless via `select`.
let private emitStrCase (m : Mod) (lower : bool) : unit =
    let f = beginFn m [ "$s" ]
    local f "$p" "i32"; local f "$len" "i32"; local f "$i" "i32"; local f "$c" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    let unpin = strGuard f [ "$s" ]
    strAllocN f (fun () -> lg f "$len")
    unpin ()
    ic f 0; ls f "$i"
    blockE f "$d"; loopE f "$go"
    lg f "$i"; lg f "$len"; ins f "i32.ge_s"; brIf f "$d"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ls f "$c"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$c"; ic f (if lower then 32 else -32); ins f "i32.add"     // val1 = c + delta
    lg f "$c"                                                        // val2 = c
    lg f "$c"; ic f (if lower then 65 else 97); ins f "i32.ge_u"
    lg f "$c"; ic f (if lower then 90 else 122); ins f "i32.le_u"; ins f "i32.and"   // cond = in range
    ins f "select"
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$go"; endB f; endB f
    lg f "$p"
    endFn f

// $str_chars(s): a fresh array of the string's units as TAGGED chars (the
// array element representation used everywhere: odd = int/char). Root $s across
// the array allocation.
let private emitStrChars (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$r" "i32"; local f "$len" "i32"; local f "$i" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    let unpin = strGuard f [ "$s" ]
    if gc then (ic f gcArrTid; lg f "$len"; callf f "$fpallocn"; ls f "$r")
    else
        ic f 8; lg f "$len"; ic f 2; ins f "i32.shl"; ins f "i32.add"; callf f "$lalloc"; ls f "$r"
        lg f "$r"; ic f CID_ARRAY; mem f "i32.store"
        lg f "$r"; ic f 4; ins f "i32.add"; lg f "$len"; mem f "i32.store"
    unpin ()
    ic f 0; ls f "$i"
    blockE f "$d"; loopE f "$go"
    lg f "$i"; lg f "$len"; ins f "i32.ge_s"; brIf f "$d"
    lg f "$r"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 2; ins f "i32.shl"; ins f "i32.add"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    ic f 1; ins f "i32.shl"; ic f 1; ins f "i32.or"     // tag the char
    mem f "i32.store"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$go"; endB f; endB f
    lg f "$r"
    endFn f

// $str_pad(s, w, pc, right): pad s to width w with unit pc. right=1 appends the
// padding (PadRight), right=0 prepends it (PadLeft). Result length = max(len,w).
let private emitStrPad (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$w"; "$pc"; "$right" ]
    local f "$p" "i32"; local f "$len" "i32"; local f "$out" "i32"; local f "$pad" "i32"
    local f "$i" "i32"; local f "$src" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    // out = max(len, w); pad = out - len
    lg f "$len"; lg f "$w"; lg f "$len"; lg f "$w"; ins f "i32.gt_s"; ins f "select"; ls f "$out"
    lg f "$out"; lg f "$len"; ins f "i32.sub"; ls f "$pad"
    let unpin = strGuard f [ "$s" ]
    strAllocN f (fun () -> lg f "$out")
    unpin ()
    ic f 0; ls f "$i"
    blockE f "$d"; loopE f "$go"
    lg f "$i"; lg f "$out"; ins f "i32.ge_s"; brIf f "$d"
    // src index: right ? i : i - pad
    lg f "$i"; lg f "$i"; lg f "$pad"; ins f "i32.sub"; lg f "$right"; ins f "select"; ls f "$src"
    // dest addr p+8+2i
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    // isContent: right ? (i < len) : (i >= pad)
    lg f "$i"; lg f "$len"; ins f "i32.lt_s"
    lg f "$i"; lg f "$pad"; ins f "i32.ge_s"
    lg f "$right"; ins f "select"
    ifV f "i32"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$src"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    elseB f
    lg f "$pc"
    endB f
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$go"; endB f; endB f
    lg f "$p"
    endFn f

// $str_trim_start_chars / _end: trim leading/trailing units that are in the set
// $cs (a char or a tagged-char array). `atStart=true` emits the start variant.
let private emitStrTrimChars (m : Mod) (atStart : bool) : unit =
    let f = beginFn m [ "$s"; "$cs" ]
    local f "$len" "i32"; local f "$a" "i32"; local f "$b" "i32"
    local f "$c" "i32"; local f "$j" "i32"; local f "$hit" "i32"; local f "$cn" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    // count of set elements: 1 for a char, array length for an array
    lg f "$cs"; ic f 1; ins f "i32.and"
    ifV f "i32"
    ic f 1
    elseB f
    lg f "$cs"; ic f 4; ins f "i32.add"; mem f "i32.load"
    endB f
    ls f "$cn"
    ic f 0; ls f "$a"
    lg f "$len"; ls f "$b"
    blockE f "$done"; loopE f "$go"
    lg f "$a"; lg f "$b"; ins f "i32.ge_s"; brIf f "$done"
    // current unit: from the start or just before the end
    (if atStart then (lg f "$s"; ic f 8; ins f "i32.add"; lg f "$a"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u")
     else (lg f "$s"; ic f 8; ins f "i32.add"; lg f "$b"; ic f 1; ins f "i32.sub"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"))
    ls f "$c"
    // hit = c in set
    ic f 0; ls f "$hit"; ic f 0; ls f "$j"
    blockE f "$sd"; loopE f "$sg"
    lg f "$j"; lg f "$cn"; ins f "i32.ge_s"; brIf f "$sd"
    // set element j (untagged): char -> cs>>1; array -> tag at elem, >>1
    lg f "$cs"; ic f 1; ins f "i32.and"
    ifV f "i32"
    lg f "$cs"; ic f 1; ins f "i32.shr_s"
    elseB f
    lg f "$cs"; ic f 8; ins f "i32.add"; lg f "$j"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ic f 1; ins f "i32.shr_s"
    endB f
    lg f "$c"; ins f "i32.eq"
    ifE f; ic f 1; ls f "$hit"; br f "$sd"; endB f
    lg f "$j"; ic f 1; ins f "i32.add"; ls f "$j"
    br f "$sg"; endB f; endB f
    lg f "$hit"; ins f "i32.eqz"; brIf f "$done"
    (if atStart then (lg f "$a"; ic f 1; ins f "i32.add"; ls f "$a") else (lg f "$b"; ic f 1; ins f "i32.sub"; ls f "$b"))
    br f "$go"; endB f; endB f
    lg f "$s"; lg f "$a"; lg f "$b"; lg f "$a"; ins f "i32.sub"; callf f "$strsub"
    endFn f

// $str_insert(s, i, v): s[0..i) ++ v ++ s[i..). $str_remove2(s, i, n): s[0..i)
// ++ s[i+n..). Both cut with $strsub then $str_cat; each intermediate string is
// rooted over the next allocation (GC only) via the shadow stack.
let private emitStrInsert (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$i"; "$v" ]
    local f "$len" "i32"; local f "$h" "i32"; local f "$t" "i32"; local f "$hv" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    // h = s[0, i)   (root s and v across the alloc)
    let u1 = strGuard f [ "$s"; "$v" ]
    lg f "$s"; ic f 0; lg f "$i"; callf f "$strsub"; ls f "$h"
    u1 ()
    // hv = h ++ v   (root s across it — $str_cat guards h and v itself)
    let u2 = strGuard f [ "$s"; "$h" ]
    lg f "$h"; lg f "$v"; callf f "$str_cat"; ls f "$hv"
    u2 ()
    // t = s[i, len-i)  (root hv across the alloc)
    let u3 = strGuard f [ "$hv" ]
    lg f "$s"; lg f "$i"; lg f "$len"; lg f "$i"; ins f "i32.sub"; callf f "$strsub"; ls f "$t"
    u3 ()
    lg f "$hv"; lg f "$t"; callf f "$str_cat"
    endFn f

let private emitStrRemove2 (m : Mod) : unit =
    let f = beginFn m [ "$s"; "$i"; "$n" ]
    local f "$len" "i32"; local f "$h" "i32"; local f "$t" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    let u1 = strGuard f [ "$s" ]
    lg f "$s"; ic f 0; lg f "$i"; callf f "$strsub"; ls f "$h"
    u1 ()
    // t = s[i+n, len-i-n)  (root h across the alloc)
    let u2 = strGuard f [ "$s"; "$h" ]
    lg f "$s"; lg f "$i"; lg f "$n"; ins f "i32.add"; lg f "$len"; lg f "$i"; ins f "i32.sub"; lg f "$n"; ins f "i32.sub"; callf f "$strsub"; ls f "$t"
    u2 ()
    lg f "$h"; lg f "$t"; callf f "$str_cat"
    endFn f

// $str_cmp(a, b): lexical comparison of two strings -> -1/0/1 (shorter first on
// a tie). Both args ARE strings, so no class-id dispatch.
let private emitStrCmp (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    local f "$n" "i32"; local f "$mm" "i32"; local f "$i" "i32"; local f "$x" "i32"; local f "$y" "i32"
    localsDone f
    lg f "$a"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$n"
    lg f "$b"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$mm"
    ic f 0; ls f "$i"
    blockE f "$d"; loopE f "$g"
    lg f "$i"; lg f "$n"; ins f "i32.ge_s"; brIf f "$d"
    lg f "$i"; lg f "$mm"; ins f "i32.ge_s"; brIf f "$d"
    lg f "$a"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ls f "$x"
    lg f "$b"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ls f "$y"
    lg f "$x"; lg f "$y"; ins f "i32.ne"
    ifE f; lg f "$x"; lg f "$y"; ins f "i32.gt_u"; lg f "$x"; lg f "$y"; ins f "i32.lt_u"; ins f "i32.sub"; ins f "return"; endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$g"; endB f; endB f
    lg f "$n"; lg f "$mm"; ins f "i32.gt_s"; lg f "$n"; lg f "$mm"; ins f "i32.lt_s"; ins f "i32.sub"
    endFn f

// $cmpv(a, b): structural comparison -> -1/0/1 for the SELF-DESCRIBING reps —
// tagged int, nil(0), string, float, int64, list and array (element-wise,
// recursively). Tuples/records have no arity in the object, so they are compared
// by TYPE-DIRECTED synthesis at the call site, not here; a nested tuple reaching
// $cmpv falls to the best-effort equal tail. Never allocates. Under GC an
// object's word-0 is (tid<<1)|1, so we match the reserved tid headers (else the
// raw class-id in the standalone path).
let private emitCmpv (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    local f "$ca" "i32"; local f "$cb" "i32"; local f "$x" "i32"; local f "$y" "i32"
    local f "$n" "i32"; local f "$mm" "i32"; local f "$i" "i32"; local f "$r" "i32"
    local f "$w" "i32"; local f "$st" "i32"; local f "$tot" "i32"; local f "$tbl" "i32"; local f "$tid" "i32"
    local f "$fa" "f64"; local f "$fb" "f64"; local f "$la" "i64"; local f "$lb" "i64"
    localsDone f
    let hv cid tid = if gc then (tid <<< 1) ||| 1 else cid
    let strH = hv CID_STRING gcStrTid
    let fltH = hv CID_FLOAT gcFloatTid
    let i64H = hv CID_INT64 gcInt64Tid
    let arrH = hv CID_ARRAY gcArrTid
    let both h = (lg f "$ca"; ic f h; ins f "i32.eq"; lg f "$cb"; ic f h; ins f "i32.eq"; ins f "i32.and")
    lg f "$a"; lg f "$b"; ins f "i32.eq"; ifE f; ic f 0; ins f "return"; endB f
    lg f "$a"; ic f 1; ins f "i32.and"; lg f "$b"; ic f 1; ins f "i32.and"; ins f "i32.and"
    ifE f
    lg f "$a"; ic f 1; ins f "i32.shr_s"; ls f "$x"
    lg f "$b"; ic f 1; ins f "i32.shr_s"; ls f "$y"
    lg f "$x"; lg f "$y"; ins f "i32.gt_s"; lg f "$x"; lg f "$y"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"
    endB f
    lg f "$a"; ins f "i32.eqz"; ifE f; ic f -1; ins f "return"; endB f
    lg f "$b"; ins f "i32.eqz"; ifE f; ic f 1; ins f "return"; endB f
    lg f "$a"; ic f 1; ins f "i32.and"; ifE f; ic f -1; ins f "return"; endB f
    lg f "$b"; ic f 1; ins f "i32.and"; ifE f; ic f 1; ins f "return"; endB f
    lg f "$a"; mem f "i32.load"; ls f "$ca"
    lg f "$b"; mem f "i32.load"; ls f "$cb"
    both strH
    ifE f; lg f "$a"; lg f "$b"; callf f "$str_cmp"; ins f "return"; endB f
    both fltH
    ifE f
    lg f "$a"; ic f HDR; ins f "i32.add"; mem f "f64.load"; ls f "$fa"
    lg f "$b"; ic f HDR; ins f "i32.add"; mem f "f64.load"; ls f "$fb"
    lg f "$fa"; lg f "$fb"; ins f "f64.gt"; lg f "$fa"; lg f "$fb"; ins f "f64.lt"; ins f "i32.sub"; ins f "return"
    endB f
    both i64H
    ifE f
    lg f "$a"; ic f HDR; ins f "i32.add"; mem f "i64.load"; ls f "$la"
    lg f "$b"; ic f HDR; ins f "i32.add"; mem f "i64.load"; ls f "$lb"
    lg f "$la"; lg f "$lb"; ins f "i64.gt_s"; lg f "$la"; lg f "$lb"; ins f "i64.lt_s"; ins f "i32.sub"; ins f "return"
    endB f
    both arrH
    ifE f
    lg f "$a"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ls f "$n"
    lg f "$b"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ls f "$mm"
    ic f 0; ls f "$i"
    blockE f "$ad"; loopE f "$ago"
    lg f "$i"; lg f "$n"; ins f "i32.ge_s"; brIf f "$ad"
    lg f "$i"; lg f "$mm"; ins f "i32.ge_s"; brIf f "$ad"
    lg f "$a"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"
    lg f "$b"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"
    callf f "$cmpv"; ls f "$r"
    lg f "$r"; ifE f; lg f "$r"; ins f "return"; endB f
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$ago"; endB f; endB f
    lg f "$n"; lg f "$mm"; ins f "i32.gt_s"; lg f "$n"; lg f "$mm"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"
    endB f
    // remaining compound shapes: under GC walk the payload words structurally via
    // the tid->info table (tuples/records/lists/cons/closures, uniform); raw
    // metadata words (a union tag) compare as ints, ref/payload words recurse.
    // Different tids order by header. Standalone has no table -> equal (0).
    if gc then
        lg f "$ca"; lg f "$cb"; ins f "i32.ne"
        ifE f; lg f "$ca"; lg f "$cb"; ins f "i32.gt_s"; lg f "$ca"; lg f "$cb"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"; endB f
        lg f "$ca"; ic f 1; ins f "i32.and"; ins f "i32.eqz"; ifE f; ic f 0; ins f "return"; endB f
        lg f "$ca"; ic f 1; ins f "i32.shr_u"; ls f "$tid"
        gg f "$roots"; ic f (4 * gcCmpTblSlot); ins f "i32.add"; mem f "i32.load"; ls f "$tbl"
        lg f "$tbl"; ic f 8; ins f "i32.add"; lg f "$tid"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$r"
        lg f "$r"; ic f 10; ins f "i32.shr_u"; ic f 0x3FF; ins f "i32.and"; ls f "$st"
        lg f "$st"; ic f 1; ins f "i32.lt_s"; ifE f; ic f 1; ls f "$st"; endB f
        lg f "$r"; ic f 0x3FF; ins f "i32.and"; ls f "$tot"
        // raw metadata words [1, start): int compare (union tag)
        ic f 1; ls f "$w"
        blockE f "$rd"; loopE f "$rgo"
        lg f "$w"; lg f "$st"; ins f "i32.ge_s"; brIf f "$rd"
        lg f "$a"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$x"
        lg f "$b"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$y"
        lg f "$x"; lg f "$y"; ins f "i32.ne"
        ifE f; lg f "$x"; lg f "$y"; ins f "i32.gt_s"; lg f "$x"; lg f "$y"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"; endB f
        lg f "$w"; ic f 1; ins f "i32.add"; ls f "$w"
        br f "$rgo"; endB f; endB f
        // payload words [start, tot): recurse
        lg f "$st"; ls f "$w"
        blockE f "$td"; loopE f "$tgo"
        lg f "$w"; lg f "$tot"; ins f "i32.ge_s"; brIf f "$td"
        lg f "$a"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"
        lg f "$b"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"
        callf f "$cmpv"; ls f "$r"
        lg f "$r"; ifE f; lg f "$r"; ins f "return"; endB f
        lg f "$w"; ic f 1; ins f "i32.add"; ls f "$w"
        br f "$tgo"; endB f; endB f
    ic f 0
    endFn f

// $hashv(v): a structural hash matching the wasm-GC backend's $hashv exactly
// (so a dictionary keyed the same way iterates the same order). A tagged int
// hashes to itself; a string is the SAMPLED FNV (offset 0x811c9dc5, prime
// 0x01000193, up to four units from each end); an array to its length; the
// wide boxes to their bit pattern folded to 32; other objects to the class-id.
let private emitHashv (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    local f "$h" "i32"; local f "$n" "i32"; local f "$i" "i32"; local f "$cid" "i32"; local f "$b" "i64"
    localsDone f
    lg f "$v"; ic f 1; ins f "i32.and"
    ifE f; lg f "$v"; ic f 1; ins f "i32.shr_s"; ins f "return"; endB f
    lg f "$v"; mem f "i32.load"; ls f "$cid"
    lg f "$cid"; ic f CID_STRING; ins f "i32.eq"
    ifE f
    lg f "$v"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$n"
    lg f "$n"; ic f -2128831035; ins f "i32.xor"; ls f "$h"
    ic f 0; ls f "$i"
    blockE f "$hd"; loopE f "$hgo"
    lg f "$i"; ic f 4; ins f "i32.ge_u"; brIf f "$hd"
    lg f "$i"; lg f "$n"; ins f "i32.ge_u"; brIf f "$hd"
    lg f "$h"
    lg f "$v"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ins f "i32.xor"; ic f 16777619; ins f "i32.mul"
    lg f "$v"; ic f 8; ins f "i32.add"; lg f "$n"; ic f 1; ins f "i32.sub"; lg f "$i"; ins f "i32.sub"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"; ins f "i32.xor"; ic f 16777619; ins f "i32.mul"
    ls f "$h"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$hgo"; endB f; endB f
    lg f "$h"; ins f "return"
    endB f
    lg f "$cid"; ic f CID_ARRAY; ins f "i32.eq"
    ifE f; lg f "$v"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ins f "return"; endB f
    lg f "$cid"; ic f CID_FLOAT; ins f "i32.eq"
    ifE f
    lg f "$v"; ic f HDR; ins f "i32.add"; mem f "f64.load"; ins f "i64.reinterpret_f64"; ls f "$b"
    lg f "$b"; ins f "i32.wrap_i64"; lg f "$b"; lc f 32L; ins f "i64.shr_u"; ins f "i32.wrap_i64"; ins f "i32.xor"; ins f "return"
    endB f
    lg f "$cid"; ic f CID_INT64; ins f "i32.eq"
    ifE f
    lg f "$v"; ic f HDR; ins f "i32.add"; mem f "i64.load"; ls f "$b"
    lg f "$b"; ins f "i32.wrap_i64"; lg f "$b"; lc f 32L; ins f "i64.shr_u"; ins f "i32.wrap_i64"; ins f "i32.xor"; ins f "return"
    endB f
    lg f "$cid"
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
            dictSet nameOf k v.Name
            // bare `compare` is the one `(builtin)` INTRINSIC with no value (a
            // coreToLowE handler lowers it) — it must never be captured, or the
            // closure reads an unresolved variable. But OTHER `(builtin)`-path
            // names are genuine locals (a prelude fold's `acc`, a lambda's `x`):
            // those MUST be captured, else the lambda that uses them is stubbed.
            if not (v.Path = "(builtin)" && v.Name.StartsWith "compare")
               && (dictTryFind bnd k).IsNone
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
        | ELet (r, v, _, rhs, b) ->
            let bnd2 = dictNew<string, bool> ()
            for kv in dictPairs bnd do dictSet bnd2 (fst kv) (snd kv)
            dictSet bnd2 (key v) true
            // a `let rec` binds v in its OWN rhs: a recursive self-reference is
            // NOT a free variable, so it must not be captured by an enclosing
            // lambda (which would then fail to resolve it in the outer scope)
            go (if r then bnd2 else bnd) rhs
            go bnd2 b
        | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> for x in xs do go bnd x
        | EApp (g, xs) -> go bnd g; for x in xs do go bnd x
        | EIf (a, b, c) | EIndexSet (_, a, b, c) -> go bnd a; go bnd b; go bnd c
        | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> go bnd a; go bnd b
        | EAssign (v, x) ->
            // a mutable ASSIGNED inside a lambda is captured too (it lives in a
            // shared cell) — count the target as free, exactly like a read
            let k = key v
            if (dictTryFind bnd k).IsNone && (dictTryFind st.Globals k).IsNone
               && (dictTryFind st.Funcs k).IsNone && (dictTryFind seen k).IsNone then
                dictSet seen k true
                vecAdd acc (v.Path, v.Offset)
            go bnd x
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
    | EIfaceCall (_, _, r, xs) ->
        dictSet st.IfaceArities (1 + List.length xs) true
        discover st r; for x in xs do discover st x
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
    | ELit (LString s) -> (if gc then internStrGc st s else internStr st s) |> ignore
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
      // parallel to register ids (0..NReg-1): each local's wasm type, so the
      // declaration loop emits f64/i64 locals — not everything is a tagged i32
      // word. A scalar f64/i64 kept in a typed local survives an allocation
      // safepoint untouched (the GC never scans a value local), which is what
      // makes unboxed floats in flat arrays / struct fields correct.
      RegTys : Vec<LTy>
      // local `let`-bindings whose value rides UNBOXED in a typed f64/i64 local
      // (var key -> its scalar type). A read re-boxes for the uniform-word
      // contract (box-elim cancels it back in arithmetic); a capture re-boxes
      // into the closure env. Captured mutables are cells, so never listed here.
      VarScalar : Dict<string, LTy>
      mutable NReg : int }

let private freshReg (ctx : LowCtx) (k : string) : int =
    match dictTryFind ctx.Regs k with
    | Some id -> id
    | None ->
        let id = ctx.NReg
        dictSet ctx.Regs k id
        vecAdd ctx.RegTys W
        ctx.NReg <- id + 1
        id

let private freshTmpT (ctx : LowCtx) (ty : LTy) : int =
    let id = ctx.NReg
    vecAdd ctx.RegTys ty
    ctx.NReg <- id + 1
    id

let private freshTmp (ctx : LowCtx) : int = freshTmpT ctx W

let private wReg (id : int) : LReg = { Id = id; RTy = W }
let private fReg (id : int) : LReg = { Id = id; RTy = F64 }
let private lReg (id : int) : LReg = { Id = id; RTy = I64 }

// element kinds stored inline as a raw packed scalar (no per-element heap box),
// with (storage machine type, byte width). `int`/`int32`/`char`/`bool`/
// `nativeint` gain nothing — they are already 4-byte tagged words — so they
// keep the generic slot. float32 stores its 4-byte f32 bits in an i32 slot.
let private storLTy (k : string) : (LTy * int) option =
    match k with
    | "float" | "double" -> Some (F64, 8)
    | "int64" | "uint64" -> Some (I64, 8)
    | "float32" | "single" -> Some (W, 4)
    | "int16" | "uint16" -> Some (I16, 2)
    | "byte" | "sbyte" -> Some (I8, 1)
    | _ -> None
// the machine type a pre-store element value rides in before it hits its slot:
// f64/i64 stay wide; a packed narrow int or f32-bits is just an i32 word.
let private storValTy (sty : LTy) : LTy = match sty with F64 -> F64 | I64 -> I64 | _ -> W
let private storShape (k : string) : string = "sa:" + k

// an array whose element is an ALL-SCALAR inline record stores the elements
// contiguously and HEADERLESS (`[tag][len][fields][fields]…`): element i's
// fields sit at ARRHDR + i*stride, stride = the record's field bytes (size-HDR),
// and a field at record-offset off is at +(off-HDR). No per-element box or
// header, GC-invisible (a scalar array). Returns (field layout, stride). Mixed
// (ref-holding) element records need a per-element ref-map — not yet.
let private ARRHDR = HDR + 4
let private podArrOf (st : St) (kind : string) : (Dict<string, int * string> * int) option =
    match dictTryFind st.RecPod kind with
    | Some (layout, size, firstRefWord) when firstRefWord = size / 4 -> Some (layout, size - HDR)
    | _ -> None
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
// the language class-id of the object in register `t`: the header word itself
// in the standalone path, or (under GC, where the header is (tid<<1)|1) the
// class-id looked up in the tid->cid table
let private lowHeaderCid (t : LReg) : LExpr =
    if gc then
        LLoad (W, LPrim (AddW, [ LGetGlobal "$t2c"
                                 LPrim (ShlW, [ LPrim (ShrUW, [ LLoad (W, LGet t, 0); LConstW 1 ]); LConstW 2 ]) ]), 0)
    else LLoad (W, LGet t, 0)

// GC shadow-stack push/pop, inlined (no call) — roots[sp]=v; sp+=4, and the
// reverse. Only tagged/pointer values are ever pushed (constants are stored
// directly), so a popped slot left non-zero always holds a valid pointer: the
// scanner retains it for at most one cycle until overwritten — no corruption,
// so pop need not clear the slot.
let private gcPushStmts (v : LExpr) : LStmt list =
    [ LStore (W, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]), 0, v)
      LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ]
let private gcPopInto (addr : LExpr) (off : int) : LStmt list =
    [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ]))
      LStore (W, addr, off, LLoad (W, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]), 0)) ]

let private lowInt (n : int) : LExpr = LConstW ((n <<< 1) ||| 1)
let private lowUntag (e : LExpr) : LExpr = LPrim (ShrSW, [ e; LConstW 1 ])
let private lowTag (e : LExpr) : LExpr = LPrim (OrW, [ LPrim (ShlW, [ e; LConstW 1 ]); LConstW 1 ])

// self-hostable integer literal parsers. The compiler runs under its OWN
// wasm-linear backend during a WasmLin self-host, where System.Int32.TryParse
// is not in the subset (it stubs coreToLowE/lowPatTest to `unreachable`). The
// literals reaching here are lexer-validated, so a plain digit fold is enough.
// invalid input -> 0, matching the Int32.TryParse fallback these replaced (a
// hex/garbage literal was already lowered to 0, so byte-exactness is preserved).
let private parseI32Lit (s : string) : int =
    let neg = strLen s > 0 && charAt s 0 = '-'
    let start = if neg then 1 else 0
    let mutable acc = 0
    let mutable ok = strLen s > start
    let mutable i = start
    while i < strLen s do
        let d = int (charAt s i) - int '0'
        if d < 0 || d > 9 then ok <- false else acc <- acc * 10 + d
        i <- i + 1
    if ok then (if neg then 0 - acc else acc) else 0
let private parseI64Lit (s : string) : int64 =
    let neg = strLen s > 0 && charAt s 0 = '-'
    let start = if neg then 1 else 0
    let mutable acc = 0L
    let mutable ok = strLen s > start
    let mutable i = start
    while i < strLen s do
        let d = int (charAt s i) - int '0'
        if d < 0 || d > 9 then ok <- false else acc <- acc * 10L + int64 d
        i <- i + 1
    if ok then (if neg then 0L - acc else acc) else 0L
// float literal -> its double value: drop the F++ width suffix (Double.Parse
// throws on `5.0f`, unlike the old TryParse), and round a `float32` literal
// through f32 so it matches the value stored. `parseFloat` (the Double.Parse
// leaf) is isolated so this caller self-hosts.
let private parseFloatLit (s : string) : float =
    let num = s |> String.filter (fun c -> (c >= '0' && c <= '9') || c = '.' || c = '-' || c = '+' || c = 'e' || c = 'E')
    if s.EndsWith "f" || s.EndsWith "F" then float (float32 (Fpp.Prelude.parseFloat num))
    else Fpp.Prelude.parseFloat num

let private intArithOp (b : string) : LOp =
    match b with
    | "+" -> AddW
    | "-" -> SubW
    | "*" -> MulW
    | "/" -> DivSW
    // bitwise AND logical ops were falling through to RemSW — `&&&`/`&&`
    // compiled as `rem`. `&&`/`||` on 0/1 bools give the right result via
    // AndW/OrW (both operands are pure comparisons where this reaches the backend).
    | "&&&" | "&&" -> AndW
    | "|||" | "||" -> OrW
    | "^^^" -> XorW
    | "<<<" -> ShlW
    | ">>>" -> ShrSW
    | "%" -> RemSW
    | other ->
        (if not (isNull (System.Environment.GetEnvironmentVariable "FPP_OPDUMP")) then
             eprintfn "INTARITHOP-DEFAULT %s" other)
        RemSW

let private intCmpOp (b : string) : LOp =
    match b with
    | "<" -> LtSW
    | ">" -> GtSW
    | "<=" -> LeSW
    | ">=" -> GeSW
    | "=" -> EqW
    | _ -> NeW

// a `let rec f = fun … and g = fun …` group is a spine of consecutive
// recursive lambda bindings; collect them and the body they wrap.
let rec private recGroupOf (e : Expr) : (VarId * Expr) list * Expr =
    match e with
    | ELet (true, v, _, (ELam (_, _) as lam), rest) -> let ms, body = recGroupOf rest in (v, lam) :: ms, body
    | _ -> [], e

// The comparison shape of an operand: how `=`/`<`/`compare` must treat it. The
// tagged-int fast path is CORRECT only for scalars (immediate values); a heap
// shape needs a STRUCTURAL comparison — a tuple element-wise (its arity is not
// in the object, so it is synthesised from the static type), a string / list /
// array through the runtime $str_cmp / $cmpv.
type private CmpShape =
    | ShScalar | ShStr | ShFloat | ShInt64
    | ShList of CmpShape | ShArr of CmpShape | ShTup of CmpShape list | ShOther

let rec private shapeOfType (t : Type) : CmpShape =
    match prune t with
    | TTuple ts -> ShTup (List.map shapeOfType ts)
    | TCon (n, _) when n.StartsWith "$tup" -> ShOther
    | TCon ("string", _) -> ShStr
    | TCon (("float" | "double" | "single" | "float32" | "float16"), _) -> ShFloat
    | TCon (("int64" | "uint64"), _) -> ShInt64
    | TCon (("int" | "int32" | "uint32" | "char" | "bool" | "byte" | "sbyte" | "int16" | "uint16" | "nativeint"), _) -> ShScalar
    | TCon (("list" | "[]" | "seq"), (e :: _)) -> ShList (shapeOfType e)
    | TCon (("list" | "[]" | "seq"), _) -> ShList ShOther
    | TCon ("array", (e :: _)) -> ShArr (shapeOfType e)
    | TCon ("array", _) -> ShArr ShOther
    | TApp (h, (e :: _)) -> (match prune h with TCon (("list" | "[]" | "seq"), _) -> ShList (shapeOfType e) | TCon ("array", _) -> ShArr (shapeOfType e) | _ -> ShOther)
    | _ -> ShOther

// the unboxed local type for a monomorphic scalar binding, or None to keep it
// a tagged word. Mirrors flatScalarTy: only the 64-bit boxed scalars gain (int/
// bool/char are already unboxed words; float32/16 still ride an f64 box).
let private scalarLTy (t : Type) : LTy option =
    match prune t with
    // float32 rides an f64 box, so an unboxed float32 local/param is just an f64
    | TCon (("float" | "double" | "float32" | "single"), _) -> Some F64
    | TCon (("int64" | "uint64"), _) -> Some I64
    | _ -> None

// the wasm ABI type a value of this type is passed as: a raw f64/i64 for a
// monomorphic 64-bit scalar, else a tagged word.
let private abiTy (t : Type) : LTy = match scalarLTy t with Some ty -> ty | None -> W

// (param abi types, return abi type) of a top-level function: peel `arity`
// arrows off its scheme. None when every slot is a plain word (nothing to
// specialize — the uniform $lfn signature already fits).
let private funSigOf (sch : Scheme) (arity : int) : (LTy list * LTy) option =
    let rec go t n = if n <= 0 then [], t else (match prune t with TFun (a, r) -> let (ps, ret) = go r (n - 1) in a :: ps, ret | _ -> [], t)
    let argTs, retT = go sch.Body arity
    if List.length argTs <> arity then None
    else
        let ps = argTs |> List.map abiTy
        let ret = abiTy retT
        if List.forall (fun t -> t = W) ps && ret = W then None else Some (ps, ret)

let rec private shapeOfExpr (e : Expr) : CmpShape =
    match e with
    | ETuple xs -> ShTup (List.map shapeOfExpr xs)
    | ELit (LString _) -> ShStr
    | ELit (LFloat _) -> ShFloat
    | ELit (LInt s) when s.EndsWith "L" || s.EndsWith "l" -> ShInt64
    | ELit (LInt _ | LChar _ | LBool _) -> ShScalar
    | EListLit (x :: _) -> ShList (shapeOfExpr x)
    | EListLit [] -> ShList ShOther
    | EArray (_, (x :: _)) -> ShArr (shapeOfExpr x)
    | EArray _ -> ShArr ShOther
    | EVar (_, sch) | EVarI (_, sch, _) -> shapeOfType sch.Body
    // a function-built value (mk 3, List.head xs, …): the shape is the head's
    // RESULT type with `args` argument arrows peeled off
    | EApp ((EVar (_, sch) | EVarI (_, sch, _)), args) ->
        let rec peel t n = if n <= 0 then t else (match prune t with TFun (_, r) -> peel r (n - 1) | _ -> t)
        shapeOfType (peel sch.Body (List.length args))
    | _ -> ShOther

let rec private mergeShape (a : CmpShape) (b : CmpShape) : CmpShape =
    match a, b with
    | ShOther, x | x, ShOther -> x
    | ShTup xs, ShTup ys when List.length xs = List.length ys -> ShTup (List.map2 mergeShape xs ys)
    | ShList x, ShList y -> ShList (mergeShape x y)
    | ShArr x, ShArr y -> ShArr (mergeShape x y)
    | _ -> a

let private needsStructCmp (sh : CmpShape) : bool =
    match sh with
    | ShStr | ShFloat | ShInt64 | ShList _ | ShArr _ | ShTup _ -> true
    // ShOther is an unknown/generic type variable ('k in a generic function, e.g.
    // dictSlotH's `d.Keys.[e-1] = k`). The tagged-int/pointer fast path below is
    // correct ONLY for a statically-known tagged scalar; a compound held in a
    // generic (tuple/string/record key) lives behind a POINTER, so the fast path
    // compares heap addresses and every distinct-but-equal key misses. $cmpv is
    // self-describing — it handles tagged ints, strings, floats and compounds
    // uniformly — so route the unknown case through it. Only a KNOWN scalar keeps
    // the fast path.
    | ShScalar -> false
    | ShOther -> true

// the shape from a mangled type name — "$tupN$<t0.t1...>", "string", "int", … —
// used for the `compare` intrinsic, whose dispatch name carries the operand type
// even when the operands themselves are opaque (e.g. eta parameters).
let rec private shapeOfName (nm : string) : CmpShape =
    if nm.Contains "#" then ShOther
    elif nm.StartsWith "$tup" && nm.Contains "$<" then
        let lt = nm.IndexOf "$<"
        let inner = substr nm (lt + 2) (strLen nm - (lt + 2) - 1)
        let parts = vecNew<string> ()
        let mutable depth = 0
        let mutable start = 0
        for i in 0 .. strLen inner - 1 do
            let c = charAt inner i
            if c = '<' then depth <- depth + 1
            elif c = '>' then depth <- depth - 1
            elif c = '.' && depth = 0 then (vecAdd parts (substr inner start (i - start)); start <- i + 1)
        vecAdd parts (substr inner start (strLen inner - start))
        ShTup (List.map shapeOfName (vecToList parts))
    else
        let bare = if nm.Contains "$<" then nm.Substring (0, nm.IndexOf "$<") else nm
        match bare with
        | "string" -> ShStr
        | "float" | "double" | "single" | "float32" | "float16" -> ShFloat
        | "int64" | "uint64" -> ShInt64
        | "int" | "int32" | "uint32" | "char" | "bool" | "byte" | "sbyte" | "int16" | "uint16" | "nativeint" -> ShScalar
        | "list" | "seq" | "[]" -> ShList ShOther
        | "array" -> ShArr ShOther
        | _ -> ShOther

// compare two operand WORDS by their static shape -> a raw -1/0/1 LExpr. Scalars
// compare their tagged payloads; strings/lists/arrays go through the runtime
// helpers; a tuple is unrolled element by element (reading HDR+4*i), recursing
// and short-circuiting on the first difference.
let rec private structCmp (ctx : LowCtx) (sh : CmpShape) (wa : LExpr) (wb : LExpr) : LExpr =
    match sh with
    | ShScalar ->
        LPrim (SubW, [ LPrim (GtSW, [ lowUntag wa; lowUntag wb ]); LPrim (LtSW, [ lowUntag wa; lowUntag wb ]) ])
    // an opaque operand (a generic HOF's element, type unknown here): the safe
    // runtime comparator — correct for ints/strings/float/int64, a no-op (0) for
    // compound FK_TAGGED shapes it cannot identify at runtime.
    | ShOther -> LCall ("$cmpv", [ wa; wb ])
    | ShStr -> LCall ("$str_cmp", [ wa; wb ])
    | ShFloat ->
        LPrim (SubW, [ LPrim (GtF, [ LLoad (F64, wa, HDR); LLoad (F64, wb, HDR) ]); LPrim (LtF, [ LLoad (F64, wa, HDR); LLoad (F64, wb, HDR) ]) ])
    | ShInt64 ->
        LPrim (SubW, [ LPrim (GtSL, [ LLoad (I64, wa, HDR); LLoad (I64, wb, HDR) ]); LPrim (LtSL, [ LLoad (I64, wa, HDR); LLoad (I64, wb, HDR) ]) ])
    | ShTup shapes ->
        let ra = freshTmp ctx
        let rb = freshTmp ctx
        let r = freshTmp ctx
        let elemCmp i shi = structCmp ctx shi (LLoad (W, LGet (wReg ra), HDR + 4 * i)) (LLoad (W, LGet (wReg rb), HDR + 4 * i))
        match shapes with
        | [] -> LConstW 0
        | sh0 :: more ->
            let init = [ LSet (wReg ra, wa); LSet (wReg rb, wb); LSet (wReg r, elemCmp 0 sh0) ]
            let guards = more |> List.mapi (fun k shi -> LIf (LPrim (EqW, [ LGet (wReg r); LConstW 0 ]), [ LSet (wReg r, elemCmp (k + 1) shi) ], []))
            LDo (init @ guards, LGet (wReg r))
    | ShList esh ->
        // walk two cons chains (head@HDR, tail@HDR+4; nil = 0) element-wise; on a
        // common prefix the shorter list is the smaller
        let pa = freshTmp ctx
        let pb = freshTmp ctx
        let r = freshTmp ctx
        let notNil p = LPrim (NeW, [ LGet (wReg p); LConstW 0 ])
        let cond = LPrim (AndW, [ notNil pa; LPrim (AndW, [ notNil pb; LPrim (EqW, [ LGet (wReg r); LConstW 0 ]) ]) ])
        let body =
            [ LSet (wReg r, structCmp ctx esh (LLoad (W, LGet (wReg pa), HDR)) (LLoad (W, LGet (wReg pb), HDR)))
              LIf (LPrim (EqW, [ LGet (wReg r); LConstW 0 ]),
                   [ LSet (wReg pa, LLoad (W, LGet (wReg pa), HDR + 4)); LSet (wReg pb, LLoad (W, LGet (wReg pb), HDR + 4)) ], []) ]
        LDo ([ LSet (wReg pa, wa); LSet (wReg pb, wb); LSet (wReg r, LConstW 0)
               LWhile (cond, body)
               LIf (LPrim (EqW, [ LGet (wReg r); LConstW 0 ]),
                    [ LSet (wReg r, LPrim (SubW, [ notNil pa; notNil pb ])) ], []) ],
             LGet (wReg r))
    | ShArr esh ->
        // element-wise over the shorter length (len@HDR, elem i @ 8+4*i); on a
        // common prefix the shorter array is the smaller
        let ra = freshTmp ctx
        let rb = freshTmp ctx
        let na = freshTmp ctx
        let nb = freshTmp ctx
        let i = freshTmp ctx
        let r = freshTmp ctx
        let elemAt reg = LLoad (W, LPrim (AddW, [ LGet (wReg reg); LPrim (AddW, [ LConstW 8; LPrim (MulW, [ LGet (wReg i); LConstW 4 ]) ]) ]), 0)
        let cond = LPrim (AndW, [ LPrim (LtSW, [ LGet (wReg i); LGet (wReg na) ]); LPrim (AndW, [ LPrim (LtSW, [ LGet (wReg i); LGet (wReg nb) ]); LPrim (EqW, [ LGet (wReg r); LConstW 0 ]) ]) ])
        let body =
            [ LSet (wReg r, structCmp ctx esh (elemAt ra) (elemAt rb))
              LIf (LPrim (EqW, [ LGet (wReg r); LConstW 0 ]), [ LSet (wReg i, LPrim (AddW, [ LGet (wReg i); LConstW 1 ])) ], []) ]
        LDo ([ LSet (wReg ra, wa); LSet (wReg rb, wb)
               LSet (wReg na, LLoad (W, LGet (wReg ra), HDR)); LSet (wReg nb, LLoad (W, LGet (wReg rb), HDR))
               LSet (wReg i, LConstW 0); LSet (wReg r, LConstW 0)
               LWhile (cond, body)
               LIf (LPrim (EqW, [ LGet (wReg r); LConstW 0 ]),
                    [ LSet (wReg r, LPrim (SubW, [ LPrim (GtSW, [ LGet (wReg na); LGet (wReg nb) ]); LPrim (LtSW, [ LGet (wReg na); LGet (wReg nb) ]) ])) ], []) ],
             LGet (wReg r))

let rec private coreToLowE (ctx : LowCtx) (e : Expr) : LExpr =
    let st = ctx.LSt
    match e with
    | ELit (LInt s) when s.EndsWith "L" || s.EndsWith "l" ->
        lowBoxI ctx (LConstL (parseI64Lit (s.Substring (0, s.Length - 1))))
    | ELit (LInt s) ->
        // strip an integer TYPE suffix before parsing — int16 `s`, uint16 `us`,
        // sbyte `y`, byte `uy`, uint32 `u`, nativeint `n` — else Int32.TryParse
        // rejects it and the literal silently becomes 0. (int64 `L` handled above.)
        let digits =
            match [ "us"; "uy"; "un"; "s"; "y"; "u"; "n" ] |> List.tryFind s.EndsWith with
            | Some suf -> s.Substring (0, s.Length - suf.Length)
            | None -> s
        lowInt (parseI32Lit digits)
    | ELit (LFloat s) -> lowBoxF ctx (LConstF (parseFloatLit s))
    | ELit (LBool b) -> lowInt (if b then 1 else 0)
    | ELit (LChar raw) -> lowInt (Fpp.Backend.BinDriver.charCode raw)
    | ELit LUnit | ELit LNull -> lowInt 0
    | ELit (LString s) -> lowStrConst st s
    | EVar (v, _) | EVarI (v, _, _) when (dictTryFind st.Externs v.Name).IsSome -> lowInt 0
    | EVar (v, _) | EVarI (v, _, _) -> dictSet nameOf (key v) v.Name; lowVarByKey ctx (key v)
    | ELet (true, _, _, ELam _, _) ->
        // a recursive local-function group: every member may reference every
        // other, so bind them all to CELLS first (their pointers are stable),
        // build each closure over those cells, then fill the cells. Reads
        // dereference the cell; a capture grabs the cell pointer. Handles both
        // self-recursion (a one-member group) and mutual `… and …`.
        let members, body = recGroupOf e
        let regs = members |> List.map (fun (v, lam) -> v, lam, freshReg ctx (key v))
        for v, _, _ in regs do dictSet ctx.LSt.CellVars (key v) true
        let allocs = regs |> List.map (fun (_, _, id) -> LSet (wReg id, lowMkCell ctx (lowInt 0)))
        let fills = regs |> List.map (fun (_, lam, id) -> LStore (W, LGet (wReg id), cellOff (), coreToLowE ctx lam))
        LDo (allocs @ fills, coreToLowE ctx body)
    | ELet (_, v, sch, rhs, body) ->
        LDo ([ lowLetBind ctx v sch rhs ], coreToLowE ctx body)
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
    // float AND float32 arithmetic: float32 rides an f64 box in this backend, so
    // an `s`-suffixed op lowers exactly like its `f` sibling (the f32 rounding
    // happens only when a value is demoted into a float32 slot).
    | EPrim (op, [ a; b ]) when (op.EndsWith "f" || op.EndsWith "s") && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/" ] ->
        let fa = lowUnboxF (coreToLowE ctx a)
        let fb = lowUnboxF (coreToLowE ctx b)
        let fop = match op.Substring (0, op.Length - 1) with | "+" -> AddF | "-" -> SubF | "*" -> MulF | _ -> DivF
        lowBoxF ctx (LPrim (fop, [ fa; fb ]))
    | EPrim (op, [ a; b ]) when (op.EndsWith "f" || op.EndsWith "s") && List.contains (op.Substring (0, op.Length - 1)) [ "<"; ">"; "<="; ">="; "="; "<>" ] ->
        let fa = lowUnboxF (coreToLowE ctx a)
        let fb = lowUnboxF (coreToLowE ctx b)
        let fop = match op.Substring (0, op.Length - 1) with | "<" -> LtF | ">" -> GtF | "<=" -> LeF | ">=" -> GeF | "=" -> EqF | _ -> NeF
        lowTag (LPrim (fop, [ fa; fb ]))
    | EPrim (("u-f" | "u-s"), [ a ]) -> lowBoxF ctx (LPrim (NegF, [ lowUnboxF (coreToLowE ctx a) ]))
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
    | EPrim ("::", [ h; t ]) -> lowObj ctx CID_LIST 0 [ coreToLowE ctx h; coreToLowE ctx t ]
    // list append: `a @ b` rebuilds a's spine onto b. Without this it fell to the
    // EPrim arithmetic path and `intArithOp`'s `%` default — `a @ b` compiled as
    // `a rem b` on two list POINTERS, trapping (divide-by-zero) the moment a spine
    // reached nil (0). Mirrors the GC backend's `$append`.
    | EPrim ("@", [ a; b ]) -> LCall ("$lappend", [ coreToLowE ctx a; coreToLowE ctx b ])
    // |n| on a tagged int, branchless: (n ^ (n>>31)) - (n>>31)
    | EPrim ("abs", [ a ]) ->
        let t = freshTmp ctx
        let n = LGet (wReg t)
        let m = LPrim (ShrSW, [ n; LConstW 31 ])
        LDo ([ LSet (wReg t, lowUntag (coreToLowE ctx a)) ], lowTag (LPrim (SubW, [ LPrim (XorW, [ n; m ]); m ])))
    // the builtin `compare a b` (an unbound EVar in the unoptimised core):
    // -1/0/1 by the operands' static shape
    | EApp ((EVar (v, _) | EVarI (v, _, _)), [ a; b ]) when v.Path = "(builtin)" && v.Name.StartsWith "compare" ->
        let sh = mergeShape (shapeOfExpr a) (shapeOfExpr b)
        let ra, rb, pre = evalRooted ctx a b
        LDo (pre, lowTag (structCmp ctx sh (LGet (wReg ra)) (LGet (wReg rb))))
    // the `compare` intrinsic: -1/0/1 by the shape its dispatch name carries
    | EApp (EUnknown n, [ a; b ]) when n.StartsWith "$class:Ordered:compare:" ->
        let sh = shapeOfName (n.Substring (strLen "$class:Ordered:compare:"))
        let ra, rb, pre = evalRooted ctx a b
        LDo (pre, lowTag (structCmp ctx sh (LGet (wReg ra)) (LGet (wReg rb))))
    // a comparison whose operands are a COMPOUND value (tuple/list/...), a STRING
    // (`=t`/`<t` — the `t` type suffix), or a STRUCTURAL `=@Type`/`<>@Type`
    // (records/unions): the tagged-int fast path below would compare heap
    // POINTERS, so route it through a structural comparison.
    | EPrim (op, [ a; b ]) when
        (let hasAt = op.Contains "@"
         let b0 = if hasAt then op.Substring (0, op.IndexOf "@") else baseOp op
         let cb = if (not hasAt) && b0.EndsWith "t" then b0.Substring (0, b0.Length - 1) else b0
         (match cb with "<" | ">" | "<=" | ">=" | "=" | "<>" -> true | _ -> false)
         && (hasAt || (baseOp op).EndsWith "t" || needsStructCmp (mergeShape (shapeOfExpr a) (shapeOfExpr b)))) ->
        let hasAt = op.Contains "@"
        let b0 = if hasAt then op.Substring (0, op.IndexOf "@") else baseOp op
        let isStr = (not hasAt) && b0.EndsWith "t"
        let cb = if isStr then b0.Substring (0, b0.Length - 1) else b0
        let sh = if isStr then ShStr elif hasAt then ShOther else mergeShape (shapeOfExpr a) (shapeOfExpr b)
        let ra, rb, pre = evalRooted ctx a b
        let cr = freshTmp ctx
        let boolOp = match cb with "=" -> EqW | "<>" -> NeW | "<" -> LtSW | ">" -> GtSW | "<=" -> LeSW | _ -> GeSW
        LDo (pre @ [ LSet (wReg cr, structCmp ctx sh (LGet (wReg ra)) (LGet (wReg rb))) ],
             lowTag (LPrim (boolOp, [ LGet (wReg cr); LConstW 0 ])))
    | EPrim (op, [ a; b ]) ->
        // Tagged-int fast paths: with x tagged as 2x+1, addition is
        // (a+b)-1 and subtraction (a-b)+1 — no untag/retag — and comparisons
        // hold on the tagged words unchanged (2x+1 is monotonic and sign-
        // preserving in x). Only *, /, % need the untagged operands.
        let bop = baseOp op
        let ta = coreToLowE ctx a
        let tb = coreToLowE ctx b
        match bop with
        | "+" -> LPrim (SubW, [ LPrim (AddW, [ ta; tb ]); LConstW 1 ])
        | "-" -> LPrim (AddW, [ LPrim (SubW, [ ta; tb ]); LConstW 1 ])
        | "<" | ">" | "<=" | ">=" | "=" | "<>" -> lowTag (LPrim (intCmpOp bop, [ ta; tb ]))
        | _ -> lowTag (LPrim (intArithOp bop, [ lowUntag ta; lowUntag tb ]))
    | ETuple xs -> lowObj ctx CID_TUPLE 0 (List.map (coreToLowE ctx) xs)
    | EListLit xs -> lowList ctx xs
    // a collapsed one-field record IS its field value — no heap object
    | ERecord (name, fields) when (dictTryFind st.Collapse name).IsSome ->
        let f = (dictTryFind st.Collapse name).Value
        (match fields |> List.tryPick (fun (fn2, e2) -> if fn2 = f then Some e2 else None) with
         | Some e2 -> coreToLowE ctx e2
         | None -> lowInt 0)
    | ERecordExt (name, baseE, updates) when (dictTryFind st.Collapse name).IsSome ->
        let f = (dictTryFind st.Collapse name).Value
        (match updates |> List.tryPick (fun (fn2, e2) -> if fn2 = f then Some e2 else None) with
         | Some e2 -> coreToLowE ctx e2
         | None -> coreToLowE ctx baseE)
    // inline value type: an all-scalar record stores its fields raw inline. Each
    // raw field value rides a typed local before the allocation (GC-invisible),
    // so no shadow rooting; a field read boxes (cancelled by unbox in arithmetic).
    | ERecord (name, fields) when (dictTryFind st.RecPod name).IsSome ->
        let (layout, _, _) = (dictTryFind st.RecPod name).Value
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst fields
        let items =
            order |> List.map (fun fn ->
                let (off, kind) = (dictTryFind layout fn).Value
                let ve = fields |> List.tryPick (fun (f, e) -> if f = fn then Some e else None)
                match storLTy kind with
                | Some (sty, _) ->
                    let raw = match ve with Some e -> storUnbox kind (coreToLowE ctx e) | None -> (match storValTy sty with F64 -> LConstF 0.0 | I64 -> LConstL 0L | _ -> LConstW 0)
                    (off, sty, storValTy sty, false, raw)
                | None -> (off, W, W, true, (match ve with Some e -> coreToLowE ctx e | None -> lowInt 0)))
        lowPodBuild ctx name items
    | ERecordExt (name, baseE, updates) when (dictTryFind st.RecPod name).IsSome ->
        let (layout, _, _) = (dictTryFind st.RecPod name).Value
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst updates
        let bl = freshTmp ctx
        // pre-evaluate each update value into a local; then bind base. lowPodBuild
        // then sees only pure reads (these locals + base loads), so its single
        // allocation cannot move an as-yet-unstored update value or the base.
        let updInfo =
            updates |> List.map (fun (fn, e) ->
                let (off, kind) = (dictTryFind layout fn).Value
                match storLTy kind with
                | Some (sty, _) -> let vty = storValTy sty in let id = freshTmpT ctx vty in (fn, LSet ({ Id = id; RTy = vty }, storUnbox kind (coreToLowE ctx e)), (off, sty, vty, false, LGet { Id = id; RTy = vty }))
                | None -> let id = freshTmp ctx in (fn, LSet (wReg id, coreToLowE ctx e), (off, W, W, true, LGet (wReg id))))
        let updEvals = updInfo |> List.map (fun (_, ev, _) -> ev)
        let items =
            order |> List.map (fun fn ->
                match updInfo |> List.tryPick (fun (f, _, it) -> if f = fn then Some it else None) with
                | Some it -> it
                | None ->
                    let (off, kind) = (dictTryFind layout fn).Value
                    match storLTy kind with
                    | Some (sty, _) -> (off, sty, storValTy sty, false, LLoad (sty, LGet (wReg bl), off))
                    | None -> (off, W, W, true, LLoad (W, LGet (wReg bl), off)))
        LDo (updEvals @ [ LSet (wReg bl, coreToLowE ctx baseE) ], lowPodBuild ctx name items)
    | ERecord (name, fields) ->
        let order = match dictTryFind st.RecFields name with Some o -> o | None -> List.map fst fields
        lowObj ctx (cidRec st name) 0 (order |> List.map (fun fnm ->
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
        LDo ([ LSet (wReg b, coreToLowE ctx baseE) ], lowObj ctx (cidRec st name) 0 slots)
    | ECtor (case, _, args) ->
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        lowObj ctx (cidCase st case) 1 (LConstW tag :: List.map (coreToLowE ctx) args)
    | EField (r, _, owner) when (dictTryFind st.Collapse owner).IsSome -> coreToLowE ctx r
    // fused element-field access on an array of inline records — MUST precede the
    // plain POD field cases, or a field write would copy the element out and
    // mutate the throwaway. Read fuses to the slot; write hits the slot directly.
    | EField (EIndex (ek, arr, i), fname, _) when (podArrOf st ek).IsSome ->
        let (layout, stride) = (podArrOf st ek).Value
        let (off, kind) = (dictTryFind layout fname).Value
        let (sty, _) = (storLTy kind).Value
        let vty = storValTy sty
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        let fv = freshTmpT ctx vty
        LDo ([ LSet (wReg ar, coreToLowE ctx arr)
               LSet (wReg ir, lowUntag (coreToLowE ctx i))
               LSet ({ Id = fv; RTy = vty }, LLoad (sty, LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ]), ARRHDR + off - HDR)) ],
             storBox ctx kind (LGet { Id = fv; RTy = vty }))
    | EFieldSet (EIndex (ek, arr, i), fname, _, v) when (podArrOf st ek).IsSome ->
        let (layout, stride) = (podArrOf st ek).Value
        let (off, kind) = (dictTryFind layout fname).Value
        let (sty, _) = (storLTy kind).Value
        let vty = storValTy sty
        let fv = freshTmpT ctx vty
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        LDo ([ LSet ({ Id = fv; RTy = vty }, storUnbox kind (coreToLowE ctx v))
               LSet (wReg ar, coreToLowE ctx arr)
               LSet (wReg ir, lowUntag (coreToLowE ctx i))
               LStore (sty, LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ]), ARRHDR + off - HDR, LGet { Id = fv; RTy = vty }) ],
             lowInt 0)
    | EField (r, fname, owner) when (dictTryFind st.RecPod owner).IsSome ->
        let (layout, _, _) = (dictTryFind st.RecPod owner).Value
        let (off, kind) = (dictTryFind layout fname).Value
        (match storLTy kind with
         | Some (sty, _) ->
             let vty = storValTy sty
             let fv = freshTmpT ctx vty
             LDo ([ LSet ({ Id = fv; RTy = vty }, LLoad (sty, coreToLowE ctx r, off)) ], storBox ctx kind (LGet { Id = fv; RTy = vty }))
         | None -> LLoad (W, coreToLowE ctx r, off))
    | EFieldSet (r, fname, owner, v) when (dictTryFind st.RecPod owner).IsSome ->
        let (layout, _, _) = (dictTryFind st.RecPod owner).Value
        let (off, kind) = (dictTryFind layout fname).Value
        (match storLTy kind with
         | Some (sty, _) ->
             let vty = storValTy sty
             let fv = freshTmpT ctx vty
             let rr = freshTmp ctx
             LDo ([ LSet ({ Id = fv; RTy = vty }, storUnbox kind (coreToLowE ctx v))
                    LSet (wReg rr, coreToLowE ctx r)
                    LStore (sty, LGet (wReg rr), off, LGet { Id = fv; RTy = vty }) ], lowInt 0)
         | None -> LDo ([ LStore (W, coreToLowE ctx r, off, coreToLowE ctx v) ], lowInt 0))
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
    // ---- arrays of inline value-type records (all-scalar elements) ----
    // elements are contiguous & HEADERLESS at ARRHDR + i*stride. A whole-element
    // read copies out to a fresh headed record; a whole-element write copies the
    // source record's fields into the slot. (The FUSED field access on an element
    // — `arr.[i].f` / `arr.[i].f <- v` — is matched earlier, ahead of the plain
    // POD field cases, so a field write hits the slot instead of a throwaway.)
    | EIndex (ek, arr, i) when (podArrOf st ek).IsSome ->
        let (layout, stride) = (podArrOf st ek).Value
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        let elemBase = LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ])
        let items = order |> List.map (fun fn ->
            let (off, kind) = (dictTryFind layout fn).Value
            let (sty, _) = (storLTy kind).Value
            (off, sty, storValTy sty, false, LLoad (sty, elemBase, ARRHDR + off - HDR)))
        LDo ([ LSet (wReg ar, coreToLowE ctx arr); LSet (wReg ir, lowUntag (coreToLowE ctx i)) ], lowPodBuild ctx ek items)
    | EIndexSet (ek, arr, i, v) when (podArrOf st ek).IsSome ->
        let (layout, stride) = (podArrOf st ek).Value
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let vr = freshTmp ctx
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        let elemBase = LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ])
        let copies = order |> List.map (fun fn ->
            let (off, kind) = (dictTryFind layout fn).Value
            let (sty, _) = (storLTy kind).Value
            LStore (sty, elemBase, ARRHDR + off - HDR, LLoad (sty, LGet (wReg vr), off)))
        LDo ([ LSet (wReg vr, coreToLowE ctx v); LSet (wReg ar, coreToLowE ctx arr); LSet (wReg ir, lowUntag (coreToLowE ctx i)) ] @ copies, lowInt 0)
    | EArrayCreate (ek, n, init) when (podArrOf st ek).IsSome ->
        let (layout, stride) = (podArrOf st ek).Value
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let cnt = freshTmp ctx
        let vr = freshTmp ctx
        let bs = freshTmp ctx
        let it = freshTmp ctx
        let elemBase = LPrim (AddW, [ LGet (wReg bs); LPrim (MulW, [ LGet (wReg it); LConstW stride ]) ])
        let copies = order |> List.map (fun fn ->
            let (off, kind) = (dictTryFind layout fn).Value
            let (sty, _) = (storLTy kind).Value
            LStore (sty, elemBase, ARRHDR + off - HDR, LLoad (sty, LGet (wReg vr), off)))
        let alloc = if gc then LCall ("$fpallocn", [ LConstW (gcTid ctx.LSt ("pa:" + ek) stride FK_SCALAR_ARRAY 0); LGet (wReg cnt) ]) else LAlloc (LPrim (AddW, [ LConstW ARRHDR; LPrim (MulW, [ LGet (wReg cnt); LConstW stride ]) ]))
        let stmts =
            [ LSet (wReg cnt, lowUntag (coreToLowE ctx n)); LSet (wReg vr, coreToLowE ctx init) ]
            @ (if gc then [ LCallVoidS ("$spush", [ LGet (wReg vr) ]) ] else [])
            @ [ LSet (wReg bs, alloc) ]
            @ (if gc then [ LSet (wReg vr, LCall ("$spop", [])) ] else [])
            @ (if gc then [] else [ LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY); LStore (W, LGet (wReg bs), HDR, LGet (wReg cnt)) ])
            @ [ LSet (wReg it, LConstW 0)
                LWhile (LPrim (LtUW, [ LGet (wReg it); LGet (wReg cnt) ]), copies @ [ LSet (wReg it, LPrim (AddW, [ LGet (wReg it); LConstW 1 ])) ]) ]
        LDo (stmts, LGet (wReg bs))
    | EArray (ek, xs) when (podArrOf st ek).IsSome ->
        let (layout, stride) = (podArrOf st ek).Value
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let n = List.length xs
        let bs = freshTmp ctx
        let alloc = if gc then LCall ("$fpallocn", [ LConstW (gcTid ctx.LSt ("pa:" + ek) stride FK_SCALAR_ARRAY 0); LConstW n ]) else LAlloc (LConstW (ARRHDR + n * stride))
        let copyFields eb vr = order |> List.map (fun fn ->
            let (off, kind) = (dictTryFind layout fn).Value
            let (sty, _) = (storLTy kind).Value
            LStore (sty, eb, ARRHDR + off - HDR, LLoad (sty, LGet (wReg vr), off)))
        if gc then
            // materialise + PUSH every element record BEFORE the array alloc (each
            // build may collect); alloc last, then pop each (LIFO) and copy its
            // fields into its slot — no allocation during the copies, so the array
            // base is stable and every element pointer was rooted across the alloc.
            let pushes = xs |> List.collect (fun x -> gcPushStmts (coreToLowE ctx x))
            let popCopy idx =
                let tr = freshTmp ctx
                let eb = LPrim (AddW, [ LGet (wReg bs); LConstW (idx * stride) ])
                LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ]))
                :: LSet (wReg tr, LLoad (W, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]), 0))
                :: copyFields eb tr
            let popCopies = List.init n (fun j -> n - 1 - j) |> List.collect popCopy
            LDo (pushes @ [ LSet (wReg bs, alloc) ] @ popCopies, LGet (wReg bs))
        else
            let copyElem idx x =
                let vr = freshTmp ctx
                LSet (wReg vr, coreToLowE ctx x) :: copyFields (LPrim (AddW, [ LGet (wReg bs); LConstW (idx * stride) ])) vr
            LDo ([ LSet (wReg bs, alloc); LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY); LStore (W, LGet (wReg bs), HDR, LConstW n) ] @ (xs |> List.mapi copyElem |> List.concat), LGet (wReg bs))
    // packed scalar arrays: `float[]`/`int64[]`/`float32[]`/`int16[]`/`byte[]`…
    // are scalar arrays [tag][len][elem x len] with elements inline at HDR+4,
    // stride = the element byte width — no per-element box, GC-invisible. The
    // value rides in a typed f64/i64/word local across the allocation (no
    // shadow-stack rooting). A read boxes (cancelled by unbox in arithmetic), a
    // write unboxes; storBox/storUnbox carry the per-kind tag / sign-extend /
    // f32-reinterpret. `int`/`char`/`bool`/`nativeint` stay generic tagged words.
    | EArray (k, xs) when (storLTy k).IsSome ->
        let (sty, w) = (storLTy k).Value
        let vty = storValTy sty
        let n = List.length xs
        let vregs = xs |> List.map (fun _ -> freshTmpT ctx vty)
        let bs = freshTmp ctx
        let evals = List.map2 (fun vr x -> LSet ({ Id = vr; RTy = vty }, storUnbox k (coreToLowE ctx x))) vregs xs
        let alloc =
            if gc then LCall ("$fpallocn", [ LConstW (gcTid ctx.LSt (storShape k) w FK_SCALAR_ARRAY 0); LConstW n ])
            else LAlloc (LConstW (HDR + 4 + n * w))
        let hdr = if gc then [] else [ LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY); LStore (W, LGet (wReg bs), HDR, LConstW n) ]
        let stores = vregs |> List.mapi (fun i vr -> LStore (sty, LGet (wReg bs), HDR + 4 + i * w, LGet { Id = vr; RTy = vty }))
        LDo (evals @ [ LSet (wReg bs, alloc) ] @ hdr @ stores, LGet (wReg bs))
    | EIndex (k, arr, i) when (storLTy k).IsSome ->
        let (sty, w) = (storLTy k).Value
        let vty = storValTy sty
        let ir = freshTmp ctx
        let fv = freshTmpT ctx vty
        LDo ([ LSet (wReg ir, lowUntag (coreToLowE ctx i))
               LSet ({ Id = fv; RTy = vty }, LLoad (sty, LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LGet (wReg ir); LConstW w ]) ]), HDR + 4)) ],
             storBox ctx k (LGet { Id = fv; RTy = vty }))
    | EIndexSet (k, arr, i, v) when (storLTy k).IsSome ->
        let (sty, w) = (storLTy k).Value
        let vty = storValTy sty
        let fv = freshTmpT ctx vty
        let ir = freshTmp ctx
        LDo ([ LSet ({ Id = fv; RTy = vty }, storUnbox k (coreToLowE ctx v))
               LSet (wReg ir, lowUntag (coreToLowE ctx i))
               LStore (sty, LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LGet (wReg ir); LConstW w ]) ]), HDR + 4, LGet { Id = fv; RTy = vty }) ],
             lowInt 0)
    | EArray (_, xs) -> lowObj ctx CID_ARRAY 0 (LConstW (List.length xs) :: List.map (coreToLowE ctx) xs)
    // `s.[i]` on a STRING: its element type comes through as a symbolic `#id`
    // (not "char"), so storLTy misses it and the general ref-array path below
    // would read a 4-byte WORD (two units) as a pointer — garbage char codes,
    // which broke every charAt and the whole lexer. A string's UTF-16 units sit
    // at HDR+4 with stride 2; read one, zero-extended (load16_u), and tag it.
    | EIndex (_, arr, i) when shapeOfExpr arr = ShStr ->
        let ir = freshTmp ctx
        LDo ([ LSet (wReg ir, lowUntag (coreToLowE ctx i)) ],
             lowTag (LLoad (I16, LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LGet (wReg ir); LConstW 2 ]) ]), HDR + 4)))
    | EIndex (_, arr, i) ->
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ lowUntag (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LLoad (W, addr, HDR)
    | EIndexSet (_, arr, i, v) ->
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ lowUntag (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LDo ([ LStore (W, addr, HDR, coreToLowE ctx v) ], lowInt 0)
    | EArrayLen (_, arr) -> lowTag (LLoad (W, coreToLowE ctx arr, HDR))
    | EArrayCreate (k, n, init) when (storLTy k).IsSome ->
        let (sty, w) = (storLTy k).Value
        let vty = storValTy sty
        let cnt = freshTmp ctx
        let fv = freshTmpT ctx vty
        let bs = freshTmp ctx
        let it = freshTmp ctx
        let alloc =
            if gc then LCall ("$fpallocn", [ LConstW (gcTid ctx.LSt (storShape k) w FK_SCALAR_ARRAY 0); LGet (wReg cnt) ])
            else LAlloc (LPrim (AddW, [ LConstW (HDR + 4); LPrim (MulW, [ LGet (wReg cnt); LConstW w ]) ]))
        // `Array.zeroCreate` keeps a `$zero` marker whose zero is per-storage —
        // fill the raw scalar zero, NOT a mis-unboxed tagged 0 (which would read
        // a bogus address as if the slot were boxed).
        let isZero = match init with EUnknown n | EApp (EUnknown n, _) -> n.StartsWith "$zero" | _ -> false
        let fill = if isZero then (match vty with F64 -> LConstF 0.0 | I64 -> LConstL 0L | _ -> LConstW 0) else storUnbox k (coreToLowE ctx init)
        let stmts =
            [ LSet (wReg cnt, lowUntag (coreToLowE ctx n))
              LSet ({ Id = fv; RTy = vty }, fill)
              LSet (wReg bs, alloc) ]
            @ (if gc then [] else [ LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY); LStore (W, LGet (wReg bs), HDR, LGet (wReg cnt)) ])
            @ [ LSet (wReg it, LConstW 0)
                LWhile (LPrim (LtUW, [ LGet (wReg it); LGet (wReg cnt) ]),
                        [ LStore (sty, LPrim (AddW, [ LGet (wReg bs); LPrim (MulW, [ LGet (wReg it); LConstW w ]) ]), HDR + 4, LGet { Id = fv; RTy = vty })
                          LSet (wReg it, LPrim (AddW, [ LGet (wReg it); LConstW 1 ])) ]) ]
        LDo (stmts, LGet (wReg bs))
    | EArrayCreate (_, n, init) ->
        let cnt = freshTmp ctx
        let iv = freshTmp ctx
        let bs = freshTmp ctx
        let it = freshTmp ctx
        let stmts =
            [ LSet (wReg cnt, lowUntag (coreToLowE ctx n))
              LSet (wReg iv, coreToLowE ctx init) ]
            // GC: the fill value may be a heap pointer live across the array
            // allocation — push it over the safepoint and read it back
            @ (if gc then [ LCallVoidS ("$spush", [ LGet (wReg iv) ]) ] else [])
            @ [ LSet (wReg bs, (if gc then LCall ("$fpallocn", [ LConstW (gcTid ctx.LSt "arr" 4 FK_REF_ARRAY 2); LGet (wReg cnt) ]) else LAlloc (LPrim (AddW, [ LConstW (HDR + 4); LPrim (MulW, [ LGet (wReg cnt); LConstW 4 ]) ])))) ]
            @ (if gc then [ LSet (wReg iv, LCall ("$spop", [])) ] else [])
            @ (if gc then [] else [ LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY); LStore (W, LGet (wReg bs), HDR, LGet (wReg cnt)) ])
            @ [ LSet (wReg it, LConstW 0)
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
    // int from int (widen/identity in the tagged model) and int truncations
    | EApp (EUnknown n, [ a ]) when n = "int#" || n.StartsWith "int#t" || n.StartsWith "int#i" -> coreToLowE ctx a
    // byte / narrow: mask the tagged value's payload to 8 bits
    | EApp (EUnknown n, [ a ]) when n.StartsWith "byte#" -> lowTag (LPrim (AndW, [ lowUntag (coreToLowE ctx a); LConstW 0xFF ]))
    // the raw bits of a double, as int64 — read the boxed payload as i64
    | EApp (EUnknown "doubleBits", [ a ]) -> lowBoxI ctx (LLoad (I64, coreToLowE ctx a, HDR))
    // print / printraw: write a string to stdout (print's newline matters only
    // on the compiler's error paths, which the fixpoint success path never hits)
    | EApp (EUnknown ("print" | "printraw" | "printRaw"), [ a ]) -> LDo ([ LCallVoidS ("$prints", [ coreToLowE ctx a ]) ], lowInt 0)
    | EApp (EUnknown "isNull", [ x ]) -> lowTag (LPrim (EqW, [ coreToLowE ctx x; LConstW 0 ]))
    | EApp (EUnknown ("refEq" | "$refeq"), [ a; b ]) -> lowTag (LPrim (EqW, [ coreToLowE ctx a; coreToLowE ctx b ]))
    | EApp (EUnknown ("hash" | "$hash"), [ a ]) -> lowTag (LCall ("$hashv", [ coreToLowE ctx a ]))
    // cells: $cellof yields the cell POINTER (its storage, no deref); $cellget
    // reads through it; $cellset writes; $forcecell is a marker
    | EApp (EUnknown "$cellof", [ (EVar (v, _) | EVarI (v, _, _)) ]) -> lowVarStore ctx (key v)
    | EApp (EUnknown "$cellget", [ c ]) -> LLoad (W, coreToLowE ctx c, cellOff ())
    | EApp (EUnknown "$cellset", [ c; v ]) -> LDo ([ LStore (W, coreToLowE ctx c, cellOff (), coreToLowE ctx v) ], lowInt 0)
    | EApp (EUnknown "$forcecell", [ r ]) -> coreToLowE ctx r
    | EApp (EUnknown "$str.StartsWith", [ s; p ]) -> lowTag (LCall ("$str_starts", [ coreToLowE ctx s; coreToLowE ctx p ]))
    | EApp (EUnknown "$str.EndsWith", [ s; p ]) -> lowTag (LCall ("$str_ends", [ coreToLowE ctx s; coreToLowE ctx p ]))
    | EApp (EUnknown "$str.Contains", [ s; p ]) ->
        lowTag (LPrim (GeSW, [ LCall ("$str_find", [ coreToLowE ctx s; coreToLowE ctx p; LConstW 0 ]); LConstW 0 ]))
    | EApp (EUnknown "$str.IndexOf", [ s; p ]) ->
        lowTag (LCall ("$str_find", [ coreToLowE ctx s; coreToLowE ctx p; LConstW 0 ]))
    | EApp (EUnknown "$str.IndexOf#2", [ s; c ]) ->
        lowTag (LCall ("$str_find_char", [ coreToLowE ctx s; lowUntag (coreToLowE ctx c) ]))
    | EApp (EUnknown "$str.IndexOf#3", [ s; p; from ]) ->
        lowTag (LCall ("$str_find", [ coreToLowE ctx s; coreToLowE ctx p; lowUntag (coreToLowE ctx from) ]))
    | EApp (EUnknown "$str.LastIndexOf", [ s; c ]) ->
        lowTag (LCall ("$str_last_find_char", [ coreToLowE ctx s; lowUntag (coreToLowE ctx c) ]))
    | EApp (EUnknown "$str.Split", [ s; c ]) ->
        // returns a heap string array (an even pointer), not a tagged value
        LCall ("$str_split_char", [ coreToLowE ctx s; lowUntag (coreToLowE ctx c) ])
    | EApp (EUnknown "$str.Contains#2", [ s; c ]) ->
        lowTag (LPrim (GeSW, [ LCall ("$str_find_char", [ coreToLowE ctx s; lowUntag (coreToLowE ctx c) ]); LConstW 0 ]))
    | EApp (EUnknown "$str.StartsWith#2", [ s; c ]) ->
        lowTag (LPrim (EqW, [ LCall ("$str_find_char", [ coreToLowE ctx s; lowUntag (coreToLowE ctx c) ]); LConstW 0 ]))
    | EApp (EUnknown "$str.EndsWith#2", [ s; c ]) ->
        // last occurrence index == len-1 (and >=0, which excludes the empty string)
        let sv = freshTmp ctx
        let nv = freshTmp ctx
        LDo ([ LSet (wReg sv, coreToLowE ctx s)
               LSet (wReg nv, LCall ("$str_last_find_char", [ LGet (wReg sv); lowUntag (coreToLowE ctx c) ])) ],
             lowTag (LPrim (AndW, [ LPrim (GeSW, [ LGet (wReg nv); LConstW 0 ])
                                    LPrim (EqW, [ LGet (wReg nv); LPrim (SubW, [ LLoad (W, LGet (wReg sv), HDR); LConstW 1 ]) ]) ])))
    | EApp (EUnknown "$str.ToUpper", [ s ]) -> LCall ("$str_upper", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.ToLower", [ s ]) -> LCall ("$str_lower", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.ToCharArray", [ s ]) -> LCall ("$str_chars", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.PadLeft", [ s; w ]) ->
        LCall ("$str_pad", [ coreToLowE ctx s; lowUntag (coreToLowE ctx w); LConstW 32; LConstW 0 ])
    | EApp (EUnknown "$str.PadRight", [ s; w ]) ->
        LCall ("$str_pad", [ coreToLowE ctx s; lowUntag (coreToLowE ctx w); LConstW 32; LConstW 1 ])
    | EApp (EUnknown ("$str.TrimStart" | "$str.TrimStart#2"), [ s; cs ]) ->
        // cs is either a tagged char or a tagged-char array — the helper tests the low bit
        LCall ("$str_trim_start_chars", [ coreToLowE ctx s; coreToLowE ctx cs ])
    | EApp (EUnknown ("$str.TrimEnd" | "$str.TrimEnd#2"), [ s; cs ]) ->
        LCall ("$str_trim_end_chars", [ coreToLowE ctx s; coreToLowE ctx cs ])
    | EApp (EUnknown "$str.Insert", [ s; i; v ]) ->
        LCall ("$str_insert", [ coreToLowE ctx s; lowUntag (coreToLowE ctx i); coreToLowE ctx v ])
    | EApp (EUnknown "$str.Remove", [ s; i ]) ->
        LCall ("$strsub", [ coreToLowE ctx s; LConstW 0; lowUntag (coreToLowE ctx i) ])
    | EApp (EUnknown "$str.Remove#2", [ s; i; n ]) ->
        LCall ("$str_remove2", [ coreToLowE ctx s; lowUntag (coreToLowE ctx i); lowUntag (coreToLowE ctx n) ])
    | EApp (EUnknown "$str.Trim", [ s ]) -> LCall ("$str_trim", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.Replace", [ s; a; b ]) -> LCall ("$str_replace", [ coreToLowE ctx s; coreToLowE ctx a; coreToLowE ctx b ])
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
    // string of a char: a fresh one-unit string (NOT the decimal of its code)
    | EApp (EUnknown "string#c", [ a ]) -> LCall ("$str_of_char", [ lowUntag (coreToLowE ctx a) ])
    // string of a string is the identity
    | EApp (EUnknown "string#t", [ a ]) -> coreToLowE ctx a
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string" -> LCall ("$str_of_int", [ coreToLowE ctx a ])
    // a call to an `extern` host import: no host env yet, so answer the null
    // default (readTextRaw null -> None), letting the pipeline RUN instead of
    // stubbing the caller. Args still evaluate for their side effects.
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when (dictTryFind st.Externs v.Name).IsSome ->
        LDo (args |> List.map (fun a -> LEval (coreToLowE ctx a)), lowInt 0)
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args)
        when (dictTryFind st.Funcs (key v)) = Some (List.length args) ->
        (match dictTryFind st.FuncSig (key v) with
         | Some (paramTys, retTy) ->
             let loweredArgs = List.map2 (fun ty a -> match ty with W -> coreToLowE ctx a | _ -> flatUnbox ty (coreToLowE ctx a)) paramTys args
             (match retTy with
              | W -> LCall (fn v, loweredArgs)
              // hold the scalar result in a typed local before boxing: the call
              // is a safepoint, so a bare box-around-call would let the GC move
              // the fresh box out from under the store. box-elim pushes through
              // the LDo, so an arithmetic use still reduces to the raw call.
              | _ -> let r = freshTmpT ctx retTy in LDo ([ LSet ({ Id = r; RTy = retTy }, LCall (fn v, loweredArgs)) ], flatBox ctx retTy (LGet { Id = r; RTy = retTy })))
         | None -> LCall (fn v, List.map (coreToLowE ctx) args))
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
        let cid = lowHeaderCid (wReg t)
        // the vtable base: a fixed constant in the standalone path; under GC the
        // vtable is a fpprt array kept in a root slot (its data starts past the
        // [tag][len] header), read fresh so a collection's move is seen
        let vtBase =
            if gc then LPrim (AddW, [ LLoad (W, LGetGlobal "$roots", 4 * st.VtSlot); LConstW 8 ])
            else LConstW st.VtBase
        let idxAddr =
            LPrim (AddW, [ vtBase
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

// evaluate two comparison operands into fresh registers, keeping the FIRST
// rooted (GC shadow stack) across the SECOND's evaluation — the second operand
// may allocate and, under the moving collector, relocate the first. Without
// this a `compare (f x) (g y)` on heap values reads a STALE first operand.
and private evalRooted (ctx : LowCtx) (a : Expr) (b : Expr) : int * int * LStmt list =
    let ra = freshTmp ctx
    let rb = freshTmp ctx
    let stmts =
        if gc then
            [ LCallVoidS ("$spush", [ coreToLowE ctx a ])
              LSet (wReg rb, coreToLowE ctx b)
              LSet (wReg ra, LCall ("$spop", [])) ]
        else
            [ LSet (wReg ra, coreToLowE ctx a); LSet (wReg rb, coreToLowE ctx b) ]
    ra, rb, stmts

and private coreToLowS (ctx : LowCtx) (e : Expr) : LStmt list =
    match e with
    | ESeq xs -> List.collect (coreToLowS ctx) xs
    | ELet (_, v, sch, rhs, body) ->
        lowLetBind ctx v sch rhs :: coreToLowS ctx body
    | EAssign (v, rhs) when (dictTryFind ctx.LSt.CellVars (key v)).IsSome ->
        // a captured mutable: store into its cell (shared with the closure)
        [ LStore (W, lowVarStore ctx (key v), cellOff (), coreToLowE ctx rhs) ]
    | EAssign (v, rhs) ->
        (match dictTryFind ctx.Regs (key v) with
         | Some id ->
             (match dictTryFind ctx.VarScalar (key v) with
              | Some ty -> [ LSet ({ Id = id; RTy = ty }, flatUnbox ty (coreToLowE ctx rhs)) ]
              | None -> [ LSet (wReg id, coreToLowE ctx rhs) ])
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
// allocate a heap object of `n = List.length slots` words, `raw` of which are
// leading non-pointer metadata (the union tag, a closure's kind+code-index)
// that a GC trace must skip. Standalone: a bump alloc + a class-id header we
// write. GC: fpprt_alloc writes the (tid<<1)|1 header itself, so we only store
// the slots; the shape gets an fpprt type-id whose TAGGED tracer scans from the
// first real word. CID_ARRAY is the variable-length REF_ARRAY case.
and private lowObj (ctx : LowCtx) (cid : int) (raw : int) (slots : LExpr list) : LExpr =
    let n = List.length slots
    let b = freshTmp ctx
    let st = ctx.LSt
    if gc && cid = CID_ARRAY then
        // [tag][len][elems]: fpprt_alloc_array writes tag@0 and len@4; we store
        // the elements from offset 8. Each element is pushed to the shadow stack
        // BEFORE the allocation (which may collect) and popped back after — a
        // move updates the pushed pointer, so nothing in flight is lost.
        let tid = gcTid st "arr" 4 FK_REF_ARRAY 2
        let len = List.head slots
        let elems = List.tail slots
        // a constant element is not a heap pointer (and an even raw constant must
        // NOT reach the pointer-scanned shadow stack) — store it directly; push
        // only the potential pointers across the allocation safepoint
        let isConst e = match e with LConstW _ -> true | _ -> false
        let idx = elems |> List.mapi (fun i v -> i, v)
        let pushes = idx |> List.filter (fun (_, v) -> not (isConst v)) |> List.collect (fun (_, v) -> gcPushStmts v)
        let pops = idx |> List.filter (fun (_, v) -> not (isConst v)) |> List.rev |> List.collect (fun (i, _) -> gcPopInto (LGet (wReg b)) (8 + 4 * i))
        let consts = idx |> List.filter (fun (_, v) -> isConst v) |> List.map (fun (i, v) -> LStore (W, LGet (wReg b), 8 + 4 * i, v))
        LDo (pushes @ [ LSet (wReg b, LCall ("$fpallocn", [ LConstW tid; len ])) ] @ pops @ consts, LGet (wReg b))
    elif gc then
        let sk = "s:" + string cid + ":" + string n + ":" + string raw
        // record the tid->cid mapping the first time a shape is allocated, so
        // `:?`/dispatch recover the class-id (covers classes, which the eager
        // record/union pass does not enumerate)
        let isNew = (dictTryFind st.Tids sk).IsNone
        let tid = gcTid st sk (HDR + 4 * n) FK_TAGGED (1 + raw)
        if isNew && cid >= CID_FIRST_USER then vecAdd st.TidCid (tid, cid)
        // constants (the union tag, a closure's kind/code index) are raw words:
        // store them directly. A pointer-or-tagged slot is pushed to the shadow
        // stack across the safepoint. NEVER push a raw constant — an even one
        // would be scanned as a bogus heap pointer.
        let isConst e = match e with LConstW _ -> true | _ -> false
        let idx = slots |> List.mapi (fun i v -> i, v)
        let pushes = idx |> List.filter (fun (_, v) -> not (isConst v)) |> List.collect (fun (_, v) -> gcPushStmts v)
        let pops = idx |> List.filter (fun (_, v) -> not (isConst v)) |> List.rev |> List.collect (fun (i, _) -> gcPopInto (LGet (wReg b)) (HDR + 4 * i))
        let consts = idx |> List.filter (fun (_, v) -> isConst v) |> List.map (fun (i, v) -> LStore (W, LGet (wReg b), HDR + 4 * i, v))
        LDo (pushes @ [ LSet (wReg b, LCall ("$fpalloc", [ LConstW tid ])) ] @ pops @ consts, LGet (wReg b))
    else
        let stores =
            LStore (W, LGet (wReg b), 0, LConstW cid)
            :: (slots |> List.mapi (fun i v -> LStore (W, LGet (wReg b), HDR + 4 * i, v)))
        LDo (LSet (wReg b, LAlloc (LConstW (HDR + 4 * n))) :: stores, LGet (wReg b))

// build an inline value-type record: items is (byte offset, store type, value
// type, isRef, value expr) per field. A SCALAR value rides a typed f64/i64/word
// local across the allocation (the GC never scans it); a REF pointer is pushed
// to the shadow stack across the alloc and popped into its slot (a constant word
// is stored directly, never scan-pushed). So a struct mixing scalars and refs
// builds with the scalars unboxed inline and every live pointer correctly rooted.
and private lowPodBuild (ctx : LowCtx) (name : string) (items : (int * LTy * LTy * bool * LExpr) list) : LExpr =
    let cid = cidRec ctx.LSt name
    let (_, size, firstRefWord) = (dictTryFind ctx.LSt.RecPod name).Value
    let bs = freshTmp ctx
    let alloc = if gc then LCall ("$fpalloc", [ LConstW (gcTid ctx.LSt ("inl:" + string cid) size FK_TAGGED firstRefWord) ]) else LAlloc (LConstW size)
    let hdr = if gc then [] else [ LStore (W, LGet (wReg bs), 0, LConstW cid) ]
    let scalars = items |> List.filter (fun (_, _, _, r, _) -> not r)
    let refs = items |> List.filter (fun (_, _, _, r, _) -> r)
    let svregs = scalars |> List.map (fun (_, _, vty, _, _) -> freshTmpT ctx vty)
    let scalarEvals = List.map2 (fun vr (_, _, vty, _, ve) -> LSet ({ Id = vr; RTy = vty }, ve)) svregs scalars
    let scalarStores = List.map2 (fun vr (off, sty, vty, _, _) -> LStore (sty, LGet (wReg bs), off, LGet { Id = vr; RTy = vty })) svregs scalars
    if gc then
        let isConst e = match e with LConstW _ -> true | _ -> false
        let refDyn = refs |> List.filter (fun (_, _, _, _, ve) -> not (isConst ve))
        let refCst = refs |> List.filter (fun (_, _, _, _, ve) -> isConst ve)
        let pushes = refDyn |> List.collect (fun (_, _, _, _, ve) -> gcPushStmts ve)
        let pops = refDyn |> List.rev |> List.collect (fun (off, _, _, _, _) -> gcPopInto (LGet (wReg bs)) off)
        let csts = refCst |> List.map (fun (off, _, _, _, ve) -> LStore (W, LGet (wReg bs), off, ve))
        LDo (scalarEvals @ pushes @ [ LSet (wReg bs, alloc) ] @ pops @ csts @ scalarStores, LGet (wReg bs))
    else
        let refStores = refs |> List.map (fun (off, _, _, _, ve) -> LStore (W, LGet (wReg bs), off, ve))
        LDo (scalarEvals @ [ LSet (wReg bs, alloc) ] @ hdr @ refStores @ scalarStores, LGet (wReg bs))

and private lowList (ctx : LowCtx) (xs : Expr list) : LExpr =
    match xs with
    | [] -> LConstW 0
    | x :: rest -> lowObj ctx CID_LIST 0 [ coreToLowE ctx x; lowList ctx rest ]

// a boxed 64-bit payload: the class-id header then an 8-byte payload at HDR;
// the wide type on the LStore/LLoad picks f64/i64 access. GC: a no-ref STRUCT
// (size 12); fpprt writes the header, we store the payload at HDR.
and private lowBox64 (ctx : LowCtx) (shape : string) (cid : int) (ty : LTy) (v : LExpr) : LExpr =
    let b = freshTmp ctx
    let alloc =
        if gc then LCall ("$fpalloc", [ LConstW (gcTid ctx.LSt shape (HDR + 8) FK_STRUCT 0) ])
        else LAlloc (LConstW (HDR + 8))
    let hdr = if gc then [] else [ LStore (W, LGet (wReg b), 0, LConstW cid) ]
    LDo (LSet (wReg b, alloc) :: hdr @ [ LStore (ty, LGet (wReg b), HDR, v) ], LGet (wReg b))

and private lowBoxF (ctx : LowCtx) (fv : LExpr) : LExpr = lowBox64 ctx "f64" CID_FLOAT F64 fv

// box elimination: unbox(box(v)) is just v — a box built here (an LDo whose
// value is its own register and whose last store is the payload) is cancelled
// on the spot, so a float/int64 chain (a+b, arr.[i]+c) never materialises the
// intermediate heap box. Correct because the elided alloc is side-effect free.
and private lowUnboxF (p : LExpr) : LExpr =
    match p with
    // a box built here is (…stmts…; store payload) with the register as its
    // value — cancel to the payload. The load-into-an-f64-local-then-box shape
    // (LDo whose value is itself a box) needs the unbox pushed through the LDo,
    // so a `float[]` read in arithmetic reduces to the bare f64 load.
    | LDo (stmts, LGet rb) when (match List.tryLast stmts with Some (LStore (F64, LGet rb2, off, _)) -> rb2 = rb && off = HDR | _ -> false) ->
        (match List.tryLast stmts with Some (LStore (_, _, _, v)) -> v | _ -> LLoad (F64, p, HDR))
    | LDo (stmts, tail) -> LDo (stmts, lowUnboxF tail)
    | _ -> LLoad (F64, p, HDR)

and private lowBoxI (ctx : LowCtx) (iv : LExpr) : LExpr = lowBox64 ctx "i64" CID_INT64 I64 iv

and private lowUnboxI (p : LExpr) : LExpr =
    match p with
    | LDo (stmts, LGet rb) when (match List.tryLast stmts with Some (LStore (I64, LGet rb2, off, _)) -> rb2 = rb && off = HDR | _ -> false) ->
        (match List.tryLast stmts with Some (LStore (_, _, _, v)) -> v | _ -> LLoad (I64, p, HDR))
    | LDo (stmts, tail) -> LDo (stmts, lowUnboxI tail)
    | _ -> LLoad (I64, p, HDR)

// box/unbox picked by the flat-scalar type (F64 vs I64) — for locals/ABI, where
// only the 64-bit scalars are unboxed.
and private flatBox (ctx : LowCtx) (ty : LTy) (v : LExpr) : LExpr =
    match ty with F64 -> lowBoxF ctx v | _ -> lowBoxI ctx v
and private flatUnbox (ty : LTy) (p : LExpr) : LExpr =
    match ty with F64 -> lowUnboxF p | _ -> lowUnboxI p

// a raw packed slot value -> the uniform tagged word, per element KIND: a wide
// scalar boxes; a narrow int sign/zero-extends then tags; float32 widens its
// stored bits to the f64 a float rides in.
and private storBox (ctx : LowCtx) (k : string) (raw : LExpr) : LExpr =
    match k with
    | "float" | "double" -> lowBoxF ctx raw
    | "int64" | "uint64" -> lowBoxI ctx raw
    | "float32" | "single" -> lowBoxF ctx (LPrim (PromF, [ LPrim (Bits2F, [ raw ]) ]))
    | "sbyte" -> lowTag (LPrim (ShrSW, [ LPrim (ShlW, [ raw; LConstW 24 ]); LConstW 24 ]))
    | "int16" -> lowTag (LPrim (ShrSW, [ LPrim (ShlW, [ raw; LConstW 16 ]); LConstW 16 ]))
    | _ -> lowTag raw   // byte / uint16: the unsigned load already zero-extended
// the uniform tagged word -> the raw packed slot value (store8/store16 truncate,
// so a narrow int just needs its low bits untagged).
and private storUnbox (k : string) (word : LExpr) : LExpr =
    match k with
    | "float" | "double" -> lowUnboxF word
    | "int64" | "uint64" -> lowUnboxI word
    | "float32" | "single" -> LPrim (F2Bits, [ LPrim (DemF, [ lowUnboxF word ]) ])
    | _ -> lowUntag word

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
    | PLit (LInt s) -> [ LBreakIf (fail, LPrim (NeW, [ lowUntag sc; LConstW (parseI32Lit s) ])) ]
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
    | PLit (LFloat s) -> [ LBreakIf (fail, LPrim (NeF, [ lowUnboxF sc; LConstF (parseFloatLit s) ])) ]
    | PLit (LString raw) ->
        // a string pattern is a value compare: $streq returns 1 when equal
        [ LBreakIf (fail, LPrim (EqW, [ LCall ("$streq", [ sc; lowStrConst st raw ]); LConstW 0 ])) ]
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
            | None -> err st ("wasm-linear LowIR: unresolved variable " + k + " name=" + (match dictTryFind nameOf k with Some n -> n | None -> "?")); lowInt 0

// bind a local `let`: a monomorphic scalar rides unboxed in a typed local
// (recorded in VarScalar, read/captured through a re-box), everything else a
// tagged word — wrapped in a cell when captured-and-mutable.
and private lowLetBind (ctx : LowCtx) (v : VarId) (sch : Scheme) (rhs : Expr) : LStmt =
    let st = ctx.LSt
    let k = key v
    let isCell = (dictTryFind st.CellVars k).IsSome
    match (if isCell then None else scalarLTy sch.Body) with
    | Some ty ->
        let id = freshReg ctx k
        vecSet ctx.RegTys id ty
        dictSet ctx.VarScalar k ty
        LSet ({ Id = id; RTy = ty }, flatUnbox ty (coreToLowE ctx rhs))
    | None ->
        let id = freshReg ctx k
        let init = if isCell then lowMkCell ctx (coreToLowE ctx rhs) else coreToLowE ctx rhs
        LSet (wReg id, init)

// read a variable: an unboxed scalar re-boxes to a word; a captured mutable
// dereferences its cell; else the storage content directly
and private lowVarByKey (ctx : LowCtx) (k : string) : LExpr =
    match dictTryFind ctx.VarScalar k with
    | Some ty -> (match dictTryFind ctx.Regs k with Some id -> flatBox ctx ty (LGet { Id = id; RTy = ty }) | None -> lowVarStore ctx k)
    | None ->
        let store = lowVarStore ctx k
        if (dictTryFind ctx.LSt.CellVars k).IsSome then LLoad (W, store, cellOff ()) else store

// a fresh 1-word cell holding `v` (headerless — cells are internal, never
// type-tested or dispatched on)
and private lowMkCell (ctx : LowCtx) (v : LExpr) : LExpr =
    let b = freshTmp ctx
    if gc then
        let tid = gcTid ctx.LSt "cell" (HDR + 4) FK_TAGGED 1
        LDo ([ LCallVoidS ("$spush", [ v ]); LSet (wReg b, LCall ("$fpalloc", [ LConstW tid ])); LStore (W, LGet (wReg b), HDR, LCall ("$spop", [])) ], LGet (wReg b))
    else
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
    // the shared pointer, so mutation is visible on both sides. An unboxed
    // scalar has no word storage to grab, so re-box it into the env slot (the
    // lambda body reads it back as an ordinary boxed word).
    :: (caps |> List.map (fun (p, o) ->
            let k = p + ":" + string o
            match dictTryFind ctx.VarScalar k with
            | Some ty -> (match dictTryFind ctx.Regs k with Some id -> flatBox ctx ty (LGet { Id = id; RTy = ty }) | None -> lowVarStore ctx k)
            | None -> lowVarStore ctx k))
    |> lowObj ctx CID_CLOSURE 2

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
    | Some tag -> lowObj ctx (cidCase ctx.LSt "Failure") 1 [ LConstW tag; msg ]
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
                [ LSet (wReg h, lowHeaderCid (wReg t)); LSet (wReg r, matchAny) ],
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
    | PromF -> "f64.promote_f32"
    | DemF -> "f32.demote_f64"
    | Bits2F -> "f32.reinterpret_i32"
    | F2Bits -> "i32.reinterpret_f32"

// the wasm value type a local of this LTy is declared as: I64 is a real i64
// local, F64 an f64; the packed byte widths live inside i32.
let private wtyName (ty : LTy) : string =
    match ty with
    | I64 -> "i64"
    | F64 -> "f64"
    | _ -> "i32"

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
    | LConstF x -> fc f (Fpp.Prelude.doubleBits x)
    | LGet r -> lg f (regNm r)
    | LGetGlobal g ->
        // GC: a top-level global lives in the root table — load its slot
        match (if gc then dictTryFind gcGlobalSlots g else None) with
        | Some slot -> gg f "$roots"; ic f (4 * slot); ins f "i32.add"; mem f "i32.load"
        | None -> gg f g
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
    | LSetGlobal (g, e) ->
        match (if gc then dictTryFind gcGlobalSlots g else None) with
        | Some slot -> gg f "$roots"; ic f (4 * slot); ins f "i32.add"; emitLowE f e; mem f "i32.store"
        | None -> emitLowE f e; gs f g
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
let private emitFuncLow (st : St) (m : Mod) (dbgName : string) (isInit : bool) (sig_ : (LTy list * LTy) option) (ps : VarId list) (body : Expr) (finish : Fn -> unit) : unit =
    let ctx = { LSt = st; Regs = dictNew (); EnvReg = -1; RegTys = vecNew (); VarScalar = dictNew (); NReg = 0 }
    let pnames = ps |> List.map (fun pv -> regNm (wReg (freshReg ctx (key pv))))
    // a specialized scalar ABI: each scalar param arrives UNBOXED in a typed
    // local (registered in VarScalar so reads re-box, just like a scalar let);
    // a scalar return is unboxed off the body's boxed word before the return.
    let retTy =
        match sig_ with
        | Some (paramTys, ret) ->
            List.iter2 (fun pv ty -> match ty with W -> () | _ -> let id = ctx.Regs.[key pv] in vecSet ctx.RegTys id ty; dictSet ctx.VarScalar (key pv) ty) ps paramTys
            ret
        | None -> W
    let sink = vecNew ()
    st.GapSink <- Some sink
    let bodyLow0 = coreToLowE ctx body
    let bodyLow = match retTy with W -> bodyLow0 | _ -> flatUnbox retTy bodyLow0
    st.GapSink <- None
    let f = beginFn m pnames
    if vecLen sink > 0 then
        // a gap in this body: emit an unreachable STUB (mirrors the wasm-GC
        // driver's per-function probe). The gap becomes a warning; the function
        // traps if ever reached. Dead prelude/backend members survive DCE.
        vecAdd st.Warnings ("stubbed " + dbgName + " (" + vecGet sink 0 + ")")
        localsDone f
        // a stubbed INIT (a .NET-only top-level `let`, e.g. an Encoding object)
        // must NOT trap: _start runs every init at startup, so store a harmless
        // 0 instead — the value is only ever touched by already-stubbed .NET
        // methods. A stubbed FUNCTION still traps loudly if it is ever called.
        if isInit then (ic f 0; finish f) else ins f "unreachable"
    else
        let np = List.length ps
        for id in np .. ctx.NReg - 1 do local f (regNm (wReg id)) (wtyName (vecGet ctx.RegTys id))
        localsDone f
        emitLowE f bodyLow
        finish f
    endFn f

// a lifted lambda body: params are (env, arg); captured free variables read
// from the env at 8+4*slot (st.Captures is set by the driver). Register 0 is
// the env, register 1 the argument.
let private emitLambdaLow (st : St) (m : Mod) (lamName : string) (pv : VarId) (body : Expr) : unit =
    let ctx = { LSt = st; Regs = dictNew (); EnvReg = 0; RegTys = vecNew (); VarScalar = dictNew (); NReg = 0 }
    let envId = freshTmp ctx
    let argId = freshReg ctx (key pv)
    let sink = vecNew ()
    st.GapSink <- Some sink
    let bodyLow = coreToLowE ctx body
    st.GapSink <- None
    let f = beginFn m [ regNm (wReg envId); regNm (wReg argId) ]
    if vecLen sink > 0 then
        vecAdd st.Warnings ("stubbed lambda " + lamName + " (" + vecGet sink 0 + ")")
        localsDone f
        ins f "unreachable"
    else
        for id in 2 .. ctx.NReg - 1 do local f (regNm (wReg id)) (wtyName (vecGet ctx.RegTys id))
        localsDone f
        emitLowE f bodyLow
    endFn f

// ---- driver ---------------------------------------------------------------
// Eta-expand a top-level function used as a VALUE (a bare reference, or an
// under-applied call) into explicit nested single-argument lambdas, so the
// ordinary closure machinery lowers it. `f` (arity N) alone becomes
// `fun a1 -> … -> fun aN -> f a1 … aN`; a partial `f x` fills the rest.
// Over-application `f a…(>N)` splits into a saturated call applied to the tail.
// Definitions (DLet heads) are never touched — only EVar/EVarI references.
let mutable private etaCtr = 0
let private etaExpand (funcs : Dict<string, int>) : Expr -> Expr =
    let fresh (sch : Scheme) : VarId * Scheme =
        etaCtr <- etaCtr + 1
        { Path = "(eta)"; Offset = etaCtr; Name = "$e" + string etaCtr }, sch
    let wrap (v : VarId) (sch : Scheme) (pre : Expr list) (need : int) : Expr =
        let ps = List.init need (fun _ -> fresh sch)
        let call = EApp (EVar (v, sch), pre @ (ps |> List.map (fun (p, s) -> EVar (p, s))))
        List.foldBack (fun p body -> ELam ([ p ], body)) ps call
    let rec go (e : Expr) : Expr =
        match e with
        // an APPLIED builtin `compare`: keep the head (do not eta it — that is
        // only for the bare-value use), recurse into the arguments
        | EApp ((EVar (v, _) | EVarI (v, _, _)) as h, args) when v.Path = "(builtin)" && v.Name.StartsWith "compare" ->
            EApp (h, List.map go args)
        | EApp ((EVar (v, sch) | EVarI (v, sch, _)) as h, args) when (dictTryFind funcs (key v)).IsSome ->
            let n = (dictTryFind funcs (key v)).Value
            let args = List.map go args
            let k = List.length args
            if k = n then EApp (h, args)
            elif k < n then wrap v sch args (n - k)
            else EApp (EApp (EVar (v, sch), List.truncate n args), List.skip n args)
        // the builtin `compare` used as a value: eta so the applied handler
        // fires (operand shapes drive it; opaque operands degrade to scalar)
        | EVar (v, sch) | EVarI (v, sch, _) when v.Path = "(builtin)" && v.Name.StartsWith "compare" ->
            let av, asch = fresh sch
            let bv, bsch = fresh sch
            ELam ([ (av, asch) ], ELam ([ (bv, bsch) ], EApp (EVar (v, sch), [ EVar (av, asch); EVar (bv, bsch) ])))
        | EVar (v, sch) | EVarI (v, sch, _) ->
            match dictTryFind funcs (key v) with Some n when n > 0 -> wrap v sch [] n | _ -> e
        // `compare` used as a VALUE (List.sortWith compare, …): eta to
        // `fun a b -> compare a b` so the applied handler fires; the operand
        // types come from the dispatch NAME, so the params' schemes are moot
        | EUnknown n when n.StartsWith "$class:Ordered:compare:" ->
            let av, asch = fresh (mono tInt)
            let bv, bsch = fresh (mono tInt)
            ELam ([ (av, asch) ], ELam ([ (bv, bsch) ], EApp (EUnknown n, [ EVar (av, asch); EVar (bv, bsch) ])))
        | EUnknown _ -> e
        | ELam (ps, b) -> ELam (ps, go b)
        | EApp (h, args) -> EApp (go h, List.map go args)
        | ELet (r, v, s, a, b) -> ELet (r, v, s, go a, go b)
        | EIf (a, b, c) -> EIf (go a, go b, go c)
        | EMatch (s, cs) -> EMatch (go s, cs |> List.map (fun (p, g, b) -> p, Option.map go g, go b))
        | ETry (b, cs) -> ETry (go b, cs |> List.map (fun (p, g, bd) -> p, Option.map go g, go bd))
        | ETuple xs -> ETuple (List.map go xs)
        | EListLit xs -> EListLit (List.map go xs)
        | ECtor (n, s, xs) -> ECtor (n, s, List.map go xs)
        | ERecord (n, fs) -> ERecord (n, fs |> List.map (fun (nm, x) -> nm, go x))
        | ERecordExt (n, b, fs) -> ERecordExt (n, go b, fs |> List.map (fun (nm, x) -> nm, go x))
        | EField (r, n, o) -> EField (go r, n, o)
        | EFieldSet (r, n, o, v) -> EFieldSet (go r, n, o, go v)
        | EPrim (op, xs) -> EPrim (op, List.map go xs)
        | ESeq xs -> ESeq (List.map go xs)
        | EWhile (a, b) -> EWhile (go a, go b)
        | EAssign (v, x) -> EAssign (v, go x)
        | EArray (t, xs) -> EArray (t, List.map go xs)
        | EIndex (t, a, b) -> EIndex (t, go a, go b)
        | EIndexSet (t, a, b, c) -> EIndexSet (t, go a, go b, go c)
        | EArrayLen (t, a) -> EArrayLen (t, go a)
        | EArrayCreate (t, a, b) -> EArrayCreate (t, go a, go b)
        | EArrayPin (t, a) -> EArrayPin (t, go a)
        | EArrayUnpin (t, a) -> EArrayUnpin (t, go a)
        | EArrayBytes (t, a) -> EArrayBytes (t, go a)
        | EIfaceCall (i, m, r, xs) -> EIfaceCall (i, m, go r, List.map go xs)
        | ECast (t, a, d) -> ECast (t, go a, d)
        | ETypeTest (t, a) -> ETypeTest (t, go a)
        | _ -> e
    go

// keys of every top-level binding that is ASSIGNED somewhere: a `let mutable`
// function must be a mutable GLOBAL holding a closure, not a fixed Func — its
// value changes at run time, and it is both read and reassigned as a value.
let private collectAssigned (decls : Decl list) : Dict<string, bool> =
    let s = dictNew<string, bool> ()
    let rec go (e : Expr) : unit =
        match e with
        | EAssign (v, x) -> dictSet s (key v) true; go x
        | ELam (_, b) -> go b
        | EApp (h, xs) -> go h; List.iter go xs
        | ELet (_, _, _, a, b) -> go a; go b
        | EIf (a, b, c) -> go a; go b; go c
        | EMatch (sc, cs) | ETry (sc, cs) -> go sc; for _, g, b in cs do (match g with Some x -> go x | None -> ()); go b
        | ETuple xs | EListLit xs | ESeq xs | EArray (_, xs) | EPrim (_, xs) | ECtor (_, _, xs) -> List.iter go xs
        | ERecord (_, fs) -> for _, x in fs do go x
        | ERecordExt (_, b, fs) -> go b; (for _, x in fs do go x)
        | EField (r, _, _) | EArrayLen (_, r) | EArrayPin (_, r) | EArrayUnpin (_, r) | EArrayBytes (_, r) | ECast (_, r, _) | ETypeTest (_, r) -> go r
        | EFieldSet (r, _, _, v) -> go r; go v
        | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> go a; go b
        | EIndexSet (_, a, b, c) -> go a; go b; go c
        | EIfaceCall (_, _, r, xs) -> go r; List.iter go xs
        | _ -> ()
    for d in decls do match d with DLet (_, _, _, e) -> go e | _ -> ()
    s

// record/type NAMES a single-field collapse must NOT touch: a field-mutated
// record (mutation needs the object's identity), or a type-tested / downcast
// type (the test reads the object's class-id header, which a raw value lacks).
// Class NAMES are excluded separately by the caller (they carry a vtable).
let private scanNoCollapse (decls : Decl list) : Dict<string, bool> =
    let m = dictNew<string, bool> ()
    let rec go (e : Expr) : unit =
        match e with
        | EFieldSet (r, _, owner, v) -> dictSet m owner true; go r; go v
        | ETypeTest (tn, r) -> dictSet m tn true; go r
        | ECast (tn, r, _) -> dictSet m tn true; go r
        | EAssign (_, x) -> go x
        | ELam (_, b) -> go b
        | EApp (h, xs) -> go h; List.iter go xs
        | ELet (_, _, _, a, b) -> go a; go b
        | EIf (a, b, c) -> go a; go b; go c
        | EMatch (sc, cs) | ETry (sc, cs) -> go sc; for _, g, b in cs do (match g with Some x -> go x | None -> ()); go b
        | ETuple xs | EListLit xs | ESeq xs | EArray (_, xs) | EPrim (_, xs) | ECtor (_, _, xs) -> List.iter go xs
        | ERecord (_, fs) -> for _, x in fs do go x
        | ERecordExt (_, b, fs) -> go b; (for _, x in fs do go x)
        | EField (r, _, _) | EArrayLen (_, r) | EArrayPin (_, r) | EArrayUnpin (_, r) | EArrayBytes (_, r) -> go r
        | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> go a; go b
        | EIndexSet (_, a, b, c) -> go a; go b; go c
        | EIfaceCall (_, _, r, xs) -> go r; List.iter go xs
        | _ -> ()
    for d in decls do match d with DLet (_, _, _, e) -> go e | _ -> ()
    m

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
        { M = m; Errors = vecNew (); GapSink = None; Warnings = vecNew ()
          Funcs = dictNew (); FuncSig = dictNew (); Globals = dictNew (); Externs = dictNew (); IfaceArities = dictNew ()
          Consts = dictNew (); ConstNext = CONST_BASE; ConstData = bytesNew ()
          LamName = refMapNew shallowLamHash; Lams = vecNew ()
          Captures = dictNew ()
          RecFields = dictNew (); RecPod = dictNew (); Collapse = dictNew (); UnionTag = dictNew (); UnionArity = dictNew ()
          ClassId = dictNew (); CaseClass = dictNew ()
          SlotOf = dictNew (); NSlots = 0; VtBase = 0; TestIds = dictNew (); UsesExn = false
          CellVars = cellScan decls0
          Tids = dictNew (); TidRegs = vecNew (); TidNext = TID_FIRST
          GcConstData = vecNew (); GlobalSlot = dictNew (); RootNext = 1; TidCid = vecNew (); VtSlot = 0; CmpTblSlot = 0 }
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
    // single-field-collapse (repr(T)): a one-field record travels as its field
    // (no heap object), UNLESS it is mutated, type-tested/cast, or a CLASS (a
    // class has a vtable + its storage is a DRecord, so it also lands in
    // RecFields — but its instance-field reads and dispatch need the object).
    let noCollapse = scanNoCollapse decls0
    let classNames = dictNew<string, bool> ()
    for d in decls0 do match d with DClass (n, _, _, _) -> dictSet classNames n true | _ -> ()
    for kv in dictPairs st.RecFields do
        match snd kv with
        | [ f ] when (dictTryFind noCollapse (fst kv)).IsNone && (dictTryFind classNames (fst kv)).IsNone ->
            dictSet st.Collapse (fst kv) f
        | _ -> ()
    // inline value-type layout: a record with >=2 fields and >=1 scalar field,
    // not a class. Scalars pack raw from HDR (each its storage width); ref/word
    // fields follow (4 bytes each). The word index where refs begin is the
    // FK_TAGGED scan start — the GC scans only the ref suffix, never the raw
    // scalar bytes. Field OFFSETS follow this scalars-first order, transparently
    // (access is by name); the value list at construction stays declared order.
    for d in decls0 do
        match d with
        | DRecord (n, _, fs, _) when List.length fs >= 2 && (dictTryFind classNames n).IsNone ->
            let scalars = fs |> List.filter (fun (_, ty) -> (storLTy ty).IsSome)
            let refs = fs |> List.filter (fun (_, ty) -> (storLTy ty).IsNone)
            if not (List.isEmpty scalars) then
                let m = dictNew<string, int * string> ()
                let mutable off = HDR
                for (fn, ty) in scalars do
                    dictSet m fn (off, ty)
                    off <- off + snd (storLTy ty).Value
                let firstRefWord = off / 4
                for (fn, ty) in refs do
                    dictSet m fn (off, ty)
                    off <- off + 4
                dictSet st.RecPod n (m, off, firstRefWord)
        | _ -> ()
    let nCid = nextCid
    // GC: eagerly intern the fpprt type-id for every type-testable shape and
    // record its tid<->cid pair. Uses the SAME shape key as allocation, so the
    // tid the header carries matches what `:?`/dispatch look up.
    if gc then
        for d in decls0 do
            match d with
            | DRecord (n, _, fs, _) ->
                match dictTryFind st.ClassId n with
                | Some cid ->
                    match dictTryFind st.RecPod n with
                    // inline value type: FK_TAGGED scanning only the ref suffix
                    // (start = first ref word); all-scalar => start = size/4 => scans nothing
                    | Some (_, size, firstRefWord) -> vecAdd st.TidCid (gcTid st ("inl:" + string cid) size FK_TAGGED firstRefWord, cid)
                    | None ->
                        let nf = List.length fs
                        vecAdd st.TidCid (gcTid st ("s:" + string cid + ":" + string nf + ":0") (HDR + 4 * nf) FK_TAGGED 1, cid)
                | None -> ()
            | DUnion (_, _, cs) ->
                for cn, ar in cs do
                    match dictTryFind st.CaseClass cn with
                    | Some cid ->
                        vecAdd st.TidCid (gcTid st ("s:" + string cid + ":" + string (1 + ar) + ":1") (HDR + 4 * (1 + ar)) FK_TAGGED 2, cid)
                    | None -> ()
            | _ -> ()
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
    // classify top-level bindings. A lambda-valued binding that is REASSIGNED
    // is a mutable global holding a closure, not a fixed function. GC: each
    // non-function global takes a root slot (before constants).
    let assigned = collectAssigned decls
    if gc then gcGlobalSlots <- dictNew ()
    for d in decls do
        match d with
        | DLet (_, v, s, ELam (ps, _)) when (dictTryFind assigned (key v)).IsNone ->
            dictSet st.Funcs (key v) (List.length ps)
            match funSigOf s (List.length ps) with Some sig_ -> dictSet st.FuncSig (key v) sig_ | None -> ()
        | DLet (_, v, _, _) ->
            dictSet st.Globals (key v) true
            if gc then
                let slot = st.RootNext
                st.RootNext <- slot + 1
                dictSet st.GlobalSlot (key v) slot
                dictSet gcGlobalSlots (gl v) slot
        | DExtern (v, _) -> dictSet st.Externs v.Name true
        | _ -> ()
    // the host FILE-I/O externs have no WasmLin implementation (DExterns are
    // stripped before the backend, so they arrive as unresolved refs). Answer
    // their calls with a null default so the pipeline RUNS: readTextRaw null ->
    // None, etc. A real fpprt-string host env is the self-host follow-up. The
    // handled host externs (print/box/mem*/js*/…) are NOT listed here.
    for n in [ "readTextRaw"; "existsRaw"; "listDirRaw"; "canonicalizeRaw"; "preludeSourceRaw" ] do
        dictSet st.Externs n true
    // eta-expand every function used as a VALUE into explicit lambdas, BEFORE
    // discover — so the synthesized closures get lifted and lowered like any
    // other and a bare/partial function reference no longer dangles
    etaCtr <- 0
    let decls = decls |> List.map (fun d -> match d with DLet (r, v, s, e) -> DLet (r, v, s, etaExpand st.Funcs e) | _ -> d)
    // function type per arity used, and the function declarations
    let arities = st.Funcs |> dictPairs |> List.map snd |> List.distinct
    for a in arities do
        tyFunc m ("$lfn" + string a) (List.replicate a "i32") [ "i32" ]
    // GC: reserve the string and scratch-byte type-ids up front (eagerly
    // registered) so the hand-emitted string/print helpers can bake the string
    // tid as an immediate and $fpreg_all can allocate the scratch buffer.
    if gc then
        gcStrTid <- gcTid st "str" 2 FK_SCALAR_ARRAY 0
        gcByteTid <- gcTid st "byte" 1 FK_SCALAR_ARRAY 0
        gcIntTid <- gcTid st "int" 4 FK_SCALAR_ARRAY 0
        gcArrTid <- gcTid st "arr" 4 FK_REF_ARRAY 2
        gcFloatTid <- gcTid st "f64" (HDR + 8) FK_STRUCT 0
        gcInt64Tid <- gcTid st "i64" (HDR + 8) FK_STRUCT 0
        gcListTid <- gcTid st "s:2:2:0" (HDR + 8) FK_TAGGED 1
        // a root slot for the vtable array pointer (filled at startup)
        st.VtSlot <- st.RootNext
        st.RootNext <- st.RootNext + 1
        st.CmpTblSlot <- st.RootNext
        st.RootNext <- st.RootNext + 1
        gcCmpTblSlot <- st.CmpTblSlot
    rtDeclsLin m
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) when (dictTryFind st.Funcs (key v)).IsSome ->
            (match dictTryFind st.FuncSig (key v) with
             | Some (paramTys, retTy) ->
                 let tn = "$ft" + fn v
                 tyFunc m tn (paramTys |> List.map wtyName) [ wtyName retTy ]
                 declFn m (fn v) tn
             | None -> declFn m (fn v) ("$lfn" + string (List.length ps)))
        | _ -> ()
    // one init function per top-level global, plus _start
    let inits = vecNew<string> ()
    let mutable initN = 0
    for d in decls do
        match d with
        | DLet (_, v, _, _) when (dictTryFind st.Funcs (key v)).IsSome -> ()
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
        | DLet (_, v, _, ELam (_, body)) when (dictTryFind st.Funcs (key v)).IsSome -> discover st body
        | DLet (_, _, _, e) -> discover st e
        | _ -> ()
    // interface dispatches (found during discover) call a `$lfn<n>` type at
    // arity `1 + argc`; declare any not already covered by a top-level function
    // arity, else `callIndirect` names a type that does not exist (a 0-arg
    // member like an enumerator's `Current` needs `$lfn1` even when nothing else
    // in the program is a 1-arg function).
    for a, _ in dictPairs st.IfaceArities do
        if not (List.contains a arities) then
            tyFunc m ("$lfn" + string a) (List.replicate a "i32") [ "i32" ]
    for name, _, _, _ in vecToList st.Lams do
        declFn m name "$lclo"
        tblIdx m name |> ignore
    // GC: one startup routine that registers every fpprt type-id the program's
    // shapes need. Declared AFTER the lambdas so its body — emitted last, once
    // lazy tid discovery during body lowering is complete — reads a full
    // TidRegs. _start calls it before any allocation.
    if gc then declFn m "$fpreg_all" "$lt_v2v"
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
    // GC: base of the shim's root table, and of the fpprt-allocated scratch
    // buffer (I/O iovec + UTF-8 staging + float formatting); filled at startup
    if gc then globalI32Mut m "$roots" 0
    if gc then globalI32Mut m "$sbuf" 0
    // GC shadow-stack pointer: a byte offset into $roots, above the fixed slots
    if gc then globalI32Mut m "$sp" 0
    // GC: base of the tid->class-id table (fixed static memory in the shim)
    if gc then globalI32Mut m "$t2c" 0
    exportFn m "_start" "$_start"
    // runtime bodies
    if gc then (emitSpush m; emitSpop m)
    emitLalloc m; emitStrOfInt m; emitStrOfChar m; emitStrCat m; emitPrints m; emitFtoa6 m; emitStreq m
    emitStrStarts m; emitStrEnds m; emitStrFind m; emitStrsub m; emitStrTrim m; emitStrReplace m; emitStrFindChar m; emitStrLastFindChar m; emitStrSplitChar m
    emitStrCase m false; emitStrCase m true; emitStrChars m; emitStrPad m; emitStrTrimChars m true; emitStrTrimChars m false; emitStrInsert m; emitStrRemove2 m
    emitStrCmp m; emitCmpv m; emitHashv m; emitLappend m
    // top-level function bodies — all through LowIR (Core/LowIR.fs); an
    // unsupported node reports a gap through coreToLowE, never a bad module
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) when (dictTryFind st.Funcs (key v)).IsSome ->
            if not (isNull (System.Environment.GetEnvironmentVariable "FPP_FUNC_DUMP")) then eprintfn "FUNC %s = %s | %s" (fn v) (key v) v.Name
            emitFuncLow st m (fn v) false (dictTryFind st.FuncSig (key v)) (ps |> List.map fst) body (fun _ -> ())
        | _ -> ()
    // init bodies — DECLARED before _start and the lambdas, so emitted here
    // too (the function and code sections are positional and must agree)
    for d in decls do
        match d with
        | DLet (_, v, _, _) when (dictTryFind st.Funcs (key v)).IsSome -> ()
        | DLet (_, v, _, rhs) ->
            emitFuncLow st m (gl v) true None [] rhs (fun f ->
                // GC: the init's result is on the stack — stash it via the spare
                // $hp global, then store into the global's root slot
                match (if gc then dictTryFind st.GlobalSlot (key v) else None) with
                | Some slot -> gs f "$hp"; gg f "$roots"; ic f (4 * slot); ins f "i32.add"; gg f "$hp"; mem f "i32.store"
                | None -> gs f (gl v))
        | _ -> ()
    // _start: in GC mode bring fpprt up first (reactor ctors, then the heap),
    // then run every init in order
    let f = beginFn m []
    localsDone f
    if gc then
        callf f "$fpinit"                 // fpprt reactor _initialize
        ic f 0; callf f "$fpheap"         // fpprt_init(NULL) -> default heap
        callf f "$fpreg_all"              // register every shape's fpprt type
    for nm in vecToList inits do callf f nm
    endFn f
    // lifted lambda bodies: (environment, argument) -> result — declared LAST.
    // st.Captures maps each captured (path:offset) to its env slot; the LowIR
    // lowering reads them from the env register.
    for name, (pv, _), body, caps in vecToList st.Lams do
        st.Captures <- dictNew ()
        caps |> List.iteri (fun i (p, o) -> dictSet st.Captures (p + ":" + string o) i)
        emitLambdaLow st m name pv body
    // GC: emit $fpreg_all LAST — every shape's tid is known now. Each shape is
    // registered as (tid, size, kind, start, refoffs=0, name=0); `start` is the
    // TAGGED tracer's first-payload word (0 for a no-ref STRUCT box).
    if gc then
        let rf = beginFn m []
        local rf "$t" "i32"
        localsDone rf
        // the root table lives in fpprt's static memory: register the whole
        // range (scratch slot 0 + one per constant) up front — the slots read 0
        // (skipped by the scanner) until filled below
        callf rf "$rootsbase"; gs rf "$roots"
        // register the fixed slots (scratch/globals/constants) AND the shadow
        // stack that follows; the shadow pointer starts just past the fixed slots
        ic rf 65536; callf rf "$rootsreg"
        ic rf (st.RootNext * 4); gs rf "$sp"
        // fill the tid->cid table (raw class-ids, fixed static memory)
        callf rf "$t2cbase"; gs rf "$t2c"
        for tid, cid in vecToList st.TidCid do
            gg rf "$t2c"; ic rf (4 * tid); ins rf "i32.add"; ic rf cid; mem rf "i32.store"
        // register every shape's fpprt type
        for tid, size, kind, start in vecToList st.TidRegs do
            ic rf tid; ic rf size; ic rf kind; ic rf start; ic rf 0; ic rf 0
            callf rf "$fpreg"
        // vtable: a fpprt int array in root slot VtSlot; fill the nonzero rows
        // (fpprt zeroed the array). Its data starts past the [tag][len] header.
        if nCid * st.NSlots > 0 then
            ic rf gcIntTid; ic rf (nCid * st.NSlots); callf rf "$fpallocn"; ls rf "$t"
            gg rf "$roots"; ic rf (4 * st.VtSlot); ins rf "i32.add"; lg rf "$t"; mem rf "i32.store"
            vtRows |> Array.iteri (fun i w ->
                if w <> 0 then (lg rf "$t"; ic rf (8 + 4 * i); ins rf "i32.add"; ic rf w; mem rf "i32.store"))
        // tid -> shape info (kind<<20 | start<<10 | nwords) for the generic $cmpv
        if st.TidNext > 0 then
            ic rf gcIntTid; ic rf st.TidNext; callf rf "$fpallocn"; ls rf "$t"
            gg rf "$roots"; ic rf (4 * st.CmpTblSlot); ins rf "i32.add"; lg rf "$t"; mem rf "i32.store"
            for tid, size, kind, start in vecToList st.TidRegs do
                let info = (kind <<< 20) ||| (start <<< 10) ||| ((size / 4) &&& 0x3FF)
                lg rf "$t"; ic rf (8 + 4 * tid); ins rf "i32.add"; ic rf info; mem rf "i32.store"
        // scratch buffer (iovec + PRINTBUF + FMTBUF) -> root slot 0; $sbuf points
        // past its [tag][len] header so the fixed offsets apply unchanged. Kept
        // in the root table so a moving collection updates it.
        ic rf gcByteTid; ic rf (PRINTBUF + PRINTCAP + FMTCAP + 64); callf rf "$fpallocn"; ls rf "$t"
        gg rf "$roots"; lg rf "$t"; mem rf "i32.store"
        lg rf "$t"; ic rf 8; ins rf "i32.add"; gs rf "$sbuf"
        // each string constant -> a fresh fpprt string in its root slot, units
        // written one at a time (no data segment is ours under GC)
        for slot, ub in vecToList st.GcConstData do
            let nunits = ub.Length / 2
            ic rf gcStrTid; ic rf nunits; callf rf "$fpallocn"; ls rf "$t"
            for j in 0 .. nunits - 1 do
                lg rf "$t"; ic rf (8 + 2 * j); ins rf "i32.add"
                ic rf ((int ub.[2 * j]) ||| ((int ub.[2 * j + 1]) <<< 8)); mem rf "i32.store16"
            gg rf "$roots"; ic rf (4 * slot); ins rf "i32.add"; lg rf "$t"; mem rf "i32.store"
        endFn rf
    // bake the constant data at CONST_BASE (standalone only; GC has no data
    // segment of its own — constants are fpprt objects built at startup)
    if not gc then activeData m CONST_BASE (bytesToArray st.ConstData)
    let pages = (st.ConstNext / 65536) + 64
    let bytes = assembleWith m pages st.UsesExn ""
    if not (isNull (System.Environment.GetEnvironmentVariable "FPP_LINWARN")) then
        for w in vecToList st.Warnings do eprintfn "LINWARN %s" w
    bytes, vecToList st.Errors

// the wasm-linear backend: Core straight to a linear-memory module through the
// shared LowIR. `--lowir` is a retained alias for the same path.
let emitLinear (decls0 : Decl list) : byte[] * string list = emitLinearImpl decls0
let emitLinearLow (decls0 : Decl list) : byte[] * string list = emitLinearImpl decls0

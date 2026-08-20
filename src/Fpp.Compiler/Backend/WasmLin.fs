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
open Fpp.Core.Link
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
// 8 bytes for the monotonic clock's out-parameter — WASI writes an i64 and
// REQUIRES 8-byte alignment, so it sits at 16, not beside the i32 slots
let private MONO_SCRATCH = 16
let private PRINTBUF = 24      // utf-8 staging for one prints
let private PRINTCAP = 262144
let private FMTBUF = PRINTBUF + PRINTCAP   // u16 staging for float formatting
let private FMTCAP = 512
let private CONST_BASE = FMTBUF + FMTCAP

// the GC nature of a value word: a RAW inline scalar (int/bool/char — never a
// pointer, skip in scan), a REF (a heap pointer — trace it), or GENERIC (a type
// parameter — unknown statically). Defined before St so St can hold a cell-kind
// map; the classifier functions that produce it live further down.
type private RefKind = RKRaw | RKRef | RKGen

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
      /// a top-level generic function's quantified type-var ids, in order. It
      /// receives one hidden LEADING witness-pointer param per id; the direct
      /// caller prepends the matching witnesses. Empty/absent = non-generic.
      FuncWitness : Dict<string, int list>
      /// interned value-witness tables: a "size:align:refMask" key -> its BYTE
      /// offset in the static g_witnesses pool. Deduped, emitted at startup.
      Witnesses : Dict<string, int>
      WitnessData : Vec<int * int * int * int>   // (offset, size, align, refMask)
      mutable WitnessCur : int
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
      /// EApp nodes in TAIL position of the function body being emitted —
      /// a full-arity SELF call there compiles to return_call (the wasm
      /// tail-call instruction), so `let rec go n acc = ... go (n-1) ...`
      /// runs at any depth like the GC backend's marked tails
      TailApp : RefMap<Expr, bool>
      /// every lifted lambda, in emission order: (name, param, body, captures)
      Lams : Vec<string * (VarId * Scheme) * Expr * (string * int * Type) list>
      /// while emitting a lifted lambda body: captured key -> its env slot
      mutable Captures : Dict<string, int>
      /// lifted lambda name -> (enclosing type-var id, env slot) list: the
      /// enclosing generic fn's witnesses captured into the closure so the
      /// lambda body's generic aggregates resolve raw-vs-ref (the closure
      /// analogue of a direct fn's witnessVars). Env slot holds a g_witnesses
      /// pointer (immortal), excluded from refoffs.
      LamWits : Dict<string, (int * int) list>
      /// record name -> its field names in DECLARED order (an offset each)
      RecFields : Dict<string, string list>
      /// a stamped subclass (Dictionary$int$int) owns no fields of its own — they
      /// belong to the base it was stamped from (Dictionary). subclass -> base,
      /// so a field access on the subclass resolves its offset THROUGH the base's
      /// RecFields rather than defaulting to index 0.
      /// every DClass name: classes compare and hash by IDENTITY
      /// (DIVERGENCES.md), unlike records' structural fold
      ClassNames : Dict<string, bool>
      RecBase : Dict<string, string>
      /// record/class name -> its fields as (name, declared-type-string), ALL
      /// records (RecFieldTys is [<Struct>]-only). Lets a `$cellget` of a
      /// class-field cell resolve the field's scalar content to RAW.
      RecFieldTypes : Dict<string, (string * string) list>
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
      /// a STRUCT record's declared fields IN ORDER, as (field, type-name).
      /// Only [<Struct>] records are listed — presence marks a value type the
      /// inline-value layout engine (`layoutOf`) lays out .NET-sequentially;
      /// absence means a reference type (one pointer word). Groundwork: written
      /// here, read only by `layoutOf`, which nothing consumes yet.
      RecFieldTys : Dict<string, (string * string) list>
      /// field name -> every record that declares it: the LAST-RESORT owner
      /// resolution for a field access whose receiver type inference lost
      /// (an un-annotated local lambda's param). Only an UNAMBIGUOUS name
      /// resolves this way; anything else is a hard gap — the old silent
      /// index-0 default compiled `sch.Body` as a Quantified read
      FieldOwnerOf : Dict<string, string list>
      /// repr(T) single-field collapse: a record with EXACTLY one field, never
      /// mutated (no EFieldSet), travels AS that field — no heap object. Maps the
      /// record name -> its sole field name. This is the general "any one-field
      /// struct is a newtype" rule; construction/access on such a record become
      /// the identity on the field value.
      Collapse : Dict<string, string>
      /// union case name -> its tag (index) and its payload arity
      UnionTag : Dict<string, int>
      UnionArity : Dict<string, int>
      /// enum case name -> its RAW integer value (an enum IS its int)
      EnumConst : Dict<string, int>
      /// the descriptor word stored at every object's offset 0: a type's
      /// class-id. type name -> class-id, and a union CASE -> its union's id
      ClassId : Dict<string, int>
      CaseClass : Dict<string, int>
      /// a Canon generic class carries a witness pointer per class type param,
      /// stored in trailing (non-scanned) instance slots after its fields and
      /// read back by its methods from `self`. name -> class-param count. A
      /// stamped subclass is concrete (empty Quantified ctor) and is absent.
      WitnessedClasses : Dict<string, int>
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
      /// a cell var's GC nature (the ref-kind of the value it holds), recorded
      /// when the cell is created. A `$cellget` of a raw-scalar cell (a mutable
      /// int) must classify RAW so the aggregate that stores its value keeps the
      /// scalar out of its scan map — without this a mutable int read into a
      /// record field defaulted to the tagged form and was chased as a pointer.
      CellKind : Dict<string, RefKind>
      /// GC mode only: a shape key ("rec:7", "tup:3", "case:9", "clo:2",
      /// "list", "arr", "str", "f64", "i64", "cell") -> its fpprt type-id, and
      /// the registrations to emit at startup as (tid, size-bytes, kind,
      /// first-payload-word-index). tids are numbered from TID_FIRST.
      Tids : Dict<string, int>
      TidRegs : Vec<int * int * int * int>
      /// FK_STRUCT tid -> the byte offsets of its POINTER words (a `layoutOf`-
      /// derived ref-map). Concrete tuples and union payloads register this so
      /// the collector traces only real pointers and skips raw inline scalars.
      TidRefoffs : Dict<int, int list>
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
// the built-in list/array enumerator (`for x in (list :> seq)`): lists carry no
// IEnumerable vtable row, so GetEnumerator/MoveNext/Current on one route to these
// linear iterator helpers instead of a vtable dispatch, mirroring the GC backend.
let private CID_ITER = 7
// a built-in ARRAY enumerator: [array][index]. Distinct from the list iterator
// (CID_ITER) so MoveNext/Current route to the array path (index-based) rather
// than the cons path. GC carries it as its own tid; non-GC uses this cid.
let private CID_ARRITER = 8
let private CID_FIRST_USER = 9

let private CLO_KIND = 2

// GC mode: allocation, the header and roots go through fpprt (the F++ runtime
// over Whippet), linked as an imported reactor module and fused with a
// wasm-merge pass. Off = the standalone bump-allocator path (no collection).
// Set by the CLI (`--gc`) before emission.
let mutable gc = false
// preload linking (wasmtime --preload fpprt=reactor.wasm): the mutator
// re-exports the imported memory as "memory" so WASI finds it on the main
// module. OFF under wasm-merge — the merged file would carry two exports.
let mutable gcExportMem = false
// the user prelude's source text: the compiler reaches it through the
// `preludeSourceRaw` host extern, which every other module stubs to null. Baking
// it as a string constant lets a WasmLin-hosted compiler load its prelude (a real
// end-to-end self-compile) without an external host. Empty for ordinary programs.
let mutable preludeSrc = ""

// JS interop (browser host): set when the program touches a `Js.*` primitive
// or declares a [<JsImport>] extern. Turns on the "jslin" boundary imports,
// the $cbreg/$jscall callback bridge and the lin_salloc string-in allocator.
// The ABI: JsObj = raw handle id (0 = null), int/bool raw i32, float f64,
// string = its linear pointer (len at +4, utf-16 units at +8).
let mutable private jsUsed = false
// [<JsImport>] externs: "path:offset" -> (wasm fn name, import name, param
// kinds, ret kind) with kinds as in the wasm-GC jsx ABI (e=JsObj s=string
// d=float b=bool i=int u=unit). The import NAME carries the kinds
// ("mix#di:d") so the JS glue's Proxy can wrap the user's plain function
// with the per-kind conversions.
let mutable private jsxSigs : Dict<string, string * string * string list * string> = dictNew ()
// plain `extern let` FFI (module "env", the wasm-GC backend's other import
// class): "path:offset" -> (wasm fn name, param kinds, ret kind), raw ABI —
// int/bool raw i32, float f64, string as its linear pointer, JsObj handle.
// The page supplies { env: { name: fn } } with no glue conversions.
let mutable private envSigs : Dict<string, string * string * string list * string> = dictNew ()
// GC mode: base slot of the callback root area (fixed slots the collector
// scans; $cbreg hands them out through the $cbnext global)
let mutable private cbBase = 0

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
let mutable private gcIterTid = 0
let mutable private gcArrIterTid = 0
// FK_STRUCT cons tids selected at a GENERIC cons site by the element witness's
// refMask: RAW head (scan tail only) vs REF head (scan head+tail). Both map to
// CID_LIST so $isBuiltinSeq still recognises them.
let mutable private curFnDbg = "?"
let mutable private chkSite = 0
let mutable private gcConsRawTid = 0
let mutable private gcConsRefTid = 0
let mutable private gcCmpTblSlot = 0
// identity dispatch ($cmpv/$hashv -> a class' own Equals/GetHashCode/CompareTo):
// where the vtable lives and how wide a row is. Slots 0/1/2 of every row are
// reserved for those three; 0 means "not declared, use the structural fold".
let mutable private vtBaseConst = 0
let mutable private vtRootSlot = 0
let mutable private vtNSlots = 0
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
    if System.Environment.GetEnvironmentVariable "FPP_CONSCHECK" = "1" then
        importFn m "fpprt" "fpprt_dbg_live" "$fpdbglive" [ "i32" ] [ "i32" ]
    importFn m "fpprt" "fpprt_alloc_array" "$fpallocn" [ "i32"; "i32" ] [ "i32" ]
    importFn m "fpprt" "fpprt_register_type_s" "$fpreg" [ "i32"; "i32"; "i32"; "i32"; "i32"; "i32" ] []
    importFn m "fpprt" "fpprt_add_static_roots" "$fproots" [ "i32"; "i32" ] []
    importFn m "fpprt" "fpprt_frame_push" "$fppush" [ "i32" ] []
    importFn m "fpprt" "fpprt_frame_pop" "$fppop" [ "i32" ] []
    importFn m "fpprt" "fpprt_write_ref" "$fpwr" [ "i32"; "i32"; "i32" ] []
    importFn m "fpprt" "fpprt_wasm_roots_base" "$rootsbase" [] [ "i32" ]
    importFn m "fpprt" "fpprt_wasm_roots_register" "$rootsreg" [ "i32" ] []
    importFn m "fpprt" "fpprt_tid2cid_base" "$t2cbase" [] [ "i32" ]
    importFn m "fpprt" "fpprt_wasm_refoffs_base" "$refoffsbase" [] [ "i32" ]
    importFn m "fpprt" "fpprt_wasm_witness_base" "$witnessbase" [] [ "i32" ]
    importFn m "fpprt" "fpprt_tid_scans" "$tidscans" [ "i32"; "i32" ] [ "i32" ]
    // deterministic cleanup: watch an object, drain its tag once dead,
    // force a collection (GC.OnCleanup / GC.Collect / Js.watch)
    importFn m "fpprt" "fpprt_watch" "$fpwatch" [ "i32"; "i32"; "i32" ] []
    importFn m "fpprt" "fpprt_idhash" "$fpidh" [ "i32" ] [ "i32" ]
    importFn m "fpprt" "fpprt_drain1" "$fpdrain1" [ "i32" ] [ "i32" ]
    importFn m "fpprt" "fpprt_collect" "$fpcollect" [] []
    // per-object pinning: real under the mmc reactor, aborts under semi —
    // Array.pin's zero-copy contract needs the object to stop moving
    importFn m "fpprt" "fpprt_pin" "$fppin" [ "i32" ] []
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
        if System.Environment.GetEnvironmentVariable "FPP_TIDDUMP" = "1" then
            eprintfn "TID %d = %s (kind %d)" t shapeKey kind
        t

// intern a FK_STRUCT tid with an explicit ref-offset map (byte offsets of the
// object's pointer words). `start` carries nrefs for the $fpreg call; the
// offsets are recorded in TidRefoffs and emitted into the static g_refoffs pool
// at startup. Lets a tuple/union hold raw inline scalars — the collector traces
// ONLY these offsets, so an even int word is never chased as a pointer.
let private gcTidRef (st : St) (shapeKey : string) (sizeBytes : int) (refoffs : int list) : int =
    match dictTryFind st.Tids shapeKey with
    | Some t -> t
    | None ->
        let t = st.TidNext
        st.TidNext <- t + 1
        dictSet st.Tids shapeKey t
        vecAdd st.TidRegs (t, sizeBytes, FK_STRUCT, List.length refoffs)
        dictSet st.TidRefoffs t refoffs
        if System.Environment.GetEnvironmentVariable "FPP_TIDDUMP" = "1" then
            // (fun r -> string r), never bare `string`: a builtin conversion
            // is not a first-class function under self-host
            eprintfn "TID %d = %s (refoffs %s)" t shapeKey (String.concat "," (List.map (fun r -> string r) refoffs))
        t

// intern a packed-scalar array tid AND map it to CID_ARRAY on first creation,
// so a dynamically seq-typed scalar array (`int[]`/`float[]`/… reached via
// `(x.ToArray() :> seq).GetEnumerator()`) is recognised by $isBuiltinSeq and
// routed to the built-in array iterator. Ref arrays share the eagerly-mapped
// gcArrTid; strings (CID_STRING) never come through here.
let private gcArrTidReg (st : St) (shapeKey : string) (sizeBytes : int) (kind : int) : int =
    let isNew = (dictTryFind st.Tids shapeKey).IsNone
    let t = gcTid st shapeKey sizeBytes kind 0
    if isNew then vecAdd st.TidCid (t, CID_ARRAY)
    t

let private rawScalarName (n : string) : bool =
    match n with
    | "int" | "int32" | "uint32" | "nativeint" | "unativeint"
    | "bool" | "char" | "int16" | "uint16" | "byte" | "sbyte" -> true
    // a JsObj is a raw HANDLE id into the JS glue's table (linear memory
    // cannot hold externref) — never a heap pointer, never scanned or rooted
    | "JsObj" -> true
    | _ -> false

// the concrete type-constructor a value expression statically denotes, ""
// when underivable. Bare `print` has no runtime value dispatch on linear (a
// raw int is indistinguishable from a pointer), so the backend picks the
// int / float / string path from this.
let rec private printConOf (st : St) (e : Expr) : string =
    match e with
    | ELit (LInt s) ->
        if s.EndsWith "UL" || s.EndsWith "uL" then "uint64"
        elif s.EndsWith "L" || s.EndsWith "l" then "int64"
        else "int"
    | ELit (LFloat s) when s.EndsWith "h" || s.EndsWith "H" -> "float16"
    | ELit (LFloat _) -> "float"
    | ELit (LBool _) -> "bool"
    | ELit (LChar _) -> "char"
    | ELit (LString _) -> "string"
    | EVar (_, sch) | EVarI (_, sch, _) ->
        (match prune sch.Body with TCon (n, []) -> n | _ -> "")
    // the intrinsics whose result type is FIXED, whatever the operand:
    // `print (hash x)` classified as "" and printed the int as a string
    | EApp (EUnknown ("hash" | "$hash" | "compare" | "sign" | "$idhash"), _) -> "int"
    | EApp (EUnknown n, _) ->
        // a builtin conversion names its RESULT before the '#'
        let i = n.IndexOf "#"
        if i > 0 then n.Substring (0, i)
        // a class-dispatch call carries the operand type as its LAST segment
        // ("$class:Math:truncate:float") — for the 'a -> 'a members that is
        // also the result type; without it `print (truncate 5.9)` classified
        // as "" and printed the boxed float as a (blank) string
        elif n.StartsWith "$class:" then
            (match n.LastIndexOf ':' with
             | j when j > 0 && j < strLen n - 1 -> n.Substring (j + 1)
             | _ -> "")
        else ""
    | EApp _ ->
        let rec flat e acc = match e with EApp (h, a) -> flat h (a @ acc) | _ -> (e, acc)
        let head, args = flat e []
        (match head with
         // a BUILTIN head whose scheme is just the "?" marker: classify the
         // type-preserving members by their OPERANDS (truncate/sqrt/abs and
         // the operator zoo return their operand type; compare/sign/hash
         // return int) — else `print (truncate 5.9)` printed a blank line
         | (EVar (v, hsch) | EVarI (v, hsch, _)) when
               v.Path = "(builtin)" && (match hsch.Body with TCon ("?", []) -> true | _ -> false) ->
             (match v.Name with
              | "truncate" | "sqrt" | "abs" | "max" | "min"
              | "exp" | "log" | "log2" | "log10" | "pow" | "pown"
              | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "atan2"
              | "sinh" | "cosh" | "tanh" | "asinh" | "acosh" | "atanh"
              | "floor" | "ceil" | "ceiling" | "round"
              | "(%)" | "(+)" | "(-)" | "(*)" | "(/)" | "(~-)" | "(**)" ->
                  (match args |> List.map (printConOf st) |> List.filter (fun c -> c <> "" && c <> "?") with
                   | c :: _ -> c
                   | [] -> "")
              | "compare" | "sign" | "hash" -> "int"
              | _ -> "")
         | (EVar (_, sch) | EVarI (_, sch, _)) as hd ->
             let rec peel t k = if k <= 0 then t else (match prune t with TFun (_, r) -> peel r (k - 1) | _ -> t)
             (match prune (peel sch.Body (List.length args)) with
              | TCon (n, []) -> n
              // a generic result ('a -> 'a members like truncate/sqrt):
              // resolve the var through the call's instantiation names; an
              // unresolved "?" falls back to the ARGUMENT declared at the
              // same var — `print (truncate 5.9)` classified as "" otherwise
              // and printed the boxed float as a (blank) string
              | TVar rv ->
                  let viaInst =
                      (match hd with
                       | EVarI (_, _, inst) ->
                           (match List.tryFindIndex (fun (qv : Var) -> qv.Id = rv.Id) sch.Quantified with
                            | Some k -> (match List.tryItem k inst with Some nm -> nm | None -> "")
                            | None -> "")
                       | _ -> "")
                  if viaInst <> "" && viaInst <> "?" && not (viaInst.StartsWith "'") && not (viaInst.StartsWith "#") then viaInst
                  else
                      let rec pars t k acc =
                          match prune t with
                          | TFun (a, r) -> pars r (k + 1) ((k, a) :: acc)
                          | _ -> acc
                      (match pars sch.Body 0 []
                             |> List.tryPick (fun (k, pt) ->
                                 match prune pt with
                                 | TVar pv when pv.Id = rv.Id -> List.tryItem k args
                                 | _ -> None) with
                       | Some argE -> printConOf st argE
                       | None -> "")
              | _ -> "")
         | ELam (ps, body) when List.length args >= List.length ps -> printConOf st body
         | _ -> "")
    | EField (_, fname, owner) ->
        (match dictTryFind st.RecFieldTypes owner with
         | Some fs -> (match fs |> List.tryPick (fun (n, t) -> if n = fname then Some t else None) with Some t -> t | None -> "")
         | None -> "")
    | ECast (tn, _, _) -> tn
    | EPrim (op, _) ->
        // arithmetic carries its operand type as the op suffix (+f, -l, …)
        let n = strLen op
        let sfx = if n > 1 then op.Substring (n - 1) else ""
        let b = if sfx = "f" || sfx = "s" || sfx = "l" || sfx = "w" then op.Substring (0, n - 1) else op
        (match b with
         | "<" | ">" | "<=" | ">=" | "=" | "<>" | "&&" | "||" | "not"
         | "=i" | "<>i" | "=t" | "<>t" | "<t" | ">t" | "<=t" | ">=t" -> "bool"
         | _ when op.Contains "@" &&
                  (match op.Substring (0, op.IndexOf "@") with
                   | "<" | ">" | "<=" | ">=" | "=" | "<>" -> true | _ -> false) -> "bool"
         | "+" | "-" | "*" | "/" | "%" | "u-" | "sqrt" | "truncate" | "abs"
         | "&&&" | "|||" | "^^^" | "<<<" | ">>>" | "u~~~" when b <> op ->
             (if sfx = "l" then "int64" elif sfx = "s" then "float32" elif sfx = "w" then "uint32" else "float")
         | "+" | "-" | "*" | "/" | "%" | "&&&" | "|||" | "^^^" | "<<<" | ">>>" | "u-" | "u~~~" | "abs" -> "int"
         | _ -> "")
    | EIf (_, a, b) -> (let x = printConOf st a in if x <> "" then x else printConOf st b)
    | ELet (_, _, _, _, b) -> printConOf st b
    | ESeq xs -> (match List.tryLast xs with Some b -> printConOf st b | None -> "")
    | EMatch (_, cs) ->
        (match cs |> List.map (fun (_, _, b) -> printConOf st b) |> List.filter (fun s -> s <> "") with
         | x :: _ -> x
         | [] -> "")
    | _ -> ""

let rec private refKindOfTy (t : Type) : RefKind =
    match prune t with
    | TVar _ -> RKGen
    | TCon (n, _) -> if rawScalarName n then RKRaw else RKRef
    | TFun _ | TTuple _ -> RKRef
    | TApp (h, _) -> (match prune h with TVar _ -> RKGen | _ -> RKRef)

// the ref-kind of an EXPRESSION's value, from its static type. Conservative:
// anything it cannot pin down is RKGen (→ the container falls back to the safe
// tagged form). It NEVER answers RKRaw unless sure — a ref mis-classified raw
// would drop a live pointer from the scan.
let rec private refKindOfExpr (e : Expr) : RefKind =
    match e with
    | ELit (LInt s) -> if s.EndsWith "L" || s.EndsWith "l" then RKRef else RKRaw
    | ELit (LBool _) | ELit (LChar _) -> RKRaw
    | ELit (LFloat s) when s.EndsWith "h" || s.EndsWith "H" -> RKRaw
    | ELit (LFloat _) | ELit (LString _) -> RKRef
    | ELit (LNull) -> RKRef
    | EVar (_, sch) | EVarI (_, sch, _) -> refKindOfTy sch.Body
    | EApp (_, _) ->
        // flatten the whole application spine so a CURRIED call
        // (`EApp(EApp(f,a1),a2)`) and a beta-redex (`EApp(ELam…,args)`, e.g. an
        // eta-expansion) resolve their result kind, not just a direct EVar head.
        let rec flat e acc = match e with EApp (h, a) -> flat h (a @ acc) | _ -> (e, acc)
        let head, args = flat e []
        (match head with
         | (EVar (_, sch) | EVarI (_, sch, _)) as hd ->
             let rec peel t n = if n <= 0 then t else (match prune t with TFun (_, r) -> peel r (n - 1) | _ -> t)
             (match prune (peel sch.Body (List.length args)) with
              | TVar rv ->
                  // a call whose result rides a quantified type var: resolve it through
                  // the call's instantiation NAMES (EVarI.inst, positional to Quantified)
                  // so a concrete raw result (an `int`-returning generic) is RKRaw.
                  (match hd with
                   | EVarI (_, _, inst) ->
                       (match List.tryFindIndex (fun (qv : Var) -> qv.Id = rv.Id) sch.Quantified with
                        | Some k -> (match List.tryItem k inst with Some nm -> (if rawScalarName nm then RKRaw else RKRef) | None -> RKGen)
                        | None -> RKGen)
                   | _ -> RKGen)
              | rt -> refKindOfTy rt)
         // a fully-applied beta-redex resolves to its body's kind
         | ELam (ps, body) when List.length args >= List.length ps -> refKindOfExpr body
         | _ -> RKGen)
    | ETuple _ | EListLit _ | EArray _ | EArrayCreate _ | ERecord _ | ERecordExt _ | ECtor _ | ELam _ -> RKRef
    // an array length / type test is always a raw scalar (int / bool), never a
    // pointer — a generic aggregate storing one must exclude it from its scan
    | EArrayLen _ | ETypeTest _ | EArrayPin _ | EArrayUnpin _ | EArrayBytes _ -> RKRaw
    | EPrim (op, _) ->
        let b = if op.Length > 1 && (op.EndsWith "f" || op.EndsWith "s" || op.EndsWith "l") then op.Substring (0, op.Length - 1) else op
        (match b with
         // int arithmetic / comparisons / bool ops -> a raw scalar result;
         // the `w` (uint32) forms are raw i32 words too
         | "+w" | "-w" | "*w" | "/w" | "%w" | "<<<w" | ">>>w" -> RKRaw
         | "+" | "-" | "*" | "/" | "%" when op = b -> RKRaw
         | "<" | ">" | "<=" | ">=" | "=" | "<>" -> RKRaw
         | "&&" | "||" | "not" | "&&&" | "|||" | "^^^" | "<<<" | ">>>" when op = b -> RKRaw
         // a float/int64-suffixed op yields a boxed scalar (pointer)
         | _ when op <> b -> RKRef
         | _ -> RKGen)
    | EIndex (k, _, _) ->
        // `arr.[i]` rides the array's ELEMENT kind, carried as the node's kind
        // string `k`. A concrete raw scalar (int/char/bool/…) is an even RAW word,
        // so the cons head must be RKRaw — excluded from refoffs, never chased as a
        // pointer. Without this the element was RKGen with no witness and rebuilt
        // under the tag-scanning gcListTid, which traced a raw int as a ref.
        if rawScalarName k then RKRaw else RKRef
    | EIf (_, a, b) -> (match refKindOfExpr a, refKindOfExpr b with x, y when x = y -> x | RKGen, y -> y | x, RKGen -> x | _ -> RKGen)
    | ELet (_, _, _, _, body) -> refKindOfExpr body
    | ESeq xs -> (match List.tryLast xs with Some b -> refKindOfExpr b | None -> RKGen)
    | EMatch (_, cs) | ETry (_, cs) ->
        (match cs |> List.map (fun (_, _, b) -> refKindOfExpr b) |> List.filter (fun k -> k <> RKGen) with
         | [] -> RKGen
         | x :: rest -> if List.forall (fun k -> k = x) rest then x else RKGen)
    | _ -> RKGen

// the type-var id of an expression whose value's type IS a type parameter (a
// generic aggregate element). Matches the RKGen cases of refKindOfExpr; used to
// find the witness param that describes the element for the GC scan map.
let rec private tyVarIdOfExpr (e : Expr) : int option =
    let ofTy t = match prune t with TVar v -> Some v.Id | _ -> None
    // the ELEMENT type-var of a generic array `'a[]` expression, for `arr.[i]`
    // whose result rides the element's type var — the witness the collector needs.
    let arrElemVar (arr : Expr) : int option =
        let elemOf ty =
            match prune ty with
            | TCon ("array", (el :: _)) -> ofTy el
            | TApp (h, (el :: _)) -> (match prune h with TCon ("array", _) -> ofTy el | _ -> None)
            | _ -> None
        match arr with EVar (_, sch) | EVarI (_, sch, _) -> elemOf sch.Body | _ -> None
    match e with
    | EVar (_, sch) | EVarI (_, sch, _) -> ofTy sch.Body
    | EApp ((EVar (_, sch) | EVarI (_, sch, _)), args) ->
        let rec peel t n = if n <= 0 then t else (match prune t with TFun (_, r) -> peel r (n - 1) | _ -> t)
        ofTy (peel sch.Body (List.length args))
    | EIndex (_, arr, _) -> arrElemVar arr
    | EIf (_, a, b) -> (match tyVarIdOfExpr a with Some x -> Some x | None -> tyVarIdOfExpr b)
    | ELet (_, _, _, _, body) -> tyVarIdOfExpr body
    | ESeq xs -> (match List.tryLast xs with Some b -> tyVarIdOfExpr b | None -> None)
    | EMatch (_, cs) | ETry (_, cs) -> cs |> List.tryPick (fun (_, _, b) -> tyVarIdOfExpr b)
    | _ -> None

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

// intern a RAW string value (already-decoded text, NOT a quoted source literal):
// each char is one UTF-16 unit verbatim. `unescape` is for LITERALS — it strips
// surrounding quotes and processes `\` escapes and UTF-8, which mangles the baked
// PRELUDE source (its own `\n`/`\\` and first/last chars), flattening the parse.
let private internStrRawGc (st : St) (s : string) : int =
    let key = "raw:" + s
    match dictTryFind st.Consts key with
    | Some slot -> slot
    | None ->
        let slot = st.RootNext
        st.RootNext <- slot + 1
        let out = vecNew<byte> ()
        let mutable k = 0
        while k < strLen s do
            let u = int (charAt s k)
            vecAdd out (byte (u % 256))
            vecAdd out (byte ((u / 256) % 256))
            k <- k + 1
        vecAdd st.GcConstData (slot, vecToArray out)
        dictSet st.Consts key slot
        slot

// a string constant as a value: standalone bakes it at a fixed address; GC
// loads its (possibly relocated) pointer from the root table
let private lowStrConst (st : St) (s : string) : LExpr =
    if gc then LLoad (W, LGetGlobal "$roots", 4 * internStrGc st s)
    else LConstW (internStr st s)

// a RAW (un-unescaped) string constant — for the baked prelude source text.
let private lowStrConstRaw (st : St) (s : string) : LExpr =
    if gc then LLoad (W, LGetGlobal "$roots", 4 * internStrRawGc st s)
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
    // $atol: string pointer -> raw i64
    tyFunc m "$lt_i2j" [ "i32" ] [ "i64" ]
    // $atof: string pointer -> raw f64
    tyFunc m "$lt_i2d" [ "i32" ] [ "f64" ]
    // WASI path_open: (dirfd, dirflags, path, len, oflags, rights, rights_inh, fdflags, retptr)
    tyFunc m "$lt_po" [ "i32"; "i32"; "i32"; "i32"; "i32"; "i64"; "i64"; "i32"; "i32" ] [ "i32" ]
    // $memcopy: (dst, src, n) -> ()
    tyFunc m "$lt_iii2v" [ "i32"; "i32"; "i32" ] []
    // half-precision: $h2f (bits -> f32), $f2h (f32 -> bits), $f2h64 (f64 -> bits)
    rtTypes12 m
    rtTypesHalf m


let private rtDeclsLin (m : Mod) : unit =
    importFn m "wasi_snapshot_preview1" "fd_write" "$fd_write" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    // host FILE READS (readTextRaw/existsRaw): WASI against the preopened
    // dir (fd 3) — what lets the SELF-HOSTED compiler load real sources
    importFn m "wasi_snapshot_preview1" "path_open" "$path_open" [ "i32"; "i32"; "i32"; "i32"; "i32"; "i64"; "i64"; "i32"; "i32" ] [ "i32" ]
    importFn m "wasi_snapshot_preview1" "fd_read" "$fd_read" [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    importFn m "wasi_snapshot_preview1" "fd_close" "$fd_close" [ "i32" ] [ "i32" ]
    importFn m "wasi_snapshot_preview1" "fd_filestat_get" "$fd_filestat_get" [ "i32"; "i32" ] [ "i32" ]
    // the monotonic clock (Time.now): id, precision, out-pointer -> errno
    importFn m "wasi_snapshot_preview1" "clock_time_get" "$clock_time_get" [ "i32"; "i64"; "i32" ] [ "i32" ]
    // the JS boundary (browser host): one import per Js.* primitive, module
    // "jslin". Handles/ints/bools cross raw, floats f64, strings as linear
    // pointers. Registered ONLY when the program touches Js.* — an unused
    // import set would break plain wasmtime programs at instantiation.
    if jsUsed then
        importFn m "jslin" "global" "$jsi_global" [ "i32" ] [ "i32" ]
        importFn m "jslin" "get" "$jsi_get" [ "i32"; "i32" ] [ "i32" ]
        importFn m "jslin" "set" "$jsi_set" [ "i32"; "i32"; "i32" ] []
        importFn m "jslin" "getNum" "$jsi_getNum" [ "i32"; "i32" ] [ "f64" ]
        importFn m "jslin" "setNum" "$jsi_setNum" [ "i32"; "i32"; "f64" ] []
        importFn m "jslin" "item" "$jsi_item" [ "i32"; "i32" ] [ "i32" ]
        importFn m "jslin" "itemSet" "$jsi_itemSet" [ "i32"; "i32"; "i32" ] []
        for a in 0 .. 12 do
            importFn m "jslin" ("call" + string a) ("$jsi_call" + string a) (List.replicate (2 + a) "i32") [ "i32" ]
        for a in 0 .. 2 do
            importFn m "jslin" ("new" + string a) ("$jsi_new" + string a) (List.replicate (1 + a) "i32") [ "i32" ]
        importFn m "jslin" "num" "$jsi_num" [ "f64" ] [ "i32" ]
        importFn m "jslin" "toNum" "$jsi_toNum" [ "i32" ] [ "f64" ]
        importFn m "jslin" "bool" "$jsi_bool" [ "i32" ] [ "i32" ]
        importFn m "jslin" "toBool" "$jsi_toBool" [ "i32" ] [ "i32" ]
        importFn m "jslin" "str" "$jsi_str" [ "i32" ] [ "i32" ]
        importFn m "jslin" "toStr" "$jsi_tostr" [ "i32" ] [ "i32" ]
        importFn m "jslin" "mkFn" "$jsi_mkFn" [ "i32" ] [ "i32" ]
        importFn m "jslin" "undef" "$jsi_undef" [] [ "i32" ]
        importFn m "jslin" "obj" "$jsi_obj" [] [ "i32" ]
        importFn m "jslin" "arr" "$jsi_arr" [] [ "i32" ]
        importFn m "jslin" "push" "$jsi_push" [ "i32"; "i32" ] []
        for sfx in [ "U8"; "U16"; "I32"; "F32"; "F64" ] do
            importFn m "jslin" ("view" + sfx) ("$jsi_view" + sfx) [ "i32"; "i32" ] [ "i32" ]
        // [<JsImport>] typed externs: module "jsxl", the kind signature
        // mangled into the import name so the glue's Proxy can wrap the
        // user's plain function with the per-kind conversions
        for _, (fnm, nm, pks, rk) in dictPairs jsxSigs do
            let vt k = if k = "d" then "f64" else "i32"
            importFn m "jsxl" nm fnm
                (pks |> List.filter (fun k -> k <> "u") |> List.map vt)
                (if rk = "u" then [] else [ vt rk ])
    // plain user externs: module "env", raw ABI, registered whenever declared
    // (an unreferenced extern is DCE-safe: nothing calls it, but the import
    // only exists when the program declared it, so wasmtime programs without
    // externs stay import-free)
    for _, (fnm, nm, pks, rk) in dictPairs envSigs do
        let vt k = if k = "d" then "f64" else "i32"
        importFn m "env" nm fnm
            (pks |> List.filter (fun k -> k <> "u") |> List.map vt)
            (if rk = "u" then [] else [ vt rk ])
    // GC mode imports fpprt's memory + API (all imports must precede declared
    // functions in the index space); the standalone path defines+exports its own
    if gc then importFpprt m else exportMem m "memory"
    if gc && gcExportMem then exportMem m "memory"
    // GC shadow-stack push/pop for in-flight roots (declared before the string
    // helpers so declaration order matches body-emission order)
    if gc then (declFn m "$spush" "$lt_i2v"; declFn m "$spop" "$lt_v2i")
    declFn m "$lalloc" "$lt_i2i"
    declFn m "$str_of_int" "$lt_i2i"
    declFn m "$str_of_char" "$lt_i2i"
    declFn m "$str_cat" "$lt_ii2i"
    declFn m "$prints" "$lt_i2v"
    declFn m "$eprints" "$lt_i2v"
    declFn m "$printraw" "$lt_i2v"
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
    declFn m "$isBuiltinSeq" "$lt_i2i"
    declFn m "$literNew" "$lt_i2i"
    declFn m "$literNext" "$lt_i2i"
    declFn m "$literCur" "$lt_i2i"
    declFn m "$atoi" "$lt_i2i"
    declFn m "$atol" "$lt_i2j"
    declFn m "$readfile" "$lt_i2i"
    declFn m "$fexists" "$lt_i2i"
    // raw linear-memory access (the Mem module): size probe and block copy
    declFn m "$memsize" "$lt_v2i"
    declFn m "$memcopy" "$lt_iii2v"
    // shortest-form float formatting (print <float>, string <float>)
    declFn m "$ftoa_s" "$lt_i2i"
    // int64/uint64 decimal formatting (print <int64>, string <int64>)
    declFn m "$ltoa_s" "$lt_i2i"
    declFn m "$ultoa_s" "$lt_i2i"
    // callback/cleanup-closure registration: needed by JS callbacks AND by
    // GC.OnCleanup (gc mode parks cleanup closures in the same slot area)
    if jsUsed || gc then declFn m "$cbreg" "$lt_i2i"
    // gc: drain the dead cleanup queue, invoking each parked closure
    if gc then (declFn m "$gcdrain" "$lt_v2v"; declFn m "$rootswipe" "$lt_v2v")
    // JS interop helpers: the JS->wasm call bridge and the string-shell
    // allocator the glue fills (utf-16 units at +8)
    if jsUsed then
        declFn m "$jscall" "$lt_ii2i"
        declFn m "$lin_salloc" "$lt_i2i"
    // half-precision widen/narrow, declared LAST — rtCore12/rtCoreHalf emit
    // their bodies last too (the function and code sections are positional)
    rtDecls12 m
    rtDeclsHalf m
    declFn m "$atof" "$lt_i2d"
    declFn m "$novt" "$lt_ii2i"
    declFn m "$clseq" "$lt_ii2i"
    declFn m "$clshash" "$lt_ii2i"
    declFn m "$showv" "$lt_i2i"
    declFn m "$strv" "$lt_i2i"

// $atoi(s): signed decimal string -> raw i32, over the linear string layout
// (len at +4, UTF-16 units at +8). Mirrors the wasm-GC oracle's $atoi: an
// optional leading '-', then digits; no error path (the compiler parses only
// numerals it printed itself — "@env:N" slot suffixes, offsets).

// $atof: string -> f64, mantissa/fraction/exponent stages. Ported from the
// GC backend verbatim except the two string reads: a linear string is
// [cid][len][utf-16 units], so length is a load at +4 and unit i a
// load16_u at +8 + 2i.
let private emitAtof (m : Mod) : unit =
    // $atof: mantissa/fraction/exponent stages
    let f = beginFn m [ "$s" ]
    local f "$i" "i32"
    local f "$n" "i32"
    local f "$neg" "i32"
    local f "$v" "f64"
    local f "$scale" "f64"
    local f "$stage" "i32"
    local f "$exp" "i32"
    local f "$esign" "i32"
    local f "$c" "i32"
    local f "$k" "i32"
    localsDone f
    lg f "$s"
    ic f 4; ins f "i32.add"; mem f "i32.load"
    ls f "$n"
    fc f FTENTH
    ls f "$scale"
    ic f 1
    ls f "$esign"
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    lg f "$n"
    ins f "i32.ge_u"
    brIf f "$done"
    lg f "$s"
    lg f "$i"
    ic f 1; ins f "i32.shl"; ins f "i32.add"; ic f 8; ins f "i32.add"; mem f "i32.load16_u"
    ls f "$c"
    lg f "$c"
    ic f 45
    ins f "i32.eq"
    lg f "$i"
    ins f "i32.eqz"
    ins f "i32.and"
    ifE f
    ic f 1
    ls f "$neg"
    endB f
    lg f "$c"
    ic f 46
    ins f "i32.eq"
    ifE f
    ic f 1
    ls f "$stage"
    endB f
    lg f "$c"
    ic f 101
    ins f "i32.eq"
    lg f "$c"
    ic f 69
    ins f "i32.eq"
    ins f "i32.or"
    ifE f
    ic f 2
    ls f "$stage"
    endB f
    lg f "$c"
    ic f 45
    ins f "i32.eq"
    lg f "$stage"
    ic f 2
    ins f "i32.eq"
    ins f "i32.and"
    ifE f
    ic f -1
    ls f "$esign"
    endB f
    lg f "$c"
    ic f 48
    ins f "i32.ge_u"
    lg f "$c"
    ic f 57
    ins f "i32.le_u"
    ins f "i32.and"
    ifE f
    lg f "$stage"
    ins f "i32.eqz"
    ifE f
    lg f "$v"
    fc f F10
    ins f "f64.mul"
    lg f "$c"
    ic f 48
    ins f "i32.sub"
    ins f "f64.convert_i32_u"
    ins f "f64.add"
    ls f "$v"
    endB f
    lg f "$stage"
    ic f 1
    ins f "i32.eq"
    ifE f
    lg f "$v"
    lg f "$c"
    ic f 48
    ins f "i32.sub"
    ins f "f64.convert_i32_u"
    lg f "$scale"
    ins f "f64.mul"
    ins f "f64.add"
    ls f "$v"
    lg f "$scale"
    fc f FTENTH
    ins f "f64.mul"
    ls f "$scale"
    endB f
    lg f "$stage"
    ic f 2
    ins f "i32.eq"
    ifE f
    lg f "$exp"
    ic f 10
    ins f "i32.mul"
    lg f "$c"
    ic f 48
    ins f "i32.sub"
    ins f "i32.add"
    ls f "$exp"
    endB f
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
    endB f
    blockE f "$edone"
    loopE f "$ego"
    lg f "$k"
    lg f "$exp"
    ins f "i32.ge_s"
    brIf f "$edone"
    lg f "$esign"
    ic f 0
    ins f "i32.gt_s"
    ifE f
    lg f "$v"
    fc f F10
    ins f "f64.mul"
    ls f "$v"
    elseB f
    lg f "$v"
    fc f F10
    ins f "f64.div"
    ls f "$v"
    endB f
    lg f "$k"
    ic f 1
    ins f "i32.add"
    ls f "$k"
    br f "$ego"
    endB f
    endB f
    lg f "$neg"
    ifV f "f64"
    lg f "$v"
    ins f "f64.neg"
    elseB f
    lg f "$v"
    endB f
    endFn f

let private emitAtoi (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$n" "i32"; local f "$i" "i32"; local f "$acc" "i32"; local f "$neg" "i32"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$n"
    ic f 0; ls f "$i"; ic f 0; ls f "$acc"; ic f 0; ls f "$neg"
    lg f "$n"; ic f 0; ins f "i32.gt_s"
    ifE f
    lg f "$s"; ic f 8; ins f "i32.add"; mem f "i32.load16_u"; ic f 45; ins f "i32.eq"
    ifE f; ic f 1; ls f "$neg"; ic f 1; ls f "$i"; endB f
    endB f
    blockE f "$ad"; loopE f "$ago"
    lg f "$i"; lg f "$n"; ins f "i32.ge_s"; brIf f "$ad"
    lg f "$acc"; ic f 10; ins f "i32.mul"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    ic f 48; ins f "i32.sub"; ins f "i32.add"; ls f "$acc"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$ago"; endB f; endB f
    lg f "$neg"
    ifE f; ic f 0; lg f "$acc"; ins f "i32.sub"; ls f "$acc"; endB f
    lg f "$acc"
    endFn f

// $atol(s): $atoi's i64 twin — signed decimal string -> raw i64, so
// `int64 "123"` parses instead of handing the string POINTER out widened
let private emitAtol (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$n" "i32"; local f "$i" "i32"; local f "$neg" "i32"; local f "$acc" "i64"
    localsDone f
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$n"
    ic f 0; ls f "$i"; lc f 0L; ls f "$acc"; ic f 0; ls f "$neg"
    lg f "$n"; ic f 0; ins f "i32.gt_s"
    ifE f
    lg f "$s"; ic f 8; ins f "i32.add"; mem f "i32.load16_u"; ic f 45; ins f "i32.eq"
    ifE f; ic f 1; ls f "$neg"; ic f 1; ls f "$i"; endB f
    endB f
    blockE f "$ald"; loopE f "$algo"
    lg f "$i"; lg f "$n"; ins f "i32.ge_s"; brIf f "$ald"
    lg f "$acc"; lc f 10L; ins f "i64.mul"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    ic f 48; ins f "i32.sub"; ins f "i64.extend_i32_s"; ins f "i64.add"; ls f "$acc"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$algo"; endB f; endB f
    lg f "$neg"
    ifE f; lc f 0L; lg f "$acc"; ins f "i64.sub"; ls f "$acc"; endB f
    lg f "$acc"
    endFn f

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

// ---- WASI file reading (readTextRaw/existsRaw) ----------------------------
// Scratch layout inside FMTBUF's 512 bytes (never live while formatting):
// path UTF-8 at +0..199, the opened fd at +200, the filestat at +208 (64 B,
// 8-aligned since FMTBUF is). The iovec staging reuses fd_write's slots.

/// stage the path string `$s` as UTF-8 at FMTBUF (ASCII paths — a unit is a
/// byte), leaving its length in `$n`
let private stagePath (f : Fn) : unit =
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$n"
    ic f 0; ls f "$i"
    blockE f "$spd"; loopE f "$spg"
    lg f "$i"; lg f "$n"; ins f "i32.ge_s"; brIf f "$spd"
    saddr f FMTBUF; lg f "$i"; ins f "i32.add"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store8"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$spg"; endB f; endB f

/// path_open on the preopened dir (fd 3), rights = fd_read|fd_filestat_get;
/// leaves the WASI errno on the stack, the fd at scratch FMTBUF+200
let private emitPathOpen (f : Fn) : unit =
    ic f 3; ic f 0
    saddr f FMTBUF; lg f "$n"
    ic f 0; lc f 0x200002L; lc f 0L; ic f 0
    saddr f (FMTBUF + 200)
    callf f "$path_open"

// $readfile(s): read the file named by string s (relative to the preopened
// dir) into a fresh Latin-1 string — one byte, one unit. 0 on any failure
// (readTextRaw null -> None upstream). The bytes are read INTO the string's
// own data area and widened in place back-to-front, so there is exactly one
// allocation and nothing to root across it.
let private emitReadFile (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$n" "i32"; local f "$i" "i32"; local f "$fd" "i32"; local f "$sz" "i32"
    local f "$p" "i32"; local f "$got" "i32"; local f "$tot" "i32"
    localsDone f
    lg f "$s"; ins f "i32.eqz"; ifE f; ic f 0; ins f "return"; endB f
    stagePath f
    emitPathOpen f
    ifE f; ic f 0; ins f "return"; endB f
    saddr f (FMTBUF + 200); mem f "i32.load"; ls f "$fd"
    lg f "$fd"; saddr f (FMTBUF + 208); callf f "$fd_filestat_get"
    ifE f; lg f "$fd"; callf f "$fd_close"; ins f "drop"; ic f 0; ins f "return"; endB f
    saddr f (FMTBUF + 208); ic f 32; ins f "i32.add"; mem f "i64.load"; ins f "i32.wrap_i64"; ls f "$sz"
    // a fresh string of $sz units; the alloc may move the scratch buffer
    strAllocN f (fun () -> lg f "$sz")
    emitSbufRefresh f
    // read $sz bytes into the string's data area, in as many reads as WASI takes
    ic f 0; ls f "$tot"
    blockE f "$rfd"; loopE f "$rfg"
    lg f "$tot"; lg f "$sz"; ins f "i32.ge_s"; brIf f "$rfd"
    saddr f IOV_PTR; lg f "$p"; ic f 8; ins f "i32.add"; lg f "$tot"; ins f "i32.add"; mem f "i32.store"
    saddr f IOV_LEN; lg f "$sz"; lg f "$tot"; ins f "i32.sub"; mem f "i32.store"
    lg f "$fd"; saddr f IOV_PTR; ic f 1; saddr f NWRITTEN; callf f "$fd_read"
    brIf f "$rfd"
    saddr f NWRITTEN; mem f "i32.load"; ls f "$got"
    lg f "$got"; ins f "i32.eqz"; brIf f "$rfd"
    lg f "$tot"; lg f "$got"; ins f "i32.add"; ls f "$tot"
    br f "$rfg"; endB f; endB f
    lg f "$fd"; callf f "$fd_close"; ins f "drop"
    lg f "$tot"; lg f "$sz"; ins f "i32.ne"
    ifE f; ic f 0; ins f "return"; endB f
    // widen in place, back to front: unit i's write (bytes 2i, 2i+1) never
    // lands on a byte j <= i still to be read
    lg f "$sz"; ls f "$i"
    blockE f "$rwd"; loopE f "$rwg"
    lg f "$i"; ins f "i32.eqz"; brIf f "$rwd"
    lg f "$i"; ic f 1; ins f "i32.sub"; ls f "$i"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ins f "i32.add"; mem f "i32.load8_u"
    mem f "i32.store16"
    br f "$rwg"; endB f; endB f
    lg f "$p"
    endFn f

// $fexists(s): path_open succeeds -> 1, else 0 (bools are RAW words here)
let private emitFexists (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$n" "i32"; local f "$i" "i32"
    localsDone f
    lg f "$s"; ins f "i32.eqz"; ifE f; ic f 0; ins f "return"; endB f
    stagePath f
    emitPathOpen f
    ifE f; ic f 0; ins f "return"; endB f
    saddr f (FMTBUF + 200); mem f "i32.load"; callf f "$fd_close"; ins f "drop"
    ic f 1
    endFn f

// $memsize(): the linear memory's current byte size (memory.size pages << 16)
let private emitMemsize (m : Mod) : unit =
    let f = beginFn m []
    localsDone f
    emitByte f.B 0x3F; emitByte f.B 0
    ic f 16; ins f "i32.shl"
    endFn f

// $memcopy(dst, src, n): a raw block move over linear memory
let private emitMemcopy (m : Mod) : unit =
    let f = beginFn m [ "$d"; "$s"; "$n" ]
    localsDone f
    lg f "$d"; lg f "$s"; lg f "$n"
    memCopy f
    endFn f

// $cbreg(clo): park a closure where JS can call back into it — the returned
// SLOT ADDRESS is the callback token the glue holds (it never sees the
// closure pointer itself, which a collection may move). Standalone: a
// $lalloc'd word, nothing moves. GC: a fixed root slot from the cbBase area,
// scanned and relocated with the heap; slots are handed out by $cbnext and
// never reclaimed (a JS-held callback has no observable death on linear).
// $clseq / $clshash: the DEFAULT identity trio for a CLASS. A class compares
// and hashes by REFERENCE (DIVERGENCES.md), so they sit in every class' vtable
// row unless the class declares its own — without them $cmpv/$hashv walked a
// class structurally and a genuinely RECURSIVE one (`{ value; nodes : cset<T> }`)
// recursed until the stack ran out.
// $novt: table index 0. A vtable row of 0 means NO IMPLEMENTATION; calling
// through it used to run whatever function happened to be first in the table
// (an eta-expanded dispatcher, which then called itself forever). Reserving
// index 0 for a trap turns a missing row into an immediate, locatable failure.
let private emitNoVt (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    localsDone f
    ins f "unreachable"
    endFn f

let private emitClsEq (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    localsDone f
    lg f "$a"; lg f "$b"; ins f "i32.eq"
    endFn f

let private emitClsHash (m : Mod) : unit =
    let f = beginFn m [ "$a"; "$b" ]
    localsDone f
    // under the moving collector the ADDRESS is not stable — fpprt keeps a
    // side table keyed by object identity; standalone never moves, so the
    // pointer itself is the hash
    if gc then (lg f "$a"; callf f "$fpidh") else lg f "$a"
    endFn f

// $showv: `%A` at a hole whose type is not known statically. Mirrors the GC
// backend's: a raw int prints decimal, the wide boxes print their value, a
// string prints QUOTED as F# does, anything else is "?" (the GC backend's
// answer too — the parity bar is exactly this).
let private emitShowv (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    local f "$c" "i32"; local f "$msz" "i32"
    localsDone f
    let hv cid tid = if gc then (tid <<< 1) ||| 1 else cid
    // not a pointer (odd, zero, or beyond memory) -> a raw int
    memSizeIns f; ic f 16; ins f "i32.shl"; ls f "$msz"
    lg f "$v"; ic f 1; ins f "i32.and"
    lg f "$v"; ins f "i32.eqz"; ins f "i32.or"
    lg f "$v"; lg f "$msz"; ins f "i32.ge_u"; ins f "i32.or"
    // BELOW the constant base is the fixed scratch area, never an object:
    // a small even int (12) would otherwise read a "header" at address 12
    lg f "$v"; ic f CONST_BASE; ins f "i32.lt_u"; ins f "i32.or"
    ifE f; lg f "$v"; callf f "$str_of_int"; ret f; endB f
    lg f "$v"; mem f "i32.load"; ls f "$c"
    lg f "$c"; ic f (hv CID_FLOAT gcFloatTid); ins f "i32.eq"
    ifE f; lg f "$v"; callf f "$ftoa_s"; ret f; endB f
    lg f "$c"; ic f (hv CID_INT64 gcInt64Tid); ins f "i32.eq"
    ifE f; lg f "$v"; callf f "$ltoa_s"; ret f; endB f
    lg f "$c"; ic f (hv CID_STRING gcStrTid); ins f "i32.eq"
    ifE f
    ic f 34; callf f "$str_of_char"; lg f "$v"; callf f "$str_cat"
    ic f 34; callf f "$str_of_char"; callf f "$str_cat"
    ret f
    endB f
    ic f 63; callf f "$str_of_char"
    endFn f

// $strv: `string x` where the operand type is NOT statically known (a
// generic function's `string x.V`). Same dispatch as $showv, but a string
// renders as ITSELF — `string` is not `%A`.
let private emitStrv (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    local f "$c" "i32"; local f "$msz" "i32"
    localsDone f
    let hv cid tid = if gc then (tid <<< 1) ||| 1 else cid
    memSizeIns f; ic f 16; ins f "i32.shl"; ls f "$msz"
    lg f "$v"; ic f 1; ins f "i32.and"
    lg f "$v"; ins f "i32.eqz"; ins f "i32.or"
    lg f "$v"; lg f "$msz"; ins f "i32.ge_u"; ins f "i32.or"
    // BELOW the constant base is the fixed scratch area, never an object:
    // a small even int (12) would otherwise read a "header" at address 12
    lg f "$v"; ic f CONST_BASE; ins f "i32.lt_u"; ins f "i32.or"
    ifE f; lg f "$v"; callf f "$str_of_int"; ret f; endB f
    lg f "$v"; mem f "i32.load"; ls f "$c"
    lg f "$c"; ic f (hv CID_FLOAT gcFloatTid); ins f "i32.eq"
    ifE f; lg f "$v"; callf f "$ftoa_s"; ret f; endB f
    lg f "$c"; ic f (hv CID_INT64 gcInt64Tid); ins f "i32.eq"
    ifE f; lg f "$v"; callf f "$ltoa_s"; ret f; endB f
    lg f "$c"; ic f (hv CID_STRING gcStrTid); ins f "i32.eq"
    ifE f; lg f "$v"; ret f; endB f
    ic f 63; callf f "$str_of_char"
    endFn f

let private emitCbreg (m : Mod) : unit =
    let f = beginFn m [ "$clo" ]
    local f "$p" "i32"
    localsDone f
    if gc then
        // pop a recycled slot (content = next | 1) or bump a fresh one;
        // $p is a zeroed wasm local, so "no recycled slot" reads as 0
        gg f "$cbfree"
        ifE f
        gg f "$cbfree"; ls f "$p"
        lg f "$p"; mem f "i32.load"; ic f -2; ins f "i32.and"; gs f "$cbfree"
        endB f
        lg f "$p"; ins f "i32.eqz"
        ifE f
        gg f "$roots"; ic f (cbBase * 4); ins f "i32.add"
        gg f "$cbnext"; ic f 2; ins f "i32.shl"; ins f "i32.add"; ls f "$p"
        gg f "$cbnext"; ic f 1; ins f "i32.add"; gs f "$cbnext"
        endB f
    else
        ic f 4; callf f "$lalloc"; ls f "$p"
    lg f "$p"; lg f "$clo"; mem f "i32.store"
    lg f "$p"
    endFn f

// $gcdrain(): pop dead cleanup tags (kind 1 = closure slot addresses) and
// invoke each parked closure once. The slot is recycled onto the $cbfree
// freelist BEFORE the call — the closure pointer already rides a local, and
// a cleanup that registers new cleanups may reuse the slot. A cleanup can
// allocate and so trigger further collections; the loop drains whatever
// they queue too, until the queue reads empty.
let private emitGcdrain (m : Mod) : unit =
    let f = beginFn m []
    local f "$t" "i32"; local f "$clo" "i32"
    localsDone f
    blockE f "$dend"; loopE f "$dgo"
    ic f 1; callf f "$fpdrain1"; ls f "$t"
    lg f "$t"; ins f "i32.eqz"; brIf f "$dend"
    lg f "$t"; mem f "i32.load"; ls f "$clo"
    lg f "$t"; gg f "$cbfree"; ic f 1; ins f "i32.or"; mem f "i32.store"
    lg f "$t"; gs f "$cbfree"
    lg f "$clo"; ic f 0
    lg f "$clo"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"
    callIndirect f "$lclo"
    ins f "drop"
    br f "$dgo"; endB f; endB f
    endFn f

// $rootswipe(): zero the shadow-stack region above $sp. Pops leave their
// values behind and the WHOLE registered range is scanned, so the residue
// acts like conservative roots — objects stay alive until their stale slot
// is overwritten. GC.Collect wipes first, which is what makes it the
// deterministic cleanup point. 2097152 slots = FPPRT_WASM_NROOTS.
let private emitRootswipe (m : Mod) : unit =
    let f = beginFn m []
    localsDone f
    gg f "$roots"; gg f "$sp"; ins f "i32.add"
    ic f 0
    ic f (2097152 * 4); gg f "$sp"; ins f "i32.sub"
    // memory.fill
    emitByte f.B 0xFC; emitU32 f.B 0x0B; emitByte f.B 0
    endFn f

// $jscall(slot, h): the JS->wasm bridge — load the closure's CURRENT pointer
// from its slot and call it with the raw handle as its one argument
let private emitJscall (m : Mod) : unit =
    let f = beginFn m [ "$slot"; "$h" ]
    local f "$clo" "i32"
    localsDone f
    lg f "$slot"; mem f "i32.load"; ls f "$clo"
    lg f "$clo"; lg f "$h"
    lg f "$clo"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"
    callIndirect f "$lclo"
    endFn f

// $lin_salloc(units): a fresh string SHELL for the JS glue to fill (utf-16
// units at +8) — how a JS string crosses INTO linear memory
let private emitLinSalloc (m : Mod) : unit =
    let f = beginFn m [ "$n" ]
    local f "$p" "i32"
    localsDone f
    strAllocN f (fun () -> lg f "$n")
    lg f "$p"
    endFn f

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

// $ftoa_s(x): the SHORTEST-form float -> string (mirrors the wasm-GC $ftoa):
// NaN, sign, ∞ (U+221E, .NET's spelling), >=1e18 normalizes to <10 with an
// E+ exponent, integer digits, then up to 15 fraction digits stopping when
// the residue hits zero — f64 rounding makes 0.1 come out as "0.1" and 5.0
// as "5". Backs `print <float>` and `string <float>`, which have no
// fixed-width form ($ftoa6 is %f's fixed six decimals).
let private emitFtoaS (m : Mod) : unit =
    let f = beginFn m [ "$x" ]
    local f "$v" "f64"; local f "$w" "i32"; local f "$ip" "f64"; local f "$frac" "f64"
    local f "$ipi" "i64"; local f "$tmp" "i64"; local f "$d" "i32"; local f "$k" "i32"
    local f "$cur" "i32"; local f "$p" "i32"; local f "$len" "i32"; local f "$i" "i32"
    local f "$e" "i32"
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
    // infinity
    lg f "$v"; fc f 9218868437227405312L; ins f "f64.eq"
    ifE f
    put (fun () -> ic f 0x221E)
    br f "$fin"
    endB f
    // >= 1e18: scale below 10, counting the exponent
    lg f "$v"; fc f 4876203697187506176L; ins f "f64.ge"
    ifE f
    blockE f "$sc"; loopE f "$sgo"
    lg f "$v"; fc f 4621819117588971520L; ins f "f64.lt"; brIf f "$sc"
    lg f "$v"; fc f 4621819117588971520L; ins f "f64.div"; ls f "$v"
    lg f "$e"; ic f 1; ins f "i32.add"; ls f "$e"
    br f "$sgo"; endB f; endB f
    endB f
    lg f "$v"; ins f "f64.floor"; ls f "$ip"
    lg f "$ip"; ins f "i64.trunc_f64_s"; ls f "$ipi"
    // integer digits: count, then write back-to-front
    ic f 1; ls f "$d"
    lg f "$ipi"; ls f "$tmp"
    blockE f "$dc"; loopE f "$dl"
    lg f "$tmp"; lc f 10L; ins f "i64.lt_u"; brIf f "$dc"
    lg f "$tmp"; lc f 10L; ins f "i64.div_u"; ls f "$tmp"
    lg f "$d"; ic f 1; ins f "i32.add"; ls f "$d"
    br f "$dl"; endB f; endB f
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
    // fraction: only when non-zero; stop the moment the residue is exact
    lg f "$v"; lg f "$ip"; ins f "f64.sub"; ls f "$frac"
    lg f "$frac"; fc f 0L; ins f "f64.gt"
    ifE f
    put (fun () -> ic f 46)
    ic f 0; ls f "$k"
    blockE f "$fc2"; loopE f "$fl2"
    lg f "$k"; ic f 15; ins f "i32.ge_s"; brIf f "$fc2"
    lg f "$frac"; fc f 4621819117588971520L; ins f "f64.mul"; ls f "$frac"
    lg f "$frac"; ins f "f64.floor"; ins f "i32.trunc_f64_s"; ls f "$d"
    put (fun () -> ic f 48; lg f "$d"; ins f "i32.add")
    lg f "$frac"; lg f "$frac"; ins f "f64.floor"; ins f "f64.sub"; ls f "$frac"
    lg f "$frac"; fc f 0L; ins f "f64.eq"; brIf f "$fc2"
    lg f "$k"; ic f 1; ins f "i32.add"; ls f "$k"
    br f "$fl2"; endB f; endB f
    endB f
    // E+<e>
    lg f "$e"; ic f 0; ins f "i32.ne"
    ifE f
    put (fun () -> ic f 69)
    put (fun () -> ic f 43)
    ic f 1; ls f "$d"
    lg f "$e"; ls f "$i"
    blockE f "$ec"; loopE f "$el"
    lg f "$i"; ic f 10; ins f "i32.lt_u"; brIf f "$ec"
    lg f "$i"; ic f 10; ins f "i32.div_u"; ls f "$i"
    lg f "$d"; ic f 1; ins f "i32.add"; ls f "$d"
    br f "$el"; endB f; endB f
    lg f "$w"; lg f "$d"; ic f 1; ins f "i32.sub"; ic f 1; ins f "i32.shl"; ins f "i32.add"; ls f "$cur"
    lg f "$e"; ls f "$i"
    blockE f "$ewc"; loopE f "$ewl"
    lg f "$cur"
    lg f "$i"; ic f 10; ins f "i32.rem_u"; ic f 48; ins f "i32.add"
    mem f "i32.store16"
    lg f "$cur"; ic f 2; ins f "i32.sub"; ls f "$cur"
    lg f "$i"; ic f 10; ins f "i32.div_u"; ls f "$i"
    lg f "$i"; ic f 0; ins f "i32.eq"; brIf f "$ewc"
    br f "$ewl"; endB f; endB f
    lg f "$w"; lg f "$d"; ic f 1; ins f "i32.shl"; ins f "i32.add"; ls f "$w"
    endB f
    endB f  // $fin
    // build the string [hdr][len][units] from FMTBUF
    lg f "$w"; saddr f FMTBUF; ins f "i32.sub"; ic f 1; ins f "i32.shr_u"; ls f "$len"
    strAllocN f (fun () -> lg f "$len")
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

// $ltoa_s / $ultoa_s: int64/uint64 BOX -> decimal string. Signed handles
// i64.min by negating in the unsigned domain (0 - v reads back the right
// magnitude). Digits stage back-to-front in FMTBUF like the other writers.
let private emitLtoa (m : Mod) (signed : bool) : unit =
    let f = beginFn m [ "$x" ]
    local f "$v" "i64"; local f "$w" "i32"; local f "$d" "i32"; local f "$cur" "i32"
    local f "$p" "i32"; local f "$len" "i32"; local f "$i" "i32"; local f "$neg" "i32"
    localsDone f
    emitSbufRefresh f
    lg f "$x"; ic f HDR; ins f "i32.add"; mem f "i64.load"; ls f "$v"
    saddr f FMTBUF; ls f "$w"
    (if signed then
        lg f "$v"; lc f 0L; ins f "i64.lt_s"
        ifE f
        ic f 1; ls f "$neg"
        lc f 0L; lg f "$v"; ins f "i64.sub"; ls f "$v"
        endB f)
    // stage digits back-to-front from the end of a 20-unit window (a u64
    // has at most 20 decimal digits), remember where the last write landed
    lg f "$w"; ic f (21 * 2); ins f "i32.add"; ls f "$cur"
    lg f "$cur"; ls f "$len"
    blockE f "$lc"; loopE f "$ll"
    lg f "$cur"; ic f 2; ins f "i32.sub"; ls f "$cur"
    lg f "$cur"
    lg f "$v"; lc f 10L; ins f "i64.rem_u"; ins f "i32.wrap_i64"; ic f 48; ins f "i32.add"
    mem f "i32.store16"
    lg f "$v"; lc f 10L; ins f "i64.div_u"; ls f "$v"
    lg f "$v"; lc f 0L; ins f "i64.eq"; brIf f "$lc"
    br f "$ll"; endB f; endB f
    // shift the digits down to $w (plus the sign), so the string starts at FMTBUF
    (if signed then
        lg f "$neg"
        ifE f
        lg f "$w"; ic f 45; mem f "i32.store16"
        endB f)
    let signOff () = if signed then (lg f "$neg"; ic f 1; ins f "i32.shl"; ins f "i32.add") else ()
    // units = (len - cur)/2; copy [cur, len) to [w+sign, ...)
    ic f 0; ls f "$i"
    blockE f "$cc"; loopE f "$cl"
    lg f "$cur"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$len"; ins f "i32.ge_u"; brIf f "$cc"
    lg f "$w"; signOff (); lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    lg f "$cur"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$cl"; endB f; endB f
    // total units = i + neg
    lg f "$i"
    (if signed then (lg f "$neg"; ins f "i32.add") else ())
    ls f "$d"
    strAllocN f (fun () -> lg f "$d")
    emitSbufRefresh f
    ic f 0; ls f "$i"
    blockE f "$sc"; loopE f "$sl"
    lg f "$i"; lg f "$d"; ins f "i32.ge_u"; brIf f "$sc"
    lg f "$p"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"
    saddr f FMTBUF; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store16"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$sl"; endB f; endB f
    lg f "$p"
    endFn f

// $lalloc(n): 8-align the bump pointer, reserve n bytes, grow memory as
// needed, return the aligned start. Eight, not four: `Mem.alloc` promises
// 8-aligned blocks (the WebGPU command stream is a Float64Array over one).
let private emitLalloc (m : Mod) : unit =
    let f = beginFn m [ "$n" ]
    local f "$p" "i32"
    localsDone f
    gg f "$hp"
    ic f 7; ins f "i32.add"; ic f -8; ins f "i32.and"
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

// $str_of_int(raw i32): decimal, with a leading '-' for negatives.
let private emitStrOfInt (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    local f "$n" "i32"; local f "$neg" "i32"; local f "$d" "i32"
    local f "$p" "i32"; local f "$w" "i32"; local f "$t" "i32"
    localsDone f
    lg f "$v"; ls f "$n"
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
    // GC: never put the HEAD on the shadow stack — it may be a RAW even int
    // (an int list) the pointer scanner would chase. Root the SOURCE cons `$a`
    // (always a real pointer) across both safepoints and re-read the head from
    // it afterwards: tracing updates $a's own head slot, so the re-read is
    // correct whether the head is raw or a moved ref.
    if gc then
        lg f "$a"; callf f "$spush"
        lg f "$a"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"
        lg f "$b"
        callf f "$lappend"; ls f "$rec"
        callf f "$spop"; ls f "$a"
        // allocate with the SOURCE list's own tid (read from `$a`'s header) — NOT
        // the uniform FK_TAGGED gcListTid: a concrete raw-headed list carries a
        // tid whose refoffs EXCLUDE the head, and rebuilding it under the
        // tag-scanning gcListTid would chase that raw head as a pointer.
        lg f "$a"; callf f "$spush"; lg f "$rec"; callf f "$spush"
        lg f "$a"; mem f "i32.load"; ic f 1; ins f "i32.shr_u"; callf f "$fpalloc"; ls f "$cell"
        callf f "$spop"; ls f "$rec"; callf f "$spop"; ls f "$a"
        lg f "$a"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ls f "$h"
    else
        lg f "$a"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ls f "$h"
        lg f "$a"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"
        lg f "$b"
        callf f "$lappend"; ls f "$rec"
        ic f (HDR + 8); callf f "$lalloc"; ls f "$cell"
        lg f "$cell"; ic f CID_LIST; mem f "i32.store"
    lg f "$cell"; ic f HDR; ins f "i32.add"; lg f "$h"; mem f "i32.store"
    lg f "$cell"; ic f (HDR + 4); ins f "i32.add"; lg f "$rec"; mem f "i32.store"
    lg f "$cell"
    endFn f

// The built-in list iterator: `for x in (list :> seq)` lowers to the enumerator
// protocol, but a cons list has no IEnumerable vtable row, so GetEnumerator/
// MoveNext/Current on one route here (see the EIfaceCall lowering) instead of a
// vtable dispatch that would read slot 0 and trap. Mirrors the GC backend's
// $isBuiltinSeq/$iterNew/$iterNext/$iterCur.
let private emitListIter (m : Mod) : unit =
    // $isBuiltinSeq(v) -> raw 0/1: nil (empty list) or a cons cell. A cons is
    // recognised by its CLASS-ID = CID_LIST, not a single tid: under GC a
    // concrete-element cons carries a per-refmap FK_STRUCT tid (so an unboxed
    // int head is skipped by the collector), and ALL of those — plus the
    // uniform cons — map to CID_LIST in the tid->cid table. Checking the raw
    // header instead would miss every FK_STRUCT variant and mis-route a real
    // list to the (absent) IEnumerable vtable row.
    // arrays route here too now (CID_ARRAY): ResizeArray/Dict enumerate via
    // `(x.ToArray() :> seq).GetEnumerator()`, and an array carries no vtable row.
    let arrIterHdr = (gcArrIterTid <<< 1) ||| 1
    let isArrIter (f : Fn) = (lg f "$it"; mem f "i32.load"; ic f (if gc then arrIterHdr else CID_ARRITER); ins f "i32.eq")
    let cidOf (f : Fn) (v : string) =
        if gc then (lg f v; mem f "i32.load"; ic f 1; ins f "i32.shr_u"; ic f 2; ins f "i32.shl"; gg f "$t2c"; ins f "i32.add"; mem f "i32.load")
        else (lg f v; mem f "i32.load")
    let f = beginFn m [ "$v" ]
    local f "$c" "i32"
    localsDone f
    lg f "$v"; ins f "i32.eqz"; ifE f; ic f 1; ins f "return"; endB f
    cidOf f "$v"; ls f "$c"
    lg f "$c"; ic f CID_LIST; ins f "i32.eq"
    lg f "$c"; ic f CID_ARRAY; ins f "i32.eq"
    ins f "i32.or"
    endFn f
    // $literNew(src): an array -> [array][index=-1] (index-based); else a list
    // iterator [remaining=list][current=0].
    let f = beginFn m [ "$src" ]
    local f "$it" "i32"; local f "$c" "i32"
    localsDone f
    cidOf f "$src"; ls f "$c"
    lg f "$c"; ic f CID_ARRAY; ins f "i32.eq"
    ifE f
    (if gc then (lg f "$src"; callf f "$spush"; ic f gcArrIterTid; callf f "$fpalloc"; ls f "$it"; callf f "$spop"; ls f "$src")
     else (ic f (HDR + 8); callf f "$lalloc"; ls f "$it"; lg f "$it"; ic f CID_ARRITER; mem f "i32.store"))
    lg f "$it"; ic f HDR; ins f "i32.add"; lg f "$src"; mem f "i32.store"
    lg f "$it"; ic f (HDR + 4); ins f "i32.add"; ic f (0 - 1); mem f "i32.store"   // index = -1
    elseB f
    (if gc then (lg f "$src"; callf f "$spush"; ic f gcIterTid; callf f "$fpalloc"; ls f "$it"; callf f "$spop"; ls f "$src")
     else (ic f (HDR + 8); callf f "$lalloc"; ls f "$it"; lg f "$it"; ic f CID_ITER; mem f "i32.store"))
    lg f "$it"; ic f HDR; ins f "i32.add"; lg f "$src"; mem f "i32.store"
    lg f "$it"; ic f (HDR + 4); ins f "i32.add"; ic f 0; mem f "i32.store"
    endB f
    lg f "$it"
    endFn f
    // $literNext(it) -> RAW bool. Array: bump the index, true while in bounds.
    // List: pop the head into current, advance remaining. RAW (0/1), not tagged.
    let f = beginFn m [ "$it" ]
    local f "$rem" "i32"; local f "$idx" "i32"
    localsDone f
    isArrIter f
    ifE f
    lg f "$it"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"; ic f 1; ins f "i32.add"; ls f "$idx"
    lg f "$it"; ic f (HDR + 4); ins f "i32.add"; lg f "$idx"; mem f "i32.store"
    lg f "$idx"; lg f "$it"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ins f "i32.lt_s"; ins f "return"
    elseB f
    lg f "$it"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ls f "$rem"
    lg f "$rem"; ins f "i32.eqz"; ifE f; ic f 0; ins f "return"; endB f   // nil -> false
    lg f "$it"; ic f (HDR + 4); ins f "i32.add"; lg f "$rem"; ic f HDR; ins f "i32.add"; mem f "i32.load"; mem f "i32.store"
    lg f "$it"; ic f HDR; ins f "i32.add"; lg f "$rem"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"; mem f "i32.store"
    ic f 1; ins f "return"
    endB f
    ins f "unreachable"
    endFn f
    // $literCur(it) -> the current element. Array: arr[idx]. List: stored current.
    let f = beginFn m [ "$it" ]
    local f "$idx" "i32"
    localsDone f
    isArrIter f
    ifE f
    lg f "$it"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"; ls f "$idx"
    lg f "$it"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ic f (HDR + 4); ins f "i32.add"; lg f "$idx"; ic f 4; ins f "i32.mul"; ins f "i32.add"; mem f "i32.load"; ins f "return"
    elseB f
    lg f "$it"; ic f (HDR + 4); ins f "i32.add"; mem f "i32.load"; ins f "return"
    endB f
    ins f "unreachable"
    endFn f

// $prints(s): UTF-16 -> UTF-8 into PRINTBUF, then fd_write(1). Handles the
// BMP (1/2/3-byte forms); surrogate pairs are written as their raw units
// (adequate for slice 1's ASCII-and-Latin output).
let private emitPrintsFd (m : Mod) (fd : int) : unit =
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
    // iovec = (PRINTBUF, w - PRINTBUF); fd_write(fd, IOV, 1, NWRITTEN)
    saddr f IOV_PTR; saddr f PRINTBUF; mem f "i32.store"
    saddr f IOV_LEN; lg f "$w"; saddr f PRINTBUF; ins f "i32.sub"; mem f "i32.store"
    ic f fd; saddr f IOV_PTR; ic f 1; saddr f NWRITTEN
    callf f "$fd_write"; ins f "drop"
    endFn f

let private emitPrints (m : Mod) : unit = emitPrintsFd m 1
let private emitEprints (m : Mod) : unit = emitPrintsFd m 2

// $printraw: each UTF-16 unit becomes ONE byte (the Latin-1 inverse) — the
// raw-byte channel a binary-emitting driver prints modules through. $prints'
// UTF-8 encoding DOUBLES bytes >= 0x80 (the linear fixpoint's stage-1 module
// came out mojibake'd).
let private emitPrintRaw (m : Mod) : unit =
    let f = beginFn m [ "$s" ]
    local f "$len" "i32"; local f "$i" "i32"; local f "$w" "i32"
    localsDone f
    if gc then (gg f "$roots"; mem f "i32.load"; ic f 8; ins f "i32.add"; gs f "$sbuf")
    lg f "$s"; ic f 4; ins f "i32.add"; mem f "i32.load"; ls f "$len"
    saddr f PRINTBUF; ls f "$w"
    ic f 0; ls f "$i"
    blockE f "$qc"; loopE f "$ql"
    lg f "$i"; lg f "$len"; ins f "i32.ge_u"; brIf f "$qc"
    // window full -> flush and rewind (a self-sized module dwarfs PRINTCAP)
    lg f "$w"; saddr f (PRINTBUF + PRINTCAP - 4); ins f "i32.ge_u"
    ifE f
    saddr f IOV_PTR; saddr f PRINTBUF; mem f "i32.store"
    saddr f IOV_LEN; lg f "$w"; saddr f PRINTBUF; ins f "i32.sub"; mem f "i32.store"
    ic f 1; saddr f IOV_PTR; ic f 1; saddr f NWRITTEN
    callf f "$fd_write"; ins f "drop"
    saddr f PRINTBUF; ls f "$w"
    endB f
    lg f "$w"
    lg f "$s"; ic f 8; ins f "i32.add"; lg f "$i"; ic f 1; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load16_u"
    mem f "i32.store8"
    lg f "$w"; ic f 1; ins f "i32.add"; ls f "$w"
    lg f "$i"; ic f 1; ins f "i32.add"; ls f "$i"
    br f "$ql"; endB f; endB f
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
    // char-array ELEMENTS are raw 4-byte words (chars are raw i32 at rest);
    // the old >>1 "untag" halved every set element and nothing ever matched
    lg f "$cs"; ic f 8; ins f "i32.add"; lg f "$j"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"
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
    local f "$w" "i32"; local f "$st" "i32"; local f "$tot" "i32"; local f "$tbl" "i32"; local f "$tid" "i32"; local f "$msz" "i32"
    local f "$fa" "f64"; local f "$fb" "f64"; local f "$la" "i64"; local f "$lb" "i64"
    localsDone f
    let hv cid tid = if gc then (tid <<< 1) ||| 1 else cid
    let strH = hv CID_STRING gcStrTid
    let fltH = hv CID_FLOAT gcFloatTid
    let i64H = hv CID_INT64 gcInt64Tid
    let arrH = hv CID_ARRAY gcArrTid
    let both h = (lg f "$ca"; ic f h; ins f "i32.eq"; lg f "$cb"; ic f h; ins f "i32.eq"; ins f "i32.and")
    lg f "$a"; lg f "$b"; ins f "i32.eq"; ifE f; ic f 0; ins f "return"; endB f
    // both odd: compare the WORDS directly. For the tagged pairs a FK_TAGGED
    // walk recurses on, sign(2x+1 - (2y+1)) = sign(x - y), so the unshifted
    // compare orders identically; for RAW full-width ints (an unwitnessed
    // `compare` eta's operands) it is the CORRECT compare, where the old
    // shifted form mis-ordered odd-vs-even raw pairs (compare 3 2 gave -1
    // and List.sort of ints — including the emitter's own vArities sort —
    // came out wrong).
    lg f "$a"; ic f 1; ins f "i32.and"; lg f "$b"; ic f 1; ins f "i32.and"; ins f "i32.and"
    ifE f
    lg f "$a"; lg f "$b"; ins f "i32.gt_s"; lg f "$a"; lg f "$b"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"
    endB f
    // ZERO is null — but only against a POINTER. Against a raw scalar (an odd
    // word) it is the integer 0, and `compare -7 0` must be -1: the old
    // null-orders-first shortcut answered 1 (`sign -7` came out positive).
    lg f "$a"; ins f "i32.eqz"
    ifE f
    lg f "$b"; ic f 1; ins f "i32.and"
    ifE f; lg f "$a"; lg f "$b"; ins f "i32.gt_s"; lg f "$a"; lg f "$b"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"; endB f
    ic f -1; ins f "return"
    endB f
    lg f "$b"; ins f "i32.eqz"
    ifE f
    lg f "$a"; ic f 1; ins f "i32.and"
    ifE f; lg f "$a"; lg f "$b"; ins f "i32.gt_s"; lg f "$a"; lg f "$b"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"; endB f
    ic f 1; ins f "return"
    endB f
    // one odd, one even: the even side is a POINTER only if it looks like a
    // managed object (in-memory, odd header, tid inside the shape table) —
    // then ints order before pointers, arbitrarily but consistently. An even
    // side that fails the test is a raw EVEN int: compare the words.
    memSizeIns f; ic f 16; ins f "i32.shl"; ls f "$msz"
    (if gc then (gg f "$roots"; ic f (4 * gcCmpTblSlot); ins f "i32.add"; mem f "i32.load"; ls f "$tbl"))
    let rawCmp () = (lg f "$a"; lg f "$b"; ins f "i32.gt_s"; lg f "$a"; lg f "$b"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return")
    // isPtr(reg): even && < msz && header odd && tid < table count
    let isPtr (r : string) =
        lg f r; lg f "$msz"; ins f "i32.lt_u"
        // ... and ABOVE the constant base: below it is fixed scratch, never an
        // object. Without this every small even int (a loop counter at 2) was
        // "a pointer" and ordered after any tagged int — `k >= n` in an
        // object-expression enumerator stopped at exactly 2, whatever n was.
        lg f r; ic f CONST_BASE; ins f "i32.ge_u"; ins f "i32.and"
        (if gc then (
            lg f r; mem f "i32.load"; ls f "$x"
            lg f "$x"; ic f 1; ins f "i32.and"; ins f "i32.and"
            lg f "$x"; ic f 1; ins f "i32.shr_u"; lg f "$tbl"; ic f 4; ins f "i32.add"; mem f "i32.load"; ins f "i32.lt_u"; ins f "i32.and"))
    lg f "$a"; ic f 1; ins f "i32.and"
    ifE f
    isPtr "$b"
    ifE f; ic f -1; ins f "return"; endB f
    rawCmp ()
    endB f
    lg f "$b"; ic f 1; ins f "i32.and"
    ifE f
    isPtr "$a"
    ifE f; ic f 1; ins f "return"; endB f
    rawCmp ()
    endB f
    // both even and non-zero here. A generic comparison is UNWITNESSED, so a RAW
    // scalar payload word (a large `int` tuple field — the compiler's synthetic
    // 5e8-range offsets) is indistinguishable from a pointer by value alone.
    // Reading its "header" below would load at that value's address and fault out
    // of bounds. Guard the header load: if EITHER side is beyond linear memory it
    // cannot be a heap object, so order the two directly as signed words. A small
    // raw int (< memory) still rides the tid-table guard below, unchanged.
    memSizeIns f; ic f 16; ins f "i32.shl"; ls f "$msz"
    lg f "$a"; lg f "$msz"; ins f "i32.ge_u"; lg f "$b"; lg f "$msz"; ins f "i32.ge_u"; ins f "i32.or"
    // ... or below the constant base: two small even ints are INTS
    lg f "$a"; ic f CONST_BASE; ins f "i32.lt_u"; ins f "i32.or"
    lg f "$b"; ic f CONST_BASE; ins f "i32.lt_u"; ins f "i32.or"
    ifE f; lg f "$a"; lg f "$b"; ins f "i32.gt_s"; lg f "$a"; lg f "$b"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"; endB f
    lg f "$a"; mem f "i32.load"; ls f "$ca"
    lg f "$b"; mem f "i32.load"; ls f "$cb"
    // IDENTITY DISPATCH: a class that declares its own CompareTo/Equals
    // orders/compares by THAT, not by the structural word fold — a Map or
    // HashMap over a tree whose SHAPE differs for equal contents would
    // otherwise call equal maps unequal. Slots 2 and 0 of the class' vtable
    // row; 0 means "not declared".
    let cidOfHdr (hdrLocal : string) =
        if gc then (lg f hdrLocal; ic f 1; ins f "i32.shr_u"; ic f 2; ins f "i32.shl"; gg f "$t2c"; ins f "i32.add"; mem f "i32.load")
        else lg f hdrLocal
    let vtRowAddr (slot : int) =
        // vtable base + (cid * NSlots + slot) * 4
        (if gc then (gg f "$roots"; ic f (4 * vtRootSlot); ins f "i32.add"; mem f "i32.load"; ic f 8; ins f "i32.add")
         else ic f vtBaseConst)
        cidOfHdr "$ca"
        ic f vtNSlots; ins f "i32.mul"; ic f slot; ins f "i32.add"; ic f 4; ins f "i32.mul"; ins f "i32.add"
        mem f "i32.load"
    if vtNSlots > 0 then
        // both sides the same class, that class has a REAL id (an unmapped
        // tid reads cid 0, whose row belongs to another type — dispatching
        // through it compared two equal `Some 0`s by reference), and it
        // declares one of the trio
        lg f "$ca"; lg f "$cb"; ins f "i32.eq"
        cidOfHdr "$ca"; ic f CID_FIRST_USER; ins f "i32.ge_s"; ins f "i32.and"
        ifE f
        vtRowAddr 2; ls f "$x"
        lg f "$x"; ifE f
        lg f "$a"; lg f "$b"; lg f "$x"; callIndirect f "$lfn2"; ins f "return"
        endB f
        vtRowAddr 0; ls f "$x"
        lg f "$x"; ifE f
        // Equals answers a bool: equal -> 0, else an arbitrary but stable
        // order (by address), so sorting a set of them still terminates
        lg f "$a"; lg f "$b"; lg f "$x"; callIndirect f "$lfn2"
        ifE f; ic f 0; ins f "return"; endB f
        lg f "$a"; lg f "$b"; ins f "i32.gt_u"; lg f "$a"; lg f "$b"; ins f "i32.lt_u"; ins f "i32.sub"; ins f "return"
        endB f
        endB f
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
    // arrays compare by IDENTITY (DIVERGENCES.md): same pointer returned 0
    // at entry, different arrays order by ADDRESS — never element-wise
    lg f "$a"; lg f "$b"; ins f "i32.gt_u"; lg f "$a"; lg f "$b"; ins f "i32.lt_u"; ins f "i32.sub"; ins f "return"
    endB f
    // remaining compound shapes: under GC walk the payload words structurally via
    // the tid->info table (tuples/records/lists/cons/closures, uniform); raw
    // metadata words (a union tag) compare as ints, ref/payload words recurse.
    // Different tids order by header. Standalone has no table -> equal (0).
    if gc then
        gg f "$roots"; ic f (4 * gcCmpTblSlot); ins f "i32.add"; mem f "i32.load"; ls f "$tbl"
        // is $a a managed heap object? its header word must be an odd (tid<<1)|1
        // with a tid inside the shape table. Otherwise $a is a RAW scalar — an
        // even int under the raw-int model, whose value-as-address read a
        // non-header — and $a/$b are compared DIRECTLY as signed words. Without
        // this, $cmpv indexed `$tbl + 8 + 4*tid` with a raw int as the tid (OOB),
        // and even the header comparison below was against garbage. (The value's
        // own witness would say raw vs ref, but comparison sites are unwitnessed;
        // the runtime shape table is the available discriminator.)
        lg f "$ca"; ic f 1; ins f "i32.and"
        lg f "$ca"; ic f 1; ins f "i32.shr_u"; lg f "$tbl"; ic f 4; ins f "i32.add"; mem f "i32.load"; ins f "i32.lt_u"
        ins f "i32.and"; ins f "i32.eqz"
        ifE f; lg f "$a"; lg f "$b"; ins f "i32.gt_s"; lg f "$a"; lg f "$b"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"; endB f
        // DIFFERENT headers are not necessarily different TYPES: one shape can
        // intern under several tids (a witness-selected raw payload and the
        // tagged fallback both build `Some 0`), and ordering by header then
        // called two equal values unequal — `tryFind k m = Some v` was false
        // for a map built inside the prelude. Order by CLASS-ID, and only when
        // the ids genuinely differ; equal ids fall through to the word walk,
        // which reads $a's layout (same shape, so it describes both).
        lg f "$ca"; lg f "$cb"; ins f "i32.ne"
        ifE f
        cidOfHdr "$ca"; ls f "$x"
        cidOfHdr "$cb"; ls f "$y"
        lg f "$x"; lg f "$y"; ins f "i32.ne"
        ifE f
        lg f "$x"; lg f "$y"; ins f "i32.gt_s"; lg f "$x"; lg f "$y"; ins f "i32.lt_s"; ins f "i32.sub"; ins f "return"
        endB f
        endB f
        lg f "$ca"; ic f 1; ins f "i32.and"; ins f "i32.eqz"; ifE f; ic f 0; ins f "return"; endB f
        lg f "$ca"; ic f 1; ins f "i32.shr_u"; ls f "$tid"
        lg f "$tbl"; ic f 8; ins f "i32.add"; lg f "$tid"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$r"
        // PACKED SCALAR ARRAY sentinel (nwords = 0x3FF): arrays compare by
        // IDENTITY (DIVERGENCES.md) — same pointer already returned 0 above,
        // so different arrays order by ADDRESS. The sentinel exists so the
        // compound word walk below never reads packed f64 payload halves as
        // refs (that faulted at the double's bit pattern).
        lg f "$r"; ic f 0x3FF; ins f "i32.and"; ic f 0x3FF; ins f "i32.eq"
        ifE f
        lg f "$a"; lg f "$b"; ins f "i32.gt_u"; lg f "$a"; lg f "$b"; ins f "i32.lt_u"; ins f "i32.sub"; ins f "return"
        endB f
        // tid -> info: low 10 bits = nword count, the high bits a REF BITMASK (bit
        // w set = word w is a pointer). ONE walk over words [1, nwords): a ref word
        // recurses through $cmpv; a raw word (a union tag, or a tuple/record's
        // inline int) orders as a signed int. The bitmask replaces a
        // raw-prefix/ref-suffix split, which could not describe a ref field BEFORE
        // a raw one (a `(string, int)` dict key) — that made $cmpv deref the int as
        // a pointer, so every generic Dict keyed by such a tuple mis-compared.
        lg f "$r"; ic f 0x3FF; ins f "i32.and"; ls f "$tot"
        lg f "$r"; ic f 10; ins f "i32.shr_u"; ls f "$st"
        ic f 1; ls f "$w"
        blockE f "$td"; loopE f "$tgo"
        lg f "$w"; lg f "$tot"; ins f "i32.ge_s"; brIf f "$td"
        lg f "$st"; lg f "$w"; ins f "i32.shr_u"; ic f 1; ins f "i32.and"
        ifE f
        lg f "$a"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"
        lg f "$b"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"
        callf f "$cmpv"; ls f "$r"
        elseB f
        lg f "$a"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$x"
        lg f "$b"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$y"
        lg f "$x"; lg f "$y"; ins f "i32.gt_s"; lg f "$x"; lg f "$y"; ins f "i32.lt_s"; ins f "i32.sub"; ls f "$r"
        endB f
        lg f "$r"; ifE f; lg f "$r"; ins f "return"; endB f
        lg f "$w"; ic f 1; ins f "i32.add"; ls f "$w"
        br f "$tgo"; endB f; endB f
    ic f 0
    endFn f

// $hashv(v): a structural hash. The dicts are insertion-ordered, so hash
// values never reach any output — only CONSISTENCY matters: equal values must
// hash equal, and $hashv must agree with the witnessed raw fast path (a raw
// element IS its own hash). Standalone: a tagged int hashes to its value; a
// string to the SAMPLED FNV (up to four units from each end); an array to its
// length; the wide boxes to their bit pattern folded to 32; other objects to
// the class-id. GC: headers are (tid<<1)|1, so the old CID dispatch never
// matched — every string hashed to the constant string-tid header and every
// same-shape tuple to ITS OWN header (equal keys, different tids from the
// interning path taken) — a `(string, int)`-keyed Dict missed on lookup,
// which is exactly how the self-hosted compiler stubbed 105 prelude members
// ("unbound variable"/"capture not in scope": VarId-tuple dict misses). GC
// path mirrors $cmpv: raw scalars (odd, beyond-memory, or not-a-managed-tid)
// hash to themselves; known tids dispatch; everything else walks the payload
// words [1,nwords) via the tid table's ref bitmask — h = h*31 + (ref word ?
// $hashv(w) : w) — matching the wasm-GC fold shape (tuple h0*31+h1, union
// tag*31+payload).
let private emitHashv (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    local f "$h" "i32"; local f "$n" "i32"; local f "$i" "i32"; local f "$cid" "i32"; local f "$b" "i64"
    local f "$tbl" "i32"; local f "$tid" "i32"; local f "$r" "i32"; local f "$tot" "i32"; local f "$st" "i32"; local f "$w" "i32"; local f "$msz" "i32"
    localsDone f
    let hv cid tid = if gc then (tid <<< 1) ||| 1 else cid
    if gc then
        // a raw int (odd, or beyond linear memory, or not a managed header
        // below) is its own hash — agree with the witnessed raw fast path
        lg f "$v"; ic f 1; ins f "i32.and"; ifE f; lg f "$v"; ins f "return"; endB f
        lg f "$v"; ins f "i32.eqz"; ifE f; ic f 0; ins f "return"; endB f
        memSizeIns f; ic f 16; ins f "i32.shl"; ls f "$msz"
        lg f "$v"; lg f "$msz"; ins f "i32.ge_u"; ifE f; lg f "$v"; ins f "return"; endB f
    else
        lg f "$v"; ic f 1; ins f "i32.and"
        ifE f; lg f "$v"; ic f 1; ins f "i32.shr_s"; ins f "return"; endB f
    // STANDALONE: an even word is a raw int unless it addresses a real
    // object. Below the constant base is fixed scratch and beyond memory is
    // nothing, so both are the value itself — reading a "header" there faulted
    // (a large int hashed out of bounds).
    if not gc then
        memSizeIns f; ic f 16; ins f "i32.shl"; ls f "$msz"
        lg f "$v"; ins f "i32.eqz"
        lg f "$v"; ic f CONST_BASE; ins f "i32.lt_u"; ins f "i32.or"
        lg f "$v"; lg f "$msz"; ins f "i32.ge_u"; ins f "i32.or"
        ifE f; lg f "$v"; ins f "return"; endB f
    lg f "$v"; mem f "i32.load"; ls f "$cid"
    // IDENTITY DISPATCH: a class that declares GetHashCode hashes by THAT —
    // equal-by-Equals values must hash equal, and the structural fold over a
    // tree's words does not (its shape varies with insertion order)
    if vtNSlots > 0 then
        let cidOfCur () =
            if gc then (lg f "$cid"; ic f 1; ins f "i32.shr_u"; ic f 2; ins f "i32.shl"; gg f "$t2c"; ins f "i32.add"; mem f "i32.load")
            else lg f "$cid"
        (if gc then (gg f "$roots"; ic f (4 * vtRootSlot); ins f "i32.add"; mem f "i32.load"; ic f 8; ins f "i32.add")
         else ic f vtBaseConst)
        cidOfCur ()
        ic f vtNSlots; ins f "i32.mul"; ic f 1; ins f "i32.add"; ic f 4; ins f "i32.mul"; ins f "i32.add"
        mem f "i32.load"; ls f "$r"
        // a row is written only for a real class/record/union id, so a
        // nonzero row IS the guard — requiring cid >= CID_FIRST_USER here
        // ALSO rejected a class whose tid the t2c map does not carry, and the
        // structural walk then recursed forever on a recursive class graph
        lg f "$r"; ifE f
        // GetHashCode takes (self) but rides the 2-param indirect signature
        // the identity trio shares — the extra word is ignored
        lg f "$v"; ic f 0; lg f "$r"; callIndirect f "$lfn2"; ins f "return"
        endB f
    lg f "$cid"; ic f (hv CID_STRING gcStrTid); ins f "i32.eq"
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
    lg f "$cid"; ic f (hv CID_ARRAY gcArrTid); ins f "i32.eq"
    ifE f; lg f "$v"; ic f HDR; ins f "i32.add"; mem f "i32.load"; ins f "return"; endB f
    lg f "$cid"; ic f (hv CID_FLOAT gcFloatTid); ins f "i32.eq"
    ifE f
    lg f "$v"; ic f HDR; ins f "i32.add"; mem f "f64.load"; ins f "i64.reinterpret_f64"; ls f "$b"
    lg f "$b"; ins f "i32.wrap_i64"; lg f "$b"; lc f 32L; ins f "i64.shr_u"; ins f "i32.wrap_i64"; ins f "i32.xor"; ins f "return"
    endB f
    lg f "$cid"; ic f (hv CID_INT64 gcInt64Tid); ins f "i32.eq"
    ifE f
    lg f "$v"; ic f HDR; ins f "i32.add"; mem f "i64.load"; ls f "$b"
    lg f "$b"; ins f "i32.wrap_i64"; lg f "$b"; lc f 32L; ins f "i64.shr_u"; ins f "i32.wrap_i64"; ins f "i32.xor"; ins f "return"
    endB f
    if gc then
        // walk the payload words via the tid table (see $cmpv): a header whose
        // tid is outside the table means a raw even int -> identity hash
        gg f "$roots"; ic f (4 * gcCmpTblSlot); ins f "i32.add"; mem f "i32.load"; ls f "$tbl"
        lg f "$cid"; ic f 1; ins f "i32.and"
        lg f "$cid"; ic f 1; ins f "i32.shr_u"; lg f "$tbl"; ic f 4; ins f "i32.add"; mem f "i32.load"; ins f "i32.lt_u"
        ins f "i32.and"; ins f "i32.eqz"
        ifE f; lg f "$v"; ins f "return"; endB f
        lg f "$cid"; ic f 1; ins f "i32.shr_u"; ls f "$tid"
        lg f "$tbl"; ic f 8; ins f "i32.add"; lg f "$tid"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$r"
        // PACKED SCALAR ARRAY sentinel: an array's hash is its LENGTH
        // (DIVERGENCES.md) — the walk below would hash the contents (a
        // mutated array then changed its hash) or read f64 payload halves
        lg f "$r"; ic f 0x3FF; ins f "i32.and"; ic f 0x3FF; ins f "i32.eq"
        ifE f; lg f "$v"; ic f 4; ins f "i32.add"; mem f "i32.load"; ins f "return"; endB f
        lg f "$r"; ic f 0x3FF; ins f "i32.and"; ls f "$tot"
        lg f "$r"; ic f 10; ins f "i32.shr_u"; ls f "$st"
        ic f 0; ls f "$h"
        ic f 1; ls f "$w"
        blockE f "$td"; loopE f "$tgo"
        lg f "$w"; lg f "$tot"; ins f "i32.ge_s"; brIf f "$td"
        lg f "$st"; lg f "$w"; ins f "i32.shr_u"; ic f 1; ins f "i32.and"
        ifE f
        lg f "$v"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; callf f "$hashv"; ls f "$r"
        elseB f
        lg f "$v"; lg f "$w"; ic f 2; ins f "i32.shl"; ins f "i32.add"; mem f "i32.load"; ls f "$r"
        endB f
        lg f "$h"; ic f 31; ins f "i32.mul"; lg f "$r"; ins f "i32.add"; ls f "$h"
        lg f "$w"; ic f 1; ins f "i32.add"; ls f "$w"
        br f "$tgo"; endB f; endB f
        lg f "$h"; ins f "return"
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
    // A var only needs a cell when it is CAPTURED by a lambda nested inside its
    // OWN binding scope. `depth` is lambda-nesting from the top; comparing a
    // use's depth to the binder's catches capture. A GLOBAL depth test was
    // wrong: a var bound AND used at the same depth inside a nested function
    // (every `let rec … and` member is one) read as captured, so an ordinary
    // loop counter became a heap cell and its `<-` never reached the condition.
    let bindDepth = dictNew<string, int> ()
    let deeper (v : VarId) (depth : int) : bool =
        match dictTryFind bindDepth (key v) with Some d -> depth > d | None -> depth > 0
    let rec go (depth : int) (e : Expr) : unit =
        let g = go depth
        match e with
        | EVar (v, _) | EVarI (v, _, _) -> if deeper v depth then dictSet inLambda (key v) true
        | ELam (ps, b) ->
            for pv, _ in ps do dictSet bindDepth (key pv) (depth + 1)
            go (depth + 1) b
        | EAssign (v, x) ->
            dictSet assigned (key v) true
            (if deeper v depth then dictSet inLambda (key v) true)
            g x
        | ELet (_, v, _, EApp (EUnknown "$forcecell", [ r ]), b) ->
            dictSet letBound (key v) true; dictSet bindDepth (key v) depth; dictSet assigned (key v) true; dictSet inLambda (key v) true; g r; g b
        | ELet (_, v, _, r, b) -> dictSet letBound (key v) true; dictSet bindDepth (key v) depth; g r; g b
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

// the ref-kind of each cell var's held value, from the INIT value it is bound to
// (the same kind lowLetBind gives the cell at creation). A whole-program pass, so
// a `$cellget` reads the right kind even when the cell is created in a function
// emitted AFTER the one that reads it (a class-level `let mutable` read across
// members). Without this a mutable int read into a record field defaulted to the
// tagged form and its even value was chased as a pointer.
let private cellKindScan (decls : Decl list) (cells : Dict<string, bool>) : Dict<string, RefKind> =
    let out = dictNew<string, RefKind> ()
    let rec go (e : Expr) : unit =
        (match e with
         | ELet (_, v, sch, rhs, _) when (dictTryFind cells (key v)).IsSome ->
             let init = match rhs with EApp (EUnknown "$forcecell", [ r ]) -> r | _ -> rhs
             // MUST match lowLetBind: the declared type is authoritative for
             // raw-vs-ref, falling back to the initialiser only when it is generic
             dictSet out (key v) (match refKindOfTy sch.Body with RKGen -> refKindOfExpr init | k -> k)
         | _ -> ())
        match e with
        | ELet (_, _, _, r, b) -> go r; go b
        | ELam (_, b) -> go b
        | EApp (f, args) -> go f; List.iter go args
        | EIf (a, b, c) -> go a; go b; go c
        | EMatch (s, cs) | ETry (s, cs) -> go s; for _, gd, bb in cs do (match gd with Some g -> go g | None -> ()); go bb
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) -> List.iter go xs
        | ERecord (_, fs) -> for _, x in fs do go x
        | ERecordExt (_, bb, fs) -> go bb; (for _, x in fs do go x)
        | EField (r, _, _) -> go r
        | EFieldSet (r, _, _, x) -> go r; go x
        | EWhile (c, b) -> go c; go b
        | EAssign (_, x) -> go x
        | EIndex (_, a, i) -> go a; go i
        | EIndexSet (_, a, i, x) -> go a; go i; go x
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) | ECast (_, a, _) | ETypeTest (_, a) -> go a
        | EArrayCreate (_, a, b) -> go a; go b
        | EIfaceCall (_, _, recv, args) -> go recv; List.iter go args
        | _ -> ()
    for d in decls do match d with DLet (_, _, _, e) -> go e | _ -> ()
    out

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
let private freeVars (st : St) (bound : Dict<string, bool>) (body : Expr) : (string * int * Type) list =
    let acc = vecNew<string * int * Type> ()
    let seen = dictNew<string, bool> ()
    let rec go (bnd : Dict<string, bool>) (e : Expr) : unit =
        match e with
        | EVar (v, sch) | EVarI (v, sch, _) ->
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
                vecAdd acc (v.Path, v.Offset, sch.Body)
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
                // an assigned mutable is captured as its shared CELL pointer — a
                // reference; the recorded type only needs to classify non-raw.
                vecAdd acc (v.Path, v.Offset, TCon ("obj", []))
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
// a string literal in a match PATTERN interns like one in an expression:
// lowPatTest compares through lowStrConst, and a constant first seen at
// LOWERING time lands past the baked $hp — the first allocation overwrites
// it and the pattern silently stops matching (found by the dom gate's
// `match tagName with "CANVAS"`, whose literal appears ONLY in patterns)
let rec private scanPatConsts (st : St) (p : Pat) : unit =
    match p with
    | PLit (LString s) -> (if gc then internStrGc st s else internStr st s) |> ignore
    | PAs (q, _, _) -> scanPatConsts st q
    | PCtor (_, _, subs) | PTuple subs | PListLit subs | POr subs -> for q in subs do scanPatConsts st q
    | PCons (a, b) -> scanPatConsts st a; scanPatConsts st b
    | _ -> ()

let rec private scanConsts (st : St) (e : Expr) : unit =
    match e with
    | ELit (LString s) -> (if gc then internStrGc st s else internStr st s) |> ignore
    | ELet (_, _, _, a, b) | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> scanConsts st a; scanConsts st b
    | EIf (a, b, c) | EIndexSet (_, a, b, c) -> scanConsts st a; scanConsts st b; scanConsts st c
    | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> for x in xs do scanConsts st x
    // the function position matters: an eta-expansion lambda lives there and
    // may hold string literals (a missed one is interned late, past $hp, and
    // the first allocation overwrites it)
    | EApp (EUnknown "printb", xs) ->
        // printb spells its booleans out at emission time — intern the two
        // words HERE or (standalone) they land past the baked $hp
        (if gc then internStrGc st "\"True\"" |> ignore else internStr st "\"True\"" |> ignore)
        (if gc then internStrGc st "\"False\"" |> ignore else internStr st "\"False\"" |> ignore)
        for x in xs do scanConsts st x
    | EApp (g, xs) -> scanConsts st g; for x in xs do scanConsts st x
    | EAssign (_, r) | EField (r, _, _) | EArrayLen (_, r) | ECast (_, r, _) | ETypeTest (_, r) -> scanConsts st r
    | EFieldSet (r, _, _, v) -> scanConsts st r; scanConsts st v
    | ELam (_, b) -> scanConsts st b
    | EMatch (s, cs) -> scanConsts st s; for p, g, b in cs do scanPatConsts st p; (match g with Some x -> scanConsts st x | None -> ()); scanConsts st b
    | ERecord (_, fs) -> for _, v in fs do scanConsts st v
    | ERecordExt (_, b, fs) -> scanConsts st b; for _, v in fs do scanConsts st v
    | EIfaceCall (_, _, r, xs) -> scanConsts st r; for x in xs do scanConsts st x
    | ETry (b, cs) -> scanConsts st b; for p, g, x in cs do scanPatConsts st p; (match g with Some y -> scanConsts st y | None -> ()); scanConsts st x
    | _ -> ()

// a reference-map hash over lambda nodes, keyed by the bound param's offset
// the function currently being emitted, for SELF-tail-call detection: its
// wasm name, its result LTy, and (gc) the register holding the ENTRY $sp —
// return_call skips every pop between here and the epilogue, so the emitter
// restores $sp wholesale first
let mutable private tailFnName : string = ""
let mutable private tailFnRet : LTy = W
let mutable private tailSpReg : int = -1

let rec private markTails (st : St) (e : Expr) : unit =
    match e with
    | EApp (_, _) -> refMapSet st.TailApp e true
    | ELet (_, _, _, _, b) -> markTails st b
    | ESeq xs -> (match List.tryLast xs with Some x -> markTails st x | None -> ())
    | EIf (_, t, el) -> markTails st t; markTails st el
    | EMatch (_, cs) -> for _, _, b in cs do markTails st b
    | _ -> ()

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
      // in a generic function: its quantified type-var id -> the register of the
      // hidden witness-pointer param for that type. A generic aggregate reads the
      // element type's witness through here to pick its GC scan map.
      Witness : Dict<int, int>
      /// while emitting a Canon generic class' constructor: the class-param
      /// witness var-ids in declared order (= this ctor's witnessVars). The
      /// class ERecord it builds stores `ctx.Witness[each]` into trailing slots.
      mutable ClassCtorWits : int list
      /// in a stamped member with exactly ONE class type param: the register
      /// holding that param's witness. A compare/hash whose operands are generic
      /// fields (EField/EIndex of type `'k`) carries no bare type-var expr for
      /// tyVarIdOfExpr to key on, so it falls back to this unambiguous witness.
      mutable ClassWit : int option
      /// while emitting a lifted lambda body whose env is rooted on the shadow
      /// stack: the stable ADDRESS of the env's root slot (`$roots + $sp@entry`).
      /// Capture reads dereference `[EnvAddr]` so a GC that relocates the env
      /// mid-body is seen — the wasm-local `EnvReg` would go stale. None when the
      /// env is not rooted (no captures, or a top-level function).
      mutable EnvAddr : LExpr option
      /// GC: ref-typed locals rooted on the shadow stack for their scope. Maps a
      /// var key to the STABLE address of its root slot; reads/writes go through
      /// `[addr]` so a collection that relocates the value mid-scope is seen. A
      /// pointer local live across a safepoint (a for-loop's list cursor across
      /// its body's cons alloc, say) would otherwise be left stale in its wasm
      /// local — the collector never scans a wasm local. Only RKRef, non-cell,
      /// non-scalar locals are slotted; the value is a genuine pointer so the
      /// scanner (which skips odd/tagged words) traces it correctly.
      Slotted : Dict<string, LExpr>
      /// GC: generic (RKGen, type-`'a`) variables in scope whose value MIGHT be a
      /// pointer — (value register, its element witness register). A raw 'a rides
      /// an even int the pointer-scanning shadow stack would chase, so these are
      /// rooted CONDITIONALLY (only when the witness refMask says ref) across every
      /// safepoint in scope, and the register is reloaded after. The RKRef case is
      /// unconditional (Slotted); this is its generic-witness sibling.
      mutable ActiveGen : (int * int) list
      /// GC: REASSIGNED generic (`'a`) mutables that hold a ref — (value register,
      /// element witness register, slot-address register). ActiveGen's
      /// snapshot/restore would UNDO their `<-`, so instead each gets a PERSISTENT
      /// witness-conditional shadow-stack slot: pushed once at the binding (only a
      /// ref witness reserves a scanned slot; a raw 'a stays register-only), every
      /// `<-` writes through, every safepoint reloads the register from the
      /// GC-updated slot. The register stays the read home (LGet, no branch).
      mutable SlottedGen : (int * int * int) list
      mutable NReg : int }

/// ctx.Regs read WITHOUT the Dictionary indexer: under the linear
/// self-host the get_Item member call returned garbage at several
/// EMatch/binder sites while dictTryFind at the same keys answered
/// correctly (see the linear-fixpoint arc); every internal read goes
/// through this until that miscompile is found
/// Option.Value WITHOUT the member access: the stamped generic get_Value
/// (like Dictionary's get_Item) returns garbage in some linear self-host
/// contexts — patGenBinders' witOf got 0 instead of the witness register,
/// the 4-byte fixpoint diff. Plain match until the member-call miscompile
/// is found.
let private optGet (o : 'a option) : 'a =
    match o with
    | Some v -> v
    | None -> failwith "optGet: None"

let private regOf (ctx : LowCtx) (k : string) : int =
    // NOT a workaround: `.[k]` is a SEAM DIVERGENCE. Under .NET, Dict is the
    // real Dictionary (an Item indexer exists); under self-host it is the
    // bootstrap RECORD, which has none — the indexer spelling compiled as an
    // array-style read of record fields and answered garbage register ids
    // (the historical "get_Item miscompile"). dictTryFind is the seam
    // surface; use it, never `.[...]`, on bootstrap Dicts.
    match dictTryFind ctx.Regs k with
    | Some i -> i
    | None -> failwith ("regOf: no register for " + k)

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
// with (storage machine type, byte width). Since `int`/`bool`/`char` became RAW
// i32 at rest (no tag bit), they are NOT GC-safe as generic word slots — an even
// int reads as a pointer. So they store as inline scalars here, landing in the
// raw scalar prefix (records) / a FK_SCALAR_ARRAY (arrays), which the collector
// skips. float32 stores its 4-byte f32 bits in an i32 slot.
let private storLTy (k : string) : (LTy * int) option =
    match k with
    | "float" | "double" -> Some (F64, 8)
    | "int64" | "uint64" -> Some (I64, 8)
    | "float32" | "single" -> Some (W, 4)
    | "int" | "int32" | "uint32" | "nativeint" | "unativeint" | "bool" -> Some (W, 4)
    | "int16" | "uint16" -> Some (I16, 2)
    | "byte" | "sbyte" -> Some (I8, 1)
    | _ -> None
// the machine type a pre-store element value rides in before it hits its slot:
// f64/i64 stay wide; a packed narrow int or f32-bits is just an i32 word.
let private storValTy (sty : LTy) : LTy = match sty with F64 -> F64 | I64 -> I64 | _ -> W
// resolve an array-element KIND through the newtype collapse: a collapsed
// single-field record IS its field, so `F1[]` (F1 = { V : float32 }) stores
// PACKED float32 — which is what lets Array.pin + zero-copy views alias real
// scalar data (matching the wasm-GC backend's packed representations).
let rec private storKindRes (st : St) (k : string) : string =
    match dictTryFind st.Collapse k with
    | Some f ->
        (match dictTryFind st.RecFieldTypes k with
         | Some fs ->
             (match fs |> List.tryPick (fun (n, t) -> if n = f then Some t else None) with
              | Some t when t <> k -> storKindRes st t
              | _ -> k)
         | None -> k)
    | None -> k
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

// a field's slot index in its owner's layout, resolving a stamped subclass
// (which owns no field names) through the base it was stamped from.
let rec private recFieldIdxOpt (st : St) (owner : string) (fname : string) : int option =
    let viaBase () = match dictTryFind st.RecBase owner with Some b when b <> owner -> recFieldIdxOpt st b fname | _ -> None
    match dictTryFind st.RecFields owner with
    | Some order -> (match List.tryFindIndex (fun x -> x = fname) order with Some i -> Some i | None -> viaBase ())
    | None -> viaBase ()

let rec private recFieldIdx (st : St) (owner : string) (fname : string) : int =
    match recFieldIdxOpt st owner fname with Some i -> i | None -> 0

// the slot index with LOST-OWNER recovery: an unresolved owner falls back to
// the field NAME when exactly one record declares it. Anything else answers
// None — the ACCESS SITE then compiles to a warned, localized trap, never
// the old silent index 0 (which compiled `sch.Body` as a Quantified read
// and made the self-hosted keep/witOf lie; a whole-function gap was tried
// and too blunt — it stubbed RunGenerators for a `.Message` in a catch arm
// the self-compile never runs).
let private recFieldIdxE (st : St) (owner : string) (fname : string) : int option =
    match recFieldIdxOpt st owner fname with
    | Some i -> Some i
    | None ->
        // several owners are still UNAMBIGUOUS when they all place the field
        // at the same slot (Scheme and its stamped copies) — the read is
        // position-based, so any of them yields the same load
        match dictTryFind st.FieldOwnerOf fname with
        | Some owners ->
            (match owners |> List.choose (fun o -> recFieldIdxOpt st o fname) |> List.distinct with
             | [ i ] -> Some i
             | _ -> None)
        | None -> None

// a field's declared type, resolving a stamped subclass through its base — the
// subclass has no RecFieldTypes of its own, so a mutable scalar field (`&int`)
// would otherwise miss its RAW cell-content kind and be mishandled as a pointer.
let rec private recFieldTy (st : St) (owner : string) (fname : string) : string option =
    let viaBase () = match dictTryFind st.RecBase owner with Some b when b <> owner -> recFieldTy st b fname | _ -> None
    match dictTryFind st.RecFieldTypes owner with
    | Some fs -> (match fs |> List.tryPick (fun (fn, ty) -> if fn = fname then Some ty else None) with Some ty -> Some ty | None -> viaBase ())
    | None -> viaBase ()

// a class' fields in DECLARED order, resolving a stamped subclass through the
// base it was stamped from — the subclass owns no field names of its own, so
// its RecFields is empty and a construction that used it would store NO fields,
// leaving every slot uninitialised (a `'k[]` field then reads a garbage array).
let rec private recFieldsOf (st : St) (owner : string) : string list =
    match dictTryFind st.RecFields owner with
    | Some o when not (List.isEmpty o) -> o
    | _ -> (match dictTryFind st.RecBase owner with Some b when b <> owner -> recFieldsOf st b | _ -> [])

// the field order a `new`/`with` uses. A stamped SUBCLASS (has a RecBase entry)
// resolves through its base; anything else keeps the exact prior behaviour, so
// only subclass construction — previously storing zero fields — changes.
let private ctorOrder (st : St) (name : string) (provided : string list) : string list =
    match dictTryFind st.RecBase name with
    | Some _ -> (match recFieldsOf st name with [] -> provided | o -> o)
    | None -> (match dictTryFind st.RecFields name with Some o -> o | None -> provided)
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

// an aggregate field/slot value's GC nature, resolving a `$cellget` of a raw
// mutable cell (a captured `let mutable n = 0`) to RAW. refKindOfExpr alone sees
// the untyped cell read and defaults to RKGen, so the value rode the tagged form
// and an even int in the cell was chased as a pointer. The cell's kind was
// recorded when it was created (CellKind).
let rec private refKindOfExprC (st : St) (e : Expr) : RefKind =
    match e with
    | EApp (EUnknown "$cellget", [ c ]) ->
        let rec cellKey (ce : Expr) : string option =
            match ce with
            | EVar (v, _) | EVarI (v, _, _) -> Some (key v)
            | EApp (EUnknown "$cellof", [ inner ]) -> cellKey inner
            | _ -> None
        // a class-field cell (`$cellget(this.field)`): the field holds a byref
        // cell whose declared content type names the scalar. A concrete raw
        // scalar content (`&int`) resolves to RAW so the aggregate that stores
        // the value excludes it from its scan map. Only ever RKGen -> RKRaw for a
        // proven scalar; anything else falls back (never the reverse).
        let fieldCellKind () : RefKind option =
            match c with
            | EField (_, f, owner) ->
                match recFieldTy st owner f with
                | Some ty ->
                    let inner = if ty.StartsWith "&" then ty.Substring 1 else ty
                    if rawScalarName inner then Some RKRaw else None
                | None -> None
            | _ -> None
        match cellKey c |> Option.bind (fun k -> dictTryFind st.CellKind k) with
        | Some k -> k
        | None -> match fieldCellKind () with Some k -> k | None -> refKindOfExpr e
    | EField (_, f, owner) ->
        // a record field read `x.f` rides the FIELD's type. A concrete raw scalar
        // field (an `int` Offset, say) is RKRaw so an aggregate storing it excludes
        // it from the scan map; a ref/generic field falls back (RKGen ⇒ the uniform
        // tagged form still traces an even pointer correctly). Fixes a raw int
        // field mis-traced as a pointer in a tuple/record's tagged slot.
        (match recFieldTy st owner f with
         | Some ty when rawScalarName (if ty.StartsWith "&" then ty.Substring 1 else ty) -> RKRaw
         | Some ty0 ->
             // a CONCRETE non-scalar field is a ref (or an odd-tagged word,
             // which the shadow-stack scanner skips) — classifying it RKGen
             // left `x.Field` call arguments UNROOTED across allocating
             // sibling arguments, the wandering stale-read that corrupted
             // the self-hosted linear emitter's own lowering (ctx.Regs reads
             // through a moved dict gave garbage register ids)
             let ty = if ty0.StartsWith "&" then ty0.Substring 1 else ty0
             if ty <> "" && not (ty.StartsWith "#") && not (ty.StartsWith "'") && not (ty.StartsWith "?") then RKRef
             else refKindOfExpr e
         | None -> refKindOfExpr e)
    | _ -> refKindOfExpr e

// the element witness register for a comparison of two operands whose static
// type is a type PARAMETER (so its ShOther comparison can pick raw-vs-ref at
// runtime). None outside a witnessed generic body — then $cmpv is the fallback.
let private cmpWit (ctx : LowCtx) (a : Expr) (b : Expr) : int option =
    let ofExpr e = tyVarIdOfExpr e |> Option.bind (fun vid -> dictTryFind ctx.Witness vid)
    match ofExpr a with
    | Some w -> Some w
    | None -> (match ofExpr b with Some w -> Some w | None -> ctx.ClassWit)

// for an aggregate allocated inside a GENERIC body, the (slot index, witness
// register) of each slot whose static type is a type PARAMETER whose witness

// int/bool/char are RAW i32 at rest (locals, params, returns, value stack) —
// full 32-bit, no tag. lowTag/lowUntag convert to/from the tagged immediate
// (2n+1) that a GC-scanned uniform slot needs to tell an int from a pointer.
let private lowInt (n : int) : LExpr = LConstW n
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
    // `0x`/`0X` is hex — without this every hex literal (`0x7f`, `0x40`) parsed
    // as 0, so e.g. the LEB128 encoder's `v &&& 0x7f` became `v &&& 0` and its
    // loop never terminated (a runaway when the self-hosted compiler ran it).
    let isHex = strLen s > start + 1 && charAt s start = '0' && (charAt s (start + 1) = 'x' || charAt s (start + 1) = 'X')
    let mutable acc = 0
    let mutable i = if isHex then start + 2 else start
    let mutable go = true
    while go && i < strLen s do
        let c = charAt s i
        if c = '_' then i <- i + 1   // digit separator
        else
            let d =
                if c >= '0' && c <= '9' then int c - int '0'
                elif isHex && c >= 'a' && c <= 'f' then int c - int 'a' + 10
                elif isHex && c >= 'A' && c <= 'F' then int c - int 'A' + 10
                else -1
            // a non-digit ends the number: it is a type suffix (`100s`, `0x2Auy`)
            if d < 0 then go <- false
            else (acc <- (if isHex then acc * 16 else acc * 10) + d; i <- i + 1)
    if neg then 0 - acc else acc
let private parseI64Lit (s : string) : int64 =
    let neg = strLen s > 0 && charAt s 0 = '-'
    let start = if neg then 1 else 0
    let isHex = strLen s > start + 1 && charAt s start = '0' && (charAt s (start + 1) = 'x' || charAt s (start + 1) = 'X')
    let mutable acc = 0L
    let mutable i = if isHex then start + 2 else start
    let mutable go = true
    while go && i < strLen s do
        let c = charAt s i
        if c = '_' then i <- i + 1
        else
            let d =
                if c >= '0' && c <= '9' then int c - int '0'
                elif isHex && c >= 'a' && c <= 'f' then int c - int 'a' + 10
                elif isHex && c >= 'A' && c <= 'F' then int c - int 'A' + 10
                else -1
            // a non-digit ends the number: an `L`/`l` int64 suffix or a type tag
            if d < 0 then go <- false
            else (acc <- (if isHex then acc * 16L else acc * 10L) + int64 d; i <- i + 1)
    if neg then 0L - acc else acc
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
    // a float16 is its 16 raw BITS in a word — comparing those bits orders
    // wrongly (and calls -0.0h <> 0.0h), so it widens before comparing
    | ShHalf
    | ShList of CmpShape | ShArr of CmpShape | ShTup of CmpShape list | ShOther

let rec private shapeOfType (t : Type) : CmpShape =
    match prune t with
    | TTuple ts -> ShTup (List.map shapeOfType ts)
    | TCon (n, _) when n.StartsWith "$tup" -> ShOther
    | TCon ("string", _) -> ShStr
    | TCon ("float16", _) -> ShHalf
    | TCon (("float" | "double" | "single" | "float32"), _) -> ShFloat
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

// ---- inline value layout (.NET-parity, value-witness groundwork) ----------
// The bytes a VALUE of a type occupies when stored INLINE — no heap box, no
// per-value header. `Size`/`Align` follow .NET SEQUENTIAL struct layout:
// declaration order, each field on its natural alignment, the whole padded to
// the struct's alignment — the SAME rule the ABI parity harness pins against a
// real C compiler (tests/tooling/abi). `RefMask` bit i set = word i (4 bytes)
// of the value is a GC pointer the collector must trace; every other word is
// raw scalar bytes it skips. `Generic = true` marks a type whose layout is not
// known statically (a type parameter or a field typed by one): a runtime
// value-witness supplies it and Size/Align/RefMask are meaningless. A reference
// type — string, list, array, closure, a reference tuple, a heap union or a
// NON-struct record — is one pointer word {4,4,ref}.
//
// This is the single source of truth for inline .NET-parity layout. RecPod's
// current scalars-first packing is a separate, pre-parity scheme (it reorders
// fields and does not size `int`); the inline-value rewrite reconciles RecPod
// TO this. Nothing consumes `layoutOf` yet — it is groundwork.
type Layout = { Size : int; Align : int; RefMask : uint64; Generic : bool }

let private layRoundUp (n : int) (a : int) : int = if a <= 1 then n else (n + a - 1) / a * a
let private layRefWord = { Size = 4; Align = 4; RefMask = 1UL; Generic = false }
let private layWitness = { Size = 0; Align = 0; RefMask = 0UL; Generic = true }
let private layScalar (b : int) : Layout = { Size = b; Align = b; RefMask = 0UL; Generic = false }

// primitive value types at their .NET widths: byte/bool = 1, char/int16 = 2
// (char is UTF-16), int/float32 = 4, int64/float = 8. Not a primitive -> None.
let private layPrim (nm : string) : Layout option =
    match nm with
    | "bool" | "byte" | "sbyte" -> Some (layScalar 1)
    | "int16" | "uint16" | "char" -> Some (layScalar 2)
    | "int" | "int32" | "uint32" | "nativeint" | "unativeint" | "float32" | "single" -> Some (layScalar 4)
    | "int64" | "uint64" | "float" | "double" -> Some (layScalar 8)
    | "unit" -> Some { Size = 0; Align = 1; RefMask = 0UL; Generic = false }
    | _ -> None

let private layStripGen (nm : string) : string =
    let a = nm.IndexOf "$<"
    let nm = if a >= 0 then nm.Substring (0, a) else nm
    let b = nm.IndexOf "<"
    if b >= 0 then nm.Substring (0, b) else nm

// sequential .NET layout of an ordered list of already-computed field layouts.
let private laySeq (fields : Layout list) : Layout =
    let mutable off = 0
    let mutable align = 1
    let mutable mask = 0UL
    let mutable generic = false
    for l in fields do
        if l.Generic then generic <- true
        let a = if l.Align < 1 then 1 else l.Align
        off <- layRoundUp off a
        if l.RefMask <> 0UL then mask <- mask ||| (l.RefMask <<< (off / 4))
        off <- off + l.Size
        if a > align then align <- a
    if generic then layWitness
    else { Size = layRoundUp off align; Align = align; RefMask = mask; Generic = false }

// `resolve name` -> a STRUCT record's declared fields in order, or None for a
// reference type (its presence IS the struct-vs-reference distinction). Pure —
// takes `resolve` rather than St, so it unit-tests without one.
let rec layoutOfWith (resolve : string -> (string * string) list option) (t : Type) : Layout =
    match prune t with
    | TVar _ -> layWitness
    | TFun _ -> layRefWord
    | TApp (h, _) -> layoutOfWith resolve h
    | TTuple _ -> layRefWord                       // reference tuple: a heap pointer
    | TCon (n, args) when n.StartsWith "StructTuple" ->
        laySeq (args |> List.map (layoutOfWith resolve))       // value tuple: inline
    | TCon (n, _) -> layByName resolve n

and private layByName (resolve : string -> (string * string) list option) (nm0 : string) : Layout =
    let nm = layStripGen nm0
    if nm = "?" || (nm.Length > 0 && nm.[0] = '\'') then layWitness   // a type parameter
    else
        match layPrim nm with
        | Some l -> l
        | None ->
            match resolve nm with
            | Some fields -> laySeq (fields |> List.map (fun (_, ty) -> layByName resolve ty))
            | None -> layRefWord

// the inline layout of a value of `t` in the context of a program's St: a
// struct record resolves to its declared fields, everything else is primitive
// / reference / generic as above.
let private layoutOf (st : St) (t : Type) : Layout =
    layoutOfWith (fun n -> dictTryFind st.RecFieldTys n) t

// intern a {size,align,refMask} witness (deduped into the static g_witnesses
// pool) and return a runtime pointer to it: $witnesses + offset.
let private witnessPtrRM (st : St) (size : int) (align : int) (refMask : int) : LExpr =
    let k = string size + ":" + string align + ":" + string refMask
    let off =
        match dictTryFind st.Witnesses k with
        | Some o -> o
        | None ->
            let o = st.WitnessCur
            st.WitnessCur <- o + 12
            dictSet st.Witnesses k o
            vecAdd st.WitnessData (o, size, align, refMask)
            o
    LPrim (AddW, [ LGetGlobal "$witnesses"; LConstW off ])

// a concrete type's witness from its layout.
let private witnessPtr (st : St) (t : Type) : LExpr =
    let l = layoutOf st t
    witnessPtrRM st l.Size l.Align (int l.RefMask)

// the witness a call must pass for one type-arg NAME (from EVarI.inst):
// - "#N": forward the enclosing function's witness param for type-var N
// - concrete: a 1-word element, ref iff the name is not a raw scalar (int/bool/
//   char are unboxed → refMask 0; everything else is a pointer → refMask 1).
//   Multi-word inline struct elements are a later step.
let private witnessArgOfName (ctx : LowCtx) (nm : string) : LExpr =
    if nm.Length > 0 && nm.[0] = '#' then
        match dictTryFind ctx.Witness (int (nm.Substring 1)) with
        | Some reg -> LGet (wReg reg)
        | None -> witnessPtrRM ctx.LSt 4 4 1
    else
        witnessPtrRM ctx.LSt 4 4 (if rawScalarName (layStripGen nm) then 0 else 1)

// A witness LExpr for a GENERIC aggregate slot, so lowObjR takes the precise
// refoffs path (a raw element excluded, a ref included) rather than the tagged
// fallback that mis-traces even words. Resolved from whichever source applies:
// a type var's method/class witness (ctx.Witness), the call's instantiation
// (EVarI.inst), or a statically concrete type/field/element (a constant witness
// carrying that type's refMask). None only when NO source has one — a genuine
// value-witness ABI gap that lowObjR then logs.
let rec private slotWitness (ctx : LowCtx) (e : Expr) : LExpr option =
    let st = ctx.LSt
    let ofName (nm : string) = witnessPtrRM st 4 4 (if rawScalarName (layStripGen nm) then 0 else 1)
    let ofTy (t : Type) : LExpr option =
        match prune t with
        | TVar tv -> (match dictTryFind ctx.Witness tv.Id with Some r -> Some (LGet (wReg r)) | None -> None)
        | TCon (n, _) -> Some (ofName n)
        | TApp (h, _) ->
            (match prune h with
             | TVar tv -> (match dictTryFind ctx.Witness tv.Id with Some r -> Some (LGet (wReg r)) | None -> None)
             | _ -> Some (witnessPtrRM st 4 4 1))
        | _ -> None
    match e with
    | EVar (_, s) | EVarI (_, s, _) -> ofTy s.Body
    // an immediately-applied lambda rides its BODY's result type
    | EApp (ELam (_, body), _) -> slotWitness ctx body
    // a builtin conversion/op: classify by the result type its name implies —
    // int/char/bool are raw scalars, string/substring/cell/float build a ref
    | EApp (EUnknown u, _) ->
        let baseU = (let i = u.IndexOf '#' in if i >= 0 then u.Substring (0, i) else u)
        if baseU = "int" || baseU = "char" || baseU = "bool" || baseU = "byte" then Some (witnessPtrRM st 4 4 0)
        elif baseU = "string" || baseU.StartsWith "$str" || baseU = "$cellof" || baseU = "float" || baseU = "int64" then Some (witnessPtrRM st 4 4 1)
        else None
    | EApp (((EVar (_, s) | EVarI (_, s, _)) as hd), ar) ->
        let rec pl t n = if n <= 0 then t else (match prune t with TFun (_, r) -> pl r (n - 1) | _ -> t)
        (match prune (pl s.Body (List.length ar)) with
         | TVar rv ->
             // the result rides a type var: its witness is the one the call passed
             // for that var, positional to the callee's Quantified via EVarI.inst.
             (match hd with
              | EVarI (_, sch, inst) ->
                  (match List.tryFindIndex (fun (qv : Var) -> qv.Id = rv.Id) sch.Quantified with
                   | Some k -> (match List.tryItem k inst with Some nm -> Some (witnessArgOfName ctx nm) | None -> None)
                   | None -> (match dictTryFind ctx.Witness rv.Id with Some r -> Some (LGet (wReg r)) | None -> None))
              | _ -> (match dictTryFind ctx.Witness rv.Id with Some r -> Some (LGet (wReg r)) | None -> None))
         | t -> ofTy t)
    | EField (_, f, owner) -> (match recFieldTy st owner f with Some ty -> Some (ofName (if ty.StartsWith "&" then ty.Substring 1 else ty)) | None -> None)
    | EIndex (k, _, _) -> Some (ofName k)
    | ECast (t, _, _) -> Some (ofName t)
    | EPrim (op, _) ->
        // the result TYPE gives raw-vs-ref with no per-op tables: a string concat /
        // list append builds a heap value (ref); a string comparison is a bool (raw).
        if op = "+t" || op = "@" || op = "::" then Some (witnessPtrRM st 4 4 1)
        elif op.StartsWith "=" || op.StartsWith "<" || op.StartsWith ">" || op = "u-" || op = "unot" || op.StartsWith "u~" || op = "not" then Some (witnessPtrRM st 4 4 0)
        else None
    | EIf (_, a, b) -> (match slotWitness ctx a with Some w -> Some w | None -> slotWitness ctx b)
    | EMatch (_, cs) | ETry (_, cs) -> cs |> List.tryPick (fun (_, _, b) -> slotWitness ctx b)
    | ELet (_, _, _, _, b) -> slotWitness ctx b
    | _ -> (match tyVarIdOfExpr e |> Option.bind (fun vid -> dictTryFind ctx.Witness vid) with Some r -> Some (LGet (wReg r)) | None -> None)

// per-slot witness for a generic aggregate: an RKGen slot gets one from
// slotWitness; a resolved (RKRaw/RKRef) slot needs none. `base_` is the slot
// index of exprs.[0] (0 for a tuple/record, 1 past a union's raw tag).
let private genWitsOf (ctx : LowCtx) (base_ : int) (exprs : Expr list) : (int * LExpr) list =
    if not gc then [] else
    exprs
    |> List.mapi (fun j e ->
        match refKindOfExprC ctx.LSt e with
        | RKGen -> (match slotWitness ctx e with Some w -> Some (base_ + j, w) | None -> None)
        | _ -> None)
    |> List.choose id

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
    | ELit (LFloat s) when s.EndsWith "h" || s.EndsWith "H" -> ShHalf
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
    // an array length is always `int` — a KNOWN scalar. Without this it is
    // ShOther, so `count >= arr.Length` mergeShapes to ShOther and routes to
    // $cmpv on two RAW ints, which the linear backend cannot dereference.
    | EArrayLen _ -> ShScalar
    // arithmetic on raw ints yields a raw int, comparisons yield a raw bool.
    // Without this `pos + n > cap` (a class-field sum) was ShOther and went
    // to $cmpv on two RAW ints — cmpv read the even words as heap headers,
    // answered garbage, Buffer.Reserve never grew, and the next write ran
    // past the buffer into the neighbouring allocation.
    | EPrim (op, _) when not (op.Contains "@") ->
        // ONLY the raw-scalar results: an unsuffixed comparison yields a raw
        // bool, unsuffixed/w-suffixed arithmetic a raw int. Suffixed float/
        // int64/string ops stay ShOther — their operands may ride raw f64/i64
        // rails, which the ShFloat/ShInt64 struct-compare (a boxed-heap load)
        // must never see; $cmpv handled them before and still does.
        (match op with
         | "<" | ">" | "<=" | ">=" | "=" | "<>" -> ShScalar
         | "&&" | "||" | "not" -> ShScalar
         | "+" | "-" | "*" | "/" | "%" | "&&&" | "|||" | "^^^" | "<<<" | ">>>" -> ShScalar
         | _ when strLen op >= 2 && charAt op (strLen op - 1) = 'w' &&
                  (match baseOp op with
                   | "+" | "-" | "*" | "/" | "%" | "<<<" | ">>>" | "<" | ">" | "<=" | ">=" | "=" | "<>" -> true
                   | _ -> false) -> ShScalar
         | _ -> ShOther)
    | _ -> ShOther

// shapeOfExpr, but resolving a class FIELD's / array ELEMENT's declared type
// through st. EField/EIndex carry no type, so a compare of two concrete scalar
// fields (BoxI's `a < b` on int fields) would otherwise be ShOther and route to
// $cmpv on raw ints, which the tid heuristic mis-handles. A generic field/'k[]
// element stays "?"/'k -> ShOther and is served by the witness path instead.
let private shapeOfExprF (st : St) (e : Expr) : CmpShape =
    let ofTyName (ty : string) : CmpShape =
        let inner = if ty.StartsWith "&" then ty.Substring 1 else ty
        if rawScalarName inner then ShScalar elif inner = "string" then ShStr else ShOther
    match e with
    | EField (_, f, owner) -> (match recFieldTy st owner f with Some ty -> ofTyName ty | None -> ShOther)
    | EIndex (ek, _, _) -> ofTyName ek
    // a builtin conversion names its RESULT before the '#' — `compare
    // (sbyte -5) (sbyte 7)` routed to $cmpv on two RAW ints without this
    | EApp (EUnknown n, _) when n.Contains "#" && not (n.StartsWith "$") ->
        ofTyName (n.Substring (0, n.IndexOf "#"))
    | _ -> shapeOfExpr e

let rec private mergeShape (a : CmpShape) (b : CmpShape) : CmpShape =
    match a, b with
    | ShOther, x | x, ShOther -> x
    | ShTup xs, ShTup ys when List.length xs = List.length ys -> ShTup (List.map2 mergeShape xs ys)
    | ShList x, ShList y -> ShList (mergeShape x y)
    | ShArr x, ShArr y -> ShArr (mergeShape x y)
    | _ -> a

let private needsStructCmp (sh : CmpShape) : bool =
    match sh with
    | ShStr | ShFloat | ShInt64 | ShHalf | ShList _ | ShArr _ | ShTup _ -> true
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
        | "float16" -> ShHalf
        | "float" | "double" | "single" | "float32" -> ShFloat
        | "int64" | "uint64" -> ShInt64
        | "int" | "int32" | "uint32" | "char" | "bool" | "byte" | "sbyte" | "int16" | "uint16" | "nativeint" -> ShScalar
        | "list" | "seq" | "[]" -> ShList ShOther
        | "array" -> ShArr ShOther
        | _ -> ShOther

// compare two operand WORDS by their static shape -> a raw -1/0/1 LExpr. Scalars
// compare their tagged payloads; strings/lists/arrays go through the runtime
// helpers; a tuple is unrolled element by element (reading HDR+4*i), recursing
// and short-circuiting on the first difference.
let rec private structCmpW (ctx : LowCtx) (sh : CmpShape) (wa : LExpr) (wb : LExpr) (wit : int option) : LExpr =
    match sh with
    | ShScalar ->
        LPrim (SubW, [ LPrim (GtSW, [ wa; wb ]); LPrim (LtSW, [ wa; wb ]) ])
    // an opaque operand (a generic HOF's element, type unknown here). With the
    // element WITNESS in scope, branch on its refMask: a RAW element (int/bool/
    // char — an even word under the raw-int model) compares its words DIRECTLY;
    // $cmpv would read an even int as a heap header and index the shape table at
    // `$tbl + 8 + 4*tid` out of bounds. A REF element is a pointer -> $cmpv, the
    // self-describing comparator (ints-as-tagged, strings, float, compounds).
    | ShOther ->
        (match wit with
         | Some w ->
             let t = freshTmp ctx
             LDo ([ LIf (LPrim (EqW, [ LLoad (W, LGet (wReg w), 8); LConstW 0 ]),
                         [ LSet (wReg t, LPrim (SubW, [ LPrim (GtSW, [ wa; wb ]); LPrim (LtSW, [ wa; wb ]) ])) ],
                         [ LSet (wReg t, LCall ("$cmpv", [ wa; wb ])) ]) ],
                   LGet (wReg t))
         | None -> LCall ("$cmpv", [ wa; wb ]))
    | ShStr -> LCall ("$str_cmp", [ wa; wb ])
    | ShFloat ->
        LPrim (SubW, [ LPrim (GtF, [ LLoad (F64, wa, HDR); LLoad (F64, wb, HDR) ]); LPrim (LtF, [ LLoad (F64, wa, HDR); LLoad (F64, wb, HDR) ]) ])
    | ShInt64 ->
        LPrim (SubW, [ LPrim (GtSL, [ LLoad (I64, wa, HDR); LLoad (I64, wb, HDR) ]); LPrim (LtSL, [ LLoad (I64, wa, HDR); LLoad (I64, wb, HDR) ]) ])
    | ShHalf ->
        let da = LPrim (PromF, [ LCall ("$h2f", [ wa ]) ])
        let db = LPrim (PromF, [ LCall ("$h2f", [ wb ]) ])
        LPrim (SubW, [ LPrim (GtF, [ da; db ]); LPrim (LtF, [ da; db ]) ])
    | ShTup shapes ->
        let ra = freshTmp ctx
        let rb = freshTmp ctx
        let r = freshTmp ctx
        let elemCmp i shi = structCmpW ctx shi (LLoad (W, LGet (wReg ra), HDR + 4 * i)) (LLoad (W, LGet (wReg rb), HDR + 4 * i)) None
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
            [ LSet (wReg r, structCmpW ctx esh (LLoad (W, LGet (wReg pa), HDR)) (LLoad (W, LGet (wReg pb), HDR)) None)
              LIf (LPrim (EqW, [ LGet (wReg r); LConstW 0 ]),
                   [ LSet (wReg pa, LLoad (W, LGet (wReg pa), HDR + 4)); LSet (wReg pb, LLoad (W, LGet (wReg pb), HDR + 4)) ], []) ]
        LDo ([ LSet (wReg pa, wa); LSet (wReg pb, wb); LSet (wReg r, LConstW 0)
               LWhile (cond, body)
               LIf (LPrim (EqW, [ LGet (wReg r); LConstW 0 ]),
                    [ LSet (wReg r, LPrim (SubW, [ notNil pa; notNil pb ])) ], []) ],
             LGet (wReg r))
    | ShArr _ ->
        // ARRAYS compare by IDENTITY — a chosen divergence (DIVERGENCES.md):
        // equal only to themselves, ordered by address. The old element-wise
        // walk here both violated that and mis-strode packed arrays (a float
        // array's f64 halves read as 4-byte elements faulted).
        LPrim (SubW, [ LPrim (GtUW, [ wa; wb ]); LPrim (LtUW, [ wa; wb ]) ])

// Should this `let`-bound var be rooted on the shadow stack for its scope? Only
// a genuine pointer (RKRef) that is NOT a cell (cells are heap boxes with their
// own rooting) and NOT an unboxed scalar (those ride typed locals the GC never
// scans). Its value is even/pointer, so the odd-tag-skipping root scanner traces
// it correctly. Gated on gc — the standalone backend has no collector.
// Lower's desugar temps whose values are HEAP REFS by construction: the
// list-walk cursor/tail, the for-in array, the pattern-lambda scrutinee, the
// slice/range temporaries. Their schemes are the anonymous `?` (the desugar
// has no type to write), which classifies RKGen — but the values are always
// pointers, so they must be rooted like any other ref let-binder.
let private desugarRefTemps =
    Set.ofList [ "_rest"; "_tail"; "_arr"; "_arg"; "_ssrc"; "_sdst"; "_wdst"; "_wsrc"; "_rout" ]
/// FPP_CONSCHECK debug: trap when a REF-looking value (even, nonzero) about
/// to be STORED is not in the current allocation space — catches a stale
/// pointer at the write that resurrects it, with the writer in the backtrace.
// function-position on purpose: a TOP-LEVEL env read became a trapping
// stub INIT on the wasm-GC backend under self-host (BinDriver stubs value
// inits with unreachable; every probe precedent reads the env inline)
let private consCheckOn () = System.Environment.GetEnvironmentVariable "FPP_CONSCHECK" = "1"
let private chkStoreStmts (reg : int) : LStmt list =
    if consCheckOn () then
        [ LIf (LPrim (EqW, [ LPrim (AndW, [ LGet (wReg reg); LConstW 1 ]); LConstW 0 ]),
               [ LIf (LPrim (EqW, [ LCall ("$fpdbglive", [ LGet (wReg reg) ]); LConstW 0 ]),
                      [ LTrap ], []) ], []) ]
    else []

let private shouldSlot (ctx : LowCtx) (v : VarId) (sch : Scheme) : bool =
    gc
    && ((dictTryFind ctx.LSt.CellVars (key v)).IsSome
        // a cell var's REGISTER holds the heap cell's pointer whatever the value
        // type says — a local `let mutable` cell held across a safepoint went
        // stale and was captured into a closure env (coredump'd cell$s edge), so
        // the pointer is slotted like any other ref binder
        || ((scalarLTy sch.Body).IsNone
            && (refKindOfTy sch.Body = RKRef
                || (Set.contains v.Name desugarRefTemps && refKindOfTy sch.Body <> RKRaw))))

// The element-witness register of a generic (`'a`) variable, when the enclosing
// function threads one. A cell var carries a pointer already (Slotted-covered);
// only a bare `'a`-typed, non-cell local needs the witness-conditional rooting.
let private genWitOf (ctx : LowCtx) (v : VarId) (sch : Scheme) : int option =
    if gc && (dictTryFind ctx.LSt.CellVars (key v)).IsNone then
        match prune sch.Body with TVar tv -> dictTryFind ctx.Witness tv.Id | _ -> None
    else None

// Does `k` get REASSIGNED (`v <- …`) anywhere in `e`? A mutable generic local
// that is assigned in its own body must NOT ride ActiveGen: ActiveGen roots a
// value by SNAPSHOTTING it before a safepoint and reloading it after, which
// silently UNDOES any `<-` that ran in between — a generic `let mutable acc`
// accumulated in a `for`/`while` (List.fold, Set.ofList) then always returned
// its initial value. Such a local stays an ordinary register instead.
let rec private assignsTo (k : string) (e : Expr) : bool =
    match e with
    | EAssign (v, x) -> key v = k || assignsTo k x
    | ELet (_, _, _, r, b) -> assignsTo k r || assignsTo k b
    | ELam (_, b) -> assignsTo k b
    | EApp (f, args) -> assignsTo k f || List.exists (assignsTo k) args
    | EIf (a, b, c) -> assignsTo k a || assignsTo k b || assignsTo k c
    | EMatch (s, cs) | ETry (s, cs) -> assignsTo k s || List.exists (fun (_, g, b) -> (match g with Some g -> assignsTo k g | None -> false) || assignsTo k b) cs
    | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | EArray (_, xs) | ECtor (_, _, xs) -> List.exists (assignsTo k) xs
    | ERecord (_, fs) -> List.exists (fun (_, x) -> assignsTo k x) fs
    | ERecordExt (_, b, fs) -> assignsTo k b || List.exists (fun (_, x) -> assignsTo k x) fs
    | EField (r, _, _) -> assignsTo k r
    | EFieldSet (r, _, _, x) -> assignsTo k r || assignsTo k x
    | EWhile (c, b) -> assignsTo k c || assignsTo k b
    | EIndex (_, a, i) | EArrayCreate (_, a, i) -> assignsTo k a || assignsTo k i
    | EIndexSet (_, a, i, x) -> assignsTo k a || assignsTo k i || assignsTo k x
    | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) | ECast (_, a, _) | ETypeTest (_, a) -> assignsTo k a
    | EIfaceCall (_, _, r, args) -> assignsTo k r || List.exists (assignsTo k) args
    | _ -> false

// Wrap a safepoint-bearing expression (an allocation or a call) so every active
// generic variable is rooted across it: push its value BEFORE — but only when the
// witness refMask says the value is a pointer (a raw `'a` is an even int the
// pointer-scanning shadow stack must not chase) — and reload the register AFTER,
// so a relocation is reflected. No active generics ⇒ unchanged (the common,
// non-generic case), so the blast radius is generic functions only.
let private rootActiveGen (ctx : LowCtx) (inner : LExpr) : LExpr =
    match ctx.ActiveGen with
    | [] -> inner
    | gens ->
        let refMask w = LLoad (W, LGet (wReg w), 8)
        let res = freshTmp ctx
        let pushes = gens |> List.map (fun (r, w) ->
            LIf (LPrim (EqW, [ refMask w; LConstW 0 ]), [], gcPushStmts (LGet (wReg r))))
        let reloads = gens |> List.rev |> List.map (fun (r, w) ->
            LIf (LPrim (EqW, [ refMask w; LConstW 0 ]), [],
                 [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ]))
                   LSet (wReg r, LLoad (W, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]), 0)) ]))
        LDo (pushes @ [ LSet (wReg res, inner) ] @ reloads, LGet (wReg res))

// A reassigned generic mutable is rooted through a PERSISTENT slot instead of
// ActiveGen's clobbering snapshot. `slotGenRaw` is the guard "the witness says
// raw" — the slot is only pushed/written/reloaded/popped in the ELSE (ref) arm,
// so a raw `'a` never reaches the pointer scanner and its `<-` is register-only.
let private slotGenRaw (wit : int) : LExpr = LPrim (EqW, [ LLoad (W, LGet (wReg wit), 8); LConstW 0 ])
let private gcSlotPush (reg : int) (wit : int) (slotReg : int) : LStmt =
    LIf (slotGenRaw wit, [],
         [ LSet (wReg slotReg, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
           LStore (W, LGet (wReg slotReg), 0, LGet (wReg reg))
           LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ])
let private gcSlotPop (wit : int) : LStmt =
    LIf (slotGenRaw wit, [], [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ])) ])
// Reload each rooted register from its GC-updated slot after a safepoint (ref arm
// only). Mirrors rootActiveGen's post-reload, but there is no matching PUSH — the
// slot is persistent and kept current by every write-through, so a snapshot that
// could undo an intervening `<-` never exists.
let private reloadSlottedGen (ctx : LowCtx) (inner : LExpr) : LExpr =
    match ctx.SlottedGen with
    | [] -> inner
    | gens ->
        let res = freshTmp ctx
        let reloads = gens |> List.map (fun (reg, wit, slotReg) ->
            LIf (slotGenRaw wit, [], [ LSet (wReg reg, LLoad (W, LGet (wReg slotReg), 0)) ]))
        LDo (LSet (wReg res, inner) :: reloads, LGet (wReg res))

// the RKRef (pointer) variables a pattern binds — the match-arm analogue of a
// let-binder that must be rooted while the arm body runs (`let (a,b) = e` lowers
// to a PTuple match, and the tokenizer's `let kind, e = scanToken p` leaves the
// ref `kind` live across the allocating `scanTrailing e`). Raw/scalar binders
// and cells are excluded, as in shouldSlot.
// an ANONYMOUS binder type: a desugar that lost the real type writes `?`
// (Option .Value's payload tmp, the pattern-lambda temps). Its value may be
// a raw scalar — unconditionally rooting it as a REF let the collector's
// stale-edge tolerance NULL a live even int (witOf's witness register read
// 0: the stamped-member miscompile specimen, finally understood). These
// binders belong to the runtime-scan route (patCondBinders), never here.
let private isAnonTy (t : Type) : bool =
    match prune t with TCon ("?", []) -> true | _ -> false

let rec private patRefBinders (ctx : LowCtx) (pat : Pat) : (VarId * Scheme) list =
    let keep (v : VarId) (sch : Scheme) =
        (dictTryFind ctx.LSt.CellVars (key v)).IsNone && (scalarLTy sch.Body).IsNone
        && refKindOfTy sch.Body = RKRef && not (isAnonTy sch.Body)
    match pat with
    | PVar (v, sch) -> if keep v sch then [ v, sch ] else []
    | PAs (p, v, sch) -> (if keep v sch then [ v, sch ] else []) @ patRefBinders ctx p
    | PCtor (_, _, subs) | PTuple subs | PListLit subs -> List.collect (patRefBinders ctx) subs
    | PCons (h, tl) -> patRefBinders ctx h @ patRefBinders ctx tl
    // an or-pattern binds the SAME names in every alternative, and the binder
    // rides a register whichever alternative matched — collect from the first.
    // (`| TVar v, other | other, TVar v ->` left `other` unrooted across the
    // arm's `occurs` call; the register went stale and unify walked a moved
    // Type, the measured 16 MB fault in prune-under-adjustLevels.)
    | POr (p :: _) -> patRefBinders ctx p
    | _ -> []

// GENERIC (`'a`) pattern binders whose element witness is in scope — the arm-body
// analogue of a generic let. Each is rooted conditionally across the arm's
// safepoints (a `h::t` head held across a later allocation, say).
// GENERIC (`'a`) pattern binders whose element witness is in scope — the arm-body
// analogue of a generic let. Each is rooted conditionally across the arm's
// safepoints (a `h::t` head held across a later allocation, say).
// HISTORY: the original keep/witOf two-pass shape here mysteriously
// misbehaved under the linear self-host. The mystery is SOLVED and the
// causes are fixed — un-annotated local-lambda params were never rooted
// across safepoints (emitLambdaLow's rootArgGen), and a field access whose
// owner inference lost compiled as a SILENT index-0 read (recFieldIdxE).
// The annotated two-pass shape now fixpoints byte-exactly; this single-
// lookup form simply stays as the clearer code.
let rec private patGenBinders (ctx : LowCtx) (pat : Pat) : (VarId * int) list =
    let pick (v : VarId) (sch : Scheme) : (VarId * int) list =
        if (dictTryFind ctx.LSt.CellVars (key v)).IsSome then []
        else
            match prune sch.Body with
            | TVar tv ->
                (match dictTryFind ctx.Witness tv.Id with
                 | Some w -> [ v, w ]
                 | None -> [])
            | _ -> []
    match pat with
    | PVar (v, sch) -> pick v sch
    | PAs (p, v, sch) -> pick v sch @ patGenBinders ctx p
    | PCtor (_, _, subs) | PTuple subs | PListLit subs -> List.collect (patGenBinders ctx) subs
    | PCons (h, tl) -> patGenBinders ctx h @ patGenBinders ctx tl
    | POr (p :: _) -> patGenBinders ctx p   // same-binders-per-alternative, see patRefBinders
    | _ -> []

// Pattern binders whose static type is UNRESOLVED — not provably raw, not
// provably ref, and no witness in scope (a desugar lost the type; see the
// list-walk / pattern-lambda desugars in Lower). The binder's value came from
// a slot of the SCRUTINEE object, so the object's own scan map answers
// ref-vs-raw at runtime ($tidscans): each is rooted conditionally through the
// SlottedGen machinery with a fabricated 1-word witness. Top-level positions
// only — each carries its byte offset within the scrutinee.
let private patCondBinders (ctx : LowCtx) (pat : Pat) : (VarId * int) list =
    let st = ctx.LSt
    let dropped (v : VarId) (s : Scheme) =
        (dictTryFind st.CellVars (key v)).IsNone
        && (scalarLTy s.Body).IsNone
        && refKindOfTy s.Body <> RKRaw
        && (refKindOfTy s.Body <> RKRef || isAnonTy s.Body)
        && (match prune s.Body with TVar tv -> (dictTryFind ctx.Witness tv.Id).IsNone | _ -> true)
    let pick (off : int) (p : Pat) =
        match p with
        | PVar (v, sch) when dropped v sch -> Some (v, off)
        | _ -> None
    match pat with
    | PCons (h, t) -> List.choose id [ pick HDR h; pick (HDR + 4) t ]
    | PTuple subs -> subs |> List.mapi (fun i p -> pick (HDR + 4 * i) p) |> List.choose id
    | PCtor (_, _, subs) -> subs |> List.mapi (fun i p -> pick (HDR + 4 * (i + 1)) p) |> List.choose id
    | _ -> []

let private isSafepointNode (e : Expr) : bool =
    match e with
    | EApp _ | EIfaceCall _ | ERecord _ | ERecordExt _ | ETuple _ | ECtor _
    | EArray _ | EArrayCreate _ | EListLit _ | EPrim _
    // a field/element read of a boxed scalar allocates the box; a match/try can
    // allocate while dispatching (a compare box, a cell). Conservatively a safepoint.
    | EField _ | EIndex _ | EMatch _ | ETry _ -> true
    | _ -> false

// Root every active generic (ctx.ActiveGen) across an allocating/calling node — a
// GC there can move a REF `'a` whose register would go stale. Generic functions
// only (ActiveGen empty elsewhere). Control-flow nodes recurse to their
// allocating sub-expressions, each wrapped in turn.
let rec private coreToLowE (ctx : LowCtx) (e : Expr) : LExpr =
    let r = coreToLowEBody ctx e
    if isSafepointNode e then
        let r = if List.isEmpty ctx.ActiveGen then r else rootActiveGen ctx r
        if List.isEmpty ctx.SlottedGen then r else reloadSlottedGen ctx r
    else r
and private coreToLowEBody (ctx : LowCtx) (e : Expr) : LExpr =
    let st = ctx.LSt
    match e with
    | ELit (LInt s) when s.EndsWith "L" || s.EndsWith "l" ->
        lowBoxI ctx (LConstL (parseI64Lit (s.Substring (0, s.Length - 1))))
    | ELit (LInt s) ->
        // strip an integer TYPE suffix before parsing — int16 `s`, uint16 `us`,
        // sbyte `y`, byte `uy`, uint32 `u`, nativeint `n` — else Int32.TryParse
        // rejects it and the literal silently becomes 0. (int64 `L` handled above.)
        let digits =
            match [ "us"; "uy"; "un"; "s"; "y"; "u"; "n" ] |> List.tryFind (fun sfx -> s.EndsWith sfx) with
            | Some suf -> s.Substring (0, s.Length - suf.Length)
            | None -> s
        lowInt (parseI32Lit digits)
    // a HALF literal is rounded ONCE, here, into its 16 raw bits — a half
    // value IS those bits at rest, not a boxed double
    | ELit (LFloat s) when s.EndsWith "h" || s.EndsWith "H" -> LConstW (halfBits (parseFloatLit s))
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
        if gc then
            // the registers holding the group's cells go stale across the SIBLING
            // cell allocations and the closure fills; keep each cell pointer in a
            // shadow-stack slot, read through it, and build each closure BEFORE
            // re-reading its cell for the store (the store-order rule).
            let withA = regs |> List.map (fun (v, lam, id) -> v, lam, id, freshTmp ctx)
            let allocPush = withA |> List.collect (fun (_, _, id, aR) ->
                [ LSet (wReg id, lowMkCell ctx RKRef (lowInt 0))
                  LSet (wReg aR, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
                  LStore (W, LGet (wReg aR), 0, LGet (wReg id))
                  LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ])
            for v, _, _, aR in withA do dictSet ctx.Slotted (key v) (LGet (wReg aR))
            let fills = withA |> List.collect (fun (_, lam, _, aR) ->
                // fresh temp for the closure value: the member's own register
                // keeps the cell pointer (pre-lowered eta references read it)
                let cv = freshTmp ctx
                [ LSet (wReg cv, coreToLowE ctx lam)
                  LStore (W, LLoad (W, LGet (wReg aR), 0), cellOff (), LGet (wReg cv)) ])
            let bodyLow = coreToLowE ctx body
            for v, _, _, _ in withA do dictRemove ctx.Slotted (key v)
            let resReg = freshTmp ctx
            LDo (allocPush @ fills
                 @ [ LSet (wReg resReg, bodyLow)
                     LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW (4 * List.length withA) ])) ],
                 LGet (wReg resReg))
        else
        let allocs = regs |> List.map (fun (_, _, id) -> LSet (wReg id, lowMkCell ctx RKRef (lowInt 0)))
        let fills = regs |> List.map (fun (_, lam, id) -> LStore (W, LGet (wReg id), cellOff (), coreToLowE ctx lam))
        LDo (allocs @ fills, coreToLowE ctx body)
    | ELet (_, v, sch, rhs, body) when shouldSlot ctx v sch ->
        let addrReg = freshTmp ctx
        let addr = LGet (wReg addrReg)
        let initVal = lowSlotInit ctx v sch rhs
        dictSet ctx.Slotted (key v) addr
        let bodyLow = coreToLowE ctx body
        dictRemove ctx.Slotted (key v)
        let resReg = freshTmp ctx
        LDo ([ LSet (wReg addrReg, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
               LStore (W, addr, 0, initVal)
               LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ]))
               LSet (wReg resReg, bodyLow)
               LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ])) ],
             LGet (wReg resReg))
    | ELet (_, v, sch, rhs, body) when (genWitOf ctx v sch).IsSome && not (assignsTo (key v) body) ->
        // a GENERIC (`'a`) let: bind normally, then track it as an active generic
        // for its body scope so every safepoint roots it conditionally (its own
        // witness decides ref vs raw). The register is its home; reads are LGet.
        // A REASSIGNED generic mutable is excluded (assignsTo) — see genWitOf.
        let bind = lowLetBind ctx v sch rhs
        let reg = regOf ctx (key v)
        let saved = ctx.ActiveGen
        ctx.ActiveGen <- (reg, optGet (genWitOf ctx v sch)) :: ctx.ActiveGen
        let bodyLow = coreToLowE ctx body
        ctx.ActiveGen <- saved
        LDo ([ bind ], bodyLow)
    | ELet (_, v, sch, rhs, body) when (genWitOf ctx v sch).IsSome ->
        // a REASSIGNED generic mutable (the non-assigned one hit the case above):
        // ActiveGen would UNDO its `<-`, so root it through a PERSISTENT
        // witness-conditional slot instead — push once, write-through on `<-`,
        // reload from the GC-updated slot after each safepoint, pop at scope end.
        let bind = lowLetBind ctx v sch rhs
        let reg = regOf ctx (key v)
        let wit = optGet (genWitOf ctx v sch)
        let slotReg = freshTmp ctx
        let saved = ctx.SlottedGen
        ctx.SlottedGen <- (reg, wit, slotReg) :: ctx.SlottedGen
        let bodyLow = coreToLowE ctx body
        ctx.SlottedGen <- saved
        let resReg = freshTmp ctx
        LDo ([ bind; gcSlotPush reg wit slotReg; LSet (wReg resReg, bodyLow); gcSlotPop wit ], LGet (wReg resReg))
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
        LDo ([ LIf (coreToLowE ctx c,
                    [ LSet (wReg r, coreToLowE ctx a) ],
                    [ LSet (wReg r, coreToLowE ctx b) ]) ],
             LGet (wReg r))
    | EWhile (_, _) | EAssign (_, _) -> LDo (coreToLowS ctx e, lowInt 0)
    | EPrim ("+t", [ a; b ]) ->
        // GC: root `a` across `b`'s evaluation — `"x" + string n` allocates
        // in $itoa while a's pointer waits un-rooted in a temp, and a
        // collection there hands $str_cat a stale string. $str_cat guards
        // its own alloc; the caller's window is this one. Exception-safe:
        // the ETry lowering restores $sp at every handler entry.
        if gc then
            let ra = freshTmp ctx
            let rb = freshTmp ctx
            LDo ([ LCallVoidS ("$spush", [ coreToLowE ctx a ])
                   LSet (wReg rb, coreToLowE ctx b)
                   LSet (wReg ra, LCall ("$spop", [])) ],
                 LCall ("$str_cat", [ LGet (wReg ra); LGet (wReg rb) ]))
        else LCall ("$str_cat", [ coreToLowE ctx a; coreToLowE ctx b ])
    // `&&`/`||` MUST short-circuit: the right operand can have effects or THROW
    // (e.g. `n = xs.Length && List.zip xs ys …` — the zip must not run when the
    // lengths differ). Lowering them to AndW/OrW evaluated both sides and made
    // the self-hosted emitter zip mismatched lists. `if a then b else false`.
    | EPrim ("&&", [ a; b ]) ->
        let r = freshTmp ctx
        LDo ([ LIf (coreToLowE ctx a, [ LSet (wReg r, coreToLowE ctx b) ], [ LSet (wReg r, lowInt 0) ]) ], LGet (wReg r))
    | EPrim ("||", [ a; b ]) ->
        let r = freshTmp ctx
        LDo ([ LIf (coreToLowE ctx a, [ LSet (wReg r, lowInt 1) ], [ LSet (wReg r, coreToLowE ctx b) ]) ], LGet (wReg r))
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
        (LPrim (fop, [ fa; fb ]))
    | EPrim (("u-f" | "u-s"), [ a ]) -> lowBoxF ctx (LPrim (NegF, [ lowUnboxF (coreToLowE ctx a) ]))
    | EPrim ("u-l", [ a ]) -> lowBoxI ctx (LPrim (SubL, [ LConstL 0L; lowUnboxI (coreToLowE ctx a) ]))
    // nativeint and uint32 ride the RAW word, so their unary/bitwise forms
    // are the plain integer ones (`u-p` on a nativeint stubbed the whole
    // enclosing init before this)
    | EPrim (("u-" | "u-i" | "u-p" | "u-w"), [ a ]) -> LPrim (SubW, [ LConstW 0; coreToLowE ctx a ])
    | EPrim (("u~~~" | "u~~~i" | "u~~~p" | "u~~~w"), [ a ]) -> LPrim (XorW, [ coreToLowE ctx a; LConstW -1 ])
    // `~~~` bitwise complement: i32 forms flip every bit; the i64 form rides
    // the boxed payload
    | EPrim (("u~~~" | "u~~~i" | "u~~~w"), [ a ]) -> LPrim (XorW, [ coreToLowE ctx a; LConstW (-1) ])
    | EPrim (("u~~~l" | "u~~~v"), [ a ]) -> lowBoxI ctx (LPrim (XorL, [ lowUnboxI (coreToLowE ctx a); LConstL (-1L) ]))
    | EPrim (("unot" | "not"), [ a ]) -> LPrim (EqW, [ coreToLowE ctx a; LConstW 0 ])
    | EPrim (op, [ a; b ]) when (op.EndsWith "l" || op.EndsWith "v") && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%" ] ->
        // uint64 ('v') shares the boxed-i64 representation; div/rem are the
        // ops where signedness matters. Falling through to the int32 path
        // made `255UL % 16UL` arithmetic on TAGGED word halves.
        let unsigned = op.EndsWith "v"
        let ia = lowUnboxI (coreToLowE ctx a)
        let ib = lowUnboxI (coreToLowE ctx b)
        let iop =
            match op.Substring (0, op.Length - 1) with
            | "+" -> AddL | "-" -> SubL | "*" -> MulL
            | "/" -> (if unsigned then DivUL else DivSL)
            | _ -> (if unsigned then RemUL else RemSL)
        lowBoxI ctx (LPrim (iop, [ ia; ib ]))
    // int64 BITWISE — both operands are boxed i64. Without this `&&&l`/`|||l`/…
    // fell to the int32 path (or intArithOp's `%` default -> `i64 >>> n` became
    // an i32 `rem` and DIVIDED BY ZERO), which trapped the self-hosted emitter's
    // `emitF64Bits`.
    | EPrim (op, [ a; b ]) when (op.EndsWith "l" || op.EndsWith "v") && List.contains (op.Substring (0, op.Length - 1)) [ "&&&"; "|||"; "^^^" ] ->
        let ia = lowUnboxI (coreToLowE ctx a)
        let ib = lowUnboxI (coreToLowE ctx b)
        let iop = match op.Substring (0, op.Length - 1) with | "&&&" -> AndL | "|||" -> OrL | _ -> XorL
        lowBoxI ctx (LPrim (iop, [ ia; ib ]))
    // int64 SHIFT — `int64 <<< int` / `>>>`: the amount is a tagged i32, widened
    // to i64 for the wasm shift (whose count operand must match the value type).
    | EPrim (op, [ a; b ]) when (op.EndsWith "l" || op.EndsWith "v") && List.contains (op.Substring (0, op.Length - 1)) [ "<<<"; ">>>" ] ->
        let ia = lowUnboxI (coreToLowE ctx a)
        let ib = LPrim (WToL, [ (coreToLowE ctx b) ])
        // `>>>` on a UINT64 shifts in zeros: the signed form made
        // `UInt64.MaxValue >>> 60` stay all-ones instead of 15
        let iop =
            if op.Substring (0, op.Length - 1) = "<<<" then ShlL
            elif op.EndsWith "v" then ShrUL
            else ShrSL
        lowBoxI ctx (LPrim (iop, [ ia; ib ]))
    | EPrim (op, [ a; b ]) when (op.EndsWith "l" || op.EndsWith "v") && List.contains (op.Substring (0, op.Length - 1)) [ "<"; ">"; "<="; ">="; "="; "<>" ] ->
        let unsigned = op.EndsWith "v"
        let ia = lowUnboxI (coreToLowE ctx a)
        let ib = lowUnboxI (coreToLowE ctx b)
        let iop =
            match op.Substring (0, op.Length - 1) with
            | "<" -> (if unsigned then LtUL else LtSL)
            | ">" -> (if unsigned then GtUL else GtSL)
            | "<=" -> (if unsigned then LeUL else LeSL)
            | ">=" -> (if unsigned then GeUL else GeSL)
            | "=" -> EqL | _ -> NeL
        (LPrim (iop, [ ia; ib ]))
    | EPrim ("::", [ h; t ]) ->
        // concrete head: skip/scan by compile-time ref-kind. GENERIC head: pick
        // the scan map at runtime from the element type's witness refMask
        // (looked up by the head's type-var id). The tail is always a pointer.
        (match refKindOfExpr h with
         | RKGen ->
             (match tyVarIdOfExpr h |> Option.bind (fun vid -> dictTryFind ctx.Witness vid) with
              | Some wreg -> lowGenericCons ctx (LLoad (W, LGet (wReg wreg), 8)) (coreToLowE ctx h) (coreToLowE ctx t)
              | None -> lowObjR ctx CID_LIST 0 [ coreToLowE ctx h; coreToLowE ctx t ] (Some [ RKGen; RKRef ]) [])
         | k -> lowObjR ctx CID_LIST 0 [ coreToLowE ctx h; coreToLowE ctx t ] (Some [ k; RKRef ]) [])
    // list append: `a @ b` rebuilds a's spine onto b. Without this it fell to the
    // EPrim arithmetic path and `intArithOp`'s `%` default — `a @ b` compiled as
    // `a rem b` on two list POINTERS, trapping (divide-by-zero) the moment a spine
    // reached nil (0). Mirrors the GC backend's `$append`.
    | EPrim ("@", [ a; b ]) -> lowCallR ctx "$lappend" [ a; b ]
    // |n| on a raw int, branchless: (n ^ (n>>31)) - (n>>31)
    | EPrim (("abs" | "absi"), [ a ]) ->
        let t = freshTmp ctx
        let n = LGet (wReg t)
        let m = LPrim (ShrSW, [ n; LConstW 31 ])
        LDo ([ LSet (wReg t, coreToLowE ctx a) ], LPrim (SubW, [ LPrim (XorW, [ n; m ]); m ]))
    // |x| on a boxed float: the wasm instruction (clears the sign bit, so
    // abs -0.0 = 0.0 and abs nan keeps the payload, as .NET does)
    | EPrim ("absf", [ a ]) ->
        lowBoxF ctx (LPrim (AbsF, [ lowUnboxF (coreToLowE ctx a) ]))
    // sqrt/truncate on a boxed float — the INSTRUCTION (an `if x < 0`
    // rewrite gets -0.0 and NaN wrong, mirroring the GC backend's arm). The
    // float32 variants snap the result to f32: exact for all three ops on an
    // f32 input, so the narrow-then-widen is the rounding step we owe.
    | EPrim (("sqrtf" | "sqrts" | "truncatef" | "truncates" | "abss") as op, [ a ]) ->
        let v = lowUnboxF (coreToLowE ctx a)
        let r =
            if op.StartsWith "sqrt" then LPrim (SqrtF, [ v ])
            elif op.StartsWith "abs" then LPrim (AbsF, [ v ])
            else LPrim (TruncF, [ v ])
        let r = if op.EndsWith "s" then LPrim (PromF, [ LPrim (DemF, [ r ]) ]) else r
        lowBoxF ctx r
    // |n| on a boxed int64, same identity at 64 bits
    | EPrim ("absl", [ a ]) ->
        let t = freshTmpT ctx I64
        let n = LGet { Id = t; RTy = I64 }
        let m = LPrim (ShrSL, [ n; LConstL 63L ])
        LDo ([ LSet ({ Id = t; RTy = I64 }, lowUnboxI (coreToLowE ctx a)) ],
             lowBoxI ctx (LPrim (SubL, [ LPrim (XorL, [ n; m ]); m ])))
    // the builtin `compare a b` (an unbound EVar in the unoptimised core):
    // -1/0/1 by the operands' static shape
    | EApp ((EVar (v, _) | EVarI (v, _, _)), [ a; b ]) when v.Path = "(builtin)" && v.Name.StartsWith "compare" ->
        let sh = mergeShape (shapeOfExprF st a) (shapeOfExprF st b)
        let ra, rb, pre = evalRooted ctx a b
        LDo (pre, (structCmpW ctx sh (LGet (wReg ra)) (LGet (wReg rb)) (cmpWit ctx a b)))
    // the `compare` intrinsic: -1/0/1 by the shape its dispatch name carries
    | EApp (EUnknown n, [ a; b ]) when n.StartsWith "$class:Ordered:compare:" ->
        let sh = shapeOfName (n.Substring (strLen "$class:Ordered:compare:"))
        let ra, rb, pre = evalRooted ctx a b
        LDo (pre, (structCmpW ctx sh (LGet (wReg ra)) (LGet (wReg rb)) (cmpWit ctx a b)))
    // float16 arithmetic and comparison: widen both operands to f32, operate
    // there, round ONCE back to half — that single rounding is what makes the
    // result the correctly-rounded half. Comparison is IEEE on the widened
    // values, so -0.0h = 0.0h and a NaN half equals nothing.
    | EPrim (op, [ a; b ]) when
        strLen op > 1 && charAt op (strLen op - 1) = 'h' && not (op.Contains "@")
        && List.contains (substr op 0 (strLen op - 1)) [ "+"; "-"; "*"; "/"; "<"; ">"; "<="; ">="; "="; "<>" ] ->
        let bop = substr op 0 (strLen op - 1)
        let da = LPrim (PromF, [ LCall ("$h2f", [ coreToLowE ctx a ]) ])
        let db = LPrim (PromF, [ LCall ("$h2f", [ coreToLowE ctx b ]) ])
        (match bop with
         | "+" | "-" | "*" | "/" ->
             let fop = match bop with "+" -> AddF | "-" -> SubF | "*" -> MulF | _ -> DivF
             LCall ("$f2h64", [ LPrim (fop, [ da; db ]) ])
         | _ ->
             let cop = match bop with "<" -> LtF | ">" -> GtF | "<=" -> LeF | ">=" -> GeF | "=" -> EqF | _ -> NeF
             LPrim (cop, [ da; db ]))
    | EPrim (("sqrth" | "absh" | "truncateh" | "u-h") as op, [ a ]) ->
        let d = LPrim (PromF, [ LCall ("$h2f", [ coreToLowE ctx a ]) ])
        let r =
            match op with
            | "sqrth" -> LPrim (SqrtF, [ d ])
            | "absh" -> LPrim (AbsF, [ d ])
            | "truncateh" -> LPrim (TruncF, [ d ])
            | _ -> LPrim (NegF, [ d ])
        LCall ("$f2h64", [ r ])
    // a comparison whose operands are a COMPOUND value (tuple/list/...), a STRING
    // (`=t`/`<t` — the `t` type suffix), or a STRUCTURAL `=@Type`/`<>@Type`
    // (records/unions): the tagged-int fast path below would compare heap
    // POINTERS, so route it through a structural comparison.
    // `=@Class` / `<>@Class`: a CLASS compares by REFERENCE (DIVERGENCES.md)
    // — the structural route below would fold its fields and call two
    // distinct-but-equal instances equal
    | EPrim (op, [ a; b ]) when
        op.Contains "@"
        && (match op.Substring (0, op.IndexOf "@") with "=" | "<>" -> true | _ -> false)
        && (dictTryFind st.ClassNames (op.Substring (op.IndexOf "@" + 1))).IsSome ->
        let cb = op.Substring (0, op.IndexOf "@")
        let ra, rb, pre = evalRooted ctx a b
        LDo (pre, LPrim ((if cb = "=" then EqW else NeW), [ LGet (wReg ra); LGet (wReg rb) ]))
    | EPrim (op, [ a; b ]) when
        (let hasAt = op.Contains "@"
         let b0 = if hasAt then op.Substring (0, op.IndexOf "@") else baseOp op
         let cb = if (not hasAt) && b0.EndsWith "t" then b0.Substring (0, b0.Length - 1) else b0
         (match cb with "<" | ">" | "<=" | ">=" | "=" | "<>" -> true | _ -> false)
         && (hasAt || (baseOp op).EndsWith "t" || needsStructCmp (mergeShape (shapeOfExprF st a) (shapeOfExprF st b)))) ->
        let hasAt = op.Contains "@"
        let b0 = if hasAt then op.Substring (0, op.IndexOf "@") else baseOp op
        let isStr = (not hasAt) && b0.EndsWith "t"
        let cb = if isStr then b0.Substring (0, b0.Length - 1) else b0
        let sh = if isStr then ShStr elif hasAt then ShOther else mergeShape (shapeOfExprF st a) (shapeOfExprF st b)
        let ra, rb, pre = evalRooted ctx a b
        let cr = freshTmp ctx
        let boolOp = match cb with "=" -> EqW | "<>" -> NeW | "<" -> LtSW | ">" -> GtSW | "<=" -> LeSW | _ -> GeSW
        LDo (pre @ [ LSet (wReg cr, structCmpW ctx sh (LGet (wReg ra)) (LGet (wReg rb)) (cmpWit ctx a b)) ],
             (LPrim (boolOp, [ LGet (wReg cr); LConstW 0 ])))
    | EPrim (op, [ a; b ]) ->
        // int is RAW i32: plain wasm arithmetic, no tag juggling. A comparison
        // yields a raw 0/1 bool, which is also the raw representation.
        // The `w` kind suffix (uint32) picks the UNSIGNED division/remainder/
        // shift/comparison forms — the stripped route ran them signed, so
        // `4294967295u / 2u` and `4000000000u > 2u` were simply wrong.
        let unsignedW = strLen op >= 2 && charAt op (strLen op - 1) = 'w' && not (op.Contains "@")
        // baseOp strips a kind letter only off the arithmetic/comparison
        // bases; the shift/bitwise ops (`>>>w`, `&&&p`, …) kept theirs and
        // fell through intArithOp's default — `7u >>> 1` and `a &&& 24n`
        // both compiled as REM. Every kind that rides the RAW word (int,
        // nativeint, uint32) uses the plain integer instruction.
        let bop =
            let b0 = baseOp op
            if b0 <> op then b0
            else
                let last = charAt op (strLen op - 1)
                let stripped = substr op 0 (strLen op - 1)
                if (last = 'i' || last = 'p' || last = 'w')
                   && List.contains stripped [ "+"; "-"; "*"; "/"; "%"; "&&&"; "|||"; "^^^"; "<<<"; ">>>" ]
                then stripped else op
        let ta = coreToLowE ctx a
        let tb = coreToLowE ctx b
        match bop with
        | "<" -> LPrim ((if unsignedW then LtUW else LtSW), [ ta; tb ])
        | ">" -> LPrim ((if unsignedW then GtUW else GtSW), [ ta; tb ])
        | "<=" -> LPrim ((if unsignedW then LeUW else LeSW), [ ta; tb ])
        | ">=" -> LPrim ((if unsignedW then GeUW else GeSW), [ ta; tb ])
        | "=" | "<>" -> LPrim (intCmpOp bop, [ ta; tb ])
        | "/" when unsignedW -> LPrim (DivUW, [ ta; tb ])
        | "%" when unsignedW -> LPrim (RemUW, [ ta; tb ])
        | ">>>" when unsignedW -> LPrim (ShrUW, [ ta; tb ])
        | _ -> LPrim (intArithOp bop, [ ta; tb ])
    | ETuple xs -> lowObjR ctx CID_TUPLE 0 (List.map (coreToLowE ctx) xs) (Some (List.map (refKindOfExprC st) xs)) (genWitsOf ctx 0 xs)
    | EListLit xs -> lowList ctx xs
    // a collapsed one-field record IS its field value — no heap object
    | ERecord (name, fields) when (dictTryFind st.Collapse name).IsSome ->
        let f = optGet (dictTryFind st.Collapse name)
        (match fields |> List.tryPick (fun (fn2, e2) -> if fn2 = f then Some e2 else None) with
         | Some e2 -> coreToLowE ctx e2
         | None -> lowInt 0)
    | ERecordExt (name, baseE, updates) when (dictTryFind st.Collapse name).IsSome ->
        let f = optGet (dictTryFind st.Collapse name)
        (match updates |> List.tryPick (fun (fn2, e2) -> if fn2 = f then Some e2 else None) with
         | Some e2 -> coreToLowE ctx e2
         | None -> coreToLowE ctx baseE)
    // inline value type: an all-scalar record stores its fields raw inline. Each
    // raw field value rides a typed local before the allocation (GC-invisible),
    // so no shadow rooting; a field read boxes (cancelled by unbox in arithmetic).
    | ERecord (name, fields) when (dictTryFind st.RecPod name).IsSome ->
        let (layout, _, _) = optGet (dictTryFind st.RecPod name)
        let order = ctorOrder st name (List.map fst fields)
        let items =
            order |> List.map (fun fn ->
                let (off, kind) = optGet (dictTryFind layout fn)
                let ve = fields |> List.tryPick (fun (f, e) -> if f = fn then Some e else None)
                match storLTy kind with
                | Some (sty, _) ->
                    let raw = match ve with Some e -> storUnbox kind (coreToLowE ctx e) | None -> (match storValTy sty with F64 -> LConstF 0.0 | I64 -> LConstL 0L | _ -> LConstW 0)
                    (off, sty, storValTy sty, false, raw)
                | None -> (off, W, W, true, (match ve with Some e -> coreToLowE ctx e | None -> lowInt 0)))
        lowPodBuild ctx name items
    | ERecordExt (name, baseE, updates) when (dictTryFind st.RecPod name).IsSome ->
        let (layout, _, _) = optGet (dictTryFind st.RecPod name)
        let order = ctorOrder st name (List.map fst updates)
        let bl = freshTmp ctx
        // pre-evaluate each update value into a local; then bind base. lowPodBuild
        // then sees only pure reads (these locals + base loads), so its single
        // allocation cannot move an as-yet-unstored update value or the base.
        let updInfo =
            updates |> List.map (fun (fn, e) ->
                let (off, kind) = optGet (dictTryFind layout fn)
                match storLTy kind with
                | Some (sty, _) -> let vty = storValTy sty in let id = freshTmpT ctx vty in (fn, LSet ({ Id = id; RTy = vty }, storUnbox kind (coreToLowE ctx e)), (off, sty, vty, false, LGet { Id = id; RTy = vty }))
                | None -> let id = freshTmp ctx in (fn, LSet (wReg id, coreToLowE ctx e), (off, W, W, true, LGet (wReg id))))
        let updEvals = updInfo |> List.map (fun (_, ev, _) -> ev)
        let items =
            order |> List.map (fun fn ->
                match updInfo |> List.tryPick (fun (f, _, it) -> if f = fn then Some it else None) with
                | Some it -> it
                | None ->
                    let (off, kind) = optGet (dictTryFind layout fn)
                    match storLTy kind with
                    | Some (sty, _) -> (off, sty, storValTy sty, false, LLoad (sty, LGet (wReg bl), off))
                    | None -> (off, W, W, true, LLoad (W, LGet (wReg bl), off)))
        LDo (updEvals @ [ LSet (wReg bl, coreToLowE ctx baseE) ], lowPodBuild ctx name items)
    | ERecord (name, fields) ->
        let order = ctorOrder st name (List.map fst fields)
        // the field VALUE expressions in slot order — a missing field defaults to
        // 0. Their ref-kinds give a precise ref-map (an int field is excluded from
        // the scan) and, in a generic body, a generic field forwards its witness.
        let valExprs =
            order |> List.map (fun fnm ->
                match fields |> List.tryPick (fun (fn2, e2) -> if fn2 = fnm then Some e2 else None) with
                | Some e2 -> e2
                | None -> ELit (LInt "0"))
        let baseSlots = valExprs |> List.map (coreToLowE ctx)
        let baseKinds = valExprs |> List.map (refKindOfExprC st)
        let baseWits = genWitsOf ctx 0 valExprs
        match (if gc then dictTryFind st.WitnessedClasses name else None) with
        | Some k ->
            // trailing class-param witness pointers, one per class type param:
            // stored RAW (never scanned — they point into immortal g_witnesses
            // static data). Slot j forwards this ctor's j-th class-param witness
            // from its hidden param, so the class' methods can read it off self.
            let witVal j =
                match List.tryItem j ctx.ClassCtorWits |> Option.bind (fun wid -> dictTryFind ctx.Witness wid) with
                | Some r -> LGet (wReg r)
                | None -> witnessPtrRM st 4 4 1
            let wits = [ 0 .. k - 1 ] |> List.map witVal
            lowObjR ctx (cidRec st name) 0 (baseSlots @ wits) (Some (baseKinds @ List.replicate k RKRaw)) baseWits
        | None ->
            lowObjR ctx (cidRec st name) 0 baseSlots (Some baseKinds) baseWits
    | ERecordExt (name, baseE, updates) ->
        let order = ctorOrder st name (List.map fst updates)
        let b = freshTmp ctx
        let slots =
            order |> List.mapi (fun i fnm ->
                match updates |> List.tryPick (fun (fn2, e2) -> if fn2 = fnm then Some e2 else None) with
                | Some e2 -> coreToLowE ctx e2
                | None -> LLoad (W, LGet (wReg b), HDR + 4 * i))
        LDo ([ LSet (wReg b, coreToLowE ctx baseE) ], lowObj ctx (cidRec st name) 0 slots)
    // an enum case IS its raw integer value — no heap object
    | ECtor (case, _, _) when (dictTryFind st.EnumConst case).IsSome ->
        LConstW (optGet (dictTryFind st.EnumConst case))
    | ECtor (case, _, args) ->
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        // slot 0 is the raw tag word; the payload follows. A concrete payload
        // gets a ref-map so its unboxed scalars are skipped by the collector.
        let kinds = RKRaw :: List.map (refKindOfExprC st) args
        lowObjR ctx (cidCase st case) 1 (LConstW tag :: List.map (coreToLowE ctx) args) (Some kinds) (genWitsOf ctx 1 args)
    | EField (r, _, owner) when (dictTryFind st.Collapse owner).IsSome -> coreToLowE ctx r
    // fused element-field access on an array of inline records — MUST precede the
    // plain POD field cases, or a field write would copy the element out and
    // mutate the throwaway. Read fuses to the slot; write hits the slot directly.
    | EField (EIndex (ek, arr, i), fname, _) when (podArrOf st ek).IsSome ->
        let (layout, stride) = optGet (podArrOf st ek)
        let (off, kind) = optGet (dictTryFind layout fname)
        let (sty, _) = optGet (storLTy kind)
        let vty = storValTy sty
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        let fv = freshTmpT ctx vty
        LDo ([ LSet (wReg ar, coreToLowE ctx arr)
               LSet (wReg ir, (coreToLowE ctx i))
               LSet ({ Id = fv; RTy = vty }, LLoad (sty, LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ]), ARRHDR + off - HDR)) ],
             storBox ctx kind (LGet { Id = fv; RTy = vty }))
    | EFieldSet (EIndex (ek, arr, i), fname, _, v) when (podArrOf st ek).IsSome ->
        let (layout, stride) = optGet (podArrOf st ek)
        let (off, kind) = optGet (dictTryFind layout fname)
        let (sty, _) = optGet (storLTy kind)
        let vty = storValTy sty
        let fv = freshTmpT ctx vty
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        LDo ([ LSet ({ Id = fv; RTy = vty }, storUnbox kind (coreToLowE ctx v))
               LSet (wReg ar, coreToLowE ctx arr)
               LSet (wReg ir, (coreToLowE ctx i))
               LStore (sty, LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ]), ARRHDR + off - HDR, LGet { Id = fv; RTy = vty }) ],
             lowInt 0)
    | EField (r, fname, owner) when (dictTryFind st.RecPod owner).IsSome ->
        let (layout, _, _) = optGet (dictTryFind st.RecPod owner)
        let (off, kind) = optGet (dictTryFind layout fname)
        (match storLTy kind with
         | Some (sty, _) ->
             let vty = storValTy sty
             let fv = freshTmpT ctx vty
             LDo ([ LSet ({ Id = fv; RTy = vty }, LLoad (sty, coreToLowE ctx r, off)) ], storBox ctx kind (LGet { Id = fv; RTy = vty }))
         | None -> LLoad (W, coreToLowE ctx r, off))
    | EFieldSet (r, fname, owner, v) when (dictTryFind st.RecPod owner).IsSome ->
        let (layout, _, _) = optGet (dictTryFind st.RecPod owner)
        let (off, kind) = optGet (dictTryFind layout fname)
        (match storLTy kind with
         | Some (sty, _) ->
             let vty = storValTy sty
             let fv = freshTmpT ctx vty
             let rr = freshTmp ctx
             LDo ([ LSet ({ Id = fv; RTy = vty }, storUnbox kind (coreToLowE ctx v))
                    LSet (wReg rr, coreToLowE ctx r)
                    LStore (sty, LGet (wReg rr), off, LGet { Id = fv; RTy = vty }) ], lowInt 0)
         | None ->
             // ref field of a (scalars-first) record: same stale-address hazard
             // as the general EFieldSet — root the receiver across an
             // allocating value (prune's `v.Link <- Some r` lives HERE).
             if gc then
                 let ra, rb, pre = evalRooted ctx r v
                 LDo (pre @ [ LStore (W, LGet (wReg ra), off, LGet (wReg rb)) ], lowInt 0)
             else LDo ([ LStore (W, coreToLowE ctx r, off, coreToLowE ctx v) ], lowInt 0))
    | EField (r, fname, owner) ->
        (match recFieldIdxE st owner fname with
         | Some i -> LLoad (W, coreToLowE ctx r, HDR + 4 * i)
         | None ->
             let cands =
                 match dictTryFind st.FieldOwnerOf fname with
                 | Some os -> os |> List.map (fun o -> o + "@" + (match recFieldIdxOpt st o fname with Some i -> string i | None -> "?")) |> String.concat ","
                 | None -> "-"
             vecAdd st.Warnings ("field-site trap: '" + fname + "' unresolved (owner '" + owner + "', candidates " + cands + ") in " + curFnDbg)
             LDo ([ LEval (coreToLowE ctx r); LTrap ], lowInt 0))
    | EFieldSet (r, fname, owner, v) ->
        // an LStore evaluates its ADDRESS before its VALUE. When the value can
        // allocate, that collection MOVES the receiver and the store writes the
        // field into the dead copy — the live object keeps its old (soon stale)
        // ref. Root the receiver across the value and store through the
        // GC-updated pointer. (This was prune's path compression going stale.)
        (match recFieldIdxE st owner fname with
         | Some i ->
             if gc then
                 let ra, rb, pre = evalRooted ctx r v
                 LDo (pre @ chkStoreStmts rb @ [ LStore (W, LGet (wReg ra), HDR + 4 * i, LGet (wReg rb)) ], lowInt 0)
             else LDo ([ LStore (W, coreToLowE ctx r, HDR + 4 * i, coreToLowE ctx v) ], lowInt 0)
         | None ->
             vecAdd st.Warnings ("field-site trap: '" + fname + "' unresolved (owner '" + owner + "') in " + curFnDbg)
             LDo ([ LEval (coreToLowE ctx r); LEval (coreToLowE ctx v); LTrap ], lowInt 0))
    // ---- arrays of inline value-type records (all-scalar elements) ----
    // elements are contiguous & HEADERLESS at ARRHDR + i*stride. A whole-element
    // read copies out to a fresh headed record; a whole-element write copies the
    // source record's fields into the slot. (The FUSED field access on an element
    // — `arr.[i].f` / `arr.[i].f <- v` — is matched earlier, ahead of the plain
    // POD field cases, so a field write hits the slot instead of a throwaway.)
    | EIndex (ek, arr, i) when (podArrOf st ek).IsSome ->
        let (layout, stride) = optGet (podArrOf st ek)
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        let elemBase = LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ])
        let items = order |> List.map (fun fn ->
            let (off, kind) = optGet (dictTryFind layout fn)
            let (sty, _) = optGet (storLTy kind)
            (off, sty, storValTy sty, false, LLoad (sty, elemBase, ARRHDR + off - HDR)))
        LDo ([ LSet (wReg ar, coreToLowE ctx arr); LSet (wReg ir, (coreToLowE ctx i)) ], lowPodBuild ctx ek items)
    | EIndexSet (ek, arr, i, v) when (podArrOf st ek).IsSome ->
        let (layout, stride) = optGet (podArrOf st ek)
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let vr = freshTmp ctx
        let ar = freshTmp ctx
        let ir = freshTmp ctx
        let elemBase = LPrim (AddW, [ LGet (wReg ar); LPrim (MulW, [ LGet (wReg ir); LConstW stride ]) ])
        let copies = order |> List.map (fun fn ->
            let (off, kind) = optGet (dictTryFind layout fn)
            let (sty, _) = optGet (storLTy kind)
            LStore (sty, elemBase, ARRHDR + off - HDR, LLoad (sty, LGet (wReg vr), off)))
        LDo ([ LSet (wReg vr, coreToLowE ctx v); LSet (wReg ar, coreToLowE ctx arr); LSet (wReg ir, (coreToLowE ctx i)) ] @ copies, lowInt 0)
    | EArrayCreate (ek, n, init) when (podArrOf st ek).IsSome ->
        let (layout, stride) = optGet (podArrOf st ek)
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let cnt = freshTmp ctx
        let vr = freshTmp ctx
        let bs = freshTmp ctx
        let it = freshTmp ctx
        let elemBase = LPrim (AddW, [ LGet (wReg bs); LPrim (MulW, [ LGet (wReg it); LConstW stride ]) ])
        let copies = order |> List.map (fun fn ->
            let (off, kind) = optGet (dictTryFind layout fn)
            let (sty, _) = optGet (storLTy kind)
            LStore (sty, elemBase, ARRHDR + off - HDR, LLoad (sty, LGet (wReg vr), off)))
        let alloc = if gc then LCall ("$fpallocn", [ LConstW (gcArrTidReg ctx.LSt ("pa:" + ek) stride FK_SCALAR_ARRAY); LGet (wReg cnt) ]) else LAlloc (LPrim (AddW, [ LConstW ARRHDR; LPrim (MulW, [ LGet (wReg cnt); LConstW stride ]) ]))
        let stmts =
            [ LSet (wReg cnt, (coreToLowE ctx n)); LSet (wReg vr, coreToLowE ctx init) ]
            @ (if gc then [ LCallVoidS ("$spush", [ LGet (wReg vr) ]) ] else [])
            @ [ LSet (wReg bs, alloc) ]
            @ (if gc then [ LSet (wReg vr, LCall ("$spop", [])) ] else [])
            @ (if gc then [] else [ LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY); LStore (W, LGet (wReg bs), HDR, LGet (wReg cnt)) ])
            @ [ LSet (wReg it, LConstW 0)
                LWhile (LPrim (LtUW, [ LGet (wReg it); LGet (wReg cnt) ]), copies @ [ LSet (wReg it, LPrim (AddW, [ LGet (wReg it); LConstW 1 ])) ]) ]
        LDo (stmts, LGet (wReg bs))
    | EArray (ek, xs) when (podArrOf st ek).IsSome ->
        let (layout, stride) = optGet (podArrOf st ek)
        let order = match dictTryFind st.RecFields ek with Some o -> o | None -> []
        let n = List.length xs
        let bs = freshTmp ctx
        let alloc = if gc then LCall ("$fpallocn", [ LConstW (gcArrTidReg ctx.LSt ("pa:" + ek) stride FK_SCALAR_ARRAY); LConstW n ]) else LAlloc (LConstW (ARRHDR + n * stride))
        let copyFields eb vr = order |> List.map (fun fn ->
            let (off, kind) = optGet (dictTryFind layout fn)
            let (sty, _) = optGet (storLTy kind)
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
    | EArray (k, xs) when (storLTy (storKindRes ctx.LSt k)).IsSome ->
        let k = storKindRes ctx.LSt k
        let (sty, w) = optGet (storLTy k)
        let vty = storValTy sty
        let n = List.length xs
        let vregs = xs |> List.map (fun _ -> freshTmpT ctx vty)
        let bs = freshTmp ctx
        let evals = List.map2 (fun vr x -> LSet ({ Id = vr; RTy = vty }, storUnbox k (coreToLowE ctx x))) vregs xs
        let alloc =
            if gc then LCall ("$fpallocn", [ LConstW (gcArrTidReg ctx.LSt (storShape k) w FK_SCALAR_ARRAY); LConstW n ])
            else LAlloc (LConstW (HDR + 4 + n * w))
        let hdr = if gc then [] else [ LStore (W, LGet (wReg bs), 0, LConstW CID_ARRAY); LStore (W, LGet (wReg bs), HDR, LConstW n) ]
        let stores = vregs |> List.mapi (fun i vr -> LStore (sty, LGet (wReg bs), HDR + 4 + i * w, LGet { Id = vr; RTy = vty }))
        LDo (evals @ [ LSet (wReg bs, alloc) ] @ hdr @ stores, LGet (wReg bs))
    | EIndex (k, arr, i) when (storLTy (storKindRes ctx.LSt k)).IsSome ->
        let k = storKindRes ctx.LSt k
        let (sty, w) = optGet (storLTy k)
        let vty = storValTy sty
        let ir = freshTmp ctx
        let fv = freshTmpT ctx vty
        LDo ([ LSet (wReg ir, (coreToLowE ctx i))
               LSet ({ Id = fv; RTy = vty }, LLoad (sty, LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LGet (wReg ir); LConstW w ]) ]), HDR + 4)) ],
             storBox ctx k (LGet { Id = fv; RTy = vty }))
    | EIndexSet (k, arr, i, v) when (storLTy (storKindRes ctx.LSt k)).IsSome ->
        let k = storKindRes ctx.LSt k
        let (sty, w) = optGet (storLTy k)
        let vty = storValTy sty
        let fv = freshTmpT ctx vty
        let ir = freshTmp ctx
        LDo ([ LSet ({ Id = fv; RTy = vty }, storUnbox k (coreToLowE ctx v))
               LSet (wReg ir, (coreToLowE ctx i))
               LStore (sty, LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LGet (wReg ir); LConstW w ]) ]), HDR + 4, LGet { Id = fv; RTy = vty }) ],
             lowInt 0)
    | EArray (_, xs) -> lowObj ctx CID_ARRAY 0 (LConstW (List.length xs) :: List.map (coreToLowE ctx) xs)
    // `s.[i]` on a STRING: its element type comes through as a symbolic `#id`
    // (not "char"), so storLTy misses it and the general ref-array path below
    // would read a 4-byte WORD (two units) as a pointer — garbage char codes,
    // which broke every charAt and the whole lexer. A string's UTF-16 units sit
    // at HDR+4 with stride 2; read one, zero-extended (load16_u), and tag it.
    // `for c in s` marks its reads with the "$str" sentinel — the receiver
    // is a synthetic anon-typed loop temp, so shapeOfExpr cannot see the
    // string; the KIND says it
    | EIndex ("$str", arr, i) ->
        let ir = freshTmp ctx
        LDo ([ LSet (wReg ir, (coreToLowE ctx i)) ],
             (LLoad (I16, LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LGet (wReg ir); LConstW 2 ]) ]), HDR + 4)))
    | EIndex (_, arr, i) when shapeOfExpr arr = ShStr ->
        let ir = freshTmp ctx
        LDo ([ LSet (wReg ir, (coreToLowE ctx i)) ],
             (LLoad (I16, LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LGet (wReg ir); LConstW 2 ]) ]), HDR + 4)))
    | EIndex (_, arr, i) ->
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LLoad (W, addr, HDR)
    | EIndexSet (_, arr, i, v) ->
        // same stale-address hazard as EFieldSet: root the array across an
        // allocating value; the index is a raw int and needs no root.
        if gc then
            let ir = freshTmp ctx
            let rv = freshTmp ctx
            let ra = freshTmp ctx
            LDo ([ LCallVoidS ("$spush", [ coreToLowE ctx arr ])
                   LSet (wReg ir, coreToLowE ctx i)
                   LSet (wReg rv, coreToLowE ctx v)
                   LSet (wReg ra, LCall ("$spop", []))
                   LStore (W, LPrim (AddW, [ LGet (wReg ra); LPrim (MulW, [ LPrim (AddW, [ LGet (wReg ir); LConstW 1 ]); LConstW 4 ]) ]), HDR, LGet (wReg rv)) ], lowInt 0)
        else
        let addr = LPrim (AddW, [ coreToLowE ctx arr; LPrim (MulW, [ LPrim (AddW, [ (coreToLowE ctx i); LConstW 1 ]); LConstW 4 ]) ])
        LDo ([ LStore (W, addr, HDR, coreToLowE ctx v) ], lowInt 0)
    | EArrayLen (_, arr) -> (LLoad (W, coreToLowE ctx arr, HDR))
    // Array.pin answers the element-data address (elements start after
    // [hdr][len]). Standalone: storage never moves, the address IS stable.
    // GC: fpprt_pin first — real under the mmc reactor (Immix per-object
    // pinning, the browser/product collector), an abort under semi (the
    // shakeout collector; a pin-using program belongs on mmc). The pin is
    // PERMANENT — mmc pins for the object's whole life — so unpin is a
    // no-op in both modes; pin long-lived buffers once, not per call.
    | EArrayPin (_, arr) ->
        if gc then
            let r = freshTmp ctx
            LDo ([ LSet (wReg r, coreToLowE ctx arr); LCallVoidS ("$fppin", [ LGet (wReg r) ]) ],
                 LPrim (AddW, [ LGet (wReg r); LConstW (HDR + 4) ]))
        else LPrim (AddW, [ coreToLowE ctx arr; LConstW (HDR + 4) ])
    | EArrayUnpin (_, arr) -> LDo ([ LEval (coreToLowE ctx arr) ], lowInt 0)
    | EArrayBytes (nm, arr) ->
        let w =
            match storLTy (storKindRes ctx.LSt nm) with
            | Some (_, ww) -> ww
            // a packed POD element's stride is its FIELD bytes — RecPod's
            // size includes the record header that packed elements drop
            | None -> (match dictTryFind ctx.LSt.RecPod nm with Some (_, size, _) -> size - HDR | None -> 4)
        LPrim (MulW, [ LLoad (W, coreToLowE ctx arr, HDR); LConstW w ])
    | EArrayCreate (k, n, init) when (storLTy (storKindRes ctx.LSt k)).IsSome ->
        let k = storKindRes ctx.LSt k
        let (sty, w) = optGet (storLTy k)
        let vty = storValTy sty
        let cnt = freshTmp ctx
        let fv = freshTmpT ctx vty
        let bs = freshTmp ctx
        let it = freshTmp ctx
        let alloc =
            if gc then LCall ("$fpallocn", [ LConstW (gcArrTidReg ctx.LSt (storShape k) w FK_SCALAR_ARRAY); LGet (wReg cnt) ])
            else LAlloc (LPrim (AddW, [ LConstW (HDR + 4); LPrim (MulW, [ LGet (wReg cnt); LConstW w ]) ]))
        // `Array.zeroCreate` keeps a `$zero` marker whose zero is per-storage —
        // fill the raw scalar zero, NOT a mis-unboxed tagged 0 (which would read
        // a bogus address as if the slot were boxed).
        let isZero = match init with EUnknown n | EApp (EUnknown n, _) -> n.StartsWith "$zero" | _ -> false
        let fill = if isZero then (match vty with F64 -> LConstF 0.0 | I64 -> LConstL 0L | _ -> LConstW 0) else storUnbox k (coreToLowE ctx init)
        let stmts =
            [ LSet (wReg cnt, (coreToLowE ctx n))
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
            [ LSet (wReg cnt, (coreToLowE ctx n))
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
    // OUT of a half: widen the bits, then narrow to the target
    | EApp (EUnknown n, [ a ]) when
        strLen n > 2 && n.EndsWith "#h" && not (n.StartsWith "$") && not (n.StartsWith "print") ->
        let wide = LPrim (PromF, [ LCall ("$h2f", [ coreToLowE ctx a ]) ])
        (match substr n 0 (strLen n - 2) with
         | "float" | "double" -> lowBoxF ctx wide
         | "float32" | "single" -> lowBoxF ctx (LPrim (PromF, [ LPrim (DemF, [ wide ]) ]))
         | "string" -> LCall ("$ftoa_s", [ lowBoxF ctx wide ])
         | "int64" | "uint64" -> lowBoxI ctx (LPrim (FToL, [ wide ]))
         | "byte" -> LPrim (AndW, [ LPrim (FToW, [ wide ]); LConstW 0xFF ])
         | "sbyte" -> LPrim (ShrSW, [ LPrim (ShlW, [ LPrim (FToW, [ wide ]); LConstW 24 ]); LConstW 24 ])
         | "uint16" -> LPrim (AndW, [ LPrim (FToW, [ wide ]); LConstW 0xFFFF ])
         | "int16" -> LPrim (ShrSW, [ LPrim (ShlW, [ LPrim (FToW, [ wide ]); LConstW 16 ]); LConstW 16 ])
         | _ -> LPrim (FToW, [ wide ]))
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#l" || n = "int#l" ->
        (LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ]))
    // uint64 shares int64's i64 box: `int u` wraps to the low 32 bits
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#v" ->
        (LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ]))
    // int64-of-FLOAT truncates the double; int64-of-int64 is the identity;
    // anything else sign-extends the i32 word (the old single form widened a
    // boxed-double POINTER for `int64 0.0`)
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int64#f" || n.StartsWith "int64#s" ->
        lowBoxI ctx (LPrim (FToL, [ lowUnboxF (coreToLowE ctx a) ]))
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int64#l" || n.StartsWith "int64#v" -> coreToLowE ctx a
    // int64-of-STRING parses ('t' is the string kind letter): the catchall
    // widened the string POINTER before
    // parse FROM a string: float/float32 through $atof, char = its first unit
    | EApp (EUnknown n, [ a ]) when n.StartsWith "float#t" || n.StartsWith "double#t" ->
        lowBoxF ctx (LCall ("$atof", [ coreToLowE ctx a ]))
    | EApp (EUnknown n, [ a ]) when n.StartsWith "float32#t" || n.StartsWith "single#t" ->
        lowBoxF ctx (LPrim (PromF, [ LPrim (DemF, [ LCall ("$atof", [ coreToLowE ctx a ]) ]) ]))
    | EApp (EUnknown n, [ a ]) when n.StartsWith "char#t" ->
        LLoad (I16, coreToLowE ctx a, 8)
    | EApp (EUnknown n, [ a ]) when n = "int#" || n.StartsWith "int#i" -> coreToLowE ctx a
    // BARE `int x` (the operand kind was not recorded — a `|> int` pipe):
    // route by the argument's static classification; a raw word is already
    // the int
    | EApp (EUnknown "int", [ a ]) ->
        (match printConOf ctx.LSt a with
         | "float" | "float32" | "double" | "single" -> LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ])
         | "int64" | "uint64" -> LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ])
         | "string" -> LCall ("$atoi", [ coreToLowE ctx a ])
         | _ -> coreToLowE ctx a)
    | EApp (EUnknown "uint32", [ a ]) ->
        (match printConOf ctx.LSt a with
         | "float" | "float32" | "double" | "single" -> LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ])
         | "int64" | "uint64" -> LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ])
         | _ -> coreToLowE ctx a)
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int64#t" ->
        lowBoxI ctx (LCall ("$atol", [ coreToLowE ctx a ]))
    | EApp (EUnknown n, [ a ]) when n = "int64#" || n.StartsWith "int64#" ->
        lowBoxI ctx (LPrim (WToL, [ (coreToLowE ctx a) ]))
    | EApp (EUnknown n, [ a ]) when (n = "float#" || n.StartsWith "float#") && not (n.StartsWith "float32") ->
        lowBoxF ctx (LPrim (WToF, [ (coreToLowE ctx a) ]))
    // char and int share the tagged-int representation, so `int c` / `char i`
    // are the identity
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#c" || n.StartsWith "char" -> coreToLowE ctx a
    // uint32 shares the raw i32 word: int<->uint32 are identities; from a
    // float it truncates; from int64 it wraps the low word
    | EApp (EUnknown n, [ a ]) when n.StartsWith "uint32#f" || n.StartsWith "uint32#s" ->
        LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "uint32#l" || n.StartsWith "uint32#v" ->
        LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ])
    | EApp (EUnknown n, [ a ]) when n = "uint32#" || n.StartsWith "uint32#" -> coreToLowE ctx a
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#w" || n.StartsWith "int#p" -> coreToLowE ctx a
    // nativeint is the raw word: from an int/uint32 it is the identity, from
    // a float it truncates, from a wide int it wraps
    | EApp (EUnknown n, [ a ]) when n.StartsWith "nativeint#f" || n.StartsWith "nativeint#s" ->
        LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "nativeint#l" || n.StartsWith "nativeint#v" ->
        LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "nativeint#t" -> LCall ("$atoi", [ coreToLowE ctx a ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "nativeint#" -> coreToLowE ctx a
    // uint64 rides the boxed i64: from float truncates, from ints widens
    | EApp (EUnknown n, [ a ]) when n.StartsWith "uint64#f" || n.StartsWith "uint64#s" ->
        lowBoxI ctx (LPrim (FToL, [ lowUnboxF (coreToLowE ctx a) ]))
    | EApp (EUnknown n, [ a ]) when n.StartsWith "uint64#l" || n.StartsWith "uint64#v" -> coreToLowE ctx a
    | EApp (EUnknown n, [ a ]) when n.StartsWith "uint64#t" ->
        lowBoxI ctx (LCall ("$atol", [ coreToLowE ctx a ]))
    | EApp (EUnknown n, [ a ]) when n = "uint64#" || n.StartsWith "uint64#" ->
        lowBoxI ctx (LPrim (WToL, [ coreToLowE ctx a ]))
    // int from float: unbox, truncate, tag
    // int of float OR float32 — a float32 value rides the same boxed f64
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#f" || n.StartsWith "int#s" -> (LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ]))
    // int from int (widen/identity in the tagged model) and int truncations
    // int-of-STRING parses ('t' is the string kind letter): the identity here
    // returned the string POINTER — the self-hosted BinDriver's
    // `int (l.Substring 5)` env-slot parse emitted heap addresses as slot
    // indices (145 diverging bodies vs the oracle)
    | EApp (EUnknown n, [ a ]) when n.StartsWith "int#t" -> LCall ("$atoi", [ coreToLowE ctx a ])
    // byte / narrow: mask the tagged value's payload to 8 bits
    // byte-of-FLOAT truncates first ('f'/'s' operand kind); the plain mask
    // AND'd a boxed-double POINTER before
    | EApp (EUnknown n, [ a ]) when n.StartsWith "byte#f" || n.StartsWith "byte#s" ->
        LPrim (AndW, [ LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ]); LConstW 0xFF ])
    // byte-of-int64 wraps the low 8 of the wide payload
    | EApp (EUnknown n, [ a ]) when n.StartsWith "byte#l" || n.StartsWith "byte#v" ->
        LPrim (AndW, [ LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ]); LConstW 0xFF ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "byte#" -> (LPrim (AndW, [ (coreToLowE ctx a); LConstW 0xFF ]))
    // the remaining NARROW conversions, by operand kind: sbyte sign-extends
    // the low byte, int16 the low half, uint16 masks it
    | EApp (EUnknown n, [ a ]) when n.StartsWith "sbyte#" || n.StartsWith "int16#" || n.StartsWith "uint16#" ->
        let w =
            if n.StartsWith "sbyte#f" || n.StartsWith "sbyte#s" || n.StartsWith "int16#f" || n.StartsWith "int16#s" || n.StartsWith "uint16#f" || n.StartsWith "uint16#s" then
                LPrim (FToW, [ lowUnboxF (coreToLowE ctx a) ])
            elif n.StartsWith "sbyte#l" || n.StartsWith "sbyte#v" || n.StartsWith "int16#l" || n.StartsWith "int16#v" || n.StartsWith "uint16#l" || n.StartsWith "uint16#v" then
                LPrim (LToW, [ lowUnboxI (coreToLowE ctx a) ])
            else coreToLowE ctx a
        if n.StartsWith "uint16#" then LPrim (AndW, [ w; LConstW 0xFFFF ])
        elif n.StartsWith "int16#" then LPrim (ShrSW, [ LPrim (ShlW, [ w; LConstW 16 ]); LConstW 16 ])
        else LPrim (ShrSW, [ LPrim (ShlW, [ w; LConstW 24 ]); LConstW 24 ])
    // the raw bits of a double, as int64 — read the boxed payload as i64
    | EApp (EUnknown "doubleBits", [ a ]) -> lowBoxI ctx (LLoad (I64, coreToLowE ctx a, HDR))
    // singleBits: a float32's raw i32 bits. float32 rides an f64 box here, so
    // re-demote to f32 and reinterpret (mirrors storUnbox for float32).
    | EApp (EUnknown "singleBits", [ a ]) -> (LPrim (F2Bits, [ LPrim (DemF, [ lowUnboxF (coreToLowE ctx a) ]) ]))
    // `float32 x`/`float16 x` FROM a float: round to f32 precision and keep the
    // value in its f64 box (demote then promote). Half rides the same box; f32
    // rounding is the closest we do without a dedicated f16 path.
    | EApp (EUnknown ("float32#f" | "single#f"), [ a ]) ->
        lowBoxF ctx (LPrim (PromF, [ LPrim (DemF, [ lowUnboxF (coreToLowE ctx a) ]) ]))
    // ---- float16: a half IS its 16 raw bits in a word ---------------------
    // INTO a half: round the value to half precision, keep the bits
    | EApp (EUnknown "float16#f", [ a ]) -> LCall ("$f2h64", [ lowUnboxF (coreToLowE ctx a) ])
    | EApp (EUnknown "float16#s", [ a ]) -> LCall ("$f2h64", [ lowUnboxF (coreToLowE ctx a) ])
    | EApp (EUnknown "float16#h", [ a ]) -> coreToLowE ctx a
    | EApp (EUnknown "float16#l", [ a ]) -> LCall ("$f2h64", [ LPrim (LToF, [ lowUnboxI (coreToLowE ctx a) ]) ])
    | EApp (EUnknown "float16#t", [ a ]) -> LCall ("$f2h64", [ LCall ("$atof", [ coreToLowE ctx a ]) ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "float16#" ->
        LCall ("$f2h64", [ LPrim (WToF, [ coreToLowE ctx a ]) ])
    // printh: a half prints as the f64 its bits widen to
    | EApp (EUnknown "printh", [ a ]) ->
        let v = LCall ("$ftoa_s", [ lowBoxF ctx (LPrim (PromF, [ LCall ("$h2f", [ coreToLowE ctx a ]) ])) ])
        LDo ([ LCallVoidS ("$prints", [ v ]); LCallVoidS ("$prints", [ LCall ("$str_of_char", [ LConstW 10 ]) ]) ], lowInt 0)
    // print / printraw: write a string to stdout (print's newline matters only
    // on the compiler's error paths, which the fixpoint success path never hits)
    // `print` writes the string THEN a newline (matching the GC backend's putc
    // '\n'); `printraw`/`printRaw` are the newline-free form.
    | EApp (EUnknown pn, [ a ]) when pn = "print" || pn.StartsWith "print#" ->
        // linear has no runtime value dispatch ($printval): a raw int is
        // indistinguishable from a pointer. Pick the path from the argument's
        // STATIC type — ints through $str_of_int, floats through the
        // shortest-form $ftoa_s, anything else prints as the string it must be.
        // the routed kind (Lower's "print#k") beats the local classifier
        let routed =
            if pn.StartsWith "print#" then
                match pn.Substring 6 with
                | "i" -> "int" | "f" -> "float" | "s" -> "float32" | "t" -> "string"
                | "l" -> "int64" | "v" -> "uint64" | "w" -> "uint32" | "b" -> "bool"
                | "c" -> "char" | "p" -> "nativeint" | _ -> ""
            else ""
        let con =
            if routed <> "" then routed else
            match printConOf ctx.LSt a with
            | "" -> (if refKindOfExpr a = RKRaw then "int" else "")
            | c -> c
        if System.Environment.GetEnvironmentVariable "FPP_PRINT_DUMP" = "1" then
            // no %A here: it lowers to showv, which the SELF-HOSTED backend
            // stubs — and a gap anywhere in this body stubs ALL of coreToLowE
            ewarn ("PRINTARG con=" + con + " a=" + Fpp.Core.Ir.printExpr a)
        let v =
            match con with
            | "int" | "int32" | "nativeint" | "byte" | "sbyte" | "int16" | "uint16" -> LCall ("$str_of_int", [ coreToLowE ctx a ])
            | "char" -> LCall ("$str_of_char", [ coreToLowE ctx a ])
            | "bool" ->
                let t = freshTmp ctx
                LDo ([ LIf (LPrim (EqW, [ coreToLowE ctx a; LConstW 0 ]),
                            [ LSet (wReg t, lowStrConst ctx.LSt "\"False\"") ],
                            [ LSet (wReg t, lowStrConst ctx.LSt "\"True\"") ]) ], LGet (wReg t))
            | "float" | "float32" | "double" | "single" -> LCall ("$ftoa_s", [ coreToLowE ctx a ])
            | "int64" -> LCall ("$ltoa_s", [ coreToLowE ctx a ])
            | "uint64" -> LCall ("$ultoa_s", [ coreToLowE ctx a ])
            // a raw uint32 zero-extends into the unsigned 64-bit formatter
            | "uint32" ->
                LCall ("$ultoa_s", [ lowBoxI ctx (LPrim (AndL, [ LPrim (WToL, [ coreToLowE ctx a ]); LConstL 4294967295L ])) ])
            // an unclassified operand is decided at RUNTIME by shape — a
            // generic `print x` handed $prints a boxed float otherwise
            | "" -> LCall ("$strv", [ coreToLowE ctx a ])
            | _ -> coreToLowE ctx a
        LDo ([ LCallVoidS ("$prints", [ v ]); LCallVoidS ("$prints", [ LCall ("$str_of_char", [ LConstW 10 ]) ]) ], lowInt 0)
    // an unsigned 32-bit value prints unsigned: zero-extend the raw word
    // into the unsigned 64-bit formatter (mirrors the GC backend's printu)
    | EApp (EUnknown "printu", [ a ]) ->
        let v = LCall ("$ultoa_s", [ lowBoxI ctx (LPrim (AndL, [ LPrim (WToL, [ coreToLowE ctx a ]); LConstL 4294967295L ])) ])
        LDo ([ LCallVoidS ("$prints", [ v ]); LCallVoidS ("$prints", [ LCall ("$str_of_char", [ LConstW 10 ]) ]) ], lowInt 0)
    // Boolean.ToString spells it with a capital
    | EApp (EUnknown "printb", [ a ]) ->
        let t = freshTmp ctx
        LDo ([ LIf (LPrim (EqW, [ coreToLowE ctx a; LConstW 0 ]),
                    [ LSet (wReg t, lowStrConst ctx.LSt "\"False\"") ],
                    [ LSet (wReg t, lowStrConst ctx.LSt "\"True\"") ])
               LCallVoidS ("$prints", [ LGet (wReg t) ])
               LCallVoidS ("$prints", [ LCall ("$str_of_char", [ LConstW 10 ]) ]) ], lowInt 0)
    // a char prints as the character, not its code
    | EApp (EUnknown "printc", [ a ]) ->
        LDo ([ LCallVoidS ("$prints", [ LCall ("$str_of_char", [ coreToLowE ctx a ]) ])
               LCallVoidS ("$prints", [ LCall ("$str_of_char", [ LConstW 10 ]) ]) ], lowInt 0)
    | EApp (EUnknown ("printraw" | "printRaw"), [ a ]) -> LDo ([ LCallVoidS ("$printraw", [ coreToLowE ctx a ]) ], lowInt 0)
    | EApp (EUnknown "isNull", [ x ]) -> (LPrim (EqW, [ coreToLowE ctx x; LConstW 0 ]))
    | EApp (EUnknown ("refEq" | "$refeq"), [ a; b ]) -> (LPrim (EqW, [ coreToLowE ctx a; coreToLowE ctx b ]))
    // a CLASS instance hashes by IDENTITY (DIVERGENCES.md): stable across
    // mutation and moves (fpprt keeps the table), distinct per object
    | EApp (EUnknown ("hash" | "$hash"), [ a ]) when
        (dictTryFind st.ClassNames (printConOf ctx.LSt a)).IsSome ->
        if gc then LCall ("$fpidh", [ coreToLowE ctx a ])
        else coreToLowE ctx a
    | EApp (EUnknown ("hash" | "$hash"), [ a ]) ->
        // route by the operand's witness when it is a type parameter: a RAW
        // element (refMask 0 — int/char/bool) IS its own hash (matches $hashv's
        // tagged-int path, which returns the untagged value); a ref element
        // hashes structurally via $hashv. Without a witness, $hashv as before.
        (match (match tyVarIdOfExpr a |> Option.bind (fun vid -> dictTryFind ctx.Witness vid) with Some w -> Some w | None -> ctx.ClassWit) with
         | Some w ->
             let at = freshTmp ctx
             let t = freshTmp ctx
             LDo ([ LSet (wReg at, coreToLowE ctx a)
                    LIf (LPrim (EqW, [ LLoad (W, LGet (wReg w), 8); LConstW 0 ]),
                         [ LSet (wReg t, LGet (wReg at)) ],
                         [ LSet (wReg t, LCall ("$hashv", [ LGet (wReg at) ])) ]) ], LGet (wReg t))
         | None -> LCall ("$hashv", [ coreToLowE ctx a ]))
    // cells: $cellof yields the cell POINTER (its storage, no deref); $cellget
    // reads through it; $cellset writes; $forcecell is a marker
    | EApp (EUnknown "$cellof", [ (EVar (v, _) | EVarI (v, _, _)) ]) -> lowVarStore ctx (key v)
    | EApp (EUnknown "$cellget", [ c ]) -> LLoad (W, coreToLowE ctx c, cellOff ())
    | EApp (EUnknown "$cellset", [ c; v ]) ->
        // stale-address hazard (see EFieldSet): root the cell across an
        // allocating value.
        if gc then
            let ra, rb, pre = evalRooted ctx c v
            LDo (pre @ chkStoreStmts rb @ [ LStore (W, LGet (wReg ra), cellOff (), LGet (wReg rb)) ], lowInt 0)
        else LDo ([ LStore (W, coreToLowE ctx c, cellOff (), coreToLowE ctx v) ], lowInt 0)
    | EApp (EUnknown "$forcecell", [ r ]) -> coreToLowE ctx r
    | EApp (EUnknown "$str.StartsWith", [ s; p ]) -> lowCallR ctx "$str_starts" [ s; p ]
    | EApp (EUnknown "$str.EndsWith", [ s; p ]) -> lowCallR ctx "$str_ends" [ s; p ]
    | EApp (EUnknown "$str.Contains", [ s; p ]) ->
        (LPrim (GeSW, [ lowCallR ctx "$str_find" [ s; p; ELit (LInt "0") ]; LConstW 0 ]))
    | EApp (EUnknown "$str.IndexOf", [ s; p ]) ->
        (lowCallR ctx "$str_find" [ s; p; ELit (LInt "0") ])
    | EApp (EUnknown "$str.IndexOf#2", [ s; c ]) ->
        (LCall ("$str_find_char", [ coreToLowE ctx s; (coreToLowE ctx c) ]))
    | EApp (EUnknown "$str.IndexOf#3", [ s; p; from ]) ->
        (lowCallR ctx "$str_find" [ s; p; from ])
    | EApp (EUnknown "$str.LastIndexOf", [ s; c ]) ->
        (LCall ("$str_last_find_char", [ coreToLowE ctx s; (coreToLowE ctx c) ]))
    | EApp (EUnknown "$str.Split", [ s; c ]) ->
        // returns a heap string array (an even pointer), not a tagged value
        LCall ("$str_split_char", [ coreToLowE ctx s; (coreToLowE ctx c) ])
    | EApp (EUnknown "$str.Contains#2", [ s; c ]) ->
        (LPrim (GeSW, [ LCall ("$str_find_char", [ coreToLowE ctx s; (coreToLowE ctx c) ]); LConstW 0 ]))
    | EApp (EUnknown "$str.StartsWith#2", [ s; c ]) ->
        (LPrim (EqW, [ LCall ("$str_find_char", [ coreToLowE ctx s; (coreToLowE ctx c) ]); LConstW 0 ]))
    | EApp (EUnknown "$str.EndsWith#2", [ s; c ]) ->
        // last occurrence index == len-1 (and >=0, which excludes the empty string)
        let sv = freshTmp ctx
        let nv = freshTmp ctx
        LDo ([ LSet (wReg sv, coreToLowE ctx s)
               LSet (wReg nv, LCall ("$str_last_find_char", [ LGet (wReg sv); (coreToLowE ctx c) ])) ],
             LPrim (AndW, [ LPrim (GeSW, [ LGet (wReg nv); LConstW 0 ]); LPrim (EqW, [ LGet (wReg nv); LPrim (SubW, [ LLoad (W, LGet (wReg sv), HDR); LConstW 1 ]) ]) ]))
    | EApp (EUnknown "$str.ToUpper", [ s ]) -> LCall ("$str_upper", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.ToLower", [ s ]) -> LCall ("$str_lower", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.ToCharArray", [ s ]) -> LCall ("$str_chars", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.PadLeft", [ s; w ]) ->
        LCall ("$str_pad", [ coreToLowE ctx s; (coreToLowE ctx w); LConstW 32; LConstW 0 ])
    | EApp (EUnknown "$str.PadRight", [ s; w ]) ->
        LCall ("$str_pad", [ coreToLowE ctx s; (coreToLowE ctx w); LConstW 32; LConstW 1 ])
    | EApp (EUnknown ("$str.TrimStart" | "$str.TrimStart#2"), [ s; cs ]) ->
        // the helper tells a char from an array by the LOW BIT — a raw char
        // is an even word, so a statically-char argument must arrive tagged
        (match printConOf ctx.LSt cs with
         | "char" ->
             let ts = freshTmp ctx
             LDo ([ LSet (wReg ts, coreToLowE ctx s) ],
                  LCall ("$str_trim_start_chars", [ LGet (wReg ts); lowTag (coreToLowE ctx cs) ]))
         | _ -> lowCallR ctx "$str_trim_start_chars" [ s; cs ])
    | EApp (EUnknown ("$str.TrimEnd" | "$str.TrimEnd#2"), [ s; cs ]) ->
        (match printConOf ctx.LSt cs with
         | "char" ->
             let ts = freshTmp ctx
             LDo ([ LSet (wReg ts, coreToLowE ctx s) ],
                  LCall ("$str_trim_end_chars", [ LGet (wReg ts); lowTag (coreToLowE ctx cs) ]))
         | _ -> lowCallR ctx "$str_trim_end_chars" [ s; cs ])
    | EApp (EUnknown "$str.Insert", [ s; i; v ]) ->
        lowCallR ctx "$str_insert" [ s; i; v ]
    | EApp (EUnknown "$str.Remove", [ s; i ]) ->
        LCall ("$strsub", [ coreToLowE ctx s; LConstW 0; (coreToLowE ctx i) ])
    | EApp (EUnknown "$str.Remove#2", [ s; i; n ]) ->
        LCall ("$str_remove2", [ coreToLowE ctx s; (coreToLowE ctx i); (coreToLowE ctx n) ])
    | EApp (EUnknown "$str.Trim", [ s ]) -> LCall ("$str_trim", [ coreToLowE ctx s ])
    | EApp (EUnknown "$str.Replace", [ s; a; b ]) -> lowCallR ctx "$str_replace" [ s; a; b ]
    | EApp (EUnknown ("$str.Substring#2" | "strsub"), [ s; start; len ]) ->
        LCall ("$strsub", [ coreToLowE ctx s; (coreToLowE ctx start); (coreToLowE ctx len) ])
    | EApp (EUnknown "$str.Substring", [ s; start ]) ->
        // one-arg Substring runs to the end: len = s.Length - start
        let ts = freshTmp ctx
        let ti = freshTmp ctx
        LDo ([ LSet (wReg ts, coreToLowE ctx s); LSet (wReg ti, (coreToLowE ctx start)) ],
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
             (LGet (wReg n)))
    | EApp (EUnknown "failwith", [ msg ]) ->
        LDo ([ LThrow (lowFailure ctx (coreToLowE ctx msg)) ], lowInt 0)
    | EApp (EUnknown "raise", [ ex ]) ->
        st.UsesExn <- true
        LDo ([ LThrow (coreToLowE ctx ex) ], lowInt 0)
    | EApp (EUnknown ("invalidArg" | "invalidOp" | "nullArg"), args) ->
        // approximate as Failure(message): the last argument is the message
        let msg = match List.rev args with m :: _ -> coreToLowE ctx m | [] -> LConstW 0
        LDo ([ LThrow (lowFailure ctx msg) ], lowInt 0)
    // the monotonic clock in MILLISECONDS as a float: WASI writes 64-bit
    // nanoseconds into the low scratch slot, which nothing else uses between
    // the call and the read
    | EApp (EUnknown "monoms", [ u ]) ->
        LDo ([ LEval (coreToLowE ctx u)
               LEval (LCall ("$clock_time_get", [ LConstW 1; LConstL 1000000L; LConstW MONO_SCRATCH ])) ],
             lowBoxF ctx (LPrim (DivF, [ LPrim (LToF, [ LLoad (I64, LConstW MONO_SCRATCH, 0) ]); LConstF 1000000.0 ])))
    | EApp (EUnknown "showv", [ a ]) -> LCall ("$showv", [ coreToLowE ctx a ])
    // enum HasFlag: (a &&& b) = b on the raw int representation
    | EApp (EUnknown "$hasflag", [ a; b ]) ->
        let t = freshTmp ctx
        LDo ([ LSet (wReg t, coreToLowE ctx b) ],
             LPrim (EqW, [ LPrim (AndW, [ coreToLowE ctx a; LGet (wReg t) ]); LGet (wReg t) ]))
    // the REFERENCE hash: stable per object across collections (fpprt keeps
    // the side table); standalone never moves, so the address serves
    | EApp (EUnknown ("$idhash" | "idhash"), [ a ]) ->
        if gc then LCall ("$fpidh", [ coreToLowE ctx a ]) else coreToLowE ctx a
    | EApp (EUnknown "prints", [ a ]) -> LDo ([ LCallVoidS ("$prints", [ coreToLowE ctx a ]) ], lowInt 0)
    // the DEBUG channel: Lower expands eprintf/eprintfn to `eprints` (fd 2)
    | EApp (EUnknown "eprints", [ a ]) -> LDo ([ LCallVoidS ("$eprints", [ coreToLowE ctx a ]) ], lowInt 0)
    // a bare/unexpanded eprintfn reference still no-ops rather than gapping
    | EApp (EUnknown ("eprintfn" | "eprintf"), args) ->
        LDo (args |> List.map (fun a -> LEval (coreToLowE ctx a)), lowInt 0)
    // System.Environment.GetEnvironmentVariable: the debug-probe gate. A
    // null answer turns every probe OFF instead of stubbing the whole
    // function that carries it (which silently trap-stubbed the ENTIRE
    // linear emitter under self-host — gcTid, emitLowE, emitLinearImpl)
    | EApp (EField (EField (EUnknown "System", "Environment", _), "GetEnvironmentVariable", _), args) ->
        LDo (args |> List.map (fun a -> LEval (coreToLowE ctx a)), lowInt 0)
    // string of a char: a fresh one-unit string (NOT the decimal of its code)
    | EApp (EUnknown "string#c", [ a ]) -> LCall ("$str_of_char", [ (coreToLowE ctx a) ])
    // string of a string is the identity
    | EApp (EUnknown "string#t", [ a ]) -> coreToLowE ctx a
    // string of a float/float32: the shortest form, matching .NET ToString
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string#f" || n.StartsWith "string#d" || n.StartsWith "string#s" ->
        LCall ("$ftoa_s", [ coreToLowE ctx a ])
    // string of an int64/uint64 box: decimal via the i64 digit writer
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string#l" -> LCall ("$ltoa_s", [ coreToLowE ctx a ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string#v" -> LCall ("$ultoa_s", [ coreToLowE ctx a ])
    // string of a bool spells True/False, as .NET's ToString does
    | EApp (EUnknown "string#b", [ a ]) ->
        let t = freshTmp ctx
        LDo ([ LIf (LPrim (EqW, [ coreToLowE ctx a; LConstW 0 ]),
                    [ LSet (wReg t, lowStrConst ctx.LSt "\"False\"") ],
                    [ LSet (wReg t, lowStrConst ctx.LSt "\"True\"") ]) ], LGet (wReg t))
    // string of a raw uint32: zero-extend into the unsigned 64-bit writer
    | EApp (EUnknown "string#w", [ a ]) ->
        LCall ("$ultoa_s", [ lowBoxI ctx (LPrim (AndL, [ LPrim (WToL, [ coreToLowE ctx a ]); LConstL 4294967295L ])) ])
    // `string x` with NO static kind (a generic body's `string x.V`): decide
    // at RUNTIME from the representation. Answering $str_of_int printed the
    // POINTER of a boxed float.
    | EApp (EUnknown ("string#" | "string"), [ a ]) -> LCall ("$strv", [ coreToLowE ctx a ])
    | EApp (EUnknown n, [ a ]) when n.StartsWith "string" -> LCall ("$str_of_int", [ coreToLowE ctx a ])
    // a call to an `extern` host import: no host env yet, so answer the null
    // default (readTextRaw null -> None), letting the pipeline RUN instead of
    // stubbing the caller. Args still evaluate for their side effects.
    // preludeSourceRaw returns the baked prelude text (empty unless a compiler is
    // being emitted); other host externs still answer null.
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when v.Name = "preludeSourceRaw" && preludeSrc <> "" ->
        LDo (args |> List.map (fun a -> LEval (coreToLowE ctx a)), lowStrConstRaw st preludeSrc)
    // the FILE externs are real now, over WASI against the preopened dir —
    // what lets the SELF-HOSTED compiler load sources (the linear fixpoint)
    | EApp ((EVar (v, _) | EVarI (v, _, _)), [ a ]) when v.Name = "readTextRaw" ->
        LCall ("$readfile", [ coreToLowE ctx a ])
    | EApp ((EVar (v, _) | EVarI (v, _, _)), [ a ]) when v.Name = "existsRaw" ->
        LCall ("$fexists", [ coreToLowE ctx a ])
    | EApp ((EVar (v, _) | EVarI (v, _, _)), [ a ]) when v.Name = "canonicalizeRaw" ->
        coreToLowE ctx a
    // ---- the JS boundary (Js.* primitives; module "jslin") -----------------
    // Handles are raw i32 ids (JsObj is a raw scalar), ints/bools cross raw,
    // floats unbox to f64 at the boundary, strings cross as linear pointers
    // the glue decodes. Mirrors the wasm-GC jsx/js ABI minus externref.
    // String (REF) operands route through lowRootedArgsK: an import call can
    // re-enter wasm through a callback and collect mid-argument-list.
    | EApp (EUnknown "jsGlobal", [ k ]) -> lowJsi ctx "$jsi_global" "h" [ RKRef, W, coreToLowE ctx k ]
    | EApp (EUnknown "jsGet", [ o; k ]) -> lowJsi ctx "$jsi_get" "h" [ RKRaw, W, coreToLowE ctx o; RKRef, W, coreToLowE ctx k ]
    | EApp (EUnknown "jsSet", [ o; k; v ]) -> lowJsi ctx "$jsi_set" "u" [ RKRaw, W, coreToLowE ctx o; RKRef, W, coreToLowE ctx k; RKRaw, W, coreToLowE ctx v ]
    | EApp (EUnknown "jsGetNum", [ o; k ]) -> lowJsi ctx "$jsi_getNum" "d" [ RKRaw, W, coreToLowE ctx o; RKRef, W, coreToLowE ctx k ]
    | EApp (EUnknown "jsSetNum", [ o; k; v ]) -> lowJsi ctx "$jsi_setNum" "u" [ RKRaw, W, coreToLowE ctx o; RKRef, W, coreToLowE ctx k; RKRaw, F64, flatUnbox F64 (coreToLowE ctx v) ]
    | EApp (EUnknown "jsItem", [ o; i ]) -> lowJsi ctx "$jsi_item" "h" [ RKRaw, W, coreToLowE ctx o; RKRaw, W, coreToLowE ctx i ]
    | EApp (EUnknown "jsItemSet", [ o; i; v ]) -> lowJsi ctx "$jsi_itemSet" "u" [ RKRaw, W, coreToLowE ctx o; RKRaw, W, coreToLowE ctx i; RKRaw, W, coreToLowE ctx v ]
    | EApp (EUnknown "jsCallback", [ clo ]) -> lowJsi ctx "$jsi_mkFn" "h" [ RKRaw, W, LCall ("$cbreg", [ coreToLowE ctx clo ]) ]
    | EApp (EUnknown n, (o :: k :: rest)) when n.StartsWith "jsCall" ->
        lowJsi ctx ("$jsi_call" + n.Substring 6) "h"
            ((RKRaw, W, coreToLowE ctx o) :: (RKRef, W, coreToLowE ctx k)
             :: (rest |> List.map (fun a -> RKRaw, W, coreToLowE ctx a)))
    | EApp (EUnknown n, (c :: rest)) when (n = "jsNew0" || n = "jsNew1" || n = "jsNew2") ->
        lowJsi ctx ("$jsi_new" + n.Substring 5) "h"
            ((RKRaw, W, coreToLowE ctx c) :: (rest |> List.map (fun a -> RKRaw, W, coreToLowE ctx a)))
    | EApp (EUnknown "jsOfNum", [ a ]) -> lowJsi ctx "$jsi_num" "h" [ RKRaw, F64, flatUnbox F64 (coreToLowE ctx a) ]
    | EApp (EUnknown "jsToNum", [ a ]) -> lowJsi ctx "$jsi_toNum" "d" [ RKRaw, W, coreToLowE ctx a ]
    | EApp (EUnknown "jsOfBool", [ a ]) -> lowJsi ctx "$jsi_bool" "h" [ RKRaw, W, coreToLowE ctx a ]
    | EApp (EUnknown "jsToBool", [ a ]) -> lowJsi ctx "$jsi_toBool" "h" [ RKRaw, W, coreToLowE ctx a ]
    | EApp (EUnknown "jsOfString", [ a ]) -> lowJsi ctx "$jsi_str" "h" [ RKRef, W, coreToLowE ctx a ]
    | EApp (EUnknown "jsToString", [ a ]) -> lowJsi ctx "$jsi_tostr" "h" [ RKRaw, W, coreToLowE ctx a ]
    | EApp (EUnknown "jsUndefined", [ _ ]) -> LCall ("$jsi_undef", [])
    | EApp (EUnknown "jsNewObj", [ _ ]) -> LCall ("$jsi_obj", [])
    | EApp (EUnknown "jsNewArr", [ _ ]) -> LCall ("$jsi_arr", [])
    | EApp (EUnknown "jsPush", [ a; v ]) -> lowJsi ctx "$jsi_push" "u" [ RKRaw, W, coreToLowE ctx a; RKRaw, W, coreToLowE ctx v ]
    // a handle IS its id on linear: to/from int is the identity
    | EApp (EUnknown "jsHandle", [ i ]) -> coreToLowE ctx i
    | EApp (EUnknown "jsRegister", [ o ]) -> coreToLowE ctx o
    | EApp (EUnknown "jsWatch", [ w; i ]) ->
        // gc: watch the wrapper; its handle id queues (kind 0) when a
        // collection proves it dead, and the glue's drain frees the JS
        // table entry. Standalone has no collector — handles leak there.
        if gc then
            lowJsi ctx "$fpwatch" "u"
                [ RKRef, W, coreToLowE ctx w; RKRaw, W, coreToLowE ctx i; RKRaw, W, LConstW 0 ]
        else LDo ([ LEval (coreToLowE ctx w); LEval (coreToLowE ctx i) ], lowInt 0)
    // ---- deterministic cleanup (GC.OnCleanup / GC.Collect) -----------------
    | EApp (EUnknown "gcOnCleanup", [ o; f ]) ->
        // park the cleanup closure in a rooted slot, watch the object with
        // the SLOT as its tag (kind 1); $gcdrain invokes and recycles it
        if gc then
            lowJsi ctx "$fpwatch" "u"
                [ RKRef, W, coreToLowE ctx o
                  RKRaw, W, LCall ("$cbreg", [ coreToLowE ctx f ])
                  RKRaw, W, LConstW 1 ]
        else LDo ([ LEval (coreToLowE ctx o); LEval (coreToLowE ctx f) ], lowInt 0)
    | EApp (EUnknown "gcCollect", [ _ ]) ->
        // zero the shadow-stack REGION above $sp first: every popped slot
        // keeps its last value and the whole registered range is scanned,
        // so residue would keep just-dead objects alive one collection
        // longer — the fill is what makes GC.Collect the DETERMINISTIC
        // point. (Natural collections skip it: eventual cleanup is fine.)
        if gc then LDo ([ LCallVoidS ("$rootswipe", []); LCallVoidS ("$fpcollect", []); LCallVoidS ("$gcdrain", []) ], lowInt 0)
        else lowInt 0
    | EApp (EUnknown "jsNull", [ _ ]) -> lowInt 0
    | EApp (EUnknown "jsIsNull", [ a ]) -> LPrim (EqW, [ coreToLowE ctx a; LConstW 0 ])
    | EApp (EUnknown vn, [ p; n ]) when vn.StartsWith "jsView" ->
        lowJsi ctx ("$jsi_view" + vn.Substring 6) "h" [ RKRaw, W, coreToLowE ctx p; RKRaw, W, coreToLowE ctx n ]
    // ---- raw linear-memory access (the Mem module) -------------------------
    | EApp (EUnknown "memAlloc", [ n ]) -> LAlloc (coreToLowE ctx n)
    | EApp (EUnknown "memSize", [ _ ]) -> LCall ("$memsize", [])
    | EApp (EUnknown "memCopy", [ d; s; n ]) ->
        LDo ([ LCallVoidS ("$memcopy", [ coreToLowE ctx d; coreToLowE ctx s; coreToLowE ctx n ]) ], lowInt 0)
    | EApp (EUnknown "memLoadByte", [ p ]) -> LLoad (I8, coreToLowE ctx p, 0)
    | EApp (EUnknown "memStoreByte", [ p; v ]) -> LDo ([ LStore (I8, coreToLowE ctx p, 0, coreToLowE ctx v) ], lowInt 0)
    | EApp (EUnknown "memLoadInt", [ p ]) -> LLoad (W, coreToLowE ctx p, 0)
    | EApp (EUnknown "memStoreInt", [ p; v ]) -> LDo ([ LStore (W, coreToLowE ctx p, 0, coreToLowE ctx v) ], lowInt 0)
    | EApp (EUnknown "memLoadInt64", [ p ]) -> lowBoxI ctx (LLoad (I64, coreToLowE ctx p, 0))
    | EApp (EUnknown "memStoreInt64", [ p; v ]) -> LDo ([ LStore (I64, coreToLowE ctx p, 0, lowUnboxI (coreToLowE ctx v)) ], lowInt 0)
    | EApp (EUnknown "memLoadFloat", [ p ]) -> lowBoxF ctx (LLoad (F64, coreToLowE ctx p, 0))
    | EApp (EUnknown "memStoreFloat", [ p; v ]) -> LDo ([ LStore (F64, coreToLowE ctx p, 0, flatUnbox F64 (coreToLowE ctx v)) ], lowInt 0)
    // nativeint <-> int are the same raw word
    | EApp (EUnknown n, [ a ]) when n.StartsWith "nativeint#" || n = "nativeint" || n.StartsWith "int#p" ->
        coreToLowE ctx a
    // ---- [<JsImport>] typed externs (module "jsxl") ------------------------
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when (dictTryFind jsxSigs (key v)).IsSome ->
        let fnm, _, pks, rk = optGet (dictTryFind jsxSigs (key v))
        // a unit param is evaluated for effect and dropped from the import's
        // argument list (matching the import signature's u-filter)
        let unitEvals =
            List.zip pks args |> List.filter (fun (k, _) -> k = "u")
            |> List.map (fun (_, a) -> LEval (coreToLowE ctx a))
        let ops =
            List.zip pks args |> List.filter (fun (k, _) -> k <> "u")
            |> List.map (fun (k, a) ->
                match k with
                | "s" -> RKRef, W, coreToLowE ctx a
                | "d" -> RKRaw, F64, flatUnbox F64 (coreToLowE ctx a)
                | _ -> RKRaw, W, coreToLowE ctx a)
        let call = lowJsi ctx fnm rk ops
        if List.isEmpty unitEvals then call else LDo (unitEvals, call)
    // the cleanup externs referenced from the prelude MEMBERS arrive as
    // EVars (same shape as readTextRaw) — route to the EUnknown lowering
    | EApp ((EVar (v, _) | EVarI (v, _, _)), [ o; f ]) when v.Name = "gcOnCleanup" ->
        coreToLowE ctx (EApp (EUnknown "gcOnCleanup", [ o; f ]))
    | EApp ((EVar (v, _) | EVarI (v, _, _)), [ u1 ]) when v.Name = "gcCollect" ->
        coreToLowE ctx (EApp (EUnknown "gcCollect", [ u1 ]))
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when (dictTryFind envSigs (key v)).IsSome ->
        let fnm, _, pks, rk = optGet (dictTryFind envSigs (key v))
        let unitEvals =
            List.zip pks args |> List.filter (fun (k, _) -> k = "u")
            |> List.map (fun (_, a) -> LEval (coreToLowE ctx a))
        let ops =
            List.zip pks args |> List.filter (fun (k, _) -> k <> "u")
            |> List.map (fun (k, a) ->
                match k with
                | "s" -> RKRef, W, coreToLowE ctx a
                | "d" -> RKRaw, F64, flatUnbox F64 (coreToLowE ctx a)
                | _ -> RKRaw, W, coreToLowE ctx a)
        let call = lowJsi ctx fnm rk ops
        if List.isEmpty unitEvals then call else LDo (unitEvals, call)
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when (dictTryFind st.Externs v.Name).IsSome ->
        LDo (args |> List.map (fun a -> LEval (coreToLowE ctx a)), lowInt 0)
    | EApp (((EVar (v, _) | EVarI (v, _, _)) as hd), args)
        when (dictTryFind st.Funcs (key v)) = Some (List.length args) ->
        // a generic callee takes hidden LEADING witness pointers, one per
        // quantified var, positionally matched to the call's type-arg names
        // (EVarI.inst, recorded by Infer): concrete name -> its static witness,
        // "#N" -> forward the enclosing witness param.
        let inst = match hd with EVarI (_, _, i) -> i | _ -> []
        let witnessArgs =
            match dictTryFind st.FuncWitness (key v) with
            | Some vids ->
                vids |> List.mapi (fun i vid ->
                    match List.tryItem i inst with
                    | Some nm -> witnessArgOfName ctx nm
                    | None ->
                        // no instantiation on this use — a RECURSIVE self/group
                        // call (Infer records no EVarI on a monomorphic self-use).
                        // The callee's quantified var IS the caller's, so forward
                        // the caller's own witness for it; the old blanket ref
                        // default made every recursive generic call scan raw
                        // scalars as pointers (sortWith<int>'s sublists).
                        match dictTryFind ctx.Witness vid with
                        | Some reg -> LGet (wReg reg)
                        | None -> witnessPtrRM st 4 4 1)
            | None -> []
        // a SELF call in tail position transfers via return_call: same
        // function, so the signature matches by construction. The result
        // needs no re-boxing — it IS this function's result.
        let isSelfTail =
            fn v = tailFnName && tailFnName <> ""
            && (match refMapTryFind st.TailApp e with Some true -> true | _ -> false)
        (match dictTryFind st.FuncSig (key v) with
         | Some (paramTys, retTy) ->
             let argVals = List.map2 (fun ty a ->
                             let lowered = match ty with W -> coreToLowE ctx a | _ -> flatUnbox ty (coreToLowE ctx a)
                             let kind = refKindOfExprC st a
                             let wit = if kind = RKGen then slotWitness ctx a else None
                             kind, wit, ty, lowered) paramTys args
             let setup, argGets = lowRootedArgsK ctx argVals
             let loweredArgs = witnessArgs @ argGets
             let callE =
                 if isSelfTail then LTailCall (fn v, loweredArgs)
                 else
                 match retTy with
                 | W -> LCall (fn v, loweredArgs)
                 // hold the scalar result in a typed local before boxing: the call
                 // is a safepoint, so a bare box-around-call would let the GC move
                 // the fresh box out from under the store. box-elim pushes through
                 // the LDo, so an arithmetic use still reduces to the raw call.
                 | _ -> let r = freshTmpT ctx retTy in LDo ([ LSet ({ Id = r; RTy = retTy }, LCall (fn v, loweredArgs)) ], flatBox ctx retTy (LGet { Id = r; RTy = retTy }))
             (if List.isEmpty setup then callE else LDo (setup, callE))
         | None ->
             let setup, argGets =
                 lowRootedArgsK ctx (args |> List.map (fun a ->
                     let kind = refKindOfExprC st a
                     let wit = if kind = RKGen then slotWitness ctx a else None
                     kind, wit, W, coreToLowE ctx a))
             let callE =
                 if isSelfTail then LTailCall (fn v, witnessArgs @ argGets)
                 else LCall (fn v, witnessArgs @ argGets)
             (if List.isEmpty setup then callE else LDo (setup, callE)))
    | ELam (_, _) ->
        (match refMapTryFind st.LamName e with
         | Some name -> lowClosure ctx name
         | None -> err st "wasm-linear LowIR: lambda not discovered"; lowInt 0)
    | EApp (g, args) -> lowApply ctx (coreToLowE ctx g) args
    | EMatch (scrut, clauses) ->
        let sc = freshTmp ctx
        let mr = freshTmp ctx
        // A clause GUARD can allocate (a safepoint): the collector moves the
        // scrutinee, and a FAILED guard falls to the next clause's tests, which
        // re-read the stale register (mapExpr's `| P when g e -> …` chain died
        // exactly there). Whenever any pattern dereferences the scrutinee — so
        // its value is a pointer at runtime whatever its static type says —
        // keep it in a shadow-stack slot for the whole match and reload the
        // register at each clause entry.
        let rec derefPat (p : Pat) =
            match p with
            // an enum case compares the RAW scrutinee value — never slotted
            // (a raw even int in a scanned root slot reads as a pointer)
            | PCtor (c, _, []) when (dictTryFind st.EnumConst c).IsSome -> false
            | PCtor _ | PTuple _ | PCons _ | PListLit _ | PTypeTest _ -> true
            | PLit (LString _) | PLit LNull -> true
            | PAs (p, _, _) -> derefPat p
            | POr ps -> List.exists derefPat ps
            | _ -> false
        let slotScrut = gc && List.exists (fun (p, _, _) -> derefPat p) clauses
        let scAddr = if slotScrut then freshTmp ctx else 0
        let scPush =
            if slotScrut then
                [ LSet (wReg scAddr, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
                  LStore (W, LGet (wReg scAddr), 0, LGet (wReg sc))
                  LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ]
            else []
        let scPop = if slotScrut then [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ])) ] else []
        let clauseStmts =
            clauses |> List.map (fun (pat, guard, body) ->
                let reload = if slotScrut then [ LSet (wReg sc, LLoad (W, LGet (wReg scAddr), 0)) ] else []
                let tests = lowPatTest ctx sc "$mnext" pat
                // root the arm's ref binders across the GUARD and the body: the
                // guard itself can allocate, and both the matched path (binders
                // read after it) and the fail path would otherwise see pre-GC
                // values. Copy each from its register into a shadow-stack slot,
                // read through the slot from here on.
                let slotRegs = (if gc then patRefBinders ctx pat else []) |> List.map (fun (v, _) -> v, freshTmp ctx)
                let pushes = slotRegs |> List.collect (fun (v, addrReg) ->
                    [ LSet (wReg addrReg, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
                      LStore (W, LGet (wReg addrReg), 0, LGet (wReg (regOf ctx (key v))))
                      LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ])
                for v, addrReg in slotRegs do dictSet ctx.Slotted (key v) (LGet (wReg addrReg))
                // generic (RKGen) binders: active across the arm body, rooted
                // conditionally at each safepoint via their element witness.
                let genB = patGenBinders ctx pat |> List.map (fun (v, w) -> regOf ctx (key v), w)
                // UNRESOLVED binders: ask the scrutinee object's scan map at
                // runtime and root conditionally (see patCondBinders)
                let condB =
                    if gc then
                        patCondBinders ctx pat |> List.map (fun (v, off) ->
                            v, off, freshTmp ctx, freshTmp ctx, freshTmp ctx)
                    else []
                let condSetup =
                    condB |> List.collect (fun (v, off, flagR, witR, slotR) ->
                        let w0 = witnessPtrRM ctx.LSt 4 4 0
                        let w1 = witnessPtrRM ctx.LSt 4 4 1
                        [ LSet (wReg flagR, LCall ("$tidscans", [ LPrim (ShrUW, [ LLoad (W, LGet (wReg sc), 0); LConstW 1 ]); LConstW off ]))
                          // wit = flag ? w1 : w0, branchless
                          LSet (wReg witR, LPrim (XorW, [ w0; LPrim (AndW, [ LPrim (XorW, [ w0; w1 ]); LPrim (SubW, [ LConstW 0; LGet (wReg flagR) ]) ]) ]))
                          gcSlotPush (regOf ctx (key v)) witR slotR ])
                let condPop = condB |> List.rev |> List.map (fun (_, _, _, witR, _) -> gcSlotPop witR)
                let pop = if List.isEmpty slotRegs then [] else [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW (4 * List.length slotRegs) ])) ]
                let savedGen = ctx.ActiveGen
                ctx.ActiveGen <- genB @ ctx.ActiveGen
                let savedSG = ctx.SlottedGen
                ctx.SlottedGen <- (condB |> List.map (fun (v, _, _, witR, slotR) -> regOf ctx (key v), witR, slotR)) @ ctx.SlottedGen
                // the guard runs AFTER the binder slots are live (its safepoints
                // are covered); a failing guard pops what this clause pushed
                // before breaking to the next clause's tests.
                let guardStmt =
                    match guard with
                    | Some g when List.isEmpty condPop && List.isEmpty pop ->
                        [ LBreakIf ("$mnext", LPrim (EqW, [ (coreToLowE ctx g); LConstW 0 ])) ]
                    | Some g ->
                        let gr = freshTmp ctx
                        [ LSet (wReg gr, coreToLowE ctx g)
                          LIf (LPrim (EqW, [ LGet (wReg gr); LConstW 0 ]),
                               condPop @ pop @ [ LBreak "$mnext" ], []) ]
                    | None -> []
                let bodyLow = coreToLowE ctx body
                ctx.SlottedGen <- savedSG
                ctx.ActiveGen <- savedGen
                for v, _ in slotRegs do dictRemove ctx.Slotted (key v)
                LBlock ("$mnext", reload @ tests @ pushes @ condSetup @ guardStmt @ [ LSet (wReg mr, bodyLow) ] @ condPop @ pop @ [ LBreak "$mdone" ]))
        LDo ([ LSet (wReg sc, coreToLowE ctx scrut) ] @ scPush
             @ [ LBlock ("$mdone", clauseStmts @ [ LTrap ]) ] @ scPop, LGet (wReg mr))
    | ETypeTest (tn, e2) -> (lowTypeTest ctx tn (coreToLowE ctx e2))
    | ECast (tn, e2, true) when
          not (List.isEmpty (typeTestIds st tn))
          || (let b = (if tn.Contains "$<" then tn.Substring (0, tn.IndexOf "$<") else tn) in
              List.contains b [ "int"; "bool"; "char"; "byte"; "sbyte"; "int16"; "uint16"; "uint32"
                                "float"; "int64"; "uint64"; "string" ]) ->
        // `:?>` downcast to a type we carry a class-id for: check the header
        // and trap on a mismatch, then yield the value unchanged
        // a failed `:?>` THROWS (an InvalidCastException in F#), it does not
        // trap: `try (o :?> B).N with _ -> ...` has to catch it. A trap is
        // uncatchable and killed the whole module.
        // NULL downcasts to anything (as in .NET): `downcast x.SetNext` at the
        // end of a linked chain is a null, and rejecting it threw where the
        // reference implementation walks off the end normally. A failed cast
        // of a NON-null value THROWS (an InvalidCastException), it does not
        // trap — `try (o :?> B).N with _ -> ...` has to catch it.
        let t = freshTmp ctx
        LDo ([ LSet (wReg t, coreToLowE ctx e2)
               LIf (LPrim (AndW, [ LPrim (NeW, [ LGet (wReg t); LConstW 0 ])
                                   LPrim (EqW, [ lowTypeTest ctx tn (LGet (wReg t)); LConstW 0 ]) ]),
                    [ LThrow (lowFailure ctx (lowStrConst ctx.LSt "\"invalid cast\"")) ], []) ],
             LGet (wReg t))
    | ECast (_, e2, _) ->
        // `:>` widening, and `:?>` to a type without a class-id: the identity —
        // the representation does not change under a cast in the tagged model
        coreToLowE ctx e2
    | EIfaceCall (iface, method, recv, args) ->
        let bi = bareIfaceOf iface
        let t = freshTmp ctx
        // dispatch through the vtable: the receiver's class-id header indexes a
        // row, the slot the column; the word there is the impl's table index.
        // Under GC the vtable is a fpprt array in a root slot (data past the
        // [tag][len] header), read fresh so a collection's move is seen.
        let vtDispatchWith (argEs : LExpr list) =
            let slot = match dictTryFind st.SlotOf (bi + "|" + method) with Some s -> s | None -> 0
            let cid = lowHeaderCid (wReg t)
            let vtBase =
                if gc then LPrim (AddW, [ LLoad (W, LGetGlobal "$roots", 4 * st.VtSlot); LConstW 8 ])
                else LConstW st.VtBase
            let idxAddr =
                LPrim (AddW, [ vtBase
                               LPrim (MulW, [ LPrim (AddW, [ LPrim (MulW, [ cid; LConstW st.NSlots ]); LConstW slot ]); LConstW 4 ]) ])
            LCallIdx (1 + List.length args, LLoad (W, idxAddr, 0), LGet (wReg t) :: argEs)
        let vtDispatch () = vtDispatchWith (List.map (coreToLowE ctx) args)
        // a list has no IEnumerable vtable row, so route the enumerator protocol
        // to the built-in iterator when the receiver IS a built-in seq / iterator,
        // else fall through to the vtable (an object-expression IEnumerator).
        let iterHdr = if gc then (gcIterTid <<< 1) ||| 1 else CID_ITER
        let arrIterHdr = if gc then (gcArrIterTid <<< 1) ||| 1 else CID_ARRITER
        // the receiver is one of OUR built-in iterators (list or array) -> route
        // MoveNext/Current to the linear helper; else it is an object-expression
        // IEnumerator and goes through the vtable.
        let isBuiltinIter () =
            let h = LLoad (W, LGet (wReg t), 0)
            LPrim (OrW, [ LPrim (EqW, [ h; LConstW iterHdr ]); LPrim (EqW, [ h; LConstW arrIterHdr ]) ])
        let branch (builtin : LExpr) (cond : LExpr) =
            let res = freshTmp ctx
            LDo ([ LSet (wReg t, coreToLowE ctx recv)
                   LIf (cond, [ LSet (wReg res, builtin) ], [ LSet (wReg res, vtDispatch ()) ]) ],
                 LGet (wReg res))
        (if bi = "IEnumerable" && method = "GetEnumerator" then
                branch (LCall ("$literNew", [ LGet (wReg t) ])) (LCall ("$isBuiltinSeq", [ LGet (wReg t) ]))
             elif bi = "IEnumerator" && method = "MoveNext" then
                branch (LCall ("$literNext", [ LGet (wReg t) ])) (isBuiltinIter ())
             elif bi = "IEnumerator" && method = "Current" then
                branch (LCall ("$literCur", [ LGet (wReg t) ])) (isBuiltinIter ())
             elif bi = "IEnumerator" && method = "Dispose" then
                // the BUILT-IN iterator holds no resource: disposing it is a
                // no-op. It has no vtable row, so without this `use e =
                // xs.GetEnumerator ()` dispatched through a row of 0.
                branch (lowInt 0) (isBuiltinIter ())
             elif gc && not (List.isEmpty args) then
                // ROOT the receiver and every argument across each other's
                // (possibly allocating) evaluations: register t and the wasm
                // operand stack are invisible to the collector, so the old
                // shape (set t, then evaluate args) read a STALE receiver —
                // and an earlier arg went stale across a later allocating
                // one. This was the wandering `ctx.Regs.[key v]` garbage-
                // register corruption in the self-hosted linear emitter.
                let setup, gets =
                    lowRootedArgsK ctx ((RKRef, None, W, coreToLowE ctx recv)
                                        :: (args |> List.map (fun a ->
                                                let kind = refKindOfExprC st a
                                                let wit = if kind = RKGen then slotWitness ctx a else None
                                                kind, wit, W, coreToLowE ctx a)))
                (match gets with
                 | recvG :: argGs -> LDo (setup @ [ LSet (wReg t, recvG) ], vtDispatchWith argGs)
                 | [] -> LDo ([ LSet (wReg t, coreToLowE ctx recv) ], vtDispatch ()))
             else
                LDo ([ LSet (wReg t, coreToLowE ctx recv) ], vtDispatch ()))
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
                    | Some g -> [ LBreakIf ("$cnext", LPrim (EqW, [ (coreToLowE ctx g); LConstW 0 ])) ]
                    | None -> []
                LBlock ("$cnext", tests @ guardStmt @ [ LSet (wReg res, coreToLowE ctx handler); LBreak "$tdone" ]))
        // GC: an exception unwinds the body's wasm frames WITHOUT running their
        // shadow-stack pops (a lifted lambda's env root, or any in-flight spush),
        // so restore $sp to its try-entry value before the handler runs — else
        // every caught exception leaks roots until the shadow stack overflows.
        if gc then
            let spSave = freshTmp ctx
            let restore = LSetGlobal ("$sp", LGet (wReg spSave))
            let catchStmts = restore :: catchStmts
            LDo ([ LSet (wReg spSave, LGetGlobal "$sp")
                   LTryStmt (coreToLowE ctx body, wReg res, wReg exn, catchStmts) ], LGet (wReg res))
        else
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
    // a `let rec f = fun … and g = fun …` group in STATEMENT position needs the
    // same cell treatment as in expression position (coreToLowE): bind every
    // member to a cell FIRST so a member's closure can capture its siblings,
    // then fill the cells. Without this the statement path bound each member in
    // turn, so an earlier member captured a later one before it existed and the
    // reference lowered to an unresolved variable (a stub that traps when the
    // enclosing function runs — a `let rec quoteTy …` in `lower` did exactly this).
    | ELet (true, _, _, ELam _, _) ->
        let members, body = recGroupOf e
        let regs = members |> List.map (fun (v, lam) -> v, lam, freshReg ctx (key v))
        for v, _, _ in regs do dictSet ctx.LSt.CellVars (key v) true
        if gc then
            // same slot treatment as the expression-position group above
            let withA = regs |> List.map (fun (v, lam, id) -> v, lam, id, freshTmp ctx)
            let allocPush = withA |> List.collect (fun (_, _, id, aR) ->
                [ LSet (wReg id, lowMkCell ctx RKRef (lowInt 0))
                  LSet (wReg aR, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
                  LStore (W, LGet (wReg aR), 0, LGet (wReg id))
                  LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ])
            for v, _, _, aR in withA do dictSet ctx.Slotted (key v) (LGet (wReg aR))
            let fills = withA |> List.collect (fun (_, lam, _, aR) ->
                // fresh temp for the closure value: the member's own register
                // keeps the cell pointer (pre-lowered eta references read it)
                let cv = freshTmp ctx
                [ LSet (wReg cv, coreToLowE ctx lam)
                  LStore (W, LLoad (W, LGet (wReg aR), 0), cellOff (), LGet (wReg cv)) ])
            let bodyStmts = coreToLowS ctx body
            for v, _, _, _ in withA do dictRemove ctx.Slotted (key v)
            allocPush @ fills @ bodyStmts
            @ [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW (4 * List.length withA) ])) ]
        else
        let allocs = regs |> List.map (fun (_, _, id) -> LSet (wReg id, lowMkCell ctx RKRef (lowInt 0)))
        let fills = regs |> List.map (fun (_, lam, id) -> LStore (W, LGet (wReg id), cellOff (), coreToLowE ctx lam))
        allocs @ fills @ coreToLowS ctx body
    | ELet (_, v, sch, rhs, body) when shouldSlot ctx v sch ->
        let addrReg = freshTmp ctx
        let addr = LGet (wReg addrReg)
        let initVal = lowSlotInit ctx v sch rhs
        dictSet ctx.Slotted (key v) addr
        let bodyStmts = coreToLowS ctx body
        dictRemove ctx.Slotted (key v)
        [ LSet (wReg addrReg, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
          LStore (W, addr, 0, initVal)
          LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ]
        @ bodyStmts
        @ [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ])) ]
    | ELet (_, v, sch, rhs, body) when (genWitOf ctx v sch).IsSome && assignsTo (key v) body ->
        // a REASSIGNED generic mutable: persistent witness-conditional slot with
        // write-through (ActiveGen's snapshot/restore would undo its `<-`).
        let bind = lowLetBind ctx v sch rhs
        let reg = regOf ctx (key v)
        let wit = optGet (genWitOf ctx v sch)
        let slotReg = freshTmp ctx
        let saved = ctx.SlottedGen
        ctx.SlottedGen <- (reg, wit, slotReg) :: ctx.SlottedGen
        let bodyStmts = coreToLowS ctx body
        ctx.SlottedGen <- saved
        (bind :: gcSlotPush reg wit slotReg :: bodyStmts) @ [ gcSlotPop wit ]
    | ELet (_, v, sch, rhs, body) when (genWitOf ctx v sch).IsSome ->
        let bind = lowLetBind ctx v sch rhs
        let saved = ctx.ActiveGen
        ctx.ActiveGen <- (regOf ctx (key v), optGet (genWitOf ctx v sch)) :: ctx.ActiveGen
        let bodyStmts = coreToLowS ctx body
        ctx.ActiveGen <- saved
        bind :: bodyStmts
    | ELet (_, v, sch, rhs, body) ->
        lowLetBind ctx v sch rhs :: coreToLowS ctx body
    | EAssign (v, rhs) when (dictTryFind ctx.LSt.CellVars (key v)).IsSome ->
        // a captured mutable: store into its cell (shared with the closure).
        // The VALUE is evaluated first — it can allocate and move the cell —
        // and the cell pointer is read after (a Slotted read sees the GC-updated
        // address), so the store never hits the cell's dead pre-GC copy.
        let t = freshTmp ctx
        [ LSet (wReg t, coreToLowE ctx rhs)
          LStore (W, lowVarStore ctx (key v), cellOff (), LGet (wReg t)) ]
    | EAssign (v, rhs) when (dictTryFind ctx.Slotted (key v)).IsSome ->
        // a shadow-stack-rooted ref local: write the new value into its root slot
        if consCheckOn () then
            let t = freshTmp ctx
            [ LSet (wReg t, coreToLowE ctx rhs) ]
            @ chkStoreStmts t
            @ [ LStore (W, optGet (dictTryFind ctx.Slotted (key v)), 0, LGet (wReg t)) ]
        else
        [ LStore (W, optGet (dictTryFind ctx.Slotted (key v)), 0, coreToLowE ctx rhs) ]
    | EAssign (v, rhs) ->
        (match dictTryFind ctx.Regs (key v) with
         | Some id ->
             (match dictTryFind ctx.VarScalar (key v) with
              | Some ty -> [ LSet ({ Id = id; RTy = ty }, flatUnbox ty (coreToLowE ctx rhs)) ]
              | None ->
                  match ctx.SlottedGen |> List.tryFind (fun (r, _, _) -> r = id) with
                  | Some (_, wit, slotReg) ->
                      // reassigned generic ref mutable: write BOTH the register and
                      // its persistent root slot (ref witness only), so a later GC
                      // sees the current value and the reload restores it.
                      let t = freshTmp ctx
                      [ LSet (wReg t, coreToLowE ctx rhs)
                        LSet (wReg id, LGet (wReg t))
                        LIf (slotGenRaw wit, [], [ LStore (W, LGet (wReg slotReg), 0, LGet (wReg t)) ]) ]
                  | None -> [ LSet (wReg id, coreToLowE ctx rhs) ])
         | None when (dictTryFind ctx.LSt.Globals (key v)).IsSome -> [ LSetGlobal (gl v, coreToLowE ctx rhs) ]
         | None -> err ctx.LSt ("wasm-linear LowIR: assignment to unbound " + v.Name); [ LEval (coreToLowE ctx rhs) ])
    | EIf (c, a, b) -> [ LIf (coreToLowE ctx c, coreToLowS ctx a, coreToLowS ctx b) ]
    | EWhile (c, b) -> [ LWhile (coreToLowE ctx c, coreToLowS ctx b) ]
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
    lowObjR ctx cid raw slots None []
// a cons cell whose head is a GENERIC element: its ref-ness is only known at
// runtime, from the element type's witness refMask. Branch on it — a RAW head
// (refMask 0) uses CONS_RAW and is stored directly (an unboxed int, never
// shadow-stacked); a REF head uses CONS_REF and is rooted across the alloc. The
// tail is a list pointer, rooted in both. Head/tail are evaluated ONCE.
and private lowGenericCons (ctx : LowCtx) (refMask : LExpr) (hExpr : LExpr) (tExpr : LExpr) : LExpr =
    if System.Environment.GetEnvironmentVariable "FPP_GENCONS" = "1" then
        eprintfn "GENCONS in %s" curFnDbg
    let b = freshTmp ctx
    let ht = freshTmp ctx
    let tt = freshTmp ctx
    let r = freshTmp ctx
    let rawBuild =
        gcPushStmts (LGet (wReg tt))
        @ [ LSet (wReg b, LCall ("$fpalloc", [ LConstW gcConsRawTid ])) ]
        @ gcPopInto (LGet (wReg b)) (HDR + 4)
        @ [ LStore (W, LGet (wReg b), HDR, LGet (wReg ht)); LSet (wReg r, LGet (wReg b)) ]
    let refBuild =
        gcPushStmts (LGet (wReg ht))
        @ gcPushStmts (LGet (wReg tt))
        @ [ LSet (wReg b, LCall ("$fpalloc", [ LConstW gcConsRefTid ])) ]
        @ gcPopInto (LGet (wReg b)) (HDR + 4)
        @ gcPopInto (LGet (wReg b)) HDR
        @ [ LSet (wReg r, LGet (wReg b)) ]
    // Evaluate the head, then the tail. The tail's evaluation may allocate and
    // collect; a REF head sitting in `ht` would be left stale (its object moved,
    // the register not updated), so root it across the tail eval — but only when
    // the element witness says it is a pointer (a raw `'a` head is an even int the
    // shadow-stack scanner must not chase). Materialise the refMask once.
    let mreg = freshTmp ctx
    let popHt =
        [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ]))
          LSet (wReg ht, LLoad (W, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]), 0)) ]
    // FPP_CONSCHECK=1 debug: a REF head whose target header word is EVEN is a
    // FORWARDING pointer — the head went stale (its object moved while the
    // value sat un-rooted). Trap HERE, at the cons, with the guilty function
    // in the backtrace — instead of at the next collection's trace.
    let chk =
        if System.Environment.GetEnvironmentVariable "FPP_CONSCHECK" = "1" then
            fun (guarded : bool) (reg : int) ->
                let t = [ LIf (LPrim (EqW, [ LCall ("$fpdbglive", [ LGet (wReg reg) ]); LConstW 0 ]), [ LTrap ], []) ]
                if guarded then [ LIf (LPrim (EqW, [ LGet (wReg mreg); LConstW 0 ]), [], t) ] else t
        else fun _ _ -> []
    LDo ([ LSet (wReg mreg, refMask)
           LSet (wReg ht, hExpr) ]
         @ chk true ht
         @ [ LIf (LPrim (EqW, [ LGet (wReg mreg); LConstW 0 ]),
                  [ LSet (wReg tt, tExpr) ],
                  gcPushStmts (LGet (wReg ht)) @ [ LSet (wReg tt, tExpr) ] @ popHt) ]
         @ chk true ht
         @ chk false tt
         @ [ LIf (LPrim (EqW, [ LGet (wReg mreg); LConstW 0 ]), rawBuild, refBuild) ], LGet (wReg r))
// as lowObj, but with a per-slot ref-kind classification (when every slot's
// kind is statically known). A fully-concrete shape registers FK_STRUCT with a
// ref-map: raw scalar slots are stored inline and NEVER pushed to the shadow
// stack, so an unboxed int in a tuple/union is invisible to the collector.
and private lowObjR (ctx : LowCtx) (cid : int) (raw : int) (slots : LExpr list) (refKinds : RefKind list option) (genWits : (int * LExpr) list) : LExpr =
    let n = List.length slots
    let b = freshTmp ctx
    let st = ctx.LSt
    let witOf i = genWits |> List.tryPick (fun (j, w) -> if j = i then Some w else None)
    // generic slots that a witness resolves at runtime (RKGen with a witness in
    // scope); an RKGen slot with NO witness leaves the whole object on the safe
    // tagged form (its scalars must be tagged, the pre-raw-int fallback)
    let genIdx =
        match refKinds with
        | Some ks when List.length ks = n -> [ 0 .. n - 1 ] |> List.filter (fun i -> List.item i ks = RKGen && (witOf i).IsSome)
        | _ -> []
    let unresolvedGen =
        match refKinds with
        | Some ks when List.length ks = n -> [ 0 .. n - 1 ] |> List.exists (fun i -> List.item i ks = RKGen && (witOf i).IsNone)
        | _ -> false
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
    elif gc && not (List.isEmpty genIdx) && not unresolvedGen then
        // GENERIC aggregate in a generic body: every slot's witness is in scope,
        // so build PRECISE refoffs even though some slots are type parameters.
        // A raw generic slot (witness refMask 0) is EXCLUDED from refoffs — the
        // collector never chases its unboxed even int — and a ref one is included
        // and rooted across the alloc. With g generic slots there are 2^g possible
        // ref-slot sets; intern an FK_STRUCT tid per set and pick it at runtime
        // from the witness refMasks. (This is lowGenericCons generalised past the
        // list-cons binary case to records/tuples/unions with N generic fields.)
        let ks = optGet refKinds
        let isConst e = match e with LConstW _ -> true | _ -> false
        let staticRef i = List.item i ks = RKRef
        let staticRaw i = List.item i ks = RKRaw
        let refMaskOf (w : LExpr) = LLoad (W, w, 8)
        let g = List.length genIdx
        let staticRefOffs = [ 0 .. n - 1 ] |> List.filter staticRef |> List.map (fun i -> HDR + 4 * i)
        let pat = ks |> List.map (fun k -> match k with RKRef -> "r" | RKRaw -> "s" | RKGen -> "g") |> String.concat ""
        let tidForMask (mask : int) : int =
            let extra =
                genIdx |> List.mapi (fun j i -> (mask >>> j) &&& 1, i)
                |> List.filter (fun (bit, _) -> bit = 1) |> List.map (fun (_, i) -> HDR + 4 * i)
            let offs = List.sort (staticRefOffs @ extra)
            // intern under the CONCRETE path's canonical key for the RESOLVED
            // shape (not a separate "sg:…:mask" key): a `(string, int)` tuple
            // built here and one built with static types must share ONE tid —
            // $cmpv orders differing headers as unequal, so a second tid for
            // the same shape made equal dict keys miss (task #69's stub class).
            let rpat =
                [ 0 .. n - 1 ]
                |> List.map (fun i -> if List.contains (HDR + 4 * i) offs then "r" else "s")
                |> String.concat ""
            let sk = "s:" + string cid + ":" + string n + ":" + string raw + ":" + rpat
            let isNew = (dictTryFind st.Tids sk).IsNone
            let t = gcTidRef st sk (HDR + 4 * n) offs
            if isNew && (cid >= CID_FIRST_USER || cid = CID_LIST) then vecAdd st.TidCid (t, cid)
            t
        let tidTmp = freshTmp ctx
        let rec selTid (j : int) (accMask : int) : LStmt list =
            if j = g then [ LSet (wReg tidTmp, LConstW (tidForMask accMask)) ]
            else
                let w = optGet (witOf (List.item j genIdx))
                [ LIf (LPrim (EqW, [ refMaskOf w; LConstW 0 ]),
                       selTid (j + 1) accMask,
                       selTid (j + 1) (accMask ||| (1 <<< j))) ]
        let idx = slots |> List.mapi (fun i v -> i, v)
        let tempOf = idx |> List.map (fun (i, v) -> i, (if isConst v then None else Some (freshTmp ctx)))
        let tregOf i = match List.tryPick (fun (j, t) -> if j = i then Some t else None) tempOf with Some (Some tr) -> tr | _ -> freshTmp ctx
        let tval i = match List.tryPick (fun (j, t) -> if j = i then Some t else None) tempOf with Some (Some tr) -> LGet (wReg tr) | _ -> List.item i slots
        // Evaluate each non-const slot and, if it holds a pointer, push it to the
        // shadow stack IMMEDIATELY — before the NEXT slot's (possibly collecting)
        // evaluation. Evaluating all slots into temps first and pushing afterwards
        // left an earlier ref operand stale when a later operand allocated (a heap
        // ref-slot then held a moved/wild pointer, and the collector traced garbage).
        // A generic slot pushes only when its witness refMask says ref.
        let evalAndPush =
            idx |> List.collect (fun (i, v) ->
                if isConst v then []
                else
                    let tr = tregOf i
                    let ev = [ LSet (wReg tr, v) ]
                    let push =
                        if staticRef i then gcPushStmts (LGet (wReg tr))
                        elif List.contains i genIdx then [ LIf (LPrim (EqW, [ refMaskOf (optGet (witOf i)); LConstW 0 ]), [], gcPushStmts (LGet (wReg tr))) ]
                        else []
                    ev @ push)
        // pops mirror the pushes in descending slot order (LIFO). A raw slot (static
        // or a generic one whose witness said raw) was never pushed — store its temp.
        let popsAndStores =
            [ 0 .. n - 1 ] |> List.rev |> List.collect (fun i ->
                if isConst (List.item i slots) then []
                elif staticRef i then gcPopInto (LGet (wReg b)) (HDR + 4 * i)
                elif List.contains i genIdx then
                    [ LIf (LPrim (EqW, [ refMaskOf (optGet (witOf i)); LConstW 0 ]),
                           [ LStore (W, LGet (wReg b), HDR + 4 * i, tval i) ],
                           gcPopInto (LGet (wReg b)) (HDR + 4 * i)) ]
                else [ LStore (W, LGet (wReg b), HDR + 4 * i, tval i) ])
        let consts = idx |> List.filter (fun (_, v) -> isConst v) |> List.map (fun (i, v) -> LStore (W, LGet (wReg b), HDR + 4 * i, v))
        LDo (evalAndPush @ selTid 0 0
             @ [ LSet (wReg b, LCall ("$fpalloc", [ LGet (wReg tidTmp) ])) ]
             @ popsAndStores @ consts, LGet (wReg b))
    elif gc then
        // every slot's ref-kind known and none generic -> FK_STRUCT with a ref-
        // map. Otherwise the uniform tagged form (scan by low-bit tag from the
        // first payload word), which needs its scalars TAGGED — the pre-raw-int
        // world, still the fallback for a generic slot.
        let concrete = match refKinds with Some ks -> List.length ks = n && not (List.contains RKGen ks) | None -> false
        let isRefSlot (i : int) : bool =
            match refKinds with Some ks when concrete -> (List.item i ks) = RKRef | _ -> true
        let sk =
            if concrete then
                let pat = optGet refKinds |> List.map (fun k -> if k = RKRef then "r" else "s") |> String.concat ""
                "s:" + string cid + ":" + string n + ":" + string raw + ":" + pat
            else "s:" + string cid + ":" + string n + ":" + string raw
        // record the tid->cid mapping the first time a shape is allocated, so
        // `:?`/dispatch recover the class-id (covers classes, which the eager
        // record/union pass does not enumerate)
        let isNew = (dictTryFind st.Tids sk).IsNone
        let tid =
            if concrete then
                let refOffs = [ 0 .. n - 1 ] |> List.filter isRefSlot |> List.map (fun i -> HDR + 4 * i)
                gcTidRef st sk (HDR + 4 * n) refOffs
            else gcTid st sk (HDR + 4 * n) FK_TAGGED (1 + raw)
        // built-in cids skip the tid->cid table, EXCEPT CID_LIST: $isBuiltinSeq
        // recovers a cons cell's class-id from it, so every FK_STRUCT cons variant
        // must map back to CID_LIST.
        if isNew && (cid >= CID_FIRST_USER || cid = CID_LIST) then vecAdd st.TidCid (tid, cid)
        let isConst e = match e with LConstW _ -> true | _ -> false
        let idx = slots |> List.mapi (fun i v -> i, v)
        // REF slots are live pointers: evaluate and push to the shadow stack
        // before the (collecting) alloc, pop back after. RAW non-const slots are
        // materialised into a temp before the alloc and stored after — a raw
        // scalar must NEVER reach the pointer-scanned shadow stack. Consts store
        // directly.
        let refIdx = idx |> List.filter (fun (i, v) -> isRefSlot i && not (isConst v))
        let rawIdx = idx |> List.filter (fun (i, v) -> not (isRefSlot i) && not (isConst v))
        let pushes = refIdx |> List.collect (fun (_, v) -> gcPushStmts v)
        let pops = refIdx |> List.rev |> List.collect (fun (i, _) -> gcPopInto (LGet (wReg b)) (HDR + 4 * i))
        let rawTemps = rawIdx |> List.map (fun (i, v) -> i, freshTmp ctx, v)
        let rawEvals = rawTemps |> List.map (fun (_, t, v) -> LSet (wReg t, v))
        let rawStores = rawTemps |> List.map (fun (i, t, _) -> LStore (W, LGet (wReg b), HDR + 4 * i, LGet (wReg t)))
        let consts = idx |> List.filter (fun (_, v) -> isConst v) |> List.map (fun (i, v) -> LStore (W, LGet (wReg b), HDR + 4 * i, v))
        LDo (rawEvals @ pushes @ [ LSet (wReg b, LCall ("$fpalloc", [ LConstW tid ])) ] @ pops @ rawStores @ consts, LGet (wReg b))
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
    let (_, size, firstRefWord) = optGet (dictTryFind ctx.LSt.RecPod name)
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
    | x :: rest ->
        (match refKindOfExpr x with
         | RKGen ->
             (match tyVarIdOfExpr x |> Option.bind (fun vid -> dictTryFind ctx.Witness vid) with
              | Some wreg -> lowGenericCons ctx (LLoad (W, LGet (wReg wreg), 8)) (coreToLowE ctx x) (lowList ctx rest)
              | None -> lowObjR ctx CID_LIST 0 [ coreToLowE ctx x; lowList ctx rest ] (Some [ RKGen; RKRef ]) [])
         | k -> lowObjR ctx CID_LIST 0 [ coreToLowE ctx x; lowList ctx rest ] (Some [ k; RKRef ]) [])

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
    | "sbyte" -> (LPrim (ShrSW, [ LPrim (ShlW, [ raw; LConstW 24 ]); LConstW 24 ]))
    | "int16" -> (LPrim (ShrSW, [ LPrim (ShlW, [ raw; LConstW 16 ]); LConstW 16 ]))
    | _ -> raw   // byte / uint16: the unsigned load already zero-extended; raw at rest
// the uniform tagged word -> the raw packed slot value (store8/store16 truncate,
// so a narrow int just needs its low bits untagged).
and private storUnbox (k : string) (word : LExpr) : LExpr =
    match k with
    | "float" | "double" -> lowUnboxF word
    | "int64" | "uint64" -> lowUnboxI word
    | "float32" | "single" -> LPrim (F2Bits, [ LPrim (DemF, [ lowUnboxF word ]) ])
    | _ -> word

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
    | PLit (LInt s) -> [ LBreakIf (fail, LPrim (NeW, [ sc; LConstW (parseI32Lit s) ])) ]
    | PLit (LBool b) -> [ LBreakIf (fail, LPrim (NeW, [ sc; LConstW (if b then 1 else 0) ])) ]
    | PLit LUnit -> []
    // an enum case pattern is a raw integer compare — no heap object to tag-test
    | PCtor (case, _, []) when (dictTryFind ctx.LSt.EnumConst case).IsSome ->
        [ LBreakIf (fail, LPrim (NeW, [ sc; LConstW (optGet (dictTryFind ctx.LSt.EnumConst case)) ])) ]
    | PCtor (case, _, subs) ->
        let tag = match dictTryFind st.UnionTag case with Some t -> t | None -> 0
        // a union case is [cid/tid][tag][payload…]. A union's cases do not all
        // share one class-id: they land in several groups, and the tag is
        // numbered PER GROUP, so two cases in different groups can carry the
        // same tag — the `Type` union's `TFun` and `TApp` both come out tag 2
        // (headers 225 vs 227), and a tag-only test then reads a `TFun` as a
        // `TApp`. Test the class-id too whenever the case is a real user union.
        let cid = cidCase st case
        let cidTest =
            if cid >= CID_FIRST_USER then
                [ LBreakIf (fail, LPrim (NeW, [ lowHeaderCid (wReg scrutReg); LConstW cid ])) ]
            else []
        let tagTest = LBreakIf (fail, LPrim (NeW, [ LLoad (W, sc, HDR); LConstW tag ]))
        cidTest @ tagTest :: List.concat (subs |> List.mapi (fun i sub ->
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
    | PLit (LChar raw) -> [ LBreakIf (fail, LPrim (NeW, [ sc; LConstW (Fpp.Backend.BinDriver.charCode raw) ])) ]
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
/// a runtime call whose operands are refs: root every operand across the
/// LATER operands' (possibly allocating) evaluations — operand-stack values
/// and plain registers are invisible to the collector. The generalized `+t`
/// shape; tagged scalars are scan-safe, so uniform args root unconditionally.
and private lowCallR (ctx : LowCtx) (fn : string) (args : Expr list) : LExpr =
    let n = List.length args
    if not gc || n <= 1 then LCall (fn, args |> List.map (coreToLowE ctx))
    else
        let regs = args |> List.map (fun _ -> freshTmp ctx)
        let pairs = List.zip args regs
        let head = List.truncate (n - 1) pairs
        let lastA, lastR = List.item (n - 1) pairs
        LDo ((head |> List.map (fun (a, _) -> LCallVoidS ("$spush", [ coreToLowE ctx a ])))
             @ [ LSet (wReg lastR, coreToLowE ctx lastA) ]
             @ (head |> List.rev |> List.map (fun (_, r) -> LSet (wReg r, LCall ("$spop", [])))),
             LCall (fn, regs |> List.map (fun r -> LGet (wReg r))))

/// FPP_CONSCHECK debug: validate a LOADED ref-looking value at the READ —
/// a stale env/slot/register edge traps HERE, the reader in the backtrace,
/// after naming the variable and site on stderr
and private chkReadE (ctx : LowCtx) (tag : string) (e : LExpr) : LExpr =
    if consCheckOn () then
        let t = freshTmp ctx
        chkSite <- chkSite + 1
        let site = chkSite
        eprintfn "CCHKSITE %d = %s in %s" site tag curFnDbg
        let fail =
            [ LCallVoidS ("$eprints", [ LCall ("$str_of_int", [ LConstW site ]) ])
              LTrap ]
        LDo ([ LSet (wReg t, e)
               LIf (LPrim (EqW, [ LPrim (AndW, [ LGet (wReg t); LConstW 1 ]); LConstW 0 ]),
                    [ LIf (LPrim (NeW, [ LGet (wReg t); LConstW 0 ]),
                           [ LIf (LPrim (EqW, [ LCall ("$fpdbglive", [ LGet (wReg t) ]); LConstW 0 ]), fail, []) ], []) ], []) ],
             LGet (wReg t))
    else e

and private lowVarStore (ctx : LowCtx) (k : string) : LExpr =
    let st = ctx.LSt
    match dictTryFind ctx.Slotted k with
    | Some addr -> chkReadE ctx ("slot:" + k) (LLoad (W, addr, 0))   // a shadow-stack-rooted ref local: read the current (post-GC) value
    | None ->
    match dictTryFind ctx.Regs k with
    | Some id -> chkReadE ctx ("reg:" + k) (LGet (wReg id))
    | None ->
        match dictTryFind st.Captures k with
        | Some slot when ctx.EnvReg >= 0 ->
            // read the env through its rooted slot when the body roots it, so a
            // GC that relocated the env mid-body is reflected; else the wasm-local.
            let envPtr = chkReadE ctx ("envp:" + k) (match ctx.EnvAddr with Some a -> LLoad (W, a, 0) | None -> LGet (wReg ctx.EnvReg))
            chkReadE ctx ("env:" + k) (LLoad (W, envPtr, HDR + 8 + 4 * slot))
        | _ ->
            match st.Globals |> dictPairs |> List.tryFind (fun (gk, _) -> gk = k) with
            | Some _ -> LGetGlobal ("$g" + string (abs (strHash k)))
            | None -> err st ("wasm-linear LowIR: unresolved variable " + k + " name=" + (match dictTryFind nameOf k with Some n -> n | None -> "?")); lowInt 0

// the initial value a shouldSlot binder's shadow-stack slot holds: for a cell
// var the CELL itself (the heap box around the rhs — its pointer is what the
// slot roots and reads dereference), else the rhs value. Mirrors lowLetBind's
// cell-kind resolution.
and private lowSlotInit (ctx : LowCtx) (v : VarId) (sch : Scheme) (rhs : Expr) : LExpr =
    let k = key v
    if (dictTryFind ctx.LSt.CellVars k).IsSome then
        let ck = match refKindOfTy sch.Body with RKGen -> refKindOfExpr rhs | kk -> kk
        dictSet ctx.LSt.CellKind k ck
        lowMkCell ctx ck (coreToLowE ctx rhs)
    else coreToLowE ctx rhs

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
        let init =
            if isCell then
                // the cell's declared TYPE is authoritative for raw-vs-ref: a
                // mutable `int`/`bool` cell holds a RAW even word even when its
                // initialiser is a generic call (refKindOfExpr rhs = RKGen) that
                // monomorphises to a scalar — the tagged form would scan that raw
                // int as a pointer. Only fall back to the rhs when the type itself
                // is unresolved (a genuinely generic mutable).
                let ck = match refKindOfTy sch.Body with RKGen -> refKindOfExpr rhs | k -> k
                dictSet ctx.LSt.CellKind k ck
                lowMkCell ctx ck (coreToLowE ctx rhs)
            else coreToLowE ctx rhs
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
// type-tested or dispatched on). `kind` is the ref-kind of the value the cell
// holds: a RAW-scalar cell (a mutable int/bool) registers FK_STRUCT with no
// ref-map and stores its word directly — never scanned, never shadow-stacked,
// so an even int in the cell is not chased as a pointer. A ref/generic cell
// keeps the tagged form (scan the word, push across the alloc).
and private lowMkCell (ctx : LowCtx) (kind : RefKind) (v : LExpr) : LExpr =
    let b = freshTmp ctx
    if gc then
        if kind = RKRaw then
            let tid = gcTidRef ctx.LSt "cell$s" (HDR + 4) []
            let t = freshTmp ctx
            LDo ([ LSet (wReg t, v); LSet (wReg b, LCall ("$fpalloc", [ LConstW tid ])); LStore (W, LGet (wReg b), HDR, LGet (wReg t)) ], LGet (wReg b))
        else
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
    // capture the STORAGE, not the dereferenced value: for a cell var that is
    // the shared pointer, so mutation is visible on both sides. An unboxed
    // scalar has no word storage to grab, so re-box it into the env slot (the
    // lambda body reads it back as an ordinary boxed word).
    let capVals =
        caps |> List.map (fun (p, o, _) ->
            let k = p + ":" + string o
            match dictTryFind ctx.VarScalar k with
            | Some ty -> (match dictTryFind ctx.Regs k with Some id -> flatBox ctx ty (LGet { Id = id; RTy = ty }) | None -> lowVarStore ctx k)
            | None -> lowVarStore ctx k)
    // the env slot's GC nature: a VarScalar rides a boxed pointer (flatBox), a
    // cell is a pointer, and any other capture is its var's own storage — a raw
    // i32 for an int/bool/char, a pointer otherwise. Slots 0/1 (kind, code idx)
    // are raw words.
    let capKinds =
        caps |> List.map (fun (p, o, ty) ->
            let k = p + ":" + string o
            if (dictTryFind ctx.VarScalar k).IsSome then RKRef
            elif (dictTryFind ctx.LSt.CellVars k).IsSome then RKRef
            else refKindOfTy ty)
    // a capture whose type is a TYPE PARAMETER rides its raw storage in the env
    // slot (an unboxed int for 'a=int); resolve its GC nature at runtime from the
    // enclosing body's witness, so a captured even int is not chased as a pointer.
    // Env slots 0/1 are the kind/code words, so a capture at position i is slot 2+i.
    let capGenWits =
        caps |> List.mapi (fun i (p, o, ty) ->
            let k = p + ":" + string o
            if (dictTryFind ctx.VarScalar k).IsSome || (dictTryFind ctx.LSt.CellVars k).IsSome then None
            else
                match prune ty with
                | TVar v -> (match dictTryFind ctx.Witness v.Id with Some w -> Some (2 + i, LGet (wReg w)) | None -> None)
                | _ -> None)
        |> List.choose id
    // capture the ENCLOSING generic fn's witnesses (ctx.Witness) as trailing
    // RKRaw env slots, so the lambda body's own generic aggregates (a tuple of
    // its type-param params, e.g. zip's `fun x y -> (x,y)`) resolve raw-vs-ref.
    // Sorted by id for a deterministic layout. Only fires when the enclosing is
    // generic (non-empty Witness); non-generic closures are unchanged.
    let encWits = ctx.Witness |> dictPairs |> Seq.sortBy fst |> Seq.toList
    let ncaps = List.length caps
    (if not (List.isEmpty encWits) then
        dictSet st.LamWits name (encWits |> List.mapi (fun j (tvId, _) -> (tvId, ncaps + j))))
    let witVals = encWits |> List.map (fun (_, r) -> LGet (wReg r))
    let witKinds = encWits |> List.map (fun _ -> RKRaw)
    lowObjR ctx CID_CLOSURE 2
        (LConstW CLO_KIND :: LConstW (tblIdx st.M name) :: (capVals @ witVals))
        (Some (RKRaw :: RKRaw :: (capKinds @ witKinds))) capGenWits

// Root ref-typed call ARGUMENTS across the evaluation of later args. Evaluating
// `f(a, b)` leaves a's pointer on the wasm operand stack — which the GC never
// scans — so if b's evaluation allocates and collects, a is left stale before
// the call lands. Each ref arg that is followed by another arg is pushed to the
// shadow stack across the remaining evaluations and popped back into its temp;
// the last arg (consumed immediately by the call) and raw args ride a temp
// directly. Returns (setup stmts, per-arg value exprs) — emit the call inside an
// LDo over the setup. This is the n-ary form of `evalRooted`.
and private lowRootedArgs (ctx : LowCtx) (args : (bool * LTy * LExpr) list) : LStmt list * LExpr list =
    lowRootedArgsK ctx (args |> List.map (fun (isRef, ty, e) -> (if isRef then RKRef else RKRaw), None, ty, e))

/// kind-aware operand rooting for a call: each operand is rooted across the
/// LATER operands' (possibly allocating) evaluations. A REF roots
/// unconditionally; a GENERIC with a WITNESS roots conditionally on its
/// refMask (a raw 'a must never reach the pointer scanner); a GENERIC with
/// no witness is on the canonical TAGGED form and roots unconditionally; a
/// RAW value never roots — W lanes DO carry raw evens in stamped code (the
/// hash argument of dictSlotH), so root-everything scanned raw ints as
/// pointers and the stale-edge tolerance NULLED them.
and private lowRootedArgsK (ctx : LowCtx) (args : (RefKind * LExpr option * LTy * LExpr) list) : LStmt list * LExpr list =
    let n = List.length args
    let ts =
        args |> List.mapi (fun i (kind, wit, ty, e) ->
            let mode =
                if not gc || ty <> W || i = n - 1 then 0
                elif kind = RKRef then 1
                elif kind = RKGen then (match wit with Some _ -> 2 | None -> 1)
                else 0
            mode, wit, { Id = freshTmpT ctx ty; RTy = ty }, e,
            (if mode = 2 then Some (freshTmp ctx, freshTmp ctx) else None))
    let eval = ts |> List.collect (fun (mode, wit, r, e, aux) ->
        LSet (r, e)
        :: (match mode, wit, aux with
            | 1, _, _ -> gcPushStmts (LGet r)
            | 2, Some wexpr, Some (wR, slotR) ->
                [ LSet (wReg wR, wexpr); gcSlotPush r.Id wR slotR ]
            | _ -> []))
    let pops =
        ts |> List.rev
        |> List.collect (fun (mode, _, r, _, aux) ->
            match mode, aux with
            | 1, _ ->
                [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ]))
                  LSet (r, LLoad (W, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]), 0)) ]
            | 2, Some (wR, slotR) ->
                [ LIf (slotGenRaw wR, [],
                       [ LSet (r, LLoad (W, LGet (wReg slotR), 0))
                         LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ])) ]) ]
            | _ -> [])
    (eval @ pops, ts |> List.map (fun (_, _, r, _, _) -> LGet r))

/// one JS-boundary import call: operands as (kind, lane, lowered) triples,
/// routed through the rooted-args machinery (a string operand is a heap
/// pointer live across the LATER operands' evaluations — and the import
/// itself can re-enter wasm through a callback and collect). `ret` is the
/// jsx kind of the result: "d" boxes the f64 through a temp (the box
/// allocation is a safepoint), "u" answers unit, anything else passes the
/// raw i32 (handle / string pointer / int / bool) straight through.
and private lowJsi (ctx : LowCtx) (fname : string) (ret : string) (args : (RefKind * LTy * LExpr) list) : LExpr =
    let setup, vals = lowRootedArgsK ctx (args |> List.map (fun (k, ty, e) -> k, None, ty, e))
    let call =
        match ret with
        | "u" -> LDo ([ LCallVoidS (fname, vals) ], lowInt 0)
        | "d" ->
            let r = freshTmpT ctx F64
            LDo ([ LSet ({ Id = r; RTy = F64 }, LCall (fname, vals)) ], flatBox ctx F64 (LGet { Id = r; RTy = F64 }))
        | _ -> LCall (fname, vals)
    if List.isEmpty setup then call else LDo (setup, call)

and private lowApply (ctx : LowCtx) (cloE : LExpr) (args : Expr list) : LExpr =
    match args with
    | [] -> cloE
    | _ when not gc ->
        // bind the closure to a register so LCallIndirect can read it twice
        // (as env and to load the code index) without re-evaluating it
        let rec chain (clo : LExpr) (rem : Expr list) : LExpr =
            match rem with
            | [] -> clo
            | a :: rest ->
                let tclo = freshTmp ctx
                chain (LDo ([ LSet (wReg tclo, clo) ], LCallIndirect ([ W ], LGet (wReg tclo), [ coreToLowE ctx a ]))) rest
        chain cloE args
    | _ ->
        // GC: EVERY step of a curried chain allocates (the partial closure), so
        // a register read after an earlier step sees pre-GC addresses. The outer
        // rootActiveGen wrap reloads registers only AFTER the whole chain — too
        // late for the mid-chain arg reads (forall2's `f x y`: apply(f,x)
        // allocated, then y's register was read stale — the measured 16 MB fault
        // in prune-under-compatible). Evaluate the closure and every argument
        // UP FRONT, left to right, slotting the closure and each ref arg (a
        // generic arg by its witness); the chain then reads each value through
        // its GC-updated slot and no step can see a stale word.
        let tclo = freshTmp ctx
        let cloA = freshTmp ctx
        let push valReg addrReg =
            [ LSet (wReg addrReg, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
              LStore (W, LGet (wReg addrReg), 0, LGet (wReg valReg))
              LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ]
        let setupClo = LSet (wReg tclo, cloE) :: push tclo cloA
        let infos =
            args |> List.map (fun a ->
                let r = freshTmp ctx
                match refKindOfExprC ctx.LSt a with
                | RKRef -> a, r, Some (freshTmp ctx), None
                | RKGen ->
                    (match slotWitness ctx a with
                     | Some wexpr -> a, r, Some (freshTmp ctx), Some (freshTmp ctx, wexpr)
                     | None -> a, r, None, None)
                | _ -> a, r, None, None)
        let setupArgs =
            infos |> List.collect (fun (a, r, addrOpt, witOpt) ->
                LSet (wReg r, coreToLowE ctx a)
                :: (match addrOpt, witOpt with
                    | Some aR, None -> push r aR
                    | Some aR, Some (wR, wexpr) -> [ LSet (wReg wR, wexpr); gcSlotPush r wR aR ]
                    | _ -> []))
        let pops =
            (infos |> List.rev |> List.collect (fun (_, _, addrOpt, witOpt) ->
                match addrOpt, witOpt with
                | Some _, None -> [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ])) ]
                | Some _, Some (wR, _) -> [ gcSlotPop wR ]
                | _ -> []))
            @ [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW 4 ])) ]
        let argVal (r, addrOpt, witOpt) =
            match addrOpt, witOpt with
            | Some aR, None -> LLoad (W, LGet (wReg aR), 0)
            | Some aR, Some (wR, _) ->
                LDo ([ LIf (slotGenRaw wR, [], [ LSet (wReg r, LLoad (W, LGet (wReg aR), 0)) ]) ], LGet (wReg r))
            | _ -> LGet (wReg r)
        let rec chain (clo : LExpr) (rem : (Expr * int * int option * (int * LExpr) option) list) : LExpr =
            match rem with
            | [] -> clo
            | (_, r, addrOpt, witOpt) :: rest ->
                let t = freshTmp ctx
                chain (LDo ([ LSet (wReg t, clo) ], LCallIndirect ([ W ], LGet (wReg t), [ argVal (r, addrOpt, witOpt) ]))) rest
        let res = freshTmp ctx
        LDo (setupClo @ setupArgs
             @ [ LSet (wReg res, chain (LLoad (W, LGet (wReg cloA), 0)) infos) ]
             @ pops,
             LGet (wReg res))

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
    let bare = if tn.Contains "$<" then tn.Substring (0, tn.IndexOf "$<") else tn
    // boxed SCALARS: an odd word IS a tagged 31-bit int (bool/char/byte
    // share the tag — `box true :? int` is true here where F# says false,
    // the shared-scalar divergence); floats, 64-bit ints and strings are
    // heap boxes with their own class-id headers
    if List.contains bare [ "int"; "bool"; "char"; "byte"; "sbyte"; "int16"; "uint16"; "uint32" ] then
        let t = freshTmp ctx
        LDo ([ LSet (wReg t, v) ], LPrim (AndW, [ LGet (wReg t); LConstW 1 ]))
    else
    let scalarCids =
        match bare with
        | "float" -> [ CID_FLOAT ]
        | "int64" | "uint64" -> [ CID_INT64 ]
        | "string" -> [ CID_STRING ]
        // the BUILT-IN collections answer by representation: a cons cell
        // carries CID_LIST, an array CID_ARRAY (the tid->cid table maps every
        // witness-selected cons/array variant back to them). Without these
        // `o :? list<int>` had no ids at all and answered false for a list.
        | "list" | "seq" | "[]" -> [ CID_LIST ]
        | "array" -> [ CID_ARRAY ]
        | _ -> []
    let ids = if List.isEmpty scalarCids then typeTestIds ctx.LSt tn else scalarCids
    // NIL is the null word, not a cons cell: the empty list is still a list,
    // so `([] : int list) :? list<int>` answers true (the pointer test below
    // rejects 0)
    let nilIsMatch = (match bare with "list" | "seq" | "[]" -> true | _ -> false)
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
                [ LSet (wReg r, (if nilIsMatch then LPrim (EqW, [ LGet (wReg t); LConstW 0 ]) else LConstW 0)) ]) ],
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
    | GtUW -> "i32.gt_u"
    | LeUW -> "i32.le_u"
    | DivUW -> "i32.div_u"
    | RemUW -> "i32.rem_u"
    | GeUW -> "i32.ge_u"
    | AddL -> "i64.add"
    | SubL -> "i64.sub"
    | MulL -> "i64.mul"
    | DivSL -> "i64.div_s"
    | RemSL -> "i64.rem_s"
    | DivUL -> "i64.div_u"
    | RemUL -> "i64.rem_u"
    | AndL -> "i64.and"
    | OrL -> "i64.or"
    | XorL -> "i64.xor"
    | ShlL -> "i64.shl"
    | ShrSL -> "i64.shr_s"
    | ShrUL -> "i64.shr_u"
    | EqL -> "i64.eq"
    | NeL -> "i64.ne"
    | LtSL -> "i64.lt_s"
    | GtSL -> "i64.gt_s"
    | LeSL -> "i64.le_s"
    | GeSL -> "i64.ge_s"
    | LtUL -> "i64.lt_u"
    | GtUL -> "i64.gt_u"
    | LeUL -> "i64.le_u"
    | GeUL -> "i64.ge_u"
    | AddF -> "f64.add"
    | SubF -> "f64.sub"
    | MulF -> "f64.mul"
    | DivF -> "f64.div"
    | NegF -> "f64.neg"
    | AbsF -> "f64.abs"
    | SqrtF -> "f64.sqrt"
    | TruncF -> "f64.trunc"
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
    // bare `doubleBits`, not the Fpp.Prelude path: the name is BACKEND-OWNED
    // under self-host and only the unqualified use lowers to the builtin
    | LConstF x -> fc f (doubleBits x)
    | LGet r when r.Id > 100000000 -> failwith ("bad reg " + string r.Id + " while emitting " + curFnDbg)
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
    | LTailCall (sym, args) ->
        // args ride the wasm VALUE stack; restoring $sp after evaluating
        // them is safe (the shadow stack is memory, not the value stack) and
        // discharges every push return_call would otherwise skip
        for a in args do emitLowE f a
        (if gc && tailSpReg >= 0 then (lg f (regNm (wReg tailSpReg)); gs f "$sp"))
        retCall f sym
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
// Pre-assign a register and cell mark to every `let rec f = fun … and …` member
// anywhere in a body BEFORE it is lowered. The rec-group lowering does this too,
// but only when it REACHES the group; eta-expansion can lift a bare member
// reference (`List.map quoteTy xs` -> `… (fun a -> quoteTy a) …`) to a position
// that lowers earlier, and then the reference found no register and stubbed the
// whole function (a `let rec … and quoteTy` in `lower` did exactly this under
// self-host). freshReg is idempotent, so the group lowering reuses these slots.
// Pre-assign a register and cell mark to every `let rec f = fun … and …` member
// reachable from a body BEFORE it is lowered. The rec-group lowering does this
// too, but only when it REACHES the group; eta-expansion can lift a bare member
// reference (`List.map quoteTy xs`) to a spot that lowers earlier, and the
// reference then finds no register and stubs the whole function (a `let rec …
// and quoteTy` inside `lower` did exactly this under self-host). freshReg is
// idempotent, so the group lowering reuses these slots.
let rec private preRecGroups (ctx : LowCtx) (e : Expr) : unit =
    match e with
    | ELet (true, _, _, ELam _, _) ->
        let members, body = recGroupOf e
        for v, _ in members do
            freshReg ctx (key v) |> ignore
            dictSet ctx.LSt.CellVars (key v) true
        for _, lam in members do preRecGroups ctx lam
        preRecGroups ctx body
    | ELam (_, b) -> preRecGroups ctx b
    | ELet (_, _, _, a, b) | EWhile (a, b) | EIndex (_, a, b) | EArrayCreate (_, a, b) -> preRecGroups ctx a; preRecGroups ctx b
    | EApp (f, xs) -> preRecGroups ctx f; List.iter (preRecGroups ctx) xs
    | EIf (a, b, c) | EIndexSet (_, a, b, c) -> preRecGroups ctx a; preRecGroups ctx b; preRecGroups ctx c
    | EMatch (s, cs) | ETry (s, cs) -> preRecGroups ctx s; for _, gd, b in cs do (match gd with Some x -> preRecGroups ctx x | None -> ()); preRecGroups ctx b
    | ESeq xs | EPrim (_, xs) | ETuple xs | EListLit xs | ECtor (_, _, xs) | EArray (_, xs) -> List.iter (preRecGroups ctx) xs
    | ERecord (_, fs) -> for _, x in fs do preRecGroups ctx x
    | ERecordExt (_, b, fs) -> preRecGroups ctx b; for _, x in fs do preRecGroups ctx x
    | EField (r, _, _) | EArrayLen (_, r) | ECast (_, r, _) | ETypeTest (_, r) | EArrayPin (_, r) | EArrayUnpin (_, r) | EArrayBytes (_, r) | EAssign (_, r) -> preRecGroups ctx r
    | EFieldSet (r, _, _, x) -> preRecGroups ctx r; preRecGroups ctx x
    | EIfaceCall (_, _, r, xs) -> preRecGroups ctx r; List.iter (preRecGroups ctx) xs
    | _ -> ()

let private emitFuncLow (st : St) (m : Mod) (dbgName : string) (isInit : bool) (sig_ : (LTy list * LTy) option) (witnessVars : int list) (selfWits : (int * int) list) (constWits : (int * LExpr) list) (ps : VarId list) (paramTypes : Type list) (body : Expr) (finish : Fn -> unit) : unit =
    curFnDbg <- dbgName
    let ctx = { LSt = st; Regs = dictNew (); EnvReg = -1; RegTys = vecNew (); VarScalar = dictNew (); Witness = dictNew (); ClassCtorWits = []; ClassWit = None; EnvAddr = None; Slotted = dictNew (); ActiveGen = []; SlottedGen = []; NReg = 0 }
    // hidden witness-pointer params come FIRST (i32), one per quantified type
    // var, recorded in ctx.Witness so a generic aggregate can read the element
    // type's witness. Regular params follow.
    let wnames = witnessVars |> List.map (fun vid -> let r = freshReg ctx ("$w" + string vid) in dictSet ctx.Witness vid r; regNm (wReg r))
    let pnames = ps |> List.map (fun pv -> regNm (wReg (freshReg ctx (key pv))))
    let pnames = wnames @ pnames
    // this ctor's class-param witnesses (for the class ERecord it builds).
    ctx.ClassCtorWits <- witnessVars
    // a method of a Canon generic class reads its class-param witnesses off
    // `self` (ps[0]) at construction-time trailing slots, seeding ctx.Witness so
    // the same routing (cmpv/hash/generic-cons) that serves function type vars
    // serves the class' type vars. (int off) is the byte offset of slot j.
    let selfPreamble =
        match ps with
        | self0 :: _ when not (List.isEmpty selfWits) ->
            let selfReg = regOf ctx (key self0)
            selfWits |> List.map (fun (vid, off) ->
                let r = freshTmp ctx
                dictSet ctx.Witness vid r
                LSet (wReg r, LLoad (W, LGet (wReg selfReg), off)))
        | _ -> []
    // a STAMPED generic-class member: its class type param is concrete here, so
    // seed a CONSTANT static witness for it (the receiver is fully concrete, so
    // there is no `self` slot to read — the type is known at stamp time). The
    // residual `'k` op then routes by that refMask instead of $cmpv/$hashv.
    let constPreamble =
        constWits |> List.map (fun (vid, witExpr) ->
            let r = freshTmp ctx
            dictSet ctx.Witness vid r
            (if List.length constWits = 1 then ctx.ClassWit <- Some r)
            LSet (wReg r, witExpr))
    // a specialized scalar ABI: each scalar param arrives UNBOXED in a typed
    // local (registered in VarScalar so reads re-box, just like a scalar let);
    // a scalar return is unboxed off the body's boxed word before the return.
    let retTy =
        match sig_ with
        | Some (paramTys, ret) ->
            List.iter2 (fun pv ty -> match ty with W -> () | _ -> let id = regOf ctx (key pv) in vecSet ctx.RegTys id ty; dictSet ctx.VarScalar (key pv) ty) ps paramTys
            ret
        | None -> W
    // GC: root each ref-typed (non-scalar) parameter on the shadow stack for the
    // body's duration — a param is a wasm local the collector never scans, so a
    // pointer param used after an allocating call would go stale (the tokenizer's
    // `loop` cons'd onto its `acc` after an allocating scan moved it). Reads go
    // through the slot's stable address (ctx.Slotted). Witness-pointer params are
    // static, never rooted.
    let rootParams =
        if gc then
            List.zip ps paramTypes
            // a REF param roots in a plain slot; a GENERIC param with NO
            // witness is on the canonical TAGGED form and roots the same
            // way (the Dictionary's dictSlotH key went stale un-rooted);
            // a GENERIC with a witness stays on ActiveGen's conditional
            // rooting (at a raw stamp its W lane holds a raw even int the
            // scanner must never chase); RAW/scalar params never root.
            |> List.filter (fun (pv, ty) ->
                (scalarLTy ty).IsNone && (dictTryFind ctx.VarScalar (key pv)).IsNone
                && (match refKindOfTy ty with
                    | RKRef -> true
                    | RKGen -> (match prune ty with
                                | TVar tv -> (dictTryFind ctx.Witness tv.Id).IsNone
                                | _ -> true)
                    | RKRaw -> false))
            |> List.map (fun (pv, _) -> pv, freshTmp ctx)
        else []
    for pv, slotReg in rootParams do dictSet ctx.Slotted (key pv) (LGet (wReg slotReg))
    // GC: a GENERIC (`'a`) param whose element witness is in scope is rooted
    // conditionally across safepoints (a raw 'a must not reach the pointer scanner),
    // for the whole body — its register is its scope. Fixes a stale generic head in
    // `x :: rest` where `x` is a param held across an allocating call.
    ctx.ActiveGen <-
        (if gc then
            List.zip ps paramTypes
            |> List.choose (fun (pv, ty) ->
                match prune ty with
                | TVar tv when (dictTryFind ctx.VarScalar (key pv)).IsNone && (dictTryFind ctx.LSt.CellVars (key pv)).IsNone ->
                    (match dictTryFind ctx.Witness tv.Id with Some w -> Some (regOf ctx (key pv), w) | None -> None)
                | _ -> None)
         else [])
    let sink = vecNew ()
    st.GapSink <- Some sink
    preRecGroups ctx body
    // SELF-tail-calls: mark the body's tail applications; a full-arity call
    // to THIS function there lowers to LTailCall (wasm return_call). The
    // entry $sp is saved (gc) so the transfer can discharge every
    // outstanding shadow-stack push in one restore.
    tailFnName <- (if isInit || not (isNull (System.Environment.GetEnvironmentVariable "FPP_NO_TAILCALL")) then "" else dbgName)
    tailSpReg <- -1
    if tailFnName <> "" then
        markTails st body
        if gc then tailSpReg <- freshTmp ctx
    let bodyLow1 = coreToLowE ctx body
    // the entry-$sp save must come BEFORE the rootParams pushes (they wrap
    // the whole body below) — saving after them made every return_call
    // restore to the post-push level, leaking one frame of pushes per tail
    // transfer until the shadow stack ran off the end of memory
    let preamble =
        (if tailSpReg >= 0 && List.isEmpty rootParams then [ LSet (wReg tailSpReg, LGetGlobal "$sp") ] else [])
        @ selfPreamble @ constPreamble
    let bodyLow0 = if List.isEmpty preamble then bodyLow1 else LDo (preamble, bodyLow1)
    let bodyLow2 =
        if List.isEmpty rootParams then bodyLow0
        else
            let resReg = freshTmp ctx
            let spSave = if tailSpReg >= 0 then [ LSet (wReg tailSpReg, LGetGlobal "$sp") ] else []
            let pushes = spSave @ (rootParams |> List.collect (fun (pv, slotReg) ->
                let pvReg = match dictTryFind ctx.Regs (key pv) with Some i -> i | None -> 0 - 1
                [ LSet (wReg slotReg, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
                  LStore (W, LGet (wReg slotReg), 0, LGet (wReg pvReg))
                  LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ]))
            let pop = LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW (4 * List.length rootParams) ]))
            LDo (pushes @ [ LSet (wReg resReg, bodyLow0); pop ], LGet (wReg resReg))
    // FPP_CONSCHECK: the shadow-stack pointer must be BALANCED across the
    // body (pushes = pops on every path) — an imbalance desyncs every later
    // frame's slots and the collector scans junk
    let bodyLow2 =
        if consCheckOn () then
            let spSave = freshTmp ctx
            let r2 = freshTmp ctx
            chkSite <- chkSite + 1
            let site = chkSite
            eprintfn "SPSITE %d = %s" site dbgName
            LDo ([ LSet (wReg spSave, LGetGlobal "$sp")
                   LSet (wReg r2, bodyLow2)
                   LIf (LPrim (NeW, [ LGetGlobal "$sp"; LGet (wReg spSave) ]),
                        [ LCallVoidS ("$eprints", [ LCall ("$str_of_int", [ LConstW site ]) ]); LTrap ], []) ],
                 LGet (wReg r2))
        else bodyLow2
    let bodyLow = match retTy with W -> bodyLow2 | _ -> flatUnbox retTy bodyLow2
    // TEMP DEBUG: validate the freshly-lowered tree — every register it
    // names must be below ctx.NReg. Corrupt-at-build vs corrupt-at-walk.
    let mutable maxReg = -1
    let seeR (r : LReg) = if r.Id > maxReg then maxReg <- r.Id
    let rec seeE (e : LExpr) : unit =
        match e with
        | LConstW _ | LConstL _ | LConstF _ | LGetGlobal _ -> ()
        | LGet r -> seeR r
        | LLoad (_, a, _) -> seeE a
        | LPrim (_, xs) | LCall (_, xs) | LTailCall (_, xs) -> for x in xs do seeE x
        | LAlloc a -> seeE a
        | LCallIndirect (_, a, xs) | LCallIdx (_, a, xs) -> seeE a; (for x in xs do seeE x)
        | LDo (ss, e2) -> (for st2 in ss do seeS st2); seeE e2
    and seeS (st2 : LStmt) : unit =
        match st2 with
        | LStore (_, a, _, b) -> seeE a; seeE b
        | LSet (r, e2) -> seeR r; seeE e2
        | LSetGlobal (_, e2) | LEval e2 | LBreakIf (_, e2) | LThrow e2 | LReturn e2 -> seeE e2
        | LCallVoidS (_, xs) -> for x in xs do seeE x
        | LIf (c, a, b) -> seeE c; (for x in a do seeS x); (for x in b do seeS x)
        | LWhile (c, b) -> seeE c; for x in b do seeS x
        | LBlock (_, b) -> for x in b do seeS x
        | LBreak _ | LTrap -> ()
        | LTryStmt (b, r1, r2, hs) -> seeE b; seeR r1; seeR r2; for x in hs do seeS x
    seeE bodyLow
    let rec dumpE (e : LExpr) : string =
        match e with
        | LConstW n -> "w" + string n
        | LConstL _ -> "l"
        | LConstF _ -> "f"
        | LGet r -> "g" + string r.Id
        | LGetGlobal n -> "G(" + n + ")"
        | LLoad (_, a, o) -> "ld[" + dumpE a + "+" + string o + "]"
        | LPrim (_, xs) -> "p(" + String.concat " " (List.map dumpE xs) + ")"
        | LCall (n, xs) -> "c:" + n + "(" + String.concat " " (List.map dumpE xs) + ")"
        | LTailCall (n, xs) -> "tc:" + n + "(" + String.concat " " (List.map dumpE xs) + ")"
        | LAlloc a -> "al(" + dumpE a + ")"
        | LCallIndirect (_, a, xs) -> "ci(" + dumpE a + ";" + String.concat " " (List.map dumpE xs) + ")"
        | LCallIdx (i, a, xs) -> "cx" + string i + "(" + dumpE a + ";" + String.concat " " (List.map dumpE xs) + ")"
        | LDo (ss, e2) -> "do{" + String.concat "; " (List.map dumpS ss) + "}" + dumpE e2
    and dumpS (st2 : LStmt) : string =
        match st2 with
        | LStore (_, a, o, b) -> "st[" + dumpE a + "+" + string o + "]=" + dumpE b
        | LSet (r, e2) -> "s" + string r.Id + "=" + dumpE e2
        | LSetGlobal (n, e2) -> "SG(" + n + ")=" + dumpE e2
        | LEval e2 -> "ev " + dumpE e2
        | LCallVoidS (n, xs) -> "cv:" + n + "(" + String.concat " " (List.map dumpE xs) + ")"
        | LIf (c, a, b) -> "if(" + dumpE c + "){" + String.concat "; " (List.map dumpS a) + "}{" + String.concat "; " (List.map dumpS b) + "}"
        | LWhile (c, b) -> "wh(" + dumpE c + "){" + String.concat "; " (List.map dumpS b) + "}"
        | LBlock (n, b) -> "bl:" + n + "{" + String.concat "; " (List.map dumpS b) + "}"
        | LBreakIf (n, e2) -> "bi:" + n + "(" + dumpE e2 + ")"
        | LBreak n -> "br:" + n
        | LTrap -> "trap"
        | LReturn e2 -> "ret " + dumpE e2
        | LThrow e2 -> "th " + dumpE e2
        | LTryStmt (b, r1, r2, hs) -> "try{" + dumpE b + "}r" + string r1.Id + ",r" + string r2.Id + "{" + String.concat "; " (List.map dumpS hs) + "}"
    if maxReg >= ctx.NReg then
        // corrupt-at-build sanity: a register the lowering never allocated
        // in this function's tree means state corruption (the self-host GC
        // staleness class) — fail LOUDLY, never emit a bad module
        err st ("lowered tree of " + dbgName + " names register " + string maxReg
                + " of " + string ctx.NReg + " — corrupt lowering state; tree: "
                + (let d = dumpE bodyLow in if d.Length > 2000 then d.Substring (0, 2000) else d))
    if System.Environment.GetEnvironmentVariable "FPP_TREE_DUMP" = dbgName then
        eprintfn "TREE %s %s" dbgName (dumpE bodyLow)
    st.GapSink <- None
    let f = beginFn m pnames
    if vecLen sink > 0 then
        // a gap in this body: emit an unreachable STUB (mirrors the wasm-GC
        // driver's per-function probe). The gap becomes a warning; the function
        // traps if ever reached. Dead prelude/backend members survive DCE.
        // A SYMBOLIC class marker ("#N") sits only in an unstamped TEMPLATE
        // whose stamps carry the real instantiation — expected, kept quiet.
        let e0 = vecGet sink 0
        if not (isNull (System.Environment.GetEnvironmentVariable "FPP_GAP_DUMP")) then
            eprintfn "GAP %s (%s)" dbgName e0
        if not (e0.Contains "$class:" && e0.Contains "#") then
            vecAdd st.Warnings ("stubbed " + dbgName + " (" + e0 + ")")
        else
            vecAdd st.Warnings ("quietstub " + dbgName + " (" + e0 + ")")
        localsDone f
        // a stubbed INIT (a .NET-only top-level `let`, e.g. an Encoding object)
        // must NOT trap: _start runs every init at startup, so store a harmless
        // 0 instead — the value is only ever touched by already-stubbed .NET
        // methods. A stubbed FUNCTION still traps loudly if it is ever called.
        if isInit then (ic f 0; finish f) else ins f "unreachable"
    else
        let np = List.length witnessVars + List.length ps
        for id in np .. ctx.NReg - 1 do local f (regNm (wReg id)) (wtyName (vecGet ctx.RegTys id))
        localsDone f
        emitLowE f bodyLow
        finish f
    endFn f

// a lifted lambda body: params are (env, arg); captured free variables read
// from the env at 8+4*slot (st.Captures is set by the driver). Register 0 is
// the env, register 1 the argument.
let private emitLambdaLow (st : St) (m : Mod) (lamName : string) (pv : VarId) (psch : Scheme) (body : Expr) : unit =
    let ctx = { LSt = st; Regs = dictNew (); EnvReg = 0; RegTys = vecNew (); VarScalar = dictNew (); Witness = dictNew (); ClassCtorWits = []; ClassWit = None; EnvAddr = None; Slotted = dictNew (); ActiveGen = []; SlottedGen = []; NReg = 0 }
    let envId = freshTmp ctx
    let argId = freshReg ctx (key pv)
    // GC: root the env AND a ref-typed argument on the shadow stack for the body's
    // duration. A collection triggered by any allocation in the body can relocate
    // either; the wasm-locals `envId`/`argId` are then stale, so a capture read
    // (`[env+8+4*slot]`) or a use of the arg after a call would hit a moved object.
    // Storing them in scanned root slots lets the collector update them in place;
    // reads go through each slot's stable address (ctx.EnvAddr / ctx.Slotted).
    // Self-host: blam14 rebuilt its env from a stale env; the tokenizer's `loop`
    // consed onto its `acc` arg after an allocating scan that had moved it.
    let rootEnv = gc && not (dictPairs st.Captures |> List.isEmpty)
    let envSlotReg = if rootEnv then Some (freshTmp ctx) else None
    (match envSlotReg with Some r -> ctx.EnvAddr <- Some (LGet (wReg r)) | None -> ())
    let rootArg = gc && refKindOfTy psch.Body = RKRef && (scalarLTy psch.Body).IsNone
    let argSlotReg = if rootArg then Some (freshTmp ctx) else None
    (match argSlotReg with Some r -> dictSet ctx.Slotted (key pv) (LGet (wReg r)) | None -> ())
    let sink = vecNew ()
    st.GapSink <- Some sink
    preRecGroups ctx body
    // read the enclosing fn's captured witnesses out of the env ONCE at entry
    // (before any body allocation, so the env param is fresh) into stable regs,
    // and seed ctx.Witness so the body's generic aggregates resolve. Witnesses
    // point into immortal g_witnesses, so they never relocate.
    let witLoads =
        match dictTryFind st.LamWits lamName with
        | Some wits -> wits |> List.map (fun (tvId, slot) -> let r = freshTmp ctx in dictSet ctx.Witness tvId r; LSet (wReg r, LLoad (W, LGet (wReg envId), HDR + 8 + 4 * slot)))
        | None -> []
    // an UNRESOLVED (`'a`-typed) arg with a captured witness in scope: root it
    // conditionally on the witness refMask, exactly like a generic let (a raw
    // `'a` must NOT be pushed; a ref `'a` unrooted goes stale across the
    // body's safepoints — the substVars-walk lambdas hit this).
    let condArg =
        if gc && not rootArg && (scalarLTy psch.Body).IsNone && refKindOfTy psch.Body <> RKRaw then
            match prune psch.Body with
            | TVar tv -> (match dictTryFind ctx.Witness tv.Id with
                          | Some witR -> Some (witR, freshTmp ctx)
                          | None -> None)
            | _ -> None
        else None
    (match condArg with
     | Some (witR, slotR) -> ctx.SlottedGen <- (argId, witR, slotR) :: ctx.SlottedGen
     | None -> ())
    // a GENERIC arg with NO witness in scope rides the canonical TAGGED form
    // (closure args always do) — root it UNCONDITIONALLY, exactly as
    // rootParams does for top-level functions. DROPPING it was the
    // stamped-member miscompile: `keep`'s un-annotated Scheme arg (a TVar
    // with no captured witness) went stale across $key's allocation, prune
    // walked a moved object, and every gen binder of the arm vanished —
    // rootActiveGen sequences missing from the self-hosted output.
    let rootArgGen =
        gc && not rootArg && condArg.IsNone
        && (scalarLTy psch.Body).IsNone && refKindOfTy psch.Body = RKGen
    let argGenSlotReg = if rootArgGen then Some (freshTmp ctx) else None
    (match argGenSlotReg with Some r -> dictSet ctx.Slotted (key pv) (LGet (wReg r)) | None -> ())
    let bodyLow0 = coreToLowE ctx body
    st.GapSink <- None
    // roots to establish at entry: (slot register, initial value). Pushed in
    // order (distinct slots), all popped together at the single fall-through exit.
    let entryRoots =
        (match envSlotReg with Some r -> [ r, LGet (wReg envId) ] | None -> [])
        @ (match argSlotReg with Some r -> [ r, LGet (wReg argId) ] | None -> [])
        @ (match argGenSlotReg with Some r -> [ r, LGet (wReg argId) ] | None -> [])
    let bodyLow =
        if List.isEmpty entryRoots && condArg.IsNone then bodyLow0
        else
            let resReg = freshTmp ctx
            let pushes = entryRoots |> List.collect (fun (r, v) ->
                [ LSet (wReg r, LPrim (AddW, [ LGetGlobal "$roots"; LGetGlobal "$sp" ]))
                  LStore (W, LGet (wReg r), 0, v)
                  LSetGlobal ("$sp", LPrim (AddW, [ LGetGlobal "$sp"; LConstW 4 ])) ])
            let condPush = match condArg with Some (witR, slotR) -> [ gcSlotPush argId witR slotR ] | None -> []
            let condPop = match condArg with Some (witR, _) -> [ gcSlotPop witR ] | None -> []
            let pop = if List.isEmpty entryRoots then [] else [ LSetGlobal ("$sp", LPrim (SubW, [ LGetGlobal "$sp"; LConstW (4 * List.length entryRoots) ])) ]
            LDo (pushes @ condPush @ [ LSet (wReg resReg, bodyLow0) ] @ condPop @ pop, LGet (wReg resReg))
    let bodyLow = if List.isEmpty witLoads then bodyLow else LDo (witLoads, bodyLow)
    let f = beginFn m [ regNm (wReg envId); regNm (wReg argId) ]
    if vecLen sink > 0 then
        if not (isNull (System.Environment.GetEnvironmentVariable "FPP_GAP_DUMP")) then
            eprintfn "GAPLAM %s (%s)" lamName (vecGet sink 0)
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
let private etaExpand (funcs : Dict<string, int>) (caseArity : Dict<string, int>) : Expr -> Expr =
    let fresh (sch : Scheme) : VarId * Scheme =
        etaCtr <- etaCtr + 1
        { Path = "(eta)"; Offset = etaCtr; Name = "$e" + string etaCtr }, sch
    // The type of a synthetic eta param: the `idx`-th argument type of `sch`
    // AFTER `skip` already-applied arrows. A synthetic param must carry its OWN
    // type, NOT the whole function scheme — a function type is RKRef, so giving a
    // raw param (an `int`) the fn scheme classified it as a pointer, and the eta
    // closure rooted a raw int on the GC shadow stack for the collector to chase
    // as a wild pointer (only when a collection landed inside the call).
    let peelArg (sch : Scheme) (skip : int) (idx : int) : Scheme =
        let rec peel t n = if n <= 0 then t else (match prune t with TFun (_, r) -> peel r (n - 1) | _ -> t)
        let rec argAt t j = match prune t with TFun (a, r) -> (if j = 0 then a else argAt r (j - 1)) | _ -> t
        { sch with Body = argAt (peel sch.Body skip) idx }
    // `hd` is the ORIGINAL head node — an EVarI must survive the wrap: the call
    // lowering resolves the hidden witness arguments from EVarI.inst, and a
    // rebuilt bare EVar made every witness fall back to the ref-claiming
    // default, so a raw-scalar type param (distinctBy's 'k = int) was consed
    // onto a REF-scanned list and the collector chased the raw ints.
    let wrap (hd : Expr) (sch : Scheme) (pre : Expr list) (need : int) : Expr =
        // an EVarI head carries the INSTANTIATION: substitute it into the eta
        // params' peeled types so a `'a`-typed param resolves concrete and the
        // lambda machinery can classify (root/skip) it — an unresolved param
        // can be neither rooted nor skipped and goes stale across the body.
        let instSub : (Type -> Type) =
            match hd with
            | EVarI (_, hsch, inst) when not (List.isEmpty inst) && not (List.isEmpty hsch.Quantified) ->
                let m = dictNew<int, Type> ()
                (List.zip (List.truncate (List.length inst) hsch.Quantified)
                          (List.truncate (List.length hsch.Quantified) inst)
                 |> List.iter (fun (qv, nm) ->
                        if nm <> "" && not (nm.StartsWith "#") && nm <> "obj" then
                            dictSet m qv.Id (TCon (nm, []))
                            dictSet m (prunedId qv) (TCon (nm, []))))
                let rec sub t =
                    match prune t with
                    | TVar v -> (match dictTryFind m v.Id with Some c -> c | None -> TVar v)
                    | TCon (n, args) -> TCon (n, List.map sub args)
                    | TFun (x, y) -> TFun (sub x, sub y)
                    | TTuple ts -> TTuple (List.map sub ts)
                    | TApp (h, args) -> TApp (sub h, List.map sub args)
                sub
            | _ -> id
        let ps = List.init need (fun i -> let s0 = peelArg sch (List.length pre) i in fresh { s0 with Body = instSub s0.Body })
        let call = EApp (hd, pre @ (ps |> List.map (fun (p, s) -> EVar (p, s))))
        List.foldBack (fun p body -> ELam ([ p ], body)) ps call
    let rec go (e : Expr) : Expr =
        match e with
        // an APPLIED builtin `compare`: keep the head (do not eta it — that is
        // only for the bare-value use), recurse into the arguments
        | EApp ((EVar (v, _) | EVarI (v, _, _)) as h, args) when v.Path = "(builtin)" && v.Name.StartsWith "compare" ->
            EApp (h, List.map go args)
        | EApp ((EVar (v, sch) | EVarI (v, sch, _)) as h, args) when (dictTryFind funcs (key v)).IsSome ->
            let n = optGet (dictTryFind funcs (key v))
            let args = List.map go args
            let k = List.length args
            if k = n then EApp (h, args)
            elif k < n then wrap h sch args (n - k)
            else EApp (EApp (h, List.truncate n args), List.skip n args)
        // the builtin `compare` used as a value: eta so the applied handler
        // fires (operand shapes drive it; opaque operands degrade to scalar)
        | (EVar (v, sch) | EVarI (v, sch, _)) as hd when v.Path = "(builtin)" && v.Name.StartsWith "compare" ->
            // operands take compare's ARGUMENT type, not its whole `'a -> 'a -> int`
            // scheme — else a raw operand rode the shadow stack as a wild pointer.
            // Route through `wrap`: it peels each operand's own type AND
            // substitutes an EVarI head's instantiation into it, so the
            // applied-compare handler sees typed operands and picks the
            // scalar/string/shape comparator. The old direct eta left the
            // params at compare's own quantified var — the body fell to the
            // generic $cmpv, whose odd/even int-vs-pointer discrimination is
            // WRONG for raw full-width ints (compare 3 2 = -1), which
            // mis-sorted every `List.sort` of ints — including the
            // emitter's own vArities sort, the last 881 bytes vs the oracle.
            wrap hd sch [] 2
        | (EVar (v, sch) | EVarI (v, sch, _)) as hd ->
            match dictTryFind funcs (key v) with Some n when n > 0 -> wrap hd sch [] n | _ -> e
        // `compare` used as a VALUE (List.sortWith compare, …): eta to
        // `fun a b -> compare a b` so the applied handler fires; the operand
        // types come from the dispatch NAME, so the params' schemes are moot
        | EUnknown n when n.StartsWith "$class:Ordered:compare:" ->
            let av, asch = fresh (mono tInt)
            let bv, bsch = fresh (mono tInt)
            ELam ([ (av, asch) ], ELam ([ (bv, bsch) ], EApp (EUnknown n, [ EVar (av, asch); EVar (bv, bsch) ])))
        | EUnknown _ -> e
        // a case constructor used as a VALUE (`List.map TVar ps`, `xs |> List.map Some`):
        // the plain ECtor lowering builds the case OBJECT, which has no code
        // index — calling it read past the object and call_indirect'ed through
        // garbage. Wrap it into a lambda building the saturated case, so it
        // lifts and lowers like any closure. The ctor value is TUPLED (one
        // arrow); a multi-payload case takes its tuple apart in a match.
        | ECtor (cn, sch, []) when (match dictTryFind caseArity cn with Some ar -> ar > 0 | None -> false) ->
            let ar = optGet (dictTryFind caseArity cn)
            (match prune sch.Body with
             | TFun (dom, _) ->
                 (match prune dom with
                  | TTuple ts when ar > 1 && List.length ts = ar ->
                      let pv, psch = fresh { sch with Body = dom }
                      let elems = ts |> List.map (fun t -> fresh { sch with Body = t })
                      let pat = PTuple (elems |> List.map PVar)
                      ELam ([ (pv, psch) ],
                            EMatch (EVar (pv, psch), [ pat, None, ECtor (cn, sch, elems |> List.map EVar) ]))
                  | _ ->
                      let pv, psch = fresh { sch with Body = dom }
                      ELam ([ (pv, psch) ], ECtor (cn, sch, [ EVar (pv, psch) ])))
             | _ -> e)
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
    // Prelude impls included: leaving them out dropped the stamped
    // ResizeArray.GetEnumerator, its vtable row stayed 0, and every
    // `List.ofSeq (r :> seq)` dispatched through index 0 — an empty list at
    // best and a WILD indirect call at worst (the self-host's inference-time
    // heap scribble). A prelude method a gap still can't lower stubs loudly.
    for d in decls0 do
        match d with
        | DClass (_, _, own, impls) ->
            for _, ms in impls do
                for _, v in ms do
                    visit (v.Path + ":" + string v.Offset)
            // ... and the class' OWN members: an `override` of an abstract
            // base member dispatches through the same vtable but lives in
            // `own`, not `impls`. Leaving them out dropped every
            // HashEmpty/HashLeaf/HashInner override, their rows stayed 0, and
            // `HashMap.ofList` dispatched through index 0 — an indirect call
            // whose signature did not match (the whole Map/Set/HashMap
            // cluster). deadCodeEliminate already parked these on the
            // constructor, so only CONSTRUCTED classes reach here.
            for _, v in own do
                visit (v.Path + ":" + string v.Offset)
        // a RECORD's or UNION's identity members are reached the same way —
        // $cmpv/$hashv dispatch through the vtable row, never by name (a
        // union's `member x.Equals` is what makes Map content equality work)
        | DMembers (_, own) ->
            for mn, v in own do
                if mn = "Equals" || mn = "GetHashCode" || mn = "CompareTo" then
                    visit (v.Path + ":" + string v.Offset)
        | _ -> ()
    // keep decls0 order (prelude before user — inits sequence correctly),
    // filtered to what is reachable
    let decls =
        decls0 |> List.filter (fun d ->
            match d with
            | DLet (_, v, _, _) -> (dictTryFind reachable (v.Path + ":" + string v.Offset)).IsSome
            | _ -> false)
    let m = modNew ()
    // table index 0 is the missing-row trap (see $novt): a vtable row of 0
    // means NO implementation, and calling through it used to run whatever
    // function registered first. Claimed HERE, before any lambda.
    tblIdx m "$novt" |> ignore
    let st =
        { M = m; Errors = vecNew (); GapSink = None; Warnings = vecNew ()
          Funcs = dictNew (); FuncSig = dictNew (); FuncWitness = dictNew (); Witnesses = dictNew (); WitnessData = vecNew (); WitnessCur = 0; Globals = dictNew (); Externs = dictNew (); IfaceArities = dictNew ()
          Consts = dictNew (); ConstNext = CONST_BASE; ConstData = bytesNew ()
          LamName = refMapNew shallowLamHash; TailApp = refMapNew shallowLamHash; Lams = vecNew ()
          Captures = dictNew (); LamWits = dictNew ()
          RecFields = dictNew (); ClassNames = dictNew (); RecBase = dictNew (); RecFieldTypes = dictNew (); RecPod = dictNew (); RecFieldTys = dictNew (); Collapse = dictNew (); UnionTag = dictNew (); UnionArity = dictNew (); EnumConst = dictNew ()
          ClassId = dictNew (); CaseClass = dictNew (); WitnessedClasses = dictNew ()
          SlotOf = dictNew (); NSlots = 0; VtBase = 0; TestIds = dictNew (); UsesExn = false
          CellVars = cellScan decls0; CellKind = cellKindScan decls0 (cellScan decls0)
          Tids = dictNew (); TidRegs = vecNew (); TidRefoffs = dictNew (); TidNext = TID_FIRST
          FieldOwnerOf = dictNew ()
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
            dictSet st.RecFieldTypes n fs
            for f, _ in fs do
                let prev = match dictTryFind st.FieldOwnerOf f with Some xs -> xs | None -> []
                if not (List.contains n prev) then dictSet st.FieldOwnerOf f (n :: prev)
            if (dictTryFind st.ClassId n).IsNone then (dictSet st.ClassId n nextCid; nextCid <- nextCid + 1)
        | DUnion (uname, _, cs) ->
            let cid = match dictTryFind st.ClassId uname with Some c -> c | None -> (let c = nextCid in dictSet st.ClassId uname c; nextCid <- nextCid + 1; c)
            cs |> List.iteri (fun i (cn, ar) ->
                dictSet st.UnionTag cn i
                dictSet st.UnionArity cn ar
                dictSet st.CaseClass cn cid)
        | DEnum (_, cs) -> for c, v in cs do dictSet st.EnumConst c v
        | _ -> ()
    // single-field-collapse (repr(T)): a one-field record travels as its field
    // (no heap object), UNLESS it is mutated, type-tested/cast, or a CLASS (a
    // class has a vtable + its storage is a DRecord, so it also lands in
    // RecFields — but its instance-field reads and dispatch need the object).
    let noCollapse = scanNoCollapse decls0
    let classNames = st.ClassNames
    for d in decls0 do match d with DClass (n, _, _, _) -> dictSet classNames n true | _ -> ()
    // a stamped subclass resolves its fields through the base it was stamped
    // from (DClass carries `Some base`); record subclass -> base for EField.
    for d in decls0 do match d with DClass (n, Some b, _, _) when b <> n -> dictSet st.RecBase n b | _ -> ()
    // a class that INHERITS lays its base's fields out as a PREFIX: the base's
    // members read their slots at the same offsets through an upcast receiver.
    // Only classes with OWN fields expand — a stamped clone (own list empty)
    // keeps resolving through its base and must not claim the field names
    // (Cat(name, lives) previously registered ["lives"] alone, so the object
    // dropped `name` and Animal.Name read `lives` as a string).
    let origFields = dictNew<string, string list> ()
    for kv in dictPairs st.RecFields do dictSet origFields (fst kv) (snd kv)
    let rec chainFields (seen : string list) (n : string) : string list =
        let own = match dictTryFind origFields n with Some o -> o | None -> []
        match dictTryFind st.RecBase n with
        | Some b when b <> n && not (List.contains b seen) -> chainFields (n :: seen) b @ own
        | _ -> own
    for d in decls0 do
        match d with
        | DClass (n, Some b, _, _) when b <> n ->
            (match dictTryFind origFields n with
             | Some own when not (List.isEmpty own) ->
                 let full = chainFields [] n
                 if List.length full > List.length own then dictSet st.RecFields n full
             | _ -> ())
        | _ -> ()
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
        // a BARE type-variable field (`'a`, not `'a[]`/`list<'a>` which are
        // pointers) can hold a raw scalar at runtime, so it cannot ride the inline
        // POD form whose FK_TAGGED tracer scans the ref suffix uniformly — that
        // chased an even int. Such records fall to the heap path, where lowObjR
        // builds precise witness-driven refoffs. Concrete records are unaffected.
        | DRecord (n, _, fs, _) when
                List.length fs >= 2 && (dictTryFind classNames n).IsNone
                && not (fs |> List.exists (fun (_, ty) -> ty.StartsWith "'" && not (ty.Contains "[") && not (ty.Contains "<"))) ->
            let scalars = fs |> List.filter (fun (_, ty) -> (storLTy ty).IsSome)
            let refs = fs |> List.filter (fun (_, ty) -> (storLTy ty).IsNone)
            if not (List.isEmpty scalars) then
                let m = dictNew<string, int * string> ()
                // C's natural alignment: each scalar sits at a multiple of its
                // own width and the struct's SIZE rounds up to the widest
                // member's. `{ M : float; T : byte }` is 16 bytes in C, not 9 —
                // an array of them strides 16, and a foreign reader walking at
                // 9 read every element after the first at the wrong offset.
                let widthOf (ty : string) = snd (optGet (storLTy ty))
                let maxA = scalars |> List.fold (fun acc (_, ty) -> max acc (widthOf ty)) 1
                let align (o : int) (a : int) = ((o + a - 1) / a) * a
                let mutable off = HDR
                for (fn, ty) in scalars do
                    let w = widthOf ty
                    off <- HDR + align (off - HDR) w
                    dictSet m fn (off, ty)
                    off <- off + w
                // pad to the widest member so the ARRAY stride is C's
                off <- HDR + align (off - HDR) maxA
                let firstRefWord = off / 4
                for (fn, ty) in refs do
                    dictSet m fn (off, ty)
                    off <- off + 4
                dictSet st.RecPod n (m, off, firstRefWord)
        | _ -> ()
    // record every STRUCT record's ordered declared fields for the inline-value
    // layout engine (`layoutOf`). Value types only — reference records stay a
    // pointer word. Written for groundwork; no codegen path reads it yet.
    for d in decls0 do
        match d with
        | DRecord (n, _, fs, true) -> dictSet st.RecFieldTys n fs
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
        let fromIface =
            chainOf cn
            |> List.tryPick (fun c ->
                classDecls
                |> List.tryPick (fun (n2, _, _, impls) ->
                    if n2 <> c then None
                    else impls |> List.tryPick (fun (i, ms) -> if bareIface i = owner then ms |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None) else None)))
        match fromIface with
        | Some v -> Some v
        | None ->
            // ABSTRACT dispatch through a base CLASS: the nearest own
            // member anywhere in the chain answers the slot (mirrors
            // BinDriver/CEmit — without this the slot lookup silently
            // dispatched through slot 0 and read a garbage table index)
            if List.contains owner (chainOf cn) then
                chainOf cn
                |> List.tryPick (fun c ->
                    classDecls
                    |> List.tryPick (fun (n2, _, own, _) ->
                        if n2 <> c then None
                        else own |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None)))
            else None
    let declaredMemberSlots =
        decls0
        |> List.collect (fun d ->
            match d with
            | DMembers (n, own) -> own |> List.map (fun (mn, _) -> bareIfaceOf n, mn)
            | _ -> [])
    // slots 0/1/2 of EVERY row are the identity trio: a class' own Equals,
    // GetHashCode and CompareTo. $cmpv/$hashv dispatch through them, so a
    // type that defines content equality (Map/HashMap over an AVL/patricia
    // tree, whose SHAPE differs for equal contents) compares by its own rule
    // instead of the structural word fold. 0 = not declared.
    let identitySlots = [ "$id", "Equals"; "$id", "GetHashCode"; "$id", "CompareTo" ]
    let vtableSlots =
        identitySlots
        @ (((interfaceDecls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> bareIface i, mn)))
            @ (classDecls |> List.collect (fun (_, _, _, impls) -> impls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> bareIface i, mn))))
            // abstract/override members dispatched through the CLASS: a slot
            // per declared member name, keyed by the declaring class
            @ declaredMemberSlots)
           |> List.distinct |> List.sort)
    st.NSlots <- List.length vtableSlots
    vtableSlots |> List.iteri (fun i (ifn, mn) -> dictSet st.SlotOf (ifn + "|" + mn) i)
    // the class-id set a `:? T` accepts: a class matches itself and its
    // subclasses; an interface matches its implementors; anything else is exact
    let cidsOf (names : string list) = names |> List.choose (fun n -> dictTryFind st.ClassId n)
    for cn, _, _, _ in classDecls do dictSet st.TestIds cn (cidsOf (subclassesOf cn))
    // an ABSTRACT base has no DClass of its own (nothing constructs it),
    // but `:? Base` must still answer for every subclass — without this
    // the test id set was simply absent and the test was always false
    for _, b, _, _ in classDecls do
        match b with
        | Some bn when not ((dictTryFind st.TestIds bn).IsSome) ->
            dictSet st.TestIds bn (cidsOf (subclassesOf bn))
        | _ -> ()
    for ifn, _ in interfaceDecls do
        let impls = classDecls |> List.filter (fun (_, _, _, impls) -> impls |> List.exists (fun (i, _) -> bareIface i = bareIface ifn)) |> List.collect (fun (cn, _, _, _) -> subclassesOf cn) |> List.distinct
        // MERGE with what the class loop recorded: an abstract class is
        // both a DClass and a DInterface, and overwriting here replaced
        // its subclass set with the (empty) impl-clause set — `:? Shape`
        // answered false for every Shape subclass
        let merged (key : string) =
            let prior = match dictTryFind st.TestIds key with Some xs -> xs | None -> []
            (prior @ cidsOf impls) |> List.distinct
        dictSet st.TestIds ifn (merged ifn)
        dictSet st.TestIds (bareIface ifn) (merged (bareIface ifn))
    rtTypesLin m
    // classify top-level bindings. A lambda-valued binding that is REASSIGNED
    // is a mutable global holding a closure, not a fixed function. GC: each
    // non-function global takes a root slot (before constants).
    let assigned = collectAssigned decls
    if gc then gcGlobalSlots <- dictNew ()
    // interface-method impls are reached ONLY through the vtable, which dispatches
    // at the uniform `$lfn<n>` type. So a vtable member must NEVER take a
    // funSigOf-specialized signature (a raw f64/i64 param/return) — its declared
    // type would then differ from the call_indirect type and trap. It keeps the
    // uniform sig; a scalar rides the boxed-at-rest representation coreToLowE
    // already produces. (Matches the wasm-GC backend's all-anyref vtable rule.)
    let vtImpls = dictNew<string, bool> ()
    // the identity trio is dispatched INDIRECTLY by $cmpv/$hashv, so it must
    // keep the uniform (self, other) signature: no specialized scalar ABI and
    // no hidden witness params, or the call_indirect type mismatches
    for d in decls0 do
        match d with
        | DMembers (_, own) ->
            for mn, v in own do
                if mn = "Equals" || mn = "GetHashCode" || mn = "CompareTo" then dictSet vtImpls (key v) true
        | DClass (_, _, own, _) ->
            for mn, v in own do
                if mn = "Equals" || mn = "GetHashCode" || mn = "CompareTo" then dictSet vtImpls (key v) true
        | _ -> ()
    for d in decls0 do
        match d with
        | DClass (cn, _, _, impls) ->
            for _, ms in impls do (for _, v in ms do dictSet vtImpls (key v) true)
            // any function a class-keyed SLOT can resolve to is vtable-
            // reachable too (abstract-through-class dispatch, the object-
            // expression overrides) — it must keep the uniform signature
            // or the call_indirect type mismatches
            for ifn, mn in vtableSlots do
                (match slotImpl cn ifn mn with
                 | Some v -> dictSet vtImpls (key v) true
                 | None -> ())
        | _ -> ()
    for d in decls do
        match d with
        | DLet (_, v, s, ELam (ps, _)) when (dictTryFind assigned (key v)).IsNone ->
            dictSet st.Funcs (key v) (List.length ps)
            match funSigOf s (List.length ps) with
            | Some sig_ when (dictTryFind vtImpls (key v)).IsNone -> dictSet st.FuncSig (key v) sig_
            | _ -> ()
            // a generic top-level fn takes a hidden witness pointer per quantified
            // type var (in Quantified order); a direct caller prepends them. The
            // witness ABI is a GC-scan concern only — under --linear (no collector)
            // nothing needs it, so FuncWitness stays empty and the whole hidden-
            // param path (decl, emit, call, generic cons) is a no-op there.
            if gc && not (List.isEmpty s.Quantified) && (dictTryFind vtImpls (key v)).IsNone then
                dictSet st.FuncWitness (key v) (s.Quantified |> List.map (fun qv -> qv.Id))
        | DLet (_, v, s, _) ->
            dictSet st.Globals (key v) true
            // a RAW-scalar top-level binding (int/bool/char) stays in its
            // unscanned wasm global — an even int in the SCANNED root table
            // reads as a bogus pointer. Only ref/generic globals take a root
            // slot (they hold heap pointers a moving collection must update).
            if gc && refKindOfTy s.Body <> RKRaw then
                let slot = st.RootNext
                st.RootNext <- slot + 1
                dictSet st.GlobalSlot (key v) slot
                dictSet gcGlobalSlots (gl v) slot
        | DExtern (v, _) -> dictSet st.Externs v.Name true
        | _ -> ()
    // JS interop detection: any Js.* primitive use (EUnknown "js<Upper>…") or
    // a [<JsImport>] extern turns on the "jslin" boundary imports. Runs before
    // rtDeclsLin — imports must precede every declared function.
    jsUsed <- false
    jsxSigs <- dictNew ()
    envSigs <- dictNew ()
    // markers/externs live in decls0 — the reachability filter above keeps
    // only DLets in `decls`
    let jsxMarked = dictNew<string, bool> ()
    for d in decls0 do
        match d with
        | DExport (v, "$jsimport") -> dictSet jsxMarked (key v) true
        | _ -> ()
    let rec jsScan (e : Expr) : unit =
        (match e with
         | EApp (EUnknown n, _) when strLen n > 2 && n.StartsWith "js" && System.Char.IsUpper (charAt n 2) ->
             jsUsed <- true
         | _ -> ())
        match e with
        | ELet (_, _, _, r, b) -> jsScan r; jsScan b
        | ELam (_, b) -> jsScan b
        | EApp (f, args) -> jsScan f; List.iter jsScan args
        | EIf (a, b, c) -> jsScan a; jsScan b; jsScan c
        | EMatch (s, cs) | ETry (s, cs) ->
            jsScan s
            for _, gd, bb in cs do (match gd with Some g -> jsScan g | None -> ()); jsScan bb
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) -> List.iter jsScan xs
        | ERecord (_, fs) -> for _, x in fs do jsScan x
        | ERecordExt (_, bb, fs) -> jsScan bb; (for _, x in fs do jsScan x)
        | EField (r, _, _) -> jsScan r
        | EFieldSet (r, _, _, x) -> jsScan r; jsScan x
        | EWhile (c, b) -> jsScan c; jsScan b
        | EAssign (_, x) -> jsScan x
        | EIndex (_, a, i) -> jsScan a; jsScan i
        | EIndexSet (_, a, i, x) -> jsScan a; jsScan i; jsScan x
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) | ECast (_, a, _) | ETypeTest (_, a) -> jsScan a
        | EArrayCreate (_, a, b) -> jsScan a; jsScan b
        | EIfaceCall (_, _, recv, args) -> jsScan recv; List.iter jsScan args
        | _ -> ()
    for d in decls do
        match d with DLet (_, _, _, e) -> jsScan e | _ -> ()
    let mutable jsxN = 0
    for d in decls0 do
        match d with
        | DExtern (v, sch) when (dictTryFind jsxMarked (key v)).IsSome ->
            // kind derivation mirrors BinDriver's jsx ABI exactly
            let jsKind (t : Type) : string =
                match prune t with
                | TCon ("JsObj", []) -> "e"
                | TCon (("float" | "float32"), []) -> "d"
                | TCon ("string", []) -> "s"
                | TCon ("bool", []) -> "b"
                | TCon ("unit", []) -> "u"
                | _ -> "i"
            let rec peel (t : Type) : string list * string =
                match prune t with
                | TFun (a, b) ->
                    let ps, r = peel b
                    jsKind a :: ps, r
                | r -> [], jsKind r
            let pks, rk = peel sch.Body
            let fnm = "$jsx" + string jsxN
            jsxN <- jsxN + 1
            let nm = v.Name + "#" + String.concat "" pks + ":" + rk
            dictSet jsxSigs (key v) (fnm, nm, pks, rk)
            jsUsed <- true
        | DExtern (v, sch) when
              v.Path <> Fpp.Analysis.Classes.builtinPath
              && not (List.contains v.Name [ "readTextRaw"; "existsRaw"; "listDirRaw"; "canonicalizeRaw"; "preludeSourceRaw" ]) ->
            // a USER extern is a real "env" import (prelude externs are
            // builtins with their own arms; the FILE externs ride WASI)
            let jsKind (t : Type) : string =
                match prune t with
                | TCon ("JsObj", []) -> "e"
                | TCon (("float" | "float32"), []) -> "d"
                | TCon ("string", []) -> "s"
                | TCon ("unit", []) -> "u"
                | _ -> "i"
            let rec peel (t : Type) : string list * string =
                match prune t with
                | TFun (a, b) ->
                    let ps, r = peel b
                    jsKind a :: ps, r
                | r -> [], jsKind r
            let pks, rk = peel sch.Body
            let fnm = "$jsx" + string jsxN
            jsxN <- jsxN + 1
            dictSet envSigs (key v) (fnm, v.Name, pks, rk)
        | _ -> ()
    // GC: reserve a fixed area of root slots for $cbreg (callback and
    // cleanup closures live there, below the shadow stack) — handed out at
    // runtime by $cbnext, recycled through the $cbfree freelist when a
    // cleanup has run
    if gc then
        cbBase <- st.RootNext
        st.RootNext <- st.RootNext + 1024
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
    let decls = decls |> List.map (fun d -> match d with DLet (r, v, s, e) -> DLet (r, v, s, etaExpand st.Funcs st.UnionArity e) | _ -> d)
    // function type per arity used, and the function declarations
    // arity 2 is always present: $cmpv/$hashv dispatch the identity trio
    // (Equals/GetHashCode/CompareTo) through a (self, other) indirect call
    let arities = 2 :: (st.Funcs |> dictPairs |> List.map snd) |> List.distinct
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
        // map the ref-array tid to CID_ARRAY so a dynamically seq-typed array
        // (e.g. `(x.ToArray() :> seq).GetEnumerator()`) is recognised by
        // $isBuiltinSeq at runtime and routed to the built-in array iterator
        // rather than an (absent) IEnumerable vtable row.
        vecAdd st.TidCid (gcArrTid, CID_ARRAY)
        gcFloatTid <- gcTid st "f64" (HDR + 8) FK_STRUCT 0
        gcInt64Tid <- gcTid st "i64" (HDR + 8) FK_STRUCT 0
        // map the scalar-box tids so `:? float` / `:? int64` / `:? string`
        // read their class-ids through $t2c under the reactor — unmapped
        // tids read cid 0 and every scalar type test answered false
        vecAdd st.TidCid (gcStrTid, CID_STRING)
        vecAdd st.TidCid (gcFloatTid, CID_FLOAT)
        vecAdd st.TidCid (gcInt64Tid, CID_INT64)
        gcListTid <- gcTid st "s:2:2:0" (HDR + 8) FK_TAGGED 1
        // map the uniform cons tid to CID_LIST so $isBuiltinSeq recognises it
        // (the FK_STRUCT per-refmap cons variants register their own mapping)
        vecAdd st.TidCid (gcListTid, CID_LIST)
        // the two witness-selected cons shapes ([head@HDR][tail@HDR+4])
        gcConsRawTid <- gcTidRef st "cons$raw" (HDR + 8) [ HDR + 4 ]
        vecAdd st.TidCid (gcConsRawTid, CID_LIST)
        gcConsRefTid <- gcTidRef st "cons$ref" (HDR + 8) [ HDR; HDR + 4 ]
        vecAdd st.TidCid (gcConsRefTid, CID_LIST)
        // the built-in list iterator: [remaining][current], both scanned as
        // tagged words (start=1) so a ref element is rooted and a tagged int skipped
        gcIterTid <- gcTid st "iter" (HDR + 8) FK_TAGGED 1
        // the built-in ARRAY iterator: [array][index]. The array (HDR) is a real
        // pointer the collector must trace+update; the index (HDR+4) is a raw int
        // (NEVER scanned), so an FK_STRUCT with refoffs = [HDR] only. Distinct tid
        // from the list iterator so MoveNext/Current pick the index-based path.
        gcArrIterTid <- gcTidRef st "arriter" (HDR + 8) [ HDR ]
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
            let nw = match dictTryFind st.FuncWitness (key v) with Some ws -> List.length ws | None -> 0
            (match dictTryFind st.FuncSig (key v) with
             | Some (paramTys, retTy) ->
                 let tn = "$ft" + fn v
                 tyFunc m tn ((List.replicate nw "i32") @ (paramTys |> List.map wtyName)) [ wtyName retTy ]
                 declFn m (fn v) tn
             | None ->
                 let a = nw + List.length ps
                 tyFunc m ("$lfn" + string a) (List.replicate a "i32") [ "i32" ]
                 declFn m (fn v) ("$lfn" + string a))
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
    let vtdbg = System.Environment.GetEnvironmentVariable "FPP_VTDBG" = "1"
    // the identity trio, by NAME, from anywhere in the class' own chain. An
    // arity check keeps a same-named member of a different shape out: Equals
    // and CompareTo take (self, other), GetHashCode takes (self) — a unit
    // parameter makes that 2, which the runtime call passes 0 for.
    let ownMemberNamed (cn : string) (mn : string) : VarId option =
        chainOf cn
        |> List.tryPick (fun c ->
            classDecls
            |> List.tryPick (fun (n2, _, own, _) ->
                if n2 <> c then None
                else own |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None)))
    // the identity trio for RECORDS and UNIONS too: `type Map<'k,'v> = ... member
    // x.Equals o` is a DMembers on the union name, and all its cases share the
    // union's class-id, so one row serves them all. Without this a Map compared
    // by its TREE and two equal maps built in different orders came out unequal.
    let fillIdentity (owner : string) (own : (string * VarId) list) =
        match dictTryFind st.ClassId owner with
        | Some cid when st.NSlots > 0 ->
            [ 0, "Equals"; 1, "GetHashCode"; 2, "CompareTo" ]
            |> List.iter (fun (slot, mn) ->
                match own |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None) with
                | Some v when (dictTryFind st.Funcs (key v)) = Some 2 ->
                    vtRows.[cid * st.NSlots + slot] <- tblIdx m (fn v)
                | Some v ->
                    if System.Environment.GetEnvironmentVariable "FPP_VTDBG" = "1" then
                        eprintfn "IDENT %s.%s SKIP arity=%s" owner mn
                            (match dictTryFind st.Funcs (key v) with Some a -> string a | None -> "none")
                | _ ->
                    if System.Environment.GetEnvironmentVariable "FPP_VTDBG" = "1" then
                        eprintfn "IDENT %s.%s absent" owner mn)
        | _ -> ()
    for d in decls0 do
        match d with
        | DMembers (n, own) -> fillIdentity n own
        | _ -> ()
    for cn, _, _, _ in classDecls do
        match dictTryFind st.ClassId cn with
        | Some cid ->
            // the DEFAULTS first: reference equality and identity hash, the
            // semantics a class has unless it says otherwise
            if st.NSlots > 0 then
                vtRows.[cid * st.NSlots + 0] <- tblIdx m "$clseq"
                vtRows.[cid * st.NSlots + 1] <- tblIdx m "$clshash"
            [ 0, "Equals"; 1, "GetHashCode"; 2, "CompareTo" ]
            |> List.iter (fun (slot, mn) ->
                match ownMemberNamed cn mn with
                | Some v when (dictTryFind st.Funcs (key v)) = Some 2 ->
                    vtRows.[cid * st.NSlots + slot] <- tblIdx m (fn v)
                | _ -> ())
            vtableSlots |> List.iteri (fun slot (ifn, mn) ->
                match slotImpl cn ifn mn with
                // only a declared top-level function can go in the table; an
                // impl that never became one (not reachable / not a plain
                // function) leaves the slot 0
                | Some v when (dictTryFind st.Funcs (key v)).IsSome ->
                    (if vtdbg then eprintfn "VT %s cid=%d slot=%d %s.%s -> %s" cn cid slot ifn mn v.Name)
                    vtRows.[cid * st.NSlots + slot] <- tblIdx m (fn v)
                | Some v -> (if vtdbg then eprintfn "VT %s cid=%d slot=%d %s.%s MISS-func %s" cn cid slot ifn mn v.Name)
                | None -> (if vtdbg then eprintfn "VT %s cid=%d slot=%d %s.%s no-impl" cn cid slot ifn mn))
        | None -> (if vtdbg then eprintfn "VT %s NO-CID" cn)
    // intern all string constants FIRST, so the heap starts after them
    for d in decls do
        match d with DLet (_, _, _, e) -> scanConsts st e | _ -> ()
    // the failed-downcast message, interned like any other literal
    (if gc then internStrGc st "\"invalid cast\"" |> ignore else internStr st "\"invalid cast\"" |> ignore)
    // bool prints spell True/False at runtime — intern both up front
    (if gc then internStrGc st "\"True\"" |> ignore else internStr st "\"True\"" |> ignore)
    (if gc then internStrGc st "\"False\"" |> ignore else internStr st "\"False\"" |> ignore)
    // bake the vtable right after the string constants; $hp starts after it
    st.VtBase <- st.ConstNext
    vtBaseConst <- st.VtBase
    vtRootSlot <- st.VtSlot
    vtNSlots <- st.NSlots
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
    if gc then globalI32Mut m "$witnesses" 0
    // callbacks/cleanups (GC): the next free slot in the cbBase root area,
    // and the freelist of recycled one-shot cleanup slots (odd-tagged links
    // threaded through the free slots themselves — odd, so the root scanner
    // skips them)
    if gc then (globalI32Mut m "$cbnext" 0; globalI32Mut m "$cbfree" 0)
    // GC: scratch for stashing an init's result while addressing its root
    // slot. This must NOT be $hp — $lalloc still bump-allocates Memory.alloc
    // and lin_salloc from $hp under GC, and stashing a pointer here pointed
    // the bump heap INTO the live fpprt heap (Buffer data then overwrote
    // neighbouring objects: cap cells read 0 and Reserve span forever,
    // union headers read garbage and exhaustive matches fell through).
    if gc then globalI32Mut m "$gstash" 0
    exportFn m "_start" "$_start"
    if jsUsed then
        exportFn m "jscall" "$jscall"
        exportFn m "lin_salloc" "$lin_salloc"
    // [<Export>]: a declared top-level function exported under its own name
    // (markers live in decls0 — the reachability filter keeps only DLets)
    for d in decls0 do
        match d with
        | DExport (v, nm) when nm <> "$jsimport" && (dictTryFind st.Funcs (key v)).IsSome ->
            exportFn m nm (fn v)
        | _ -> ()
    // runtime bodies
    if gc then (emitSpush m; emitSpop m)
    emitLalloc m; emitStrOfInt m; emitStrOfChar m; emitStrCat m; emitPrints m; emitEprints m; emitPrintRaw m; emitFtoa6 m; emitStreq m
    emitStrStarts m; emitStrEnds m; emitStrFind m; emitStrsub m; emitStrTrim m; emitStrReplace m; emitStrFindChar m; emitStrLastFindChar m; emitStrSplitChar m
    emitStrCase m false; emitStrCase m true; emitStrChars m; emitStrPad m; emitStrTrimChars m true; emitStrTrimChars m false; emitStrInsert m; emitStrRemove2 m
    emitStrCmp m; emitCmpv m; emitHashv m; emitLappend m; emitListIter m; emitAtoi m; emitAtol m; emitReadFile m; emitFexists m
    emitMemsize m; emitMemcopy m; emitFtoaS m; emitLtoa m true; emitLtoa m false
    if jsUsed || gc then emitCbreg m
    if gc then (emitGcdrain m; emitRootswipe m)
    if jsUsed then (emitJscall m; emitLinSalloc m)
    // half-precision widen/narrow — pure i32/f32 arithmetic, shared verbatim
    // with the GC backend (a float16 IS its 16 raw bits in a word). LAST,
    // matching where rtDecls12/rtDeclsHalf declare them: the function and
    // code sections are positional and must agree.
    rtCore12 m
    rtCoreHalf m
    emitAtof m
    emitNoVt m
    emitClsEq m
    emitClsHash m
    emitShowv m
    emitStrv m
    // top-level function bodies — all through LowIR (Core/LowIR.fs); an
    // unsupported node reports a gap through coreToLowE, never a bad module
    for d in decls do
        match d with
        | DLet (_, v, sch, ELam (ps, body)) when (dictTryFind st.Funcs (key v)).IsSome ->
            if not (isNull (System.Environment.GetEnvironmentVariable "FPP_FUNC_DUMP")) then eprintfn "FUNC %s = %s | %s" (fn v) (key v) v.Name
            // a method of a Canon generic class: (class-var id, self byte-offset)
            // for each class type param that survives as a TVar in the receiver
            // type. The witness lives in the instance's trailing slot after its
            // fields (see the ERecord append above).
            let selfWits =
                match (match prune sch.Body with TFun (a, _) -> Some a | _ -> None) with
                | Some recv ->
                    (match prune recv with
                     | TCon (cn, args) when (dictTryFind st.WitnessedClasses cn).IsSome ->
                         let nf = match dictTryFind st.RecFields cn with Some fs -> List.length fs | None -> 0
                         args |> List.mapi (fun j a -> match prune a with TVar vv -> Some (vv.Id, HDR + 4 * nf + 4 * j) | _ -> None) |> List.choose id
                     | _ -> [])
                | None -> []
            // a stamped generic-class member: constant witnesses for its class
            // type params (Link forwards the enclosingSubst it already computes).
            let constWits =
                match (if gc then dictTryFind stampedClassWits (v.Path, v.Offset) else None) with
                | Some pairs ->
                    pairs |> List.map (fun (vid, nm) -> vid, witnessPtrRM st 4 4 (if rawScalarName (layStripGen nm) then 0 else 1))
                | None -> []
            emitFuncLow st m (fn v) false (dictTryFind st.FuncSig (key v)) (match dictTryFind st.FuncWitness (key v) with Some ws -> ws | None -> []) selfWits constWits (ps |> List.map fst) (ps |> List.map (fun (_, s) -> s.Body)) body (fun _ -> ())
        | _ -> ()
    // init bodies — DECLARED before _start and the lambdas, so emitted here
    // too (the function and code sections are positional and must agree)
    for d in decls do
        match d with
        | DLet (_, v, _, _) when (dictTryFind st.Funcs (key v)).IsSome -> ()
        | DLet (_, v, _, rhs) ->
            emitFuncLow st m (gl v) true None [] [] [] [] [] rhs (fun f ->
                // GC: the init's result is on the stack — stash it via the
                // dedicated $gstash global, then store into the root slot
                match (if gc then dictTryFind st.GlobalSlot (key v) else None) with
                | Some slot -> gs f "$gstash"; gg f "$roots"; ic f (4 * slot); ins f "i32.add"; gg f "$gstash"; mem f "i32.store"
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
    for name, (pv, psch), body, caps in vecToList st.Lams do
        st.Captures <- dictNew ()
        caps |> List.iteri (fun i (p, o, _) -> dictSet st.Captures (p + ":" + string o) i)
        emitLambdaLow st m name pv psch body
    // GC: emit $fpreg_all LAST — every shape's tid is known now. Each shape is
    // registered as (tid, size, kind, start, refoffs=0, name=0); `start` is the
    // TAGGED tracer's first-payload word (0 for a no-ref STRUCT box).
    if gc then
        let rf = beginFn m []
        local rf "$t" "i32"
        local rf "$ro" "i32"
        localsDone rf
        // the root table lives in fpprt's static memory: register the whole
        // range (scratch slot 0 + one per constant) up front — the slots read 0
        // (skipped by the scanner) until filled below
        callf rf "$rootsbase"; gs rf "$roots"
        // register the fixed slots (scratch/globals/constants) AND the shadow
        // stack that follows; the shadow pointer starts just past the fixed slots.
        // Must equal FPPRT_WASM_NROOTS in fpprt-wasm-shim.c — the shadow stack has
        // no bounds check, so this range has to cover the deepest recursion the
        // compiler reaches self-hosting (the full-prelude compile needs >>64K).
        ic rf 2097152; callf rf "$rootsreg"
        ic rf (st.RootNext * 4); gs rf "$sp"
        // fill the tid->cid table (raw class-ids, fixed static memory)
        callf rf "$t2cbase"; gs rf "$t2c"
        // value-witness pool: point $witnesses at it and write each interned
        // {size,align,refMask} triple (static metadata the generic ABI passes).
        callf rf "$witnessbase"; gs rf "$witnesses"
        for off, size, align, refMask in vecToList st.WitnessData do
            gg rf "$witnesses"; ic rf off; ins rf "i32.add"; ic rf size; mem rf "i32.store"
            gg rf "$witnesses"; ic rf (off + 4); ins rf "i32.add"; ic rf align; mem rf "i32.store"
            gg rf "$witnesses"; ic rf (off + 8); ins rf "i32.add"; ic rf refMask; mem rf "i32.store"
        for tid, cid in vecToList st.TidCid do
            gg rf "$t2c"; ic rf (4 * tid); ins rf "i32.add"; ic rf cid; mem rf "i32.store"
        // register every shape's fpprt type. A FK_STRUCT shape with a ref-map
        // writes its byte-offsets into the static g_refoffs pool (a compile-time
        // cursor packs them contiguously) and passes (nrefs, &pool[cursor]);
        // everything else passes (start, refoffs=0) — a NULL map with nrefs=0
        // scans nothing, which is exactly an all-scalar tuple/union.
        callf rf "$refoffsbase"; ls rf "$ro"
        if System.Environment.GetEnvironmentVariable "FPP_TID_DUMP" = "1" then
            for k, t in dictPairs st.Tids do eprintfn "TID %d = %s" t k
        let mutable roCur = 0
        for tid, size, kind, start in vecToList st.TidRegs do
            match dictTryFind st.TidRefoffs tid with
            | Some offs when not (List.isEmpty offs) ->
                offs |> List.iteri (fun j off ->
                    lg rf "$ro"; ic rf (roCur + 4 * j); ins rf "i32.add"; ic rf off; mem rf "i32.store")
                ic rf tid; ic rf size; ic rf kind; ic rf start
                lg rf "$ro"; ic rf roCur; ins rf "i32.add"
                ic rf 0
                callf rf "$fpreg"
                roCur <- roCur + 4 * List.length offs
            | _ ->
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
            // tid -> its shape key, for naming a SCALAR ARRAY's element kind
            let keyOfTid = dictNew<int, string> ()
            for k2, t2 in dictPairs st.Tids do dictSet keyOfTid t2 k2
            for tid, size, kind, start in vecToList st.TidRegs do
                let nwords = size / 4
                // ref bitmask (bit w set = word w is a pointer), packed above the
                // 10-bit word count. FK_STRUCT knows its exact ref OFFSETS, so a raw
                // scalar anywhere (a tuple's trailing int) is marked raw; every other
                // kind keeps the old contiguous [start, nwords) ref suffix (a union
                // tag prefix stays raw). Words past 21 don't fit the mask -> raw.
                //
                // A PACKED SCALAR ARRAY cannot ride that encoding at all: its
                // "size" is the ELEMENT width and its length is per-object.
                // Sentinel: nwords = 0x3FF (no real object has 1022 fields) with
                // the element-compare CODE above it — $cmpv's scalar-array
                // branch reads len from the object and compares elements at the
                // right width/signedness (a float array's f64 payload words
                // walked as refs faulted at the double's bit pattern).
                let scalarCode =
                    if kind <> FK_SCALAR_ARRAY then 0
                    else
                        match dictTryFind keyOfTid tid with
                        | Some k2 ->
                            let en = if k2.StartsWith "sa:" then k2.Substring 3 elif k2.StartsWith "pa:" then k2.Substring 3 else k2
                            (match en with
                             | "float" | "double" -> 1
                             | "int64" -> 2
                             | "uint64" -> 3
                             | "int" | "int32" | "nativeint" | "bool" -> 4
                             | "uint32" | "unativeint" -> 5
                             | "int16" -> 6
                             | "uint16" | "str" | "char" -> 7
                             | "byte" -> 8
                             | "sbyte" -> 9
                             | "float32" | "single" -> 10
                             | _ -> 0)
                        | None -> 0
                let info =
                    if scalarCode <> 0 then (scalarCode <<< 10) ||| 0x3FF
                    else
                        let mask =
                            if kind = FK_STRUCT then
                                match dictTryFind st.TidRefoffs tid with
                                | Some offs -> offs |> List.fold (fun m b -> let w = b / 4 in if w < 22 then m ||| (1 <<< w) else m) 0
                                | None -> 0
                            else
                                let mutable m = 0
                                for w in (max 1 start) .. (min (nwords - 1) 21) do m <- m ||| (1 <<< w)
                                m
                        (mask <<< 10) ||| (nwords &&& 0x3FF)
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
        for (k, _) in dictPairs st.Funcs do
            for h in [ "2034791193"; "658953085"; "2143567545"; "1381067340"; "1380175341" ] do
                if string (abs (strHash k)) = h then eprintfn "FNMAP f%s = %s name=%s" h k (match dictTryFind nameOf k with Some n -> n | None -> "?")
    bytes, vecToList st.Errors

// the wasm-linear backend: Core straight to a linear-memory module through the
// shared LowIR. `--lowir` is a retained alias for the same path.
let emitLinear (decls0 : Decl list) : byte[] * string list = emitLinearImpl decls0
let emitLinearLow (decls0 : Decl list) : byte[] * string list = emitLinearImpl decls0

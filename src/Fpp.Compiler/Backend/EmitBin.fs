module Fpp.Backend.EmitBin

open Fpp.Prelude
open Fpp.Backend.WasmBinary

// DIRECT binary emission — the module is built as bytes from the start.
// There is no text form and no assembler: mnemonics are table lookups
// (`opByte`/`gcByte`), names resolve through index dictionaries, labels
// through the block stack. `wasm-tools print` is the debug view.
//
// Index spaces are the part text let us ignore, so they are explicit here:
// - TYPES: the fixed prelude types first, in a fixed order, then generated
//   ones; every reference is a backward index, so no rec groups are needed.
// - FUNCS: imports first, then defined functions in declaration order.
// - `ref.func` in a body is only VALID if the function is declared in a
//   declarative element segment — the wat parser was adding that silently;
//   here `refFunc` records the target and `assemble` emits the segment.
// - DATA: passive segments, indexed in creation order; array.new_data
//   validation requires the DataCount section.

type Mod =
    { /// (offset into the code payload, source path, source offset) — what a
      /// source map is made of. Recorded as code is emitted, resolved to
      /// absolute file offsets once the module is assembled.
      SrcPos : Vec<int * string * int>
      /// struct type name -> its field names, in order. Without these a heap
      /// snapshot shows `field 0`, `field 1`; with them, `X` and `Y`.
      FieldNames : Vec<string * string list>
      /// function index -> its locals' names, so a debugger's scope view says
      /// `x` rather than `var3`
      LocalNames : Vec<int * (int * string) list>
      TypeIdx : Dict<string, int>
      TypeBody : Bytes
      mutable TypeCount : int
      ImportBody : Bytes
      mutable ImportCount : int
      FuncIdx : Dict<string, int>
      FuncSigs : Bytes
      mutable FuncCount : int
      mutable ImportedFuncs : int
      GlobalIdx : Dict<string, int>
      GlobalBody : Bytes
      mutable GlobalCount : int
      ExportBody : Bytes
      mutable ExportCount : int
      CodeBody : Bytes
      mutable CodeCount : int
      DataIdx : Dict<string, int>
      DataBody : Bytes
      mutable DataCount : int
      /// the CLOSURE CODE TABLE: $u1 functions callable through a $clo's
      /// i32 index via call_indirect — funcrefs never enter the GC heap
      /// (wasmtime interns them per store, with SipHash, and that was ~10%%
      /// of a self-compile)
      TableIdx : Dict<string, int>
      TableOrder : Vec<string>
      /// funcs referenced first-class; the declarative elem segment
      Declared : Dict<string, bool>
      DeclaredOrder : Vec<string>
      /// when Some (module, field, min, max): memory is IMPORTED (the GC
      /// backend shares fpprt's linear memory) instead of defined+exported,
      /// so assembleWith emits an import entry and skips the memory section
      mutable MemImport : (string * string * int * int) option }

let modNew () : Mod =
    { SrcPos = vecNew (); FieldNames = vecNew (); LocalNames = vecNew (); TypeIdx = dictNew (); TypeBody = bytesNew (); TypeCount = 0
      ImportBody = bytesNew (); ImportCount = 0
      FuncIdx = dictNew (); FuncSigs = bytesNew (); FuncCount = 0; ImportedFuncs = 0
      GlobalIdx = dictNew (); GlobalBody = bytesNew (); GlobalCount = 0
      ExportBody = bytesNew (); ExportCount = 0
      CodeBody = bytesNew (); CodeCount = 0
      DataIdx = dictNew (); DataBody = bytesNew (); DataCount = 0
      Declared = dictNew (); DeclaredOrder = vecNew ()
      TableIdx = dictNew (); TableOrder = vecNew (); MemImport = None }

let tyIdx (m : Mod) (name : string) : int =
    match dictTryFind m.TypeIdx name with
    | Some i -> i
    | None -> -1

let private tyAdd (m : Mod) (name : string) : unit =
    dictSet m.TypeIdx name m.TypeCount
    m.TypeCount <- m.TypeCount + 1

// ---- storage/value type writers, by NAME ----------------------------------
// "i32" "anyref" "(ref $t)" style names are what call sites know; a concrete
// $name resolves through the type table.

let emitVal (m : Mod) (b : Bytes) (t : string) : unit =
    if t = "(ref extern)" then emitRefAbs b false "extern"
    elif strLen t > 0 && charAt t 0 = '$' then emitRefType b true (tyIdx m t)
    else
        let v = valByte t
        emitByte b v

/// (ref $t) non-null
let tyFunc (m : Mod) (name : string) (ps : string list) (rs : string list) : unit =
    emitFuncTypeHead m.TypeBody
    emitU32 m.TypeBody (List.length ps)
    for p in ps do emitVal m m.TypeBody p
    emitU32 m.TypeBody (List.length rs)
    for r in rs do emitVal m m.TypeBody r
    tyAdd m name

/// one struct field: mutability + storage ("i8"/"i16" allowed)
type FieldT = { FMut : bool; FTy : string; FRefNullOf : string; FRefOf : string }
let fld (mut : bool) (ty : string) : FieldT = { FMut = mut; FTy = ty; FRefNullOf = ""; FRefOf = "" }
let fldRef (mut : bool) (name : string) : FieldT = { FMut = mut; FTy = ""; FRefNullOf = ""; FRefOf = name }
let private emitFieldT (m : Mod) (b : Bytes) (f : FieldT) : unit =
    if f.FRefOf <> "" then emitRefType b false (tyIdx m f.FRefOf)
    elif f.FRefNullOf <> "" then emitRefType b true (tyIdx m f.FRefNullOf)
    else emitByte b (valByte f.FTy)
    emitByte b (if f.FMut then 1 else 0)

/// (type $name (struct fields...)), optionally (sub $base ...) / open (sub ...)
let tyStructSub (m : Mod) (name : string) (base_ : string) (openSub : bool) (fs : FieldT list) : unit =
    if base_ <> "" then emitSubHead m.TypeBody (tyIdx m base_)
    elif openSub then
        emitByte m.TypeBody 0x50
        emitU32 m.TypeBody 0
    emitStructHead m.TypeBody
    emitU32 m.TypeBody (List.length fs)
    for f in fs do emitFieldT m m.TypeBody f
    tyAdd m name

let tyStruct (m : Mod) (name : string) (fs : FieldT list) : unit =
    tyStructSub m name "" false fs

/// name a struct's fields, for the debugger and for heap snapshots
let tyArray (m : Mod) (name : string) (elem : string) : unit =
    emitArrayHead m.TypeBody
    emitFieldT m m.TypeBody (fld true elem)
    tyAdd m name

/// (type $name (sub (array (mut ty)))) — an OPEN subtype: same shape as a
/// final array but a DISTINCT type, so ref.test can tell them apart
let tyArrayOpen (m : Mod) (name : string) (elem : string) : unit =
    emitByte m.TypeBody 0x50
    emitU32 m.TypeBody 0
    emitArrayHead m.TypeBody
    emitFieldT m m.TypeBody (fld true elem)
    tyAdd m name

/// (type $name (array funcref)) — immutable funcref array (vtables)
let tyArrayFuncref (m : Mod) (name : string) : unit =
    emitArrayHead m.TypeBody
    emitByte m.TypeBody (valByte "funcref")
    emitByte m.TypeBody 0
    tyAdd m name

// ---- functions -------------------------------------------------------------

/// import "mod" "field" with an anonymous func type (params/results by name)
let importFn (m : Mod) (module_ : string) (field : string) (fname : string)
             (ps : string list) (rs : string list) : unit =
    // the import's type goes in the type section like any other
    let tn = "$imp" + string m.ImportCount
    tyFunc m tn ps rs
    emitVec m.ImportBody (stringBytes module_)
    emitVec m.ImportBody (stringBytes field)
    emitByte m.ImportBody 0x00
    emitU32 m.ImportBody (tyIdx m tn)
    m.ImportCount <- m.ImportCount + 1
    dictSet m.FuncIdx fname m.FuncCount
    m.FuncCount <- m.FuncCount + 1
    m.ImportedFuncs <- m.ImportedFuncs + 1

/// declare a function's index + signature type (body comes via beginFn/endFn,
/// which must run in the SAME order as declaration)
let declFn (m : Mod) (fname : string) (tyName : string) : unit =
    dictSet m.FuncIdx fname m.FuncCount
    m.FuncCount <- m.FuncCount + 1
    emitU32 m.FuncSigs (tyIdx m tyName)

let funcIdx (m : Mod) (fname : string) : int =
    match dictTryFind m.FuncIdx fname with
    | Some i -> i
    | None -> -1

/// register a $u1 function in the closure code table, returning its index
let tblIdx (m : Mod) (fname : string) : int =
    match dictTryFind m.TableIdx fname with
    | Some i -> i
    | None ->
        let i = vecLen m.TableOrder
        dictSet m.TableIdx fname i
        vecAdd m.TableOrder fname
        i

// ---- function bodies -------------------------------------------------------

type Fn =
    { /// local index -> the name it was WRITTEN with. Display only: LocalIdx
      /// stays the key, so a debugger name can never repoint a read.
      SrcNames : Dict<int, string>
      M : Mod
      B : Bytes
      LocalIdx : Dict<string, int>
      /// local valtypes in order, AFTER the params
      LocalTys : Vec<string>
      mutable NParams : int
      Labels : Labels
      /// where this body's size patch started
      mutable PatchAt : int
      /// >= 0: REPLAY mode — `local` maps onto pre-declared slots in call
      /// order instead of growing the vector (the two-pass body emission)
      mutable Replay : int
      /// the box/unbox cancellation peephole: the last (and the one before)
      /// box-or-unbox emission, as (op, startOffset, endOffset). Validity is
      /// positional — the entry only counts if NOTHING was emitted since
      /// (Count = endOffset), so no other emitter needs to invalidate it.
      mutable PeepLast : (string * int * int) option
      mutable PeepPrev : (string * int * int) option
      /// span of a just-emitted boxed-zero push (`i32.const 0; ref.i31`),
      /// valid only while UnitEnd = B.Count: a statement-position drop
      /// erases the push instead of materializing a value nobody reads
      mutable UnitAt : int
      mutable UnitEnd : int }

/// open a body: params get indices 0.., locals follow as they are created
let beginFn (m : Mod) (paramNames : string list) : Fn =
    let f = { SrcNames = dictNew (); M = m; B = m.CodeBody; LocalIdx = dictNew (); LocalTys = vecNew ()
              NParams = List.length paramNames; Labels = labelsNew (); PatchAt = 0; Replay = -1
              PeepLast = None; PeepPrev = None; UnitAt = -1; UnitEnd = -1 }
    f.PatchAt <- beginPatch m.CodeBody
    let mutable i = 0
    for p in paramNames do
        dictSet f.LocalIdx p i
        i <- i + 1
    f

/// a fresh named local of a given valtype name
let local (f : Fn) (name : string) (ty : string) : unit =
    // A local must never take a name a PARAMETER already holds: the name is
    // the key, so rebinding it would silently repoint every read of that
    // parameter at this slot. (It cost the HashMap tests: a prelude function
    // with a parameter `h` met an emitter local `$h`.) Emitter-internal names
    // are free to be reused; parameter names are not.
    let name =
        match dictTryFind f.LocalIdx name with
        | Some i when i < f.NParams -> name + "'"
        | _ -> name
    if f.Replay >= 0 then
        dictSet f.LocalIdx name (f.NParams + f.Replay)
        f.Replay <- f.Replay + 1
    else
        dictSet f.LocalIdx name (f.NParams + vecLen f.LocalTys)
        vecAdd f.LocalTys ty

/// a fresh uniquely-named local — the counter advances in BOTH the scratch
/// pass and the replay pass, so names agree across the two
let localIdx (f : Fn) (name : string) : int =
    match dictTryFind f.LocalIdx name with
    | Some i -> i
    | None -> failwith ("unknown local " + name + " (a -1 here became emitU32's negative-index failure, nameless)")

/// close the body: the locals vector is PREPENDED logically — since the size
/// patch wraps everything, we emitted instructions into a scratch? No: we
/// declare locals FIRST via `local` before any instruction, then call
/// `localsDone`, then instructions, then `endFn`.
let localsDone (f : Fn) : unit =
    // group consecutive same-typed locals
    let n = vecLen f.LocalTys
    let groups = vecNew<int * string> ()
    let mutable i = 0
    while i < n do
        let t = vecGet f.LocalTys i
        let mutable j = i + 1
        while j < n && vecGet f.LocalTys j = t do j <- j + 1
        vecAdd groups (j - i, t)
        i <- j
    emitU32 f.B (vecLen groups)
    for c, t in vecToList groups do
        emitU32 f.B c
        emitVal f.M f.B t

let endFn (f : Fn) : unit =
    emitByte f.B opEnd
    endPatch f.B f.PatchAt
    // this function's index, and what its locals are called
    let idx = f.M.ImportedFuncs + f.M.CodeCount
    let names =
        dictPairs f.LocalIdx
        |> List.map (fun (n, i) -> i, (if n.StartsWith "$" then n.Substring 1 else n))
        // a name the source used beats a generated one
        |> List.map (fun (i, n) ->
            match dictTryFind f.SrcNames i with
            | Some src -> i, src
            | None -> i, n)
        // one name per slot, and SHADOWED bindings stay distinguishable: two
        // `x`s in one function are two slots, and a reader must be able to tell
        // which is which
        |> List.sortBy fst
        |> List.fold
            (fun acc (i, n) ->
                match acc with
                | (j, _) :: _ when j = i -> acc
                | _ ->
                    let taken = acc |> List.filter (fun (_, m) -> m = n || m.StartsWith (n + "'"))
                    let n2 = if List.isEmpty taken then n else n + String.replicate (List.length taken) "'"
                    (i, n2) :: acc)
            []
        |> List.rev
    if not (List.isEmpty names) then vecAdd f.M.LocalNames (idx, names)
    f.M.CodeCount <- f.M.CodeCount + 1

// ---- instructions ----------------------------------------------------------

let ins (f : Fn) (name : string) : unit = emitByte f.B (opByte name)
let gci (f : Fn) (name : string) : unit =
    emitByte f.B opGcPrefix
    emitU32 f.B (gcByte name)
/// GC op with one type immediate: struct.new $t, array.get $t, ref.cast...
let gcT (f : Fn) (name : string) (tyName : string) : unit =
    let at = f.B.Count
    gci f name
    (match name with
     | "ref.test" | "ref.cast" -> emitS32 f.B (tyIdx f.M tyName)
     | "ref.test_null" | "ref.cast_null" -> emitS32 f.B (tyIdx f.M tyName)
     | _ -> emitU32 f.B (tyIdx f.M tyName))
    // a literal box is a peephole producer: `$tof` right after cancels it
    if name = "struct.new" && (tyName = "$boxf" || tyName = "$boxs" || tyName = "$boxl") then
        f.PeepPrev <- f.PeepLast
        f.PeepLast <- Some ("new:" + tyName, at, f.B.Count)
/// struct.get/set $t IDX
let gcTF (f : Fn) (name : string) (tyName : string) (fieldIdx : int) : unit =
    gci f name
    emitU32 f.B (tyIdx f.M tyName)
    emitU32 f.B fieldIdx
/// array.new_fixed $t N
let arrNewData (f : Fn) (tyName : string) (dataName : string) : unit =
    gci f "array.new_data"
    emitU32 f.B (tyIdx f.M tyName)
    emitU32 f.B (dictTryFind f.M.DataIdx dataName).Value
/// array.copy $dst $src
let ic (f : Fn) (n : int) : unit =
    emitByte f.B opI32Const
    emitS32 f.B n
let lc (f : Fn) (n : int64) : unit =
    emitByte f.B opI64Const
    emitS64 f.B n
let fc (f : Fn) (bits : int64) : unit =
    emitByte f.B opF64Const
    emitF64Bits f.B bits
let sc (f : Fn) (bits : int) : unit =
    emitByte f.B opF32Const
    emitF32Bits f.B bits

let lg (f : Fn) (name : string) : unit =
    emitByte f.B opLocalGet
    emitU32 f.B (localIdx f name)
let ls (f : Fn) (name : string) : unit =
    emitByte f.B opLocalSet
    emitU32 f.B (localIdx f name)
let gg (f : Fn) (name : string) : unit =
    emitByte f.B opGlobalGet
    emitU32 f.B (dictTryFind f.M.GlobalIdx name).Value
let gs (f : Fn) (name : string) : unit =
    emitByte f.B opGlobalSet
    emitU32 f.B (dictTryFind f.M.GlobalIdx name).Value

/// which box producer a given unbox call cancels against
let private peepPairOf (unboxName : string) : string list =
    match unboxName with
    | "$toi" -> [ "$ofi"; "ref.i31" ]
    | "$tof" -> [ "$off"; "new:$boxf" ]
    | "$tos" -> [ "$oss"; "new:$boxs" ]
    | "$tol" -> [ "$ofl"; "new:$boxl" ]
    | "$ofi" -> [ "$toi" ]
    | "$off" -> [ "$tof" ]
    | "$oss" -> [ "$tos" ]
    | "$ofl" -> [ "$tol" ]
    | _ -> []

let private isPeepName (name : string) =
    match name with
    | "$toi" | "$tof" | "$tos" | "$tol" | "$ofi" | "$off" | "$oss" | "$ofl" -> true
    | _ -> false

let callf (f : Fn) (name : string) : unit =
    // the peephole: box immediately followed by its matching unbox (either
    // direction) is the identity on the value — drop BOTH. Adjacency in the
    // instruction stream means the second consumes exactly the first's
    // result, so this needs no syntactic nesting.
    let cancels =
        match f.PeepLast with
        | Some (op, at, endAt) when endAt = f.B.Count -> List.contains op (peepPairOf name)
        | _ -> false
    if cancels then
        let _, at, _ = f.PeepLast.Value
        f.B.Count <- at
        f.PeepLast <- (match f.PeepPrev with
                       | Some (_, _, pEnd) when pEnd = f.B.Count -> f.PeepPrev
                       | _ -> None)
        f.PeepPrev <- None
    else
        let at = f.B.Count
        emitByte f.B opCall
        emitU32 f.B (funcIdx f.M name)
        if isPeepName name then
            f.PeepPrev <- f.PeepLast
            f.PeepLast <- Some (name, at, f.B.Count)
let retCall (f : Fn) (name : string) : unit =
    // a tail call REPLACES this frame: drop it before handing over, or a
    // tail-recursive loop would climb the shadow stack forever
    if (dictTryFind f.M.GlobalIdx "$dbgDepth").IsSome then
        gg f "$dbgDepth"
        emitByte f.B opI32Const
        emitS32 f.B -1
        ins f "i32.add"
        gs f "$dbgDepth"
    emitByte f.B opReturnCall
    emitU32 f.B (funcIdx f.M name)
let callRef (f : Fn) (tyName : string) : unit =
    emitByte f.B opCallRef
    emitU32 f.B (tyIdx f.M tyName)
let callIndirect (f : Fn) (tyName : string) : unit =
    emitByte f.B 0x11
    emitU32 f.B (tyIdx f.M tyName)
    emitU32 f.B 0
/// ref.func — and record the target for the declarative elem segment
let rf (f : Fn) (name : string) : unit =
    emitByte f.B (opByte "ref.func")
    emitU32 f.B (funcIdx f.M name)
    if not (dictTryFind f.M.Declared name).IsSome then
        dictSet f.M.Declared name true
        vecAdd f.M.DeclaredOrder name

/// ref.null with an abstract heap ("any", "func", ...)
let refNull (f : Fn) (heap : string) : unit =
    emitByte f.B (opByte "ref.null")
    emitByte f.B (heapByte heap)
/// ref.test/cast against an ABSTRACT heap (ref i31 etc)
let gcAbs (f : Fn) (name : string) (heap : string) : unit =
    gci f name
    emitS32 f.B (heapByte heap - 0x80)  // abs heap types are NEGATIVE s33
let i31get (f : Fn) : unit = gci f "i31.get_s"
/// anyref -> externref: a value CROSSING INTO JavaScript
let refI31 (f : Fn) : unit =
    let at = f.B.Count
    gci f "ref.i31"
    // an i31 wrap is a peephole producer: `$toi` right after reads it back
    f.PeepPrev <- f.PeepLast
    f.PeepLast <- Some ("ref.i31", at, f.B.Count)

/// the boxed zero most statements answer with — recorded so that a
/// statement-position `dropU` can erase it, while `$toi` still cancels
/// against the recorded ref.i31 the ordinary way
let dropU (f : Fn) : unit =
    if f.UnitEnd = f.B.Count && f.UnitAt >= 0 then
        f.B.Count <- f.UnitAt
        f.UnitEnd <- -1
        f.UnitAt <- -1
        // the peephole entries pointed into the erased bytes; positional
        // validity already rejects them, but stale spans equal to the new
        // Count could lie, so clear outright
        f.PeepLast <- None
        f.PeepPrev <- None
    else emitByte f.B 0x1A

// blocks: named labels resolve to depths at branch sites
let blockI (f : Fn) (label : string) : unit =
    emitByte f.B opBlock
    emitBlockTypeVal f.B (valByte "i32")
    pushLabel f.Labels label
let blockE (f : Fn) (label : string) : unit =
    emitByte f.B opBlock
    emitBlockTypeEmpty f.B
    pushLabel f.Labels label
let loopE (f : Fn) (label : string) : unit =
    emitByte f.B opLoop
    emitBlockTypeEmpty f.B
    pushLabel f.Labels label
let ifE (f : Fn) : unit =
    emitByte f.B opIf
    emitBlockTypeEmpty f.B
    pushLabel f.Labels ""
let ifV (f : Fn) (ty : string) : unit =
    emitByte f.B opIf
    emitBlockTypeVal f.B (valByte ty)
    pushLabel f.Labels ""
let elseB (f : Fn) : unit = emitByte f.B opElse
let endB (f : Fn) : unit =
    emitByte f.B opEnd
    popLabel f.Labels
let br (f : Fn) (label : string) : unit =
    emitByte f.B opBr
    emitU32 f.B (labelDepth f.Labels label)
let brIf (f : Fn) (label : string) : unit =
    emitByte f.B opBrIf
    emitU32 f.B (labelDepth f.Labels label)
let ret (f : Fn) : unit = emitByte f.B opReturn

/// memory op with natural alignment
let mem (f : Fn) (name : string) : unit =
    emitByte f.B (memByte name)
    let al =
        match name with
        | "i32.store8" | "i32.load8_u" | "i32.load8_s" -> 0
        | "i32.store16" | "i32.load16_u" | "i32.load16_s" -> 1
        | "i32.load" | "i32.store" | "f32.store" | "f32.load" -> 2
        | _ -> 3
    emitU32 f.B al
    emitU32 f.B 0

/// memory op carrying a CONSTANT displacement in its memarg instead of an
/// `i32.const off; i32.add` ahead of it. Every field read of an inline layout
/// has one, so this is two instructions saved per access. The offset is
/// unsigned in the encoding — a negative one must stay explicit.
let memOff (f : Fn) (name : string) (off : int) : unit =
    emitByte f.B (memByte name)
    let al =
        match name with
        | "i32.store8" | "i32.load8_u" | "i32.load8_s" -> 0
        | "i32.store16" | "i32.load16_u" | "i32.load16_s" -> 1
        | "i32.load" | "i32.store" | "f32.store" | "f32.load" -> 2
        | _ -> 3
    emitU32 f.B al
    emitU32 f.B off

/// memory.size, in pages
let memSizeIns (f : Fn) : unit =
    emitByte f.B 0x3F
    emitByte f.B 0

/// memory.grow by the pages on the stack; leaves the old size (or -1)
let memGrowIns (f : Fn) : unit =
    emitByte f.B 0x40
    emitByte f.B 0

/// memory.fill dst byte len — one instruction for a bulk zero
let memFill (f : Fn) : unit =
    emitByte f.B 0xFC
    emitU32 f.B 0x0B
    emitByte f.B 0

/// memory.copy dst src len — one instruction, the blit the serializer rides on
let memCopy (f : Fn) : unit =
    emitByte f.B 0xFC
    emitU32 f.B 0x0A
    emitByte f.B 0
    emitByte f.B 0

// ---- globals / exports / data ----------------------------------------------

/// (global $name (mut i32) (i32.const init))
let globalAnyref (m : Mod) (name : string) : unit =
    dictSet m.GlobalIdx name m.GlobalCount
    m.GlobalCount <- m.GlobalCount + 1
    emitByte m.GlobalBody (valByte "anyref")
    emitByte m.GlobalBody 1
    emitByte m.GlobalBody (opByte "ref.null")
    emitByte m.GlobalBody (heapByte "any")
    emitByte m.GlobalBody opEnd

let exportFn (m : Mod) (name : string) (fname : string) : unit =
    emitVec m.ExportBody (stringBytes name)
    emitByte m.ExportBody 0x00
    emitU32 m.ExportBody (funcIdx m fname)
    m.ExportCount <- m.ExportCount + 1

let exportMem (m : Mod) (name : string) : unit =
    emitVec m.ExportBody (stringBytes name)
    emitByte m.ExportBody 0x02
    emitU32 m.ExportBody 0
    m.ExportCount <- m.ExportCount + 1

/// IMPORT memory `module.field` (min/max pages) as memory 0. The GC backend
/// shares fpprt's linear memory this way; assembleWith then skips defining a
/// memory of its own. Wired to fpprt's export by wasm-merge at link time.
let importMem (m : Mod) (module_ : string) (field : string) (mn : int) (mx : int) : unit =
    emitVec m.ImportBody (stringBytes module_)
    emitVec m.ImportBody (stringBytes field)
    emitByte m.ImportBody 0x02      // memory import
    emitByte m.ImportBody 0x01      // limits: has max
    emitU32 m.ImportBody mn
    emitU32 m.ImportBody mx
    m.ImportCount <- m.ImportCount + 1
    m.MemImport <- Some (module_, field, mn, mx)

/// a passive data segment
let dataSeg (m : Mod) (name : string) (bytes : byte[]) : unit =
    dictSet m.DataIdx name m.DataCount
    m.DataCount <- m.DataCount + 1
    emitByte m.DataBody 1
    emitVec m.DataBody bytes

/// an ACTIVE data segment: `bytes` land at `offset` in memory 0 at
/// instantiation. The linear backend bakes its string constants this way.
let activeData (m : Mod) (offset : int) (bytes : byte[]) : unit =
    if bytes.Length > 0 then
        m.DataCount <- m.DataCount + 1
        emitByte m.DataBody 0            // mode 0: active, memory 0
        emitByte m.DataBody opI32Const
        emitS32 m.DataBody offset
        emitByte m.DataBody opEnd
        emitVec m.DataBody bytes

/// Record what a local was called in the source. Display only — it changes
/// what a debugger shows, never which slot anything reads.
let mutable lastCodeStart = 0

let assembleWith (m : Mod) (memPages : int) (hasTag : bool) (mapUrl : string) : byte[] =
    let out = bytesNew ()
    for v in [ 0x00; 0x61; 0x73; 0x6D; 0x01; 0x00; 0x00; 0x00 ] do emitByte out v
    emitSection out 1 (fun b ->
        emitU32 b m.TypeCount
        emitBytes b (bytesToArray m.TypeBody))
    if m.ImportCount > 0 then
        emitSection out 2 (fun b ->
            emitU32 b m.ImportCount
            emitBytes b (bytesToArray m.ImportBody))
    emitSection out 3 (fun b ->
        emitU32 b (m.FuncCount - m.ImportedFuncs)
        emitBytes b (bytesToArray m.FuncSigs))
    // table 0 always exists: applyc's call_indirect names it even when no
    // closure was ever built
    emitSection out 4 (fun b ->
        emitU32 b 1
        emitByte b (valByte "funcref")
        emitByte b 1
        emitU32 b (vecLen m.TableOrder)
        emitU32 b (vecLen m.TableOrder))
    // memory section: skipped when memory is imported (GC backend shares
    // fpprt's memory — it arrives through the import section instead)
    if m.MemImport.IsNone then
        emitSection out 5 (fun b ->
            emitU32 b 1
            emitByte b 0
            emitU32 b memPages)
    if hasTag then
        emitSection out 13 (fun b ->
            emitU32 b 1
            emitByte b 0
            emitU32 b (tyIdx m "$exntag"))
    emitSection out 6 (fun b ->
        emitU32 b m.GlobalCount
        emitBytes b (bytesToArray m.GlobalBody))
    emitSection out 7 (fun b ->
        emitU32 b m.ExportCount
        emitBytes b (bytesToArray m.ExportBody))
    // elem segments: the ACTIVE closure-code table, then the declarative
    // segment for every remaining ref.func target
    let segs =
        (if vecLen m.TableOrder > 0 then 1 else 0)
        + (if vecLen m.DeclaredOrder > 0 then 1 else 0)
    if segs > 0 then
        emitSection out 9 (fun b ->
            emitU32 b segs
            if vecLen m.TableOrder > 0 then
                emitByte b 0          // active, table 0, funcidx list
                emitByte b 0x41       // i32.const
                emitU32 b 0
                emitByte b 0x0B       // end
                emitU32 b (vecLen m.TableOrder)
                for n in vecToList m.TableOrder do
                    emitU32 b (funcIdx m n)
            if vecLen m.DeclaredOrder > 0 then
                emitByte b 3          // declarative, funcidx list
                emitByte b 0x00       // elemkind: func
                emitU32 b (vecLen m.DeclaredOrder)
                for n in vecToList m.DeclaredOrder do
                    emitU32 b (funcIdx m n))
    if m.DataCount > 0 then
        emitSection out 12 (fun b -> emitU32 b m.DataCount)
    emitSection out 10 (fun b ->
        emitU32 b m.CodeCount
        // where the code payload starts in the FILE: a source map's columns are
        // absolute byte offsets, so every recorded position shifts by this
        lastCodeStart <- b.Count
        emitBytes b (bytesToArray m.CodeBody))
    if m.DataCount > 0 then
        emitSection out 11 (fun b ->
            emitU32 b m.DataCount
            emitBytes b (bytesToArray m.DataBody))
    // sourceMappingURL (custom, id 0): what makes a browser debugger show the
    // .fpp files instead of wasm. Only when asked for — it changes the bytes,
    // and the byte fixpoint compares them.
    if mapUrl <> "" then
        emitSection out 0 (fun b ->
            emitVec b (stringBytes "sourceMappingURL")
            emitVec b (stringBytes mapUrl))
    // name section (custom, id 0): function names, so a trap backtrace or a
    // fixpoint divergence is diagnosed by NAME rather than raw byte offset
    emitSection out 0 (fun b ->
        emitVec b (stringBytes "name")
        let names =
            dictPairs m.FuncIdx
            |> List.sortBy snd
        let sub = bytesNew ()
        emitU32 sub (List.length names)
        for n, i in names do
            emitU32 sub i
            let n = if n.StartsWith "$" then n.Substring 1 else n
            emitVec sub (stringBytes n)
        emitByte b 1
        emitU32 b sub.Count
        emitBytes b (bytesToArray sub)
        // type names (subsection 4): representation assertions and dumps
        // read `$parr_i`, not a bare index
        let tnames =
            dictPairs m.TypeIdx
            |> List.sortBy snd
        let tsub = bytesNew ()
        emitU32 tsub (List.length tnames)
        for n, i in tnames do
            emitU32 tsub i
            let n = if n.StartsWith "$" then n.Substring 1 else n
            emitVec tsub (stringBytes n)
        emitByte b 4
        emitU32 b tsub.Count
        emitBytes b (bytesToArray tsub)
        // local names (subsection 2): a debugger's scope view reads these.
        // DEBUG ONLY — names cost a third of the module, which nobody should
        // pay to ship. `mapUrl` is the switch: a build that wants a source map
        // wants names with it.
        let locs =
            if mapUrl = "" then []
            else vecToList m.LocalNames |> List.filter (fun (_, ns) -> not (List.isEmpty ns))
        if not (List.isEmpty locs) then
            let lsub = bytesNew ()
            emitU32 lsub (List.length locs)
            for fi, ns in locs do
                emitU32 lsub fi
                emitU32 lsub (List.length ns)
                for li, n in ns do
                    emitU32 lsub li
                    emitVec lsub (stringBytes n)
            emitByte b 2
            emitU32 b lsub.Count
            emitBytes b (bytesToArray lsub)
        // field names (subsection 10): a heap snapshot shows `X` instead of
        // `field 0`, which is the difference between reading a snapshot and
        // guessing at it
        let flds =
            if mapUrl = "" then []
            else
                vecToList m.FieldNames
                |> List.filter (fun (t, ns) -> tyIdx m t >= 0 && not (List.isEmpty ns))
        if not (List.isEmpty flds) then
            let fsub = bytesNew ()
            emitU32 fsub (List.length flds)
            for t, ns in flds do
                emitU32 fsub (tyIdx m t)
                emitU32 fsub (List.length ns)
                for i, n in List.indexed ns do
                    emitU32 fsub i
                    emitVec fsub (stringBytes n)
            emitByte b 10
            emitU32 b fsub.Count
            emitBytes b (bytesToArray fsub))
    bytesToArray out

// ---- the runtime, transliterated ------------------------------------------
// The hand-written wat blob moves here function by function, as direct
// Fn-API emission. Each is checked against the text original when ported;
// the SDK test executes them.

/// declare the runtime's function types once
let rtTypes (m : Mod) : unit =
    tyFunc m "$rt_i2v" [ "i32" ] []
    tyFunc m "$rt_i2i" [ "i32" ] [ "i32" ]
    tyFunc m "$rt_i2a" [ "i32" ] [ "anyref" ]
    tyFunc m "$rt_s2v" [ "$str" ] []

/// the print/itoa slice — enough to see a number on stdout
let rtCore (m : Mod) : unit =
    // bodies must come in declFn order
    // $putc
    let f = beginFn m [ "$c" ]
    localsDone f
    ic f 64
    lg f "$c"
    mem f "i32.store8"
    ic f 0
    ic f 64
    mem f "i32.store"
    ic f 4
    ic f 1
    mem f "i32.store"
    ic f 1
    ic f 0
    ic f 1
    ic f 8
    callf f "$fd_write"
    ins f "drop"
    endFn f
    // $printi
    let f = beginFn m [ "$n" ]
    local f "$m" "i32"
    localsDone f
    lg f "$n"
    ic f 0
    ins f "i32.lt_s"
    ifE f
    ic f 45
    callf f "$putc"
    ic f 0
    lg f "$n"
    ins f "i32.sub"
    ls f "$n"
    endB f
    // UNSIGNED from here on. `0 - min` wraps back to min, which is still
    // negative, so a signed remainder gave -8 and printed "-(" for
    // Int32.MinValue; unsigned, the same bit pattern IS the magnitude, and
    // for every other value the two agree.
    lg f "$n"
    ic f 10
    ins f "i32.div_u"
    ls f "$m"
    lg f "$m"
    ic f 0
    ins f "i32.gt_u"
    ifE f
    lg f "$m"
    callf f "$printi"
    endB f
    ic f 48
    lg f "$n"
    ic f 10
    ins f "i32.rem_u"
    ins f "i32.add"
    callf f "$putc"
    endFn f
    // $ndigits
    let f = beginFn m [ "$n" ]
    local f "$c" "i32"
    local f "$m" "i32"
    localsDone f
    lg f "$n"
    ls f "$m"
    lg f "$m"
    ic f 0
    ins f "i32.lt_s"
    ifE f
    ic f 1
    ls f "$c"
    ic f 0
    lg f "$m"
    ins f "i32.sub"
    ls f "$m"
    elseB f
    ic f 0
    ls f "$c"
    endB f
    lg f "$c"
    ic f 1
    ins f "i32.add"
    ls f "$c"
    blockE f "$done"
    loopE f "$go"
    lg f "$m"
    ic f 10
    ins f "i32.div_u"
    ls f "$m"
    lg f "$m"
    ins f "i32.eqz"
    brIf f "$done"
    lg f "$c"
    ic f 1
    ins f "i32.add"
    ls f "$c"
    br f "$go"
    endB f
    endB f
    lg f "$c"
    endFn f
    // $itoa
    let f = beginFn m [ "$n" ]
    local f "$len" "i32"
    local f "$s" "$str"
    local f "$i" "i32"
    local f "$m" "i32"
    local f "$neg" "i32"
    localsDone f
    lg f "$n"
    callf f "$ndigits"
    ls f "$len"
    ic f 48
    lg f "$len"
    gcT f "array.new" "$str"
    ls f "$s"
    lg f "$n"
    ls f "$m"
    lg f "$m"
    ic f 0
    ins f "i32.lt_s"
    ifE f
    ic f 1
    ls f "$neg"
    ic f 0
    lg f "$m"
    ins f "i32.sub"
    ls f "$m"
    lg f "$s"
    ic f 0
    ic f 45
    gcT f "array.set" "$str"
    endB f
    lg f "$len"
    ic f 1
    ins f "i32.sub"
    ls f "$i"
    blockE f "$done"
    loopE f "$go"
    lg f "$s"
    lg f "$i"
    ic f 48
    lg f "$m"
    ic f 10
    ins f "i32.rem_u"
    ins f "i32.add"
    gcT f "array.set" "$str"
    lg f "$m"
    ic f 10
    ins f "i32.div_u"
    ls f "$m"
    lg f "$i"
    ic f 1
    ins f "i32.sub"
    ls f "$i"
    lg f "$m"
    ins f "i32.eqz"
    brIf f "$done"
    lg f "$i"
    lg f "$neg"
    ins f "i32.lt_s"
    brIf f "$done"
    br f "$go"
    endB f
    endB f
    lg f "$s"
    endFn f
    // $prints — UTF-16 units ENCODED to UTF-8 through linear memory,
    // flushed by fd_write when the 32KB staging window fills (printing the
    // 1.4MB self-compile answer must not be a host call per character)
    let f = beginFn m [ "$s" ]
    local f "$i" "i32"
    local f "$n" "i32"
    local f "$u" "i32"
    local f "$u2" "i32"
    local f "$o" "i32"
    localsDone f
    lg f "$s"
    gci f "array.len"
    ls f "$n"
    ic f 1024
    ls f "$o"
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    lg f "$n"
    ins f "i32.ge_u"
    brIf f "$done"
    // window nearly full (4-byte headroom): flush and rewind
    lg f "$o"
    ic f 33700
    ins f "i32.ge_u"
    ifE f
    ic f 8
    ic f 1024
    mem f "i32.store"
    ic f 12
    lg f "$o"
    ic f 1024
    ins f "i32.sub"
    mem f "i32.store"
    ic f 1
    ic f 8
    ic f 1
    ic f 16
    callf f "$fd_write"
    ins f "drop"
    ic f 1024
    ls f "$o"
    endB f
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ls f "$u"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    // ASCII fast path
    lg f "$u"
    ic f 128
    ins f "i32.lt_u"
    ifE f
    lg f "$o"
    lg f "$u"
    mem f "i32.store8"
    lg f "$o"
    ic f 1
    ins f "i32.add"
    ls f "$o"
    br f "$go"
    endB f
    // two bytes: 0080..07FF
    lg f "$u"
    ic f 2048
    ins f "i32.lt_u"
    ifE f
    lg f "$o"
    lg f "$u"
    ic f 6
    ins f "i32.shr_u"
    ic f 192
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 1
    ins f "i32.add"
    lg f "$u"
    ic f 63
    ins f "i32.and"
    ic f 128
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 2
    ins f "i32.add"
    ls f "$o"
    br f "$go"
    endB f
    // a HIGH surrogate with its partner: one 4-byte code point
    lg f "$u"
    ic f 0xF800
    ins f "i32.and"
    ic f 0xD800
    ins f "i32.eq"
    ifE f
    lg f "$u"
    ic f 0xDC00
    ins f "i32.lt_u"
    lg f "$i"
    lg f "$n"
    ins f "i32.lt_u"
    ins f "i32.and"
    ifE f
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ls f "$u2"
    lg f "$u2"
    ic f 0xFC00
    ins f "i32.and"
    ic f 0xDC00
    ins f "i32.eq"
    ifE f
    // cp = 0x10000 + ((u - D800) << 10) + (u2 - DC00)
    lg f "$u"
    ic f 0xD800
    ins f "i32.sub"
    ic f 10
    ins f "i32.shl"
    lg f "$u2"
    ic f 0xDC00
    ins f "i32.sub"
    ins f "i32.add"
    ic f 0x10000
    ins f "i32.add"
    ls f "$u"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    lg f "$o"
    lg f "$u"
    ic f 18
    ins f "i32.shr_u"
    ic f 240
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 1
    ins f "i32.add"
    lg f "$u"
    ic f 12
    ins f "i32.shr_u"
    ic f 63
    ins f "i32.and"
    ic f 128
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 2
    ins f "i32.add"
    lg f "$u"
    ic f 6
    ins f "i32.shr_u"
    ic f 63
    ins f "i32.and"
    ic f 128
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 3
    ins f "i32.add"
    lg f "$u"
    ic f 63
    ins f "i32.and"
    ic f 128
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 4
    ins f "i32.add"
    ls f "$o"
    br f "$go"
    endB f
    endB f
    endB f
    // three bytes: everything else (lone surrogates encode as themselves,
    // which is what .NET's WTF-8-ish lenient encoders do on output)
    lg f "$o"
    lg f "$u"
    ic f 12
    ins f "i32.shr_u"
    ic f 224
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 1
    ins f "i32.add"
    lg f "$u"
    ic f 6
    ins f "i32.shr_u"
    ic f 63
    ins f "i32.and"
    ic f 128
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 2
    ins f "i32.add"
    lg f "$u"
    ic f 63
    ins f "i32.and"
    ic f 128
    ins f "i32.or"
    mem f "i32.store8"
    lg f "$o"
    ic f 3
    ins f "i32.add"
    ls f "$o"
    br f "$go"
    endB f
    endB f
    // final flush of whatever accumulated
    lg f "$o"
    ic f 1024
    ins f "i32.gt_u"
    ifE f
    ic f 8
    ic f 1024
    mem f "i32.store"
    ic f 12
    lg f "$o"
    ic f 1024
    ins f "i32.sub"
    mem f "i32.store"
    ic f 1
    ic f 8
    ic f 1
    ic f 16
    callf f "$fd_write"
    ins f "drop"
    endB f
    endFn f

/// declare the runtime slice's functions, in body order
let rtDecls (m : Mod) : unit =
    declFn m "$putc" "$rt_i2v"
    declFn m "$printi" "$rt_i2v"
    declFn m "$ndigits" "$rt_i2i"
    declFn m "$itoa" "$rt_i2a"
    declFn m "$prints" "$rt_s2v"

// ---- exceptions ------------------------------------------------------------

/// (try_table (catch $fppexn $lbl) ...) — one catch clause to a label;
/// blocktype anyref, matching the text emitter's ETry shape
let tryTableA (f : Fn) (catchLabel : string) : unit =
    emitByte f.B opTryTable
    emitBlockTypeVal f.B (valByte "anyref")
    // clause label depths are relative to OUTSIDE the try_table — its own
    // label does not count for its immediates (checked against wasm-tools'
    // encoding of the same shape)
    let d = labelDepth f.Labels catchLabel
    pushLabel f.Labels ""
    emitU32 f.B 1
    emitByte f.B 0x00
    emitU32 f.B 0
    emitU32 f.B d

// the linear counterpart of tryTableA: try_table with an i32 result (the body
// value), one catch clause routing the thrown i32 to `catchLabel`
let tryTableI (f : Fn) (catchLabel : string) : unit =
    emitByte f.B opTryTable
    emitBlockTypeVal f.B (valByte "i32")
    let d = labelDepth f.Labels catchLabel
    pushLabel f.Labels ""
    emitU32 f.B 1
    emitByte f.B 0x00
    emitU32 f.B 0
    emitU32 f.B d

let throwExn (f : Fn) : unit =
    emitByte f.B (opByte "throw")
    emitU32 f.B 0

// ---- the fixed module frame ------------------------------------------------
// The prelude types in the SAME order the text emitter declared them, so
// every index is stable and documented in one place. `vArities` and
// `tupArities` are the program-dependent tails.

let frame (m : Mod) (vArities : int list) (tupArities : int list) : unit =
    tyFunc m "$u1" [ "anyref"; "anyref" ] [ "anyref" ]
    tyStruct m "$clo" [ fld false "i32"; fld false "anyref" ]
    tyStruct m "$cell" [ fld true "anyref" ]
    tyStruct m "$cons" [ fld true "anyref"; fld true "anyref" ]
    // UTF-16: a string is .NET's string — s.[i] and Length mean CODE UNITS,
    // cback's fpp_str_units is already uint16_t*, and the shipped js-string
    // builtins read i16 arrays. Output (fd_write) encodes to UTF-8.
    // $str stays the CANONICAL final (array (mut i16)) — the js-string
    // builtins accept nothing else — and the i16 SCALAR arrays below are
    // the open subtypes instead, so `:? string` still tells them apart.
    tyArray m "$str" "i16"
    tyStruct m "$boxf" [ fld false "f64" ]
    tyStruct m "$boxi" [ fld true "i32" ]
    tyArray m "$arr" "anyref"
    tyArray m "$parr_i" "i32"
    tyArray m "$parr_f" "f64"
    tyArray m "$parr_s" "f32"
    tyArray m "$parr_l" "i64"
    tyArrayOpen m "$parr_h" "i16"
    tyStruct m "$iter" [ fld false "i32"; fld true "anyref"; fld true "anyref"; fld true "i32" ]
    // The POD backing store, one per ALIGNMENT. A struct's size is always a
    // multiple of its alignment, so an element is a whole number of these
    // words whatever the struct — which is what makes the stride C's stride
    // for a 3-byte colour as much as for a pair of doubles. The handle's
    // storage is therefore `anyref`: every use site knows the struct, and so
    // knows which of these to cast to.
    tyArray m "$pb" "i8"
    tyArrayOpen m "$ph" "i16"
    tyArray m "$pk" "i32"
    tyArray m "$pl" "i64"
    tyArray m "$pf32" "f32"
    tyArray m "$pf64" "f64"
    tyStruct m "$hnd" [ fld true "anyref"; fld true "i32"; fld true "i32" ]
    tyStruct m "$boxl" [ fld false "i64" ]
    tyStruct m "$boxs" [ fld false "f32" ]
    tyFunc m "$exntag" [ "anyref" ] []
    importFn m "wasi_snapshot_preview1" "fd_write" "$fd_write"
        [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    importFn m "wasi_snapshot_preview1" "clock_time_get" "$clock_time_get"
        [ "i32"; "i64"; "i32" ] [ "i32" ]
    exportMem m "memory"
    tyArrayFuncref m "$vt"
    tyStruct m "$desc" [ fld false "i32"; fldRef false "$vt" ]
    tyStructSub m "$obj" "" true [ fld true "anyref" ]
    // every CLASS roots here: __desc plus the lazily-assigned identity
    // hash, which is what .NET's default GetHashCode is
    tyStructSub m "$objh" "$obj" true [ fld true "anyref"; fld true "anyref" ]
    tyStruct m "$du0" [ fld false "i32" ]
    tyStruct m "$du1" [ fld false "i32"; fld false "anyref" ]
    for k in vArities do
        let mutable ps = []
        let mutable i = 0
        while i < k do
            ps <- "anyref" :: ps
            i <- i + 1
        tyFunc m ("$v" + string k) ps [ "anyref" ]
    for k in tupArities do
        let mutable fs = []
        let mutable i = 0
        while i < k do
            fs <- fld false "anyref" :: fs
            i <- i + 1
        tyStruct m ("$tup" + string k) fs
    rtTypes m

// ---- runtime: closures and boxing ------------------------------------------

/// a mutable global of a NON-word type, zero-initialised. A module-level
/// float/int64/float32 binding lives in one of these: it holds the raw value,
/// so it needs no box and the collector never has to scan it.
let globalTypedMut (m : Mod) (name : string) (ty : string) : unit =
    dictSet m.GlobalIdx name m.GlobalCount
    m.GlobalCount <- m.GlobalCount + 1
    emitByte m.GlobalBody (valByte ty)
    emitByte m.GlobalBody 1
    if ty = "f64" then (emitByte m.GlobalBody opF64Const; emitF64Bits m.GlobalBody 0L)
    elif ty = "f32" then (emitByte m.GlobalBody opF32Const; emitF32Bits m.GlobalBody 0)
    elif ty = "i64" then (emitByte m.GlobalBody opI64Const; emitS64 m.GlobalBody 0L)
    else (emitByte m.GlobalBody opI32Const; emitS32 m.GlobalBody 0)
    emitByte m.GlobalBody opEnd

let globalI32Mut (m : Mod) (name : string) (init : int) : unit =
    dictSet m.GlobalIdx name m.GlobalCount
    m.GlobalCount <- m.GlobalCount + 1
    emitByte m.GlobalBody (valByte "i32")
    emitByte m.GlobalBody 1
    emitByte m.GlobalBody opI32Const
    emitS32 m.GlobalBody init
    emitByte m.GlobalBody opEnd

let F10 = 0x4024000000000000L
/// +infinity's bits — `nan` is built as inf - inf, so no NaN constant is
/// needed (and the payload matches the runtime's own quiet NaN)
let FINF = 0x7FF0000000000000L
let FTENTH = 0x3FB999999999999AL
let rtTypesHalf (m : Mod) : unit =
    tyFunc m "$rt_f2i" [ "f64" ] [ "i32" ]

let rtDeclsHalf (m : Mod) : unit =
    declFn m "$f2h64" "$rt_f2i"

let rtCoreHalf (m : Mod) : unit =
    // $f2h64: double -> IEEE half bits, correctly rounded (magic-constant
    // trick in the subnormal range, ties-to-even at bit 42 elsewhere)
    let f = beginFn m [ "$v" ]
    local f "$u" "i64"
    local f "$mag" "i64"
    local f "$sign" "i32"
    local f "$o" "i32"
    localsDone f
    lg f "$v"
    ins f "i64.reinterpret_f64"
    ls f "$u"
    lg f "$u"
    lc f 0x8000000000000000L
    ins f "i64.and"
    lc f 48L
    ins f "i64.shr_u"
    ins f "i32.wrap_i64"
    ls f "$sign"
    lg f "$u"
    lc f 0x7fffffffffffffffL
    ins f "i64.and"
    ls f "$mag"
    lg f "$mag"
    lc f 0x40f0000000000000L
    ins f "i64.ge_u"
    ifE f
    ic f 0x7e00
    ic f 0x7c00
    lg f "$mag"
    lc f 0x7ff0000000000000L
    ins f "i64.gt_u"
    ins f "select"
    ls f "$o"
    elseB f
    lg f "$mag"
    lc f 0x3f10000000000000L
    ins f "i64.lt_u"
    ifE f
    lg f "$mag"
    ins f "f64.reinterpret_i64"
    fc f 0x41B0000000000000L
    ins f "f64.add"
    ins f "i64.reinterpret_f64"
    lc f 0x41b0000000000000L
    ins f "i64.sub"
    ins f "i32.wrap_i64"
    ls f "$o"
    elseB f
    lg f "$mag"
    lc f 0x1ffffffffffL
    lg f "$mag"
    lc f 42L
    ins f "i64.shr_u"
    lc f 1L
    ins f "i64.and"
    ins f "i64.add"
    ins f "i64.add"
    ls f "$mag"
    lg f "$mag"
    lc f 42L
    ins f "i64.shr_u"
    lc f 1032192L
    ins f "i64.sub"
    ins f "i32.wrap_i64"
    ls f "$o"
    endB f
    endB f
    lg f "$sign"
    lg f "$o"
    ins f "i32.or"
    endFn f

let rtTypes12 (m : Mod) : unit =
    tyFunc m "$rt_i2fs" [ "i32" ] [ "f32" ]
    tyFunc m "$rt_fs2i" [ "f32" ] [ "i32" ]

let rtDecls12 (m : Mod) : unit =
    declFn m "$h2f" "$rt_i2fs"
    declFn m "$f2h" "$rt_fs2i"

let rtCore12 (m : Mod) : unit =
    // $h2f: half bits -> f32, exact
    let f = beginFn m [ "$h" ]
    local f "$exp" "i32"
    local f "$man" "i32"
    local f "$sgn" "f32"
    localsDone f
    lg f "$h"
    ic f 10
    ins f "i32.shr_u"
    ic f 0x1f
    ins f "i32.and"
    ls f "$exp"
    lg f "$h"
    ic f 0x3ff
    ins f "i32.and"
    ls f "$man"
    sc f 0xBF800000
    sc f 0x3F800000
    lg f "$h"
    ic f 15
    ins f "i32.shr_u"
    ic f 1
    ins f "i32.and"
    ins f "select"
    ls f "$sgn"
    lg f "$exp"
    ins f "i32.eqz"
    ifE f
    // zero or subnormal: mantissa * 2^-24, exact in f32
    lg f "$sgn"
    lg f "$man"
    ins f "f32.convert_i32_u"
    sc f 0x33800000
    ins f "f32.mul"
    ins f "f32.mul"
    ret f
    endB f
    lg f "$exp"
    ic f 0x1f
    ins f "i32.eq"
    ifE f
    // infinity or NaN: rebuild with f32's exponent and a shifted payload
    lg f "$h"
    ic f 15
    ins f "i32.shr_u"
    ic f 1
    ins f "i32.and"
    ic f 31
    ins f "i32.shl"
    ic f 0x7f800000
    lg f "$man"
    ic f 13
    ins f "i32.shl"
    ins f "i32.or"
    ins f "i32.or"
    ins f "f32.reinterpret_i32"
    ret f
    endB f
    lg f "$h"
    ic f 15
    ins f "i32.shr_u"
    ic f 1
    ins f "i32.and"
    ic f 31
    ins f "i32.shl"
    lg f "$exp"
    ic f 112
    ins f "i32.add"
    ic f 23
    ins f "i32.shl"
    lg f "$man"
    ic f 13
    ins f "i32.shl"
    ins f "i32.or"
    ins f "i32.or"
    ins f "f32.reinterpret_i32"
    endFn f
    // $f2h: f32 -> half bits, round-to-nearest-even incl. subnormals
    let f = beginFn m [ "$f" ]
    local f "$u" "i32"
    local f "$sign" "i32"
    local f "$o" "i32"
    localsDone f
    lg f "$f"
    ins f "i32.reinterpret_f32"
    ls f "$u"
    lg f "$u"
    ic f 0x80000000
    ins f "i32.and"
    ls f "$sign"
    lg f "$u"
    lg f "$sign"
    ins f "i32.xor"
    ls f "$u"
    lg f "$u"
    ic f 0x47800000
    ins f "i32.ge_u"
    ifE f
    ic f 0x7e00
    ic f 0x7c00
    lg f "$u"
    ic f 0x7f800000
    ins f "i32.gt_u"
    ins f "select"
    ls f "$o"
    elseB f
    lg f "$u"
    ic f 0x38800000
    ins f "i32.lt_u"
    ifE f
    lg f "$u"
    ins f "f32.reinterpret_i32"
    sc f 0x3F000000
    ins f "f32.add"
    ins f "i32.reinterpret_f32"
    ic f 0x3f000000
    ins f "i32.sub"
    ls f "$o"
    elseB f
    lg f "$u"
    ic f 0xfff
    lg f "$u"
    ic f 13
    ins f "i32.shr_u"
    ic f 1
    ins f "i32.and"
    ins f "i32.add"
    ins f "i32.add"
    ls f "$u"
    lg f "$u"
    ic f 13
    ins f "i32.shr_u"
    ic f 0x1c000
    ins f "i32.sub"
    ls f "$o"
    endB f
    endB f
    lg f "$sign"
    ic f 16
    ins f "i32.shr_u"
    lg f "$o"
    ins f "i32.or"
    endFn f

// ---- runtime: POD word handles and the linear-memory pin heap ---------------
// A POD struct array is a $hnd over 32-bit words ($pk), laid out exactly as a
// C compiler lays out an array of that struct. THIRTY-TWO bits is what makes
// that true rather than approximately true: every struct's size is a multiple
// of four, so an element occupies a whole number of words and the GC stride IS
// the C stride. With 64-bit words a three-float vector would round up from
// twelve bytes to sixteen, and a foreign reader walking the array by twelve —
// which is what clang and emscripten emit — would drift by one float per
// element.
//
// Pinning therefore copies word for word (the GC side is dropped while
// pinned); unpinning copies back. The accessors dispatch on which side holds
// the data. An eight-byte field spans two words and is assembled from them.

/// Every backing a POD array can use: the four integer widths, plus a float
/// array for structs whose fields are all floats of one width.
let assemble (m : Mod) (memPages : int) (hasTag : bool) : byte[] = assembleWith m memPages hasTag ""


// ---- runtime: the JavaScript boundary --------------------------------------
// JS values cross as externref and live inside the program as anyref (one
// conversion instruction each way, no handle table). Strings STAGE through a
// reusable scratch region in linear memory — TextEncoder/TextDecoder glue on
// the other side; property keys ride as (ptr, len) pairs so a get/set is ONE
// crossing. The import set below is the whole surface; the glue is
// stdlib/fpp-js.mjs.

/// imports from module "js" — only emitted when the program touches Js.*
/// (an unused import would still demand a host import object)
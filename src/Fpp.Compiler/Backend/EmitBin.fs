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
    { TypeIdx : Dict<string, int>
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
      /// funcs referenced first-class; the declarative elem segment
      Declared : Dict<string, bool>
      DeclaredOrder : Vec<string> }

let modNew () : Mod =
    { TypeIdx = dictNew (); TypeBody = bytesNew (); TypeCount = 0
      ImportBody = bytesNew (); ImportCount = 0
      FuncIdx = dictNew (); FuncSigs = bytesNew (); FuncCount = 0; ImportedFuncs = 0
      GlobalIdx = dictNew (); GlobalBody = bytesNew (); GlobalCount = 0
      ExportBody = bytesNew (); ExportCount = 0
      CodeBody = bytesNew (); CodeCount = 0
      DataIdx = dictNew (); DataBody = bytesNew (); DataCount = 0
      Declared = dictNew (); DeclaredOrder = vecNew () }

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
    if strLen t > 0 && charAt t 0 = '$' then emitRefType b true (tyIdx m t)
    else
        let v = valByte t
        emitByte b v

/// (ref $t) non-null
let emitRefOf (m : Mod) (b : Bytes) (name : string) : unit =
    emitRefType b false (tyIdx m name)

// ---- type declarations -----------------------------------------------------

/// (type $name (func (param ...) (result ...)))  — params/results by name
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
let fldRefNull (mut : bool) (name : string) : FieldT = { FMut = mut; FTy = ""; FRefNullOf = name; FRefOf = "" }

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

/// (type $name (array (mut ty)))
let tyArray (m : Mod) (name : string) (elem : string) : unit =
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

// ---- function bodies -------------------------------------------------------

type Fn =
    { M : Mod
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
      mutable Replay : int }

/// open a body: params get indices 0.., locals follow as they are created
let beginFn (m : Mod) (paramNames : string list) : Fn =
    let f = { M = m; B = m.CodeBody; LocalIdx = dictNew (); LocalTys = vecNew ()
              NParams = List.length paramNames; Labels = labelsNew (); PatchAt = 0; Replay = -1 }
    f.PatchAt <- beginPatch m.CodeBody
    let mutable i = 0
    for p in paramNames do
        dictSet f.LocalIdx p i
        i <- i + 1
    f

/// a fresh named local of a given valtype name
let local (f : Fn) (name : string) (ty : string) : unit =
    if f.Replay >= 0 then
        dictSet f.LocalIdx name (f.NParams + f.Replay)
        f.Replay <- f.Replay + 1
    else
        dictSet f.LocalIdx name (f.NParams + vecLen f.LocalTys)
        vecAdd f.LocalTys ty

/// a fresh uniquely-named local — the counter advances in BOTH the scratch
/// pass and the replay pass, so names agree across the two
let freshLocal (f : Fn) (prefix : string) (ty : string) : string =
    let n = if f.Replay >= 0 then f.Replay else vecLen f.LocalTys
    let name = prefix + string n
    local f name ty
    name

let localIdx (f : Fn) (name : string) : int =
    match dictTryFind f.LocalIdx name with
    | Some i -> i
    | None -> -1

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
    f.M.CodeCount <- f.M.CodeCount + 1

// ---- instructions ----------------------------------------------------------

let ins (f : Fn) (name : string) : unit = emitByte f.B (opByte name)
let gci (f : Fn) (name : string) : unit =
    emitByte f.B opGcPrefix
    emitU32 f.B (gcByte name)
/// GC op with one type immediate: struct.new $t, array.get $t, ref.cast...
let gcT (f : Fn) (name : string) (tyName : string) : unit =
    gci f name
    (match name with
     | "ref.test" | "ref.cast" -> emitS32 f.B (tyIdx f.M tyName)
     | "ref.test_null" | "ref.cast_null" -> emitS32 f.B (tyIdx f.M tyName)
     | _ -> emitU32 f.B (tyIdx f.M tyName))
/// struct.get/set $t IDX
let gcTF (f : Fn) (name : string) (tyName : string) (fieldIdx : int) : unit =
    gci f name
    emitU32 f.B (tyIdx f.M tyName)
    emitU32 f.B fieldIdx
/// array.new_fixed $t N
let arrNewFixed (f : Fn) (tyName : string) (n : int) : unit =
    gci f "array.new_fixed"
    emitU32 f.B (tyIdx f.M tyName)
    emitU32 f.B n
/// array.new_data $t $dseg
let arrNewData (f : Fn) (tyName : string) (dataName : string) : unit =
    gci f "array.new_data"
    emitU32 f.B (tyIdx f.M tyName)
    emitU32 f.B (dictTryFind f.M.DataIdx dataName).Value
/// array.copy $dst $src
let arrCopy (f : Fn) (dst : string) (src : string) : unit =
    gci f "array.copy"
    emitU32 f.B (tyIdx f.M dst)
    emitU32 f.B (tyIdx f.M src)

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

let callf (f : Fn) (name : string) : unit =
    emitByte f.B opCall
    emitU32 f.B (funcIdx f.M name)
let retCall (f : Fn) (name : string) : unit =
    emitByte f.B opReturnCall
    emitU32 f.B (funcIdx f.M name)
let callRef (f : Fn) (tyName : string) : unit =
    emitByte f.B opCallRef
    emitU32 f.B (tyIdx f.M tyName)
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
let refI31 (f : Fn) : unit = gci f "ref.i31"

// blocks: named labels resolve to depths at branch sites
let blockA (f : Fn) (label : string) : unit =
    emitByte f.B opBlock
    emitBlockTypeVal f.B (valByte "anyref")
    pushLabel f.Labels label
let blockE (f : Fn) (label : string) : unit =
    emitByte f.B opBlock
    emitBlockTypeEmpty f.B
    pushLabel f.Labels label
let loopE (f : Fn) (label : string) : unit =
    emitByte f.B opLoop
    emitBlockTypeEmpty f.B
    pushLabel f.Labels label
let ifA (f : Fn) : unit =
    emitByte f.B opIf
    emitBlockTypeVal f.B (valByte "anyref")
    pushLabel f.Labels ""
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
        | "i32.store8" -> 0
        | "i32.load" | "i32.store" | "f32.store" -> 2
        | _ -> 3
    emitU32 f.B al
    emitU32 f.B 0

// ---- globals / exports / data ----------------------------------------------

/// (global $name (mut anyref) (ref.null any))
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

/// a passive data segment
let dataSeg (m : Mod) (name : string) (bytes : byte[]) : unit =
    dictSet m.DataIdx name m.DataCount
    m.DataCount <- m.DataCount + 1
    emitByte m.DataBody 1
    emitVec m.DataBody bytes

// ---- final assembly --------------------------------------------------------

let assemble (m : Mod) (memPages : int) (hasTag : bool) : byte[] =
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
    // declarative elem segment for every ref.func target
    if vecLen m.DeclaredOrder > 0 then
        emitSection out 9 (fun b ->
            emitU32 b 1
            emitByte b 3          // declarative, funcidx list
            emitByte b 0x00       // elemkind: func
            emitU32 b (vecLen m.DeclaredOrder)
            for n in vecToList m.DeclaredOrder do
                emitU32 b (funcIdx m n))
    if m.DataCount > 0 then
        emitSection out 12 (fun b -> emitU32 b m.DataCount)
    emitSection out 10 (fun b ->
        emitU32 b m.CodeCount
        emitBytes b (bytesToArray m.CodeBody))
    if m.DataCount > 0 then
        emitSection out 11 (fun b ->
            emitU32 b m.DataCount
            emitBytes b (bytesToArray m.DataBody))
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
    lg f "$n"
    ic f 10
    ins f "i32.div_s"
    ls f "$m"
    lg f "$m"
    ic f 0
    ins f "i32.gt_s"
    ifE f
    lg f "$m"
    callf f "$printi"
    endB f
    ic f 48
    lg f "$n"
    ic f 10
    ins f "i32.rem_s"
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
    // $prints
    let f = beginFn m [ "$s" ]
    local f "$i" "i32"
    localsDone f
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    lg f "$s"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$done"
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    callf f "$putc"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
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

let throwExn (f : Fn) : unit =
    emitByte f.B (opByte "throw")
    emitU32 f.B 0

// ---- the fixed module frame ------------------------------------------------
// The prelude types in the SAME order the text emitter declared them, so
// every index is stable and documented in one place. `vArities` and
// `tupArities` are the program-dependent tails.

let frame (m : Mod) (vArities : int list) (tupArities : int list) : unit =
    tyFunc m "$u1" [ "anyref"; "anyref" ] [ "anyref" ]
    tyStruct m "$clo" [ fldRef false "$u1"; fld false "anyref" ]
    tyStruct m "$cell" [ fld true "anyref" ]
    tyStruct m "$cons" [ fld true "anyref"; fld true "anyref" ]
    tyArray m "$str" "i8"
    tyStruct m "$boxf" [ fld false "f64" ]
    tyStruct m "$boxi" [ fld true "i32" ]
    tyArray m "$arr" "anyref"
    tyArray m "$parr_i" "i32"
    tyArray m "$parr_f" "f64"
    tyArray m "$parr_s" "f32"
    tyArray m "$parr_l" "i64"
    tyArray m "$parr_h" "i16"
    tyStruct m "$iter" [ fld false "i32"; fld true "anyref"; fld true "anyref"; fld true "i32" ]
    tyArray m "$pk" "i64"
    tyStruct m "$hnd" [ fldRefNull true "$pk"; fld true "i32"; fld true "i32" ]
    tyStruct m "$boxl" [ fld false "i64" ]
    tyStruct m "$boxs" [ fld false "f32" ]
    tyFunc m "$exntag" [ "anyref" ] []
    importFn m "wasi_snapshot_preview1" "fd_write" "$fd_write"
        [ "i32"; "i32"; "i32"; "i32" ] [ "i32" ]
    exportMem m "memory"
    tyArrayFuncref m "$vt"
    tyStruct m "$desc" [ fld false "i32"; fldRef false "$vt" ]
    tyStructSub m "$obj" "" true [ fld true "anyref" ]
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

let rtCoreDecls2 (m : Mod) : unit =
    declFn m "$applyc" "$u1"
    declFn m "$ofi" "$rt_i2a"
    declFn m "$toi" "$rt_a2i"
    declFn m "$addv" "$u1"

let rtTypes2 (m : Mod) : unit =
    tyFunc m "$rt_a2i" [ "anyref" ] [ "i32" ]

let rtCore2 (m : Mod) : unit =
    // $applyc: call through the closure's code pointer with its env
    let f = beginFn m [ "$f"; "$a" ]
    localsDone f
    lg f "$a"
    lg f "$f"
    gcT f "ref.cast" "$clo"
    gcTF f "struct.get" "$clo" 1
    lg f "$f"
    gcT f "ref.cast" "$clo"
    gcTF f "struct.get" "$clo" 0
    callRef f "$u1"
    endFn f
    // $ofi: i31 when it fits, $boxi when it does not
    let f = beginFn m [ "$n" ]
    localsDone f
    lg f "$n"
    lg f "$n"
    ic f 1
    ins f "i32.shl"
    ic f 1
    ins f "i32.shr_s"
    ins f "i32.eq"
    ifA f
    lg f "$n"
    refI31 f
    elseB f
    lg f "$n"
    gcT f "struct.new" "$boxi"
    endB f
    endFn f
    // $toi
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    gcAbs f "ref.test" "i31"
    ifV f "i32"
    lg f "$v"
    gcAbs f "ref.cast" "i31"
    i31get f
    elseB f
    lg f "$v"
    gcT f "ref.cast" "$boxi"
    gcTF f "struct.get" "$boxi" 0
    endB f
    endFn f
    // $addv: two i31s fast-path, strings concat later; int fallback
    let f = beginFn m [ "$a"; "$b" ]
    localsDone f
    lg f "$a"
    gcAbs f "ref.test" "i31"
    lg f "$b"
    gcAbs f "ref.test" "i31"
    ins f "i32.and"
    ifA f
    lg f "$a"
    gcAbs f "ref.cast" "i31"
    i31get f
    lg f "$b"
    gcAbs f "ref.cast" "i31"
    i31get f
    ins f "i32.add"
    refI31 f
    elseB f
    lg f "$a"
    callf f "$toi"
    lg f "$b"
    callf f "$toi"
    ins f "i32.add"
    callf f "$ofi"
    endB f
    endFn f

// ---- runtime: strings, equality --------------------------------------------

let rtTypes3 (m : Mod) : unit =
    tyFunc m "$rt_ss2a" [ "$str"; "$str" ] [ "anyref" ]

/// a global holding a funcref VTABLE (the DU eq/hash tables); the init
/// builds it from the given function names
let globalVt (m : Mod) (name : string) (fns : string list) : unit =
    dictSet m.GlobalIdx name m.GlobalCount
    m.GlobalCount <- m.GlobalCount + 1
    emitRefType m.GlobalBody false (tyIdx m "$vt")
    emitByte m.GlobalBody 0
    for fn in fns do
        emitByte m.GlobalBody (opByte "ref.func")
        emitU32 m.GlobalBody (funcIdx m fn)
        if not (dictTryFind m.Declared fn).IsSome then
            dictSet m.Declared fn true
            vecAdd m.DeclaredOrder fn
    emitByte m.GlobalBody opGcPrefix
    emitU32 m.GlobalBody (gcByte "array.new_fixed")
    emitU32 m.GlobalBody (tyIdx m "$vt")
    emitU32 m.GlobalBody (List.length fns)
    emitByte m.GlobalBody opEnd

let rtDecls3 (m : Mod) : unit =
    declFn m "$strcat" "$rt_ss2a"
    declFn m "$eq_du_default" "$u1"
    declFn m "$equal" "$u1"

/// cast to (ref null eq) — ref.eq's operand type
let private castEq (f : Fn) : unit =
    gci f "ref.cast_null"
    emitS32 f.B (heapByte "eq" - 0x80)

let rtCore3 (m : Mod) (tupArities : int list) : unit =
    // $strcat
    let f = beginFn m [ "$a"; "$b" ]
    local f "$r" "$str"
    local f "$i" "i32"
    local f "$la" "i32"
    localsDone f
    lg f "$a"
    gci f "array.len"
    ls f "$la"
    lg f "$la"
    lg f "$b"
    gci f "array.len"
    ins f "i32.add"
    gcT f "array.new_default" "$str"
    ls f "$r"
    blockE f "$d1"
    loopE f "$l1"
    lg f "$i"
    lg f "$la"
    ins f "i32.ge_u"
    brIf f "$d1"
    lg f "$r"
    gcT f "ref.cast" "$str"
    lg f "$i"
    lg f "$a"
    lg f "$i"
    gcT f "array.get_u" "$str"
    gcT f "array.set" "$str"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$l1"
    endB f
    endB f
    ic f 0
    ls f "$i"
    blockE f "$d2"
    loopE f "$l2"
    lg f "$i"
    lg f "$b"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$d2"
    lg f "$r"
    gcT f "ref.cast" "$str"
    lg f "$la"
    lg f "$i"
    ins f "i32.add"
    lg f "$b"
    lg f "$i"
    gcT f "array.get_u" "$str"
    gcT f "array.set" "$str"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$l2"
    endB f
    endB f
    lg f "$r"
    endFn f
    // $eq_du_default: same tag already checked; compare payloads
    let f = beginFn m [ "$a"; "$b" ]
    localsDone f
    lg f "$a"
    gcT f "ref.test" "$du1"
    lg f "$b"
    gcT f "ref.test" "$du1"
    ins f "i32.and"
    ifE f
    lg f "$a"
    gcT f "ref.cast" "$du1"
    gcTF f "struct.get" "$du1" 1
    lg f "$b"
    gcT f "ref.cast" "$du1"
    gcTF f "struct.get" "$du1" 1
    callf f "$equal"
    ret f
    endB f
    ic f 1
    refI31 f
    endFn f
    // $equal — structural dispatch, ported branch for branch
    let f = beginFn m [ "$a"; "$b" ]
    local f "$i" "i32"
    localsDone f
    // null equals only null
    lg f "$a"
    ins f "ref.is_null"
    lg f "$b"
    ins f "ref.is_null"
    ins f "i32.or"
    ifE f
    lg f "$a"
    ins f "ref.is_null"
    lg f "$b"
    ins f "ref.is_null"
    ins f "i32.and"
    refI31 f
    ret f
    endB f
    // both i31
    lg f "$a"
    gcAbs f "ref.test" "i31"
    lg f "$b"
    gcAbs f "ref.test" "i31"
    ins f "i32.and"
    ifE f
    lg f "$a"
    gcAbs f "ref.cast" "i31"
    i31get f
    lg f "$b"
    gcAbs f "ref.cast" "i31"
    i31get f
    ins f "i32.eq"
    refI31 f
    ret f
    endB f
    // both strings: length then bytes
    lg f "$a"
    gcT f "ref.test" "$str"
    lg f "$b"
    gcT f "ref.test" "$str"
    ins f "i32.and"
    ifE f
    lg f "$a"
    gcT f "ref.cast" "$str"
    gci f "array.len"
    lg f "$b"
    gcT f "ref.cast" "$str"
    gci f "array.len"
    ins f "i32.ne"
    ifE f
    ic f 0
    refI31 f
    ret f
    endB f
    blockE f "$ne"
    loopE f "$go"
    lg f "$i"
    lg f "$a"
    gcT f "ref.cast" "$str"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$ne"
    lg f "$a"
    gcT f "ref.cast" "$str"
    lg f "$i"
    gcT f "array.get_u" "$str"
    lg f "$b"
    gcT f "ref.cast" "$str"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ins f "i32.ne"
    ifE f
    ic f 0
    refI31 f
    ret f
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
    endB f
    ic f 1
    refI31 f
    ret f
    endB f
    // boxed scalars
    for bt, eqop in [ "$boxl", "i64.eq"; "$boxf", "f64.eq"; "$boxs", "f32.eq"; "$boxi", "i32.eq" ] do
        lg f "$a"
        gcT f "ref.test" bt
        lg f "$b"
        gcT f "ref.test" bt
        ins f "i32.and"
        ifE f
        lg f "$a"
        gcT f "ref.cast" bt
        gcTF f "struct.get" bt 0
        lg f "$b"
        gcT f "ref.cast" bt
        gcTF f "struct.get" bt 0
        ins f eqop
        refI31 f
        ret f
        endB f
    // tuples, per arity in the frame
    for n in tupArities do
        let t = "$tup" + string n
        lg f "$a"
        gcT f "ref.test" t
        lg f "$b"
        gcT f "ref.test" t
        ins f "i32.and"
        ifE f
        let mutable i = 0
        while i < n do
            lg f "$a"
            gcT f "ref.cast" t
            gcTF f "struct.get" t i
            lg f "$b"
            gcT f "ref.cast" t
            gcTF f "struct.get" t i
            callf f "$equal"
            gcAbs f "ref.cast" "i31"
            i31get f
            ins f "i32.eqz"
            ifE f
            ic f 0
            refI31 f
            ret f
            endB f
            i <- i + 1
        ic f 1
        refI31 f
        ret f
        endB f
    // DU cases: same tag, then through the $duEq table
    for dt in [ "$du0"; "$du1" ] do
        lg f "$a"
        gcT f "ref.test" dt
        lg f "$b"
        gcT f "ref.test" dt
        ins f "i32.and"
        ifE f
        lg f "$a"
        gcT f "ref.cast" dt
        gcTF f "struct.get" dt 0
        lg f "$b"
        gcT f "ref.cast" dt
        gcTF f "struct.get" dt 0
        ins f "i32.ne"
        ifE f
        ic f 0
        refI31 f
        ret f
        endB f
        lg f "$a"
        lg f "$b"
        gg f "$duEq"
        lg f "$a"
        gcT f "ref.cast" dt
        gcTF f "struct.get" dt 0
        gcT f "array.get" "$vt"
        gcT f "ref.cast" "$u1"
        callRef f "$u1"
        ret f
        endB f
    // cons: heads then tails
    lg f "$a"
    gcT f "ref.test" "$cons"
    lg f "$b"
    gcT f "ref.test" "$cons"
    ins f "i32.and"
    ifE f
    lg f "$a"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 0
    lg f "$b"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 0
    callf f "$equal"
    gcAbs f "ref.cast" "i31"
    i31get f
    ins f "i32.eqz"
    ifE f
    ic f 0
    refI31 f
    ret f
    endB f
    lg f "$a"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    lg f "$b"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    callf f "$equal"
    ret f
    endB f
    // fallback: identity
    lg f "$a"
    castEq f
    lg f "$b"
    castEq f
    ins f "ref.eq"
    refI31 f
    endFn f

// ---- runtime: printval (floats route to '?' until printf64 is ported) -----

let rtDecls4 (m : Mod) : unit =
    declFn m "$printval" "$rt_a2v"

let rtTypes4 (m : Mod) : unit =
    tyFunc m "$rt_a2v" [ "anyref" ] []

let rtCore4 (m : Mod) : unit =
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    gcAbs f "ref.test" "i31"
    ifE f
    lg f "$v"
    gcAbs f "ref.cast" "i31"
    i31get f
    callf f "$printi"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$str"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$str"
    callf f "$prints"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxi"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxi"
    gcTF f "struct.get" "$boxi" 0
    callf f "$printi"
    ret f
    endB f
    // WIP: boxl/boxf/boxs need printl/printf64; '?' marks the gap loudly
    ic f 63
    callf f "$putc"
    endFn f

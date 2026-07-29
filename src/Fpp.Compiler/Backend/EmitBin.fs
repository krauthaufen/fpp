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
        emitBytes b (bytesToArray tsub))
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

/// a per-class descriptor global: (ref $desc) = struct.new $desc (id, vtable)
/// with "" slots as ref.null func
let globalDesc (m : Mod) (name : string) (id : int) (slots : string list) : unit =
    dictSet m.GlobalIdx name m.GlobalCount
    m.GlobalCount <- m.GlobalCount + 1
    emitRefType m.GlobalBody false (tyIdx m "$desc")
    emitByte m.GlobalBody 0
    emitByte m.GlobalBody opI32Const
    emitS32 m.GlobalBody id
    for fn in slots do
        if fn = "" then
            emitByte m.GlobalBody (opByte "ref.null")
            emitS32 m.GlobalBody (heapByte "func" - 0x80)
        else
            emitByte m.GlobalBody (opByte "ref.func")
            emitU32 m.GlobalBody (funcIdx m fn)
            if not (dictTryFind m.Declared fn).IsSome then
                dictSet m.Declared fn true
                vecAdd m.DeclaredOrder fn
    emitByte m.GlobalBody opGcPrefix
    emitU32 m.GlobalBody (gcByte "array.new_fixed")
    emitU32 m.GlobalBody (tyIdx m "$vt")
    emitU32 m.GlobalBody (List.length slots)
    emitByte m.GlobalBody opGcPrefix
    emitU32 m.GlobalBody (gcByte "struct.new")
    emitU32 m.GlobalBody (tyIdx m "$desc")
    emitByte m.GlobalBody opEnd

/// a mutable i32 global with a constant initializer
let globalI32Mut (m : Mod) (name : string) (init : int) : unit =
    dictSet m.GlobalIdx name m.GlobalCount
    m.GlobalCount <- m.GlobalCount + 1
    emitByte m.GlobalBody (valByte "i32")
    emitByte m.GlobalBody 1
    emitByte m.GlobalBody opI32Const
    emitS32 m.GlobalBody init
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
    // any reference type: descriptors are per-type, so two values whose
    // descriptors differ are of different types and cannot be equal — the
    // shape test alone is NOT sound, wasm-GC canonicalizes same-shaped
    // structs into one heap type
    lg f "$a"
    gcT f "ref.test" "$obj"
    lg f "$b"
    gcT f "ref.test" "$obj"
    ins f "i32.and"
    ifE f
    lg f "$a"
    gcT f "ref.cast" "$obj"
    gcTF f "struct.get" "$obj" 0
    castEq f
    lg f "$b"
    gcT f "ref.cast" "$obj"
    gcTF f "struct.get" "$obj" 0
    castEq f
    ins f "ref.eq"
    ins f "i32.eqz"
    ifE f
    ic f 0
    refI31 f
    ret f
    endB f
    lg f "$a"
    lg f "$b"
    lg f "$a"
    gcT f "ref.cast" "$obj"
    gcTF f "struct.get" "$obj" 0
    gcT f "ref.cast" "$desc"
    gcTF f "struct.get" "$desc" 1
    ic f 0
    gcT f "array.get" "$vt"
    gcT f "ref.cast" "$v2"
    callRef f "$v2"
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

// ---- runtime: recursive-closure knot tying ---------------------------------

let rtTypes5 (m : Mod) : unit =
    tyFunc m "$rt_aaa2v" [ "anyref"; "anyref"; "anyref" ] []

let rtDecls5 (m : Mod) : unit =
    declFn m "$patchmark" "$rt_aaa2v"

/// $patchmark c mark v — tie one strand of a rec group's knot: in closure
/// c's environment, whatever slot still holds the marker becomes v. TWO
/// environment shapes coexist: a flat $arr (captures) and a $cons chain
/// (curried partial application); patch whichever this is.
let rtCore5 (m : Mod) : unit =
    let f = beginFn m [ "$c"; "$mark"; "$v" ]
    local f "$e" "anyref"
    local f "$i" "i32"
    local f "$n" "i32"
    localsDone f
    lg f "$c"
    gcT f "ref.cast" "$clo"
    gcTF f "struct.get" "$clo" 1
    ls f "$e"
    blockE f "$done"
    lg f "$e"
    gcT f "ref.test" "$arr"
    ifE f
    lg f "$e"
    gcT f "ref.cast" "$arr"
    gci f "array.len"
    ls f "$n"
    ic f 0
    ls f "$i"
    blockE f "$out"
    loopE f "$go"
    lg f "$i"
    lg f "$n"
    ins f "i32.ge_u"
    brIf f "$out"
    lg f "$e"
    gcT f "ref.cast" "$arr"
    lg f "$i"
    gcT f "array.get" "$arr"
    castEq f
    lg f "$mark"
    castEq f
    ins f "ref.eq"
    ifE f
    lg f "$e"
    gcT f "ref.cast" "$arr"
    lg f "$i"
    lg f "$v"
    gcT f "array.set" "$arr"
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f // loop $go
    endB f // block $out
    br f "$done"
    endB f // if $arr
    blockE f "$cout"
    loopE f "$cgo"
    lg f "$e"
    gcT f "ref.test" "$cons"
    ins f "i32.eqz"
    brIf f "$cout"
    lg f "$e"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 0
    castEq f
    lg f "$mark"
    castEq f
    ins f "ref.eq"
    ifE f
    lg f "$e"
    gcT f "ref.cast" "$cons"
    lg f "$v"
    gcTF f "struct.set" "$cons" 0
    endB f
    lg f "$e"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    ls f "$e"
    br f "$cgo"
    endB f // loop $cgo
    endB f // block $cout
    endB f // block $done
    endFn f

// ---- runtime: the numeric/string kernel ------------------------------------
// Transliterated from the text runtime function by function: strcmp, the
// f64/f32/i64 boxing family, digit put/take, string->number, number->string.

let rtTypes6 (m : Mod) : unit =
    tyFunc m "$rt_ss2i" [ "$str"; "$str" ] [ "i32" ]
    tyFunc m "$rt_a2f" [ "anyref" ] [ "f64" ]
    tyFunc m "$rt_f2a" [ "f64" ] [ "anyref" ]
    tyFunc m "$rt_a2fs" [ "anyref" ] [ "f32" ]
    tyFunc m "$rt_fs2a" [ "f32" ] [ "anyref" ]
    tyFunc m "$rt_a2l" [ "anyref" ] [ "i64" ]
    tyFunc m "$rt_l2a" [ "i64" ] [ "anyref" ]
    tyFunc m "$rt_sii2i" [ "$str"; "i32"; "i32" ] [ "i32" ]
    tyFunc m "$rt_sil2i" [ "$str"; "i32"; "i64" ] [ "i32" ]
    tyFunc m "$rt_si2a" [ "$str"; "i32" ] [ "anyref" ]
    tyFunc m "$rt_s2l" [ "$str" ] [ "i64" ]
    tyFunc m "$rt_s2i" [ "$str" ] [ "i32" ]
    tyFunc m "$rt_s2f" [ "$str" ] [ "f64" ]
    tyFunc m "$rt_l2v" [ "i64" ] []
    tyFunc m "$rt_f2v" [ "f64" ] []
    tyFunc m "$rt_a2a" [ "anyref" ] [ "anyref" ]

let rtDecls6 (m : Mod) : unit =
    declFn m "$strcmp" "$rt_ss2i"
    declFn m "$tof" "$rt_a2f"
    declFn m "$off" "$rt_f2a"
    declFn m "$tos" "$rt_a2fs"
    declFn m "$oss" "$rt_fs2a"
    declFn m "$tol" "$rt_a2l"
    declFn m "$ofl" "$rt_l2a"
    declFn m "$sput" "$rt_sii2i"
    declFn m "$lput" "$rt_sil2i"
    declFn m "$strTake" "$rt_si2a"
    declFn m "$atol" "$rt_s2l"
    declFn m "$atoi" "$rt_s2i"
    declFn m "$atof" "$rt_s2f"
    declFn m "$ltoa" "$rt_l2a"
    declFn m "$ultoa" "$rt_l2a"
    declFn m "$ftoa" "$rt_f2a"
    declFn m "$printl" "$rt_l2v"
    declFn m "$printf64" "$rt_f2v"
    declFn m "$lenv" "$rt_a2a"

// f64 constants by their bit patterns — the writer speaks bits, and spelled
// this way the self-hosted compiler needs no host float formatting
let private F10 = 0x4024000000000000L
let private FTENTH = 0x3FB999999999999AL
let private F1E18 = 0x43ABC16D674EC800L
let private FINF = 0x7FF0000000000000L

let rtCore6 (m : Mod) : unit =
    // $strcmp: byte-wise ordinal; shorter sorts first
    let f = beginFn m [ "$a"; "$b" ]
    local f "$i" "i32"
    local f "$la" "i32"
    local f "$lb" "i32"
    local f "$ca" "i32"
    local f "$cb" "i32"
    localsDone f
    lg f "$a"
    gci f "array.len"
    ls f "$la"
    lg f "$b"
    gci f "array.len"
    ls f "$lb"
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    lg f "$la"
    ins f "i32.ge_u"
    lg f "$i"
    lg f "$lb"
    ins f "i32.ge_u"
    ins f "i32.or"
    brIf f "$done"
    lg f "$a"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ls f "$ca"
    lg f "$b"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ls f "$cb"
    lg f "$ca"
    lg f "$cb"
    ins f "i32.ne"
    ifE f
    ic f -1
    ic f 1
    lg f "$ca"
    lg f "$cb"
    ins f "i32.lt_u"
    ins f "select"
    ret f
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f // loop
    endB f // $done
    lg f "$la"
    lg f "$lb"
    ins f "i32.lt_u"
    ifE f
    ic f -1
    ret f
    endB f
    lg f "$la"
    lg f "$lb"
    ins f "i32.gt_u"
    ifE f
    ic f 1
    ret f
    endB f
    ic f 0
    endFn f
    // $tof
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    endFn f
    // $off
    let f = beginFn m [ "$x" ]
    localsDone f
    lg f "$x"
    gcT f "struct.new" "$boxf"
    endFn f
    // $tos
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    gcT f "ref.cast" "$boxs"
    gcTF f "struct.get" "$boxs" 0
    endFn f
    // $oss
    let f = beginFn m [ "$x" ]
    localsDone f
    lg f "$x"
    gcT f "struct.new" "$boxs"
    endFn f
    // $tol: an i31 widens; otherwise unbox
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    gcAbs f "ref.test" "i31"
    ifV f "i64"
    lg f "$v"
    gcAbs f "ref.cast" "i31"
    i31get f
    ins f "i64.extend_i32_s"
    elseB f
    lg f "$v"
    gcT f "ref.cast" "$boxl"
    gcTF f "struct.get" "$boxl" 0
    endB f
    endFn f
    // $ofl: i31 when it fits in 31 bits, $boxl when it does not
    let f = beginFn m [ "$n" ]
    localsDone f
    lg f "$n"
    lg f "$n"
    lc f 33L
    ins f "i64.shl"
    lc f 33L
    ins f "i64.shr_s"
    ins f "i64.eq"
    ifA f
    lg f "$n"
    ins f "i32.wrap_i64"
    refI31 f
    elseB f
    lg f "$n"
    gcT f "struct.new" "$boxl"
    endB f
    endFn f
    // $sput: store one byte, return the advanced position
    let f = beginFn m [ "$s"; "$p"; "$c" ]
    localsDone f
    lg f "$s"
    lg f "$p"
    lg f "$c"
    gcT f "array.set" "$str"
    lg f "$p"
    ic f 1
    ins f "i32.add"
    endFn f
    // $lput: digits of an i64 MAGNITUDE, unsigned — `0 - min` wraps to min,
    // whose unsigned value is exactly the magnitude
    let f = beginFn m [ "$s"; "$p"; "$n" ]
    local f "$m" "i64"
    localsDone f
    lg f "$n"
    lc f 10L
    ins f "i64.div_u"
    ls f "$m"
    lg f "$m"
    lc f 0L
    ins f "i64.gt_u"
    ifE f
    lg f "$s"
    lg f "$p"
    lg f "$m"
    callf f "$lput"
    ls f "$p"
    endB f
    lg f "$s"
    lg f "$p"
    ic f 48
    lg f "$n"
    lc f 10L
    ins f "i64.rem_u"
    ins f "i32.wrap_i64"
    ins f "i32.add"
    callf f "$sput"
    endFn f
    // $strTake: the first p bytes as a fresh string
    let f = beginFn m [ "$s"; "$p" ]
    local f "$r" "$str"
    localsDone f
    lg f "$p"
    gcT f "array.new_default" "$str"
    ls f "$r"
    lg f "$r"
    ic f 0
    lg f "$s"
    ic f 0
    lg f "$p"
    arrCopy f "$str" "$str"
    lg f "$r"
    endFn f
    // $atol: parse stops at the first character that cannot continue
    let f = beginFn m [ "$s" ]
    local f "$i" "i32"
    local f "$n" "i32"
    local f "$neg" "i32"
    local f "$acc" "i64"
    local f "$c" "i32"
    localsDone f
    lg f "$s"
    gci f "array.len"
    ls f "$n"
    lg f "$n"
    ic f 0
    ins f "i32.gt_u"
    ifE f
    lg f "$s"
    ic f 0
    gcT f "array.get_u" "$str"
    ic f 45
    ins f "i32.eq"
    ifE f
    ic f 1
    ls f "$neg"
    ic f 1
    ls f "$i"
    endB f
    lg f "$s"
    ic f 0
    gcT f "array.get_u" "$str"
    ic f 43
    ins f "i32.eq"
    ifE f
    ic f 1
    ls f "$i"
    endB f
    endB f
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    lg f "$n"
    ins f "i32.ge_u"
    brIf f "$done"
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ls f "$c"
    lg f "$c"
    ic f 48
    ins f "i32.lt_u"
    brIf f "$done"
    lg f "$c"
    ic f 57
    ins f "i32.gt_u"
    brIf f "$done"
    lg f "$acc"
    lc f 10L
    ins f "i64.mul"
    lg f "$c"
    ic f 48
    ins f "i32.sub"
    ins f "i64.extend_i32_u"
    ins f "i64.add"
    ls f "$acc"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
    endB f
    lg f "$neg"
    ifV f "i64"
    lc f 0L
    lg f "$acc"
    ins f "i64.sub"
    elseB f
    lg f "$acc"
    endB f
    endFn f
    // $atoi
    let f = beginFn m [ "$s" ]
    localsDone f
    lg f "$s"
    callf f "$atol"
    ins f "i32.wrap_i64"
    endFn f
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
    gci f "array.len"
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
    gcT f "array.get_u" "$str"
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
    // $ltoa
    let f = beginFn m [ "$n" ]
    local f "$s" "$str"
    local f "$p" "i32"
    localsDone f
    ic f 24
    gcT f "array.new_default" "$str"
    ls f "$s"
    lg f "$n"
    lc f 0L
    ins f "i64.lt_s"
    ifE f
    lg f "$s"
    lg f "$p"
    ic f 45
    callf f "$sput"
    ls f "$p"
    lc f 0L
    lg f "$n"
    ins f "i64.sub"
    ls f "$n"
    endB f
    lg f "$s"
    lg f "$p"
    lg f "$n"
    callf f "$lput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    endFn f
    // $ultoa
    let f = beginFn m [ "$n" ]
    local f "$s" "$str"
    local f "$p" "i32"
    localsDone f
    ic f 24
    gcT f "array.new_default" "$str"
    ls f "$s"
    lg f "$s"
    lg f "$p"
    lg f "$n"
    callf f "$lput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    endFn f
    // $ftoa: NaN, sign, ∞ (U+221E, matching .NET), 1e18 normalization,
    // integer part through $lput, up to 15 fractional digits, exponent
    let f = beginFn m [ "$v" ]
    local f "$s" "$str"
    local f "$p" "i32"
    local f "$ip" "f64"
    local f "$frac" "f64"
    local f "$k" "i32"
    local f "$d" "i32"
    local f "$e" "i32"
    localsDone f
    ic f 40
    gcT f "array.new_default" "$str"
    ls f "$s"
    lg f "$v"
    lg f "$v"
    ins f "f64.ne"
    ifE f
    lg f "$s"
    lg f "$p"
    ic f 78
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    ic f 97
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    ic f 78
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    ret f
    endB f
    lg f "$v"
    fc f 0L
    ins f "f64.lt"
    ifE f
    lg f "$s"
    lg f "$p"
    ic f 45
    callf f "$sput"
    ls f "$p"
    lg f "$v"
    ins f "f64.neg"
    ls f "$v"
    endB f
    lg f "$v"
    fc f FINF
    ins f "f64.eq"
    ifE f
    lg f "$s"
    lg f "$p"
    ic f 226
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    ic f 136
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    ic f 158
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    ret f
    endB f
    lg f "$v"
    fc f F1E18
    ins f "f64.ge"
    ifE f
    blockE f "$scaled"
    loopE f "$sgo"
    lg f "$v"
    fc f F10
    ins f "f64.lt"
    brIf f "$scaled"
    lg f "$v"
    fc f F10
    ins f "f64.div"
    ls f "$v"
    lg f "$e"
    ic f 1
    ins f "i32.add"
    ls f "$e"
    br f "$sgo"
    endB f
    endB f
    endB f
    lg f "$v"
    ins f "f64.floor"
    ls f "$ip"
    lg f "$s"
    lg f "$p"
    lg f "$ip"
    ins f "i64.trunc_f64_s"
    callf f "$lput"
    ls f "$p"
    lg f "$v"
    lg f "$ip"
    ins f "f64.sub"
    ls f "$frac"
    lg f "$frac"
    fc f 0L
    ins f "f64.gt"
    ifE f
    lg f "$s"
    lg f "$p"
    ic f 46
    callf f "$sput"
    ls f "$p"
    blockE f "$fdone"
    loopE f "$fgo"
    lg f "$k"
    ic f 15
    ins f "i32.ge_s"
    brIf f "$fdone"
    lg f "$frac"
    fc f F10
    ins f "f64.mul"
    ls f "$frac"
    lg f "$frac"
    ins f "f64.floor"
    ins f "i32.trunc_f64_s"
    ls f "$d"
    lg f "$s"
    lg f "$p"
    ic f 48
    lg f "$d"
    ins f "i32.add"
    callf f "$sput"
    ls f "$p"
    lg f "$frac"
    lg f "$frac"
    ins f "f64.floor"
    ins f "f64.sub"
    ls f "$frac"
    lg f "$frac"
    fc f 0L
    ins f "f64.eq"
    brIf f "$fdone"
    lg f "$k"
    ic f 1
    ins f "i32.add"
    ls f "$k"
    br f "$fgo"
    endB f
    endB f
    endB f
    lg f "$e"
    ic f 0
    ins f "i32.ne"
    ifE f
    lg f "$s"
    lg f "$p"
    ic f 69
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    ic f 43
    callf f "$sput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    lg f "$e"
    ins f "i64.extend_i32_u"
    callf f "$lput"
    ls f "$p"
    endB f
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    endFn f
    // $printl / $printf64: print the builder's result
    let f = beginFn m [ "$n" ]
    localsDone f
    lg f "$n"
    callf f "$ltoa"
    gcT f "ref.cast" "$str"
    callf f "$prints"
    endFn f
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    callf f "$ftoa"
    gcT f "ref.cast" "$str"
    callf f "$prints"
    endFn f
    // $lenv: .Length across every array-like representation
    let f = beginFn m [ "$v" ]
    localsDone f
    for ty in [ "$arr"; "$parr_i"; "$parr_f"; "$parr_s"; "$parr_l"; "$parr_h"; "$str" ] do
        lg f "$v"
        gcT f "ref.test" ty
        ifE f
        lg f "$v"
        gcT f "ref.cast" ty
        gci f "array.len"
        callf f "$ofi"
        ret f
        endB f
    ic f 0
    refI31 f
    endFn f

// ---- runtime: structural hash and comparison -------------------------------

let rtTypes7 (m : Mod) : unit =
    tyFunc m "$rt_aa2i" [ "anyref"; "anyref" ] [ "i32" ]

let rtDecls7 (m : Mod) : unit =
    declFn m "$hashv" "$rt_a2i"
    declFn m "$cmpv" "$rt_aa2i"
    declFn m "$cmpvBoxed" "$u1"
    declFn m "$hash_du_default" "$v1"

let rtCore7 (m : Mod) (tupArities : int list) : unit =
    // $hashv: structural hash, representation-dispatched like $equal
    let f = beginFn m [ "$v" ]
    local f "$i" "i32"
    local f "$h" "i32"
    localsDone f
    lg f "$v"
    gcAbs f "ref.test" "i31"
    ifE f
    lg f "$v"
    gcAbs f "ref.cast" "i31"
    i31get f
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxi"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxi"
    gcTF f "struct.get" "$boxi" 0
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxl"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxl"
    gcTF f "struct.get" "$boxl" 0
    ins f "i32.wrap_i64"
    lg f "$v"
    gcT f "ref.cast" "$boxl"
    gcTF f "struct.get" "$boxl" 0
    lc f 32L
    ins f "i64.shr_u"
    ins f "i32.wrap_i64"
    ins f "i32.xor"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxf"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    ins f "i64.reinterpret_f64"
    ins f "i32.wrap_i64"
    lg f "$v"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    ins f "i64.reinterpret_f64"
    lc f 32L
    ins f "i64.shr_u"
    ins f "i32.wrap_i64"
    ins f "i32.xor"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$obj"
    ifE f
    lg f "$v"
    lg f "$v"
    gcT f "ref.cast" "$obj"
    gcTF f "struct.get" "$obj" 0
    gcT f "ref.cast" "$desc"
    gcTF f "struct.get" "$desc" 1
    ic f 1
    gcT f "array.get" "$vt"
    gcT f "ref.cast" "$v1"
    callRef f "$v1"
    gcAbs f "ref.cast" "i31"
    i31get f
    ret f
    endB f
    // arrays hash to their LENGTH: identity equality only obliges equal
    // values to hash equally, and length is the one thing writes cannot
    // change (see DIVERGENCES.md)
    for ty in [ "$arr"; "$parr_i"; "$parr_f"; "$parr_s"; "$parr_l"; "$parr_h" ] do
        lg f "$v"
        gcT f "ref.test" ty
        ifE f
        lg f "$v"
        gcT f "ref.cast" ty
        gci f "array.len"
        ret f
        endB f
    for n in tupArities do
        let t = "$tup" + string n
        lg f "$v"
        gcT f "ref.test" t
        ifE f
        lg f "$v"
        gcT f "ref.cast" t
        gcTF f "struct.get" t 0
        callf f "$hashv"
        let mutable i = 1
        while i < n do
            ic f 31
            ins f "i32.mul"
            lg f "$v"
            gcT f "ref.cast" t
            gcTF f "struct.get" t i
            callf f "$hashv"
            ins f "i32.add"
            i <- i + 1
        ret f
        endB f
    for dt in [ "$du0"; "$du1" ] do
        lg f "$v"
        gcT f "ref.test" dt
        ifE f
        lg f "$v"
        gg f "$duHash"
        lg f "$v"
        gcT f "ref.cast" dt
        gcTF f "struct.get" dt 0
        gcT f "array.get" "$vt"
        gcT f "ref.cast" "$v1"
        callRef f "$v1"
        gcAbs f "ref.cast" "i31"
        i31get f
        ret f
        endB f
    lg f "$v"
    gcT f "ref.test" "$str"
    ifE f
    ic f -2128831035
    ls f "$h"
    blockE f "$hd"
    loopE f "$hgo"
    lg f "$i"
    lg f "$v"
    gcT f "ref.cast" "$str"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$hd"
    lg f "$h"
    lg f "$v"
    gcT f "ref.cast" "$str"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ins f "i32.xor"
    ic f 16777619
    ins f "i32.mul"
    ls f "$h"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$hgo"
    endB f
    endB f
    lg f "$h"
    ret f
    endB f
    lg f "$v"
    ins f "ref.is_null"
    ifE f
    ic f 0
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$cons"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 0
    callf f "$hashv"
    ic f 31
    ins f "i32.mul"
    lg f "$v"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    callf f "$hashv"
    ins f "i32.xor"
    ret f
    endB f
    ic f 1
    endFn f
    // $cmpv: structural three-way comparison
    let f = beginFn m [ "$a"; "$b" ]
    local f "$i" "i32"
    local f "$la" "i32"
    local f "$lb" "i32"
    local f "$x" "i32"
    local f "$y" "i32"
    local f "$c" "i32"
    localsDone f
    lg f "$a"
    gcT f "ref.test" "$str"
    lg f "$b"
    gcT f "ref.test" "$str"
    ins f "i32.and"
    ifE f
    lg f "$a"
    gcT f "ref.cast" "$str"
    lg f "$b"
    gcT f "ref.cast" "$str"
    callf f "$strcmp"
    ret f
    endB f
    lg f "$a"
    gcT f "ref.test" "$boxf"
    lg f "$b"
    gcT f "ref.test" "$boxf"
    ins f "i32.and"
    ifE f
    lg f "$a"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    lg f "$b"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    ins f "f64.lt"
    ifE f
    ic f -1
    ret f
    endB f
    lg f "$a"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    lg f "$b"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    ins f "f64.gt"
    ifE f
    ic f 1
    ret f
    endB f
    ic f 0
    ret f
    endB f
    lg f "$a"
    ins f "ref.is_null"
    lg f "$b"
    ins f "ref.is_null"
    ins f "i32.and"
    ifE f
    ic f 0
    ret f
    endB f
    lg f "$a"
    ins f "ref.is_null"
    ifE f
    ic f -1
    ret f
    endB f
    lg f "$b"
    ins f "ref.is_null"
    ifE f
    ic f 1
    ret f
    endB f
    for n in tupArities do
        // tuples compare LEXICOGRAPHICALLY, component by component
        let t = "$tup" + string n
        lg f "$a"
        gcT f "ref.test" t
        lg f "$b"
        gcT f "ref.test" t
        ins f "i32.and"
        ifE f
        for i in 0 .. n - 1 do
            lg f "$a"
            gcT f "ref.cast" t
            gcTF f "struct.get" t i
            lg f "$b"
            gcT f "ref.cast" t
            gcTF f "struct.get" t i
            callf f "$cmpv"
            ls f "$c"
            lg f "$c"
            ic f 0
            ins f "i32.ne"
            ifE f
            lg f "$c"
            ret f
            endB f
        ic f 0
        ret f
        endB f
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
    callf f "$cmpv"
    ls f "$c"
    lg f "$c"
    ic f 0
    ins f "i32.ne"
    ifE f
    lg f "$c"
    ret f
    endB f
    lg f "$a"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    lg f "$b"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    callf f "$cmpv"
    ret f
    endB f
    // numeric / immediates
    lg f "$a"
    callf f "$toi"
    ls f "$x"
    lg f "$b"
    callf f "$toi"
    ls f "$y"
    lg f "$x"
    lg f "$y"
    ins f "i32.lt_s"
    ifE f
    ic f -1
    ret f
    endB f
    lg f "$x"
    lg f "$y"
    ins f "i32.gt_s"
    ifE f
    ic f 1
    ret f
    endB f
    ic f 0
    endFn f
    // $cmpvBoxed: `compare` as a VALUE
    let f = beginFn m [ "$a"; "$b" ]
    localsDone f
    lg f "$a"
    lg f "$b"
    callf f "$cmpv"
    callf f "$ofi"
    endFn f
    // $hash_du_default: tag, mixed with the payload's hash for a $du1
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    gcT f "ref.test" "$du1"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$du1"
    gcTF f "struct.get" "$du1" 0
    ic f 31
    ins f "i32.mul"
    lg f "$v"
    gcT f "ref.cast" "$du1"
    gcTF f "struct.get" "$du1" 1
    callf f "$hashv"
    ins f "i32.add"
    refI31 f
    ret f
    endB f
    lg f "$v"
    gcT f "ref.cast" "$du0"
    gcTF f "struct.get" "$du0" 0
    refI31 f
    endFn f

// ---- runtime: builtin string members ---------------------------------------
// .NET semantics, deliberately: an empty needle is found at `from`, a
// missing one is -1, Replace scans left to right without overlapping.

let rtTypes8 (m : Mod) : unit =
    tyFunc m "$rt_sii2a" [ "$str"; "i32"; "i32" ] [ "anyref" ]
    tyFunc m "$rt_ssi2i" [ "$str"; "$str"; "i32" ] [ "i32" ]
    tyFunc m "$rt_si2i" [ "$str"; "i32" ] [ "i32" ]
    tyFunc m "$rt_sss2a" [ "$str"; "$str"; "$str" ] [ "anyref" ]
    tyFunc m "$rt_s2a" [ "$str" ] [ "anyref" ]
    tyFunc m "$rt_sa2a" [ "$str"; "anyref" ] [ "anyref" ]

let rtDecls8 (m : Mod) : unit =
    declFn m "$strsub" "$rt_sii2a"
    declFn m "$strFind" "$rt_ssi2i"
    declFn m "$strFindChar" "$rt_si2i"
    declFn m "$strLastFindChar" "$rt_si2i"
    declFn m "$strStarts" "$rt_ss2i"
    declFn m "$strEnds" "$rt_ss2i"
    declFn m "$strSplitChar" "$rt_si2a"
    declFn m "$strReplace" "$rt_sss2a"
    declFn m "$strIsWs" "$rt_i2i"
    declFn m "$strTrim" "$rt_s2a"
    declFn m "$strTrimEndChars" "$rt_sa2a"

let rtCore8 (m : Mod) : unit =
    // $strsub
    let f = beginFn m [ "$s"; "$start"; "$len" ]
    local f "$r" "$str"
    localsDone f
    lg f "$len"
    gcT f "array.new_default" "$str"
    ls f "$r"
    lg f "$r"
    ic f 0
    lg f "$s"
    lg f "$start"
    lg f "$len"
    arrCopy f "$str" "$str"
    lg f "$r"
    endFn f
    // $strFind
    let f = beginFn m [ "$s"; "$p"; "$from" ]
    local f "$i" "i32"
    local f "$j" "i32"
    local f "$ls" "i32"
    local f "$lp" "i32"
    localsDone f
    lg f "$s"
    gci f "array.len"
    ls f "$ls"
    lg f "$p"
    gci f "array.len"
    ls f "$lp"
    lg f "$from"
    ls f "$i"
    lg f "$i"
    ic f 0
    ins f "i32.lt_s"
    ifE f
    ic f 0
    ls f "$i"
    endB f
    lg f "$lp"
    ins f "i32.eqz"
    ifE f
    lg f "$i"
    lg f "$ls"
    lg f "$i"
    lg f "$ls"
    ins f "i32.le_s"
    ins f "select"
    ret f
    endB f
    blockE f "$done"
    loopE f "$outer"
    lg f "$i"
    lg f "$lp"
    ins f "i32.add"
    lg f "$ls"
    ins f "i32.gt_s"
    brIf f "$done"
    ic f 0
    ls f "$j"
    blockE f "$mismatch"
    loopE f "$inner"
    lg f "$j"
    lg f "$lp"
    ins f "i32.ge_u"
    ifE f
    lg f "$i"
    ret f
    endB f
    lg f "$s"
    lg f "$i"
    lg f "$j"
    ins f "i32.add"
    gcT f "array.get_u" "$str"
    lg f "$p"
    lg f "$j"
    gcT f "array.get_u" "$str"
    ins f "i32.ne"
    brIf f "$mismatch"
    lg f "$j"
    ic f 1
    ins f "i32.add"
    ls f "$j"
    br f "$inner"
    endB f
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$outer"
    endB f
    endB f
    ic f -1
    endFn f
    // $strFindChar
    let f = beginFn m [ "$s"; "$c" ]
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
    lg f "$c"
    ins f "i32.eq"
    ifE f
    lg f "$i"
    ret f
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
    endB f
    ic f -1
    endFn f
    // $strLastFindChar
    let f = beginFn m [ "$s"; "$c" ]
    local f "$i" "i32"
    localsDone f
    lg f "$s"
    gci f "array.len"
    ls f "$i"
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    ins f "i32.eqz"
    brIf f "$done"
    lg f "$i"
    ic f 1
    ins f "i32.sub"
    ls f "$i"
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    lg f "$c"
    ins f "i32.eq"
    ifE f
    lg f "$i"
    ret f
    endB f
    br f "$go"
    endB f
    endB f
    ic f -1
    endFn f
    // $strStarts
    let f = beginFn m [ "$s"; "$p" ]
    local f "$i" "i32"
    localsDone f
    lg f "$p"
    gci f "array.len"
    lg f "$s"
    gci f "array.len"
    ins f "i32.gt_u"
    ifE f
    ic f 0
    ret f
    endB f
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    lg f "$p"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$done"
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    lg f "$p"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ins f "i32.ne"
    ifE f
    ic f 0
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
    endFn f
    // $strEnds
    let f = beginFn m [ "$s"; "$p" ]
    local f "$i" "i32"
    local f "$off" "i32"
    localsDone f
    lg f "$p"
    gci f "array.len"
    lg f "$s"
    gci f "array.len"
    ins f "i32.gt_u"
    ifE f
    ic f 0
    ret f
    endB f
    lg f "$s"
    gci f "array.len"
    lg f "$p"
    gci f "array.len"
    ins f "i32.sub"
    ls f "$off"
    blockE f "$done"
    loopE f "$go"
    lg f "$i"
    lg f "$p"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$done"
    lg f "$s"
    lg f "$off"
    lg f "$i"
    ins f "i32.add"
    gcT f "array.get_u" "$str"
    lg f "$p"
    lg f "$i"
    gcT f "array.get_u" "$str"
    ins f "i32.ne"
    ifE f
    ic f 0
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
    endFn f
    // $strSplitChar: n+1 pieces for n separators
    let f = beginFn m [ "$s"; "$c" ]
    local f "$n" "i32"
    local f "$i" "i32"
    local f "$start" "i32"
    local f "$k" "i32"
    local f "$r" "$arr"
    localsDone f
    ic f 1
    ls f "$n"
    blockE f "$cd"
    loopE f "$cg"
    lg f "$i"
    lg f "$s"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$cd"
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    lg f "$c"
    ins f "i32.eq"
    ifE f
    lg f "$n"
    ic f 1
    ins f "i32.add"
    ls f "$n"
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$cg"
    endB f
    endB f
    lg f "$n"
    gcT f "array.new_default" "$arr"
    ls f "$r"
    ic f 0
    ls f "$i"
    blockE f "$sd"
    loopE f "$sg"
    lg f "$i"
    lg f "$s"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$sd"
    lg f "$s"
    lg f "$i"
    gcT f "array.get_u" "$str"
    lg f "$c"
    ins f "i32.eq"
    ifE f
    lg f "$r"
    lg f "$k"
    lg f "$s"
    lg f "$start"
    lg f "$i"
    lg f "$start"
    ins f "i32.sub"
    callf f "$strsub"
    gcT f "array.set" "$arr"
    lg f "$k"
    ic f 1
    ins f "i32.add"
    ls f "$k"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$start"
    endB f
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$sg"
    endB f
    endB f
    lg f "$r"
    lg f "$k"
    lg f "$s"
    lg f "$start"
    lg f "$s"
    gci f "array.len"
    lg f "$start"
    ins f "i32.sub"
    callf f "$strsub"
    gcT f "array.set" "$arr"
    lg f "$r"
    endFn f
    // $strReplace
    let f = beginFn m [ "$s"; "$a"; "$b" ]
    local f "$i" "i32"
    local f "$at" "i32"
    local f "$acc" "anyref"
    localsDone f
    ic f 0
    gcT f "array.new_default" "$str"
    ls f "$acc"
    lg f "$a"
    gci f "array.len"
    ins f "i32.eqz"
    ifE f
    lg f "$s"
    ret f
    endB f
    blockE f "$done"
    loopE f "$go"
    lg f "$s"
    lg f "$a"
    lg f "$i"
    callf f "$strFind"
    ls f "$at"
    lg f "$at"
    ic f 0
    ins f "i32.lt_s"
    brIf f "$done"
    lg f "$acc"
    gcT f "ref.cast" "$str"
    lg f "$s"
    lg f "$i"
    lg f "$at"
    lg f "$i"
    ins f "i32.sub"
    callf f "$strsub"
    gcT f "ref.cast" "$str"
    callf f "$strcat"
    ls f "$acc"
    lg f "$acc"
    gcT f "ref.cast" "$str"
    lg f "$b"
    callf f "$strcat"
    ls f "$acc"
    // past the match, never into it: replacements do not overlap
    lg f "$at"
    lg f "$a"
    gci f "array.len"
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
    endB f
    lg f "$acc"
    gcT f "ref.cast" "$str"
    lg f "$s"
    lg f "$i"
    lg f "$s"
    gci f "array.len"
    lg f "$i"
    ins f "i32.sub"
    callf f "$strsub"
    gcT f "ref.cast" "$str"
    callf f "$strcat"
    endFn f
    // $strIsWs
    let f = beginFn m [ "$c" ]
    localsDone f
    lg f "$c"
    ic f 32
    ins f "i32.eq"
    for ws in [ 9; 10; 13; 11; 12 ] do
        lg f "$c"
        ic f ws
        ins f "i32.eq"
        ins f "i32.or"
    endFn f
    // $strTrim
    let f = beginFn m [ "$s" ]
    local f "$a" "i32"
    local f "$b" "i32"
    localsDone f
    lg f "$s"
    gci f "array.len"
    ls f "$b"
    blockE f "$ld"
    loopE f "$lg"
    lg f "$a"
    lg f "$b"
    ins f "i32.ge_u"
    brIf f "$ld"
    lg f "$s"
    lg f "$a"
    gcT f "array.get_u" "$str"
    callf f "$strIsWs"
    ins f "i32.eqz"
    brIf f "$ld"
    lg f "$a"
    ic f 1
    ins f "i32.add"
    ls f "$a"
    br f "$lg"
    endB f
    endB f
    blockE f "$rd"
    loopE f "$rg"
    lg f "$a"
    lg f "$b"
    ins f "i32.ge_u"
    brIf f "$rd"
    lg f "$s"
    lg f "$b"
    ic f 1
    ins f "i32.sub"
    gcT f "array.get_u" "$str"
    callf f "$strIsWs"
    ins f "i32.eqz"
    brIf f "$rd"
    lg f "$b"
    ic f 1
    ins f "i32.sub"
    ls f "$b"
    br f "$rg"
    endB f
    endB f
    lg f "$s"
    lg f "$a"
    lg f "$b"
    lg f "$a"
    ins f "i32.sub"
    callf f "$strsub"
    endFn f
    // $strTrimEndChars — the char array is PACKED i32, like the text
    // emitter's
    let f = beginFn m [ "$s"; "$cs" ]
    local f "$b" "i32"
    local f "$j" "i32"
    local f "$hit" "i32"
    local f "$c" "i32"
    localsDone f
    lg f "$s"
    gci f "array.len"
    ls f "$b"
    blockE f "$done"
    loopE f "$go"
    lg f "$b"
    ins f "i32.eqz"
    brIf f "$done"
    lg f "$s"
    lg f "$b"
    ic f 1
    ins f "i32.sub"
    gcT f "array.get_u" "$str"
    ls f "$c"
    ic f 0
    ls f "$hit"
    ic f 0
    ls f "$j"
    blockE f "$sd"
    loopE f "$sg"
    lg f "$j"
    lg f "$cs"
    gcT f "ref.cast" "$parr_i"
    gci f "array.len"
    ins f "i32.ge_u"
    brIf f "$sd"
    lg f "$cs"
    gcT f "ref.cast" "$parr_i"
    lg f "$j"
    gcT f "array.get" "$parr_i"
    lg f "$c"
    ins f "i32.eq"
    ifE f
    ic f 1
    ls f "$hit"
    br f "$sd"
    endB f
    lg f "$j"
    ic f 1
    ins f "i32.add"
    ls f "$j"
    br f "$sg"
    endB f
    endB f
    lg f "$hit"
    ins f "i32.eqz"
    brIf f "$done"
    lg f "$b"
    ic f 1
    ins f "i32.sub"
    ls f "$b"
    br f "$go"
    endB f
    endB f
    lg f "$s"
    ic f 0
    lg f "$b"
    callf f "$strsub"
    endFn f

// ---- runtime: printf-family formatting helpers ------------------------------

let private F5EM7 = 0x3EA0C6F7A0B5ED8DL

let rtDecls10 (m : Mod) : unit =
    declFn m "$xput" "$rt_xput"
    declFn m "$ltobase" "$rt_lbase2a"
    declFn m "$itobase" "$rt_ibase2a"
    declFn m "$ftoa6" "$rt_f2a"
    declFn m "$showv" "$rt_a2a"

let rtTypes10 (m : Mod) : unit =
    tyFunc m "$rt_xput" [ "$str"; "i32"; "i64"; "i64"; "i32" ] [ "i32" ]
    tyFunc m "$rt_lbase2a" [ "i64"; "i64"; "i32" ] [ "anyref" ]
    tyFunc m "$rt_ibase2a" [ "i32"; "i32"; "i32" ] [ "anyref" ]

let rtCore10 (m : Mod) : unit =
    // $xput: hex/octal digits of an i64 magnitude
    let f = beginFn m [ "$s"; "$p"; "$n"; "$base"; "$upper" ]
    local f "$m" "i64"
    local f "$d" "i32"
    localsDone f
    lg f "$n"
    lg f "$base"
    ins f "i64.div_u"
    ls f "$m"
    lg f "$m"
    lc f 0L
    ins f "i64.gt_u"
    ifE f
    lg f "$s"
    lg f "$p"
    lg f "$m"
    lg f "$base"
    lg f "$upper"
    callf f "$xput"
    ls f "$p"
    endB f
    lg f "$n"
    lg f "$base"
    ins f "i64.rem_u"
    ins f "i32.wrap_i64"
    ls f "$d"
    lg f "$s"
    lg f "$p"
    lg f "$d"
    ic f 10
    ins f "i32.lt_u"
    ifV f "i32"
    ic f 48
    lg f "$d"
    ins f "i32.add"
    elseB f
    ic f 55
    ic f 87
    lg f "$upper"
    ins f "select"
    lg f "$d"
    ins f "i32.add"
    endB f
    callf f "$sput"
    endFn f
    // $ltobase
    let f = beginFn m [ "$n"; "$base"; "$upper" ]
    local f "$s" "$str"
    local f "$p" "i32"
    localsDone f
    ic f 24
    gcT f "array.new_default" "$str"
    ls f "$s"
    lg f "$s"
    ic f 0
    lg f "$n"
    lg f "$base"
    lg f "$upper"
    callf f "$xput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    endFn f
    // $itobase: an i32 formats via its UNSIGNED 32-bit reading
    let f = beginFn m [ "$n"; "$base"; "$upper" ]
    local f "$s" "$str"
    local f "$p" "i32"
    localsDone f
    ic f 24
    gcT f "array.new_default" "$str"
    ls f "$s"
    lg f "$s"
    lg f "$p"
    lg f "$n"
    ins f "i64.extend_i32_u"
    lc f 0xffffffffL
    ins f "i64.and"
    lg f "$base"
    ins f "i64.extend_i32_u"
    lg f "$upper"
    callf f "$xput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    endFn f
    // $ftoa6: %f is .NET's fixed-six-decimals form
    let f = beginFn m [ "$v" ]
    local f "$s" "$str"
    local f "$p" "i32"
    local f "$ip" "f64"
    local f "$frac" "f64"
    local f "$k" "i32"
    local f "$d" "i32"
    localsDone f
    ic f 40
    gcT f "array.new_default" "$str"
    ls f "$s"
    lg f "$v"
    lg f "$v"
    ins f "f64.ne"
    ifE f
    for c in [ 78; 97; 78 ] do
        lg f "$s"
        lg f "$p"
        ic f c
        callf f "$sput"
        ls f "$p"
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    ret f
    endB f
    lg f "$v"
    fc f 0L
    ins f "f64.lt"
    ifE f
    lg f "$s"
    lg f "$p"
    ic f 45
    callf f "$sput"
    ls f "$p"
    lg f "$v"
    ins f "f64.neg"
    ls f "$v"
    endB f
    lg f "$v"
    fc f F1E18
    ins f "f64.ge"
    ifE f
    lg f "$v"
    callf f "$ftoa"
    ret f
    endB f
    // round at the sixth decimal first, so 0.0000005 carries
    lg f "$v"
    fc f F5EM7
    ins f "f64.add"
    ls f "$v"
    lg f "$v"
    ins f "f64.floor"
    ls f "$ip"
    lg f "$s"
    lg f "$p"
    lg f "$ip"
    ins f "i64.trunc_f64_s"
    callf f "$lput"
    ls f "$p"
    lg f "$s"
    lg f "$p"
    ic f 46
    callf f "$sput"
    ls f "$p"
    lg f "$v"
    lg f "$ip"
    ins f "f64.sub"
    ls f "$frac"
    blockE f "$done"
    loopE f "$go"
    lg f "$k"
    ic f 6
    ins f "i32.ge_s"
    brIf f "$done"
    lg f "$frac"
    fc f F10
    ins f "f64.mul"
    ls f "$frac"
    lg f "$frac"
    ins f "f64.floor"
    ins f "i32.trunc_f64_s"
    ls f "$d"
    lg f "$s"
    lg f "$p"
    ic f 48
    lg f "$d"
    ins f "i32.add"
    callf f "$sput"
    ls f "$p"
    lg f "$frac"
    lg f "$frac"
    ins f "f64.floor"
    ins f "f64.sub"
    ls f "$frac"
    lg f "$k"
    ic f 1
    ins f "i32.add"
    ls f "$k"
    br f "$go"
    endB f
    endB f
    lg f "$s"
    lg f "$p"
    callf f "$strTake"
    endFn f
    // $showv: %A at an unknown hole — dispatch on the representation
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    ins f "ref.is_null"
    ifE f
    for c in [ 110; 117; 108; 108 ] do ic f c
    arrNewFixed f "$str" 4
    ret f
    endB f
    lg f "$v"
    gcAbs f "ref.test" "i31"
    ifE f
    lg f "$v"
    gcAbs f "ref.cast" "i31"
    i31get f
    callf f "$itoa"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxi"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxi"
    gcTF f "struct.get" "$boxi" 0
    callf f "$itoa"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxl"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxl"
    gcTF f "struct.get" "$boxl" 0
    callf f "$ltoa"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxf"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    callf f "$ftoa"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxs"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxs"
    gcTF f "struct.get" "$boxs" 0
    ins f "f64.promote_f32"
    callf f "$ftoa"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$str"
    ifE f
    // %A quotes strings, as F# does
    ic f 34
    arrNewFixed f "$str" 1
    lg f "$v"
    gcT f "ref.cast" "$str"
    callf f "$strcat"
    gcT f "ref.cast" "$str"
    ic f 34
    arrNewFixed f "$str" 1
    callf f "$strcat"
    ret f
    endB f
    ic f 63
    arrNewFixed f "$str" 1
    endFn f

// ---- runtime: list append and the half-precision rounder --------------------

let rtTypes11 (m : Mod) : unit =
    tyFunc m "$rt_f2i" [ "f64" ] [ "i32" ]

let rtDecls11 (m : Mod) : unit =
    declFn m "$append" "$u1"
    declFn m "$f2h64" "$rt_f2i"

let rtCore11 (m : Mod) : unit =
    // $append: rebuild the left spine onto the right
    let f = beginFn m [ "$a"; "$b" ]
    localsDone f
    lg f "$a"
    gcT f "ref.test" "$cons"
    ifA f
    lg f "$a"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 0
    lg f "$a"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    lg f "$b"
    callf f "$append"
    gcT f "struct.new" "$cons"
    elseB f
    lg f "$b"
    endB f
    endFn f
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

// ---- runtime: half-precision widen/narrow -----------------------------------

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
// A POD struct array is a $hnd over i64 words ($pk) — C-image layout.
// Pinning copies the words into linear memory (the GC side is dropped while
// pinned); unpinning copies back. The word accessors dispatch on which side
// currently holds the data.

let rtTypes13 (m : Mod) : unit =
    tyFunc m "$rt_ai2l" [ "anyref"; "i32" ] [ "i64" ]
    tyFunc m "$rt_ail2v" [ "anyref"; "i32"; "i64" ] []

let rtDecls13 (m : Mod) : unit =
    declFn m "$balloc" "$rt_i2i"
    declFn m "$pinh" "$rt_a2i"
    declFn m "$unpinh" "$rt_a2i"
    declFn m "$hwget" "$rt_ai2l"
    declFn m "$hwset" "$rt_ail2v"
    declFn m "$hlen" "$rt_a2i"

let rtCore13 (m : Mod) : unit =
    // $balloc: bump allocator over the pin pages, 8-aligned
    let f = beginFn m [ "$bytes" ]
    local f "$p" "i32"
    localsDone f
    gg f "$heap"
    ls f "$p"
    lg f "$p"
    lg f "$bytes"
    ins f "i32.add"
    ic f 7
    ins f "i32.add"
    ic f -8
    ins f "i32.and"
    gs f "$heap"
    lg f "$p"
    endFn f
    // $pinh: copy the words to linear memory, drop the GC side
    let f = beginFn m [ "$h" ]
    local f "$s" "anyref"
    local f "$n" "i32"
    local f "$i" "i32"
    local f "$p" "i32"
    localsDone f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    ls f "$s"
    lg f "$s"
    ins f "ref.is_null"
    ifE f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 1
    ret f
    endB f
    lg f "$s"
    gcT f "ref.cast" "$pk"
    gci f "array.len"
    ls f "$n"
    lg f "$n"
    ic f 8
    ins f "i32.mul"
    callf f "$balloc"
    ls f "$p"
    blockE f "$d"
    loopE f "$go"
    lg f "$i"
    lg f "$n"
    ins f "i32.ge_u"
    brIf f "$d"
    lg f "$p"
    lg f "$i"
    ic f 8
    ins f "i32.mul"
    ins f "i32.add"
    lg f "$s"
    gcT f "ref.cast" "$pk"
    lg f "$i"
    gcT f "array.get" "$pk"
    mem f "i64.store"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
    endB f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    lg f "$p"
    gcTF f "struct.set" "$hnd" 1
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    lg f "$n"
    gcTF f "struct.set" "$hnd" 2
    // drop the GC storage: managed side is reclaimed while pinned
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    refNull f "none"
    gcTF f "struct.set" "$hnd" 0
    lg f "$p"
    endFn f
    // $unpinh: copy linear memory back into fresh GC words
    let f = beginFn m [ "$h" ]
    local f "$s" "anyref"
    local f "$n" "i32"
    local f "$i" "i32"
    local f "$p" "i32"
    localsDone f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    ins f "ref.is_null"
    ins f "i32.eqz"
    ifE f
    ic f 0
    ret f
    endB f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 2
    ls f "$n"
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 1
    ls f "$p"
    lg f "$n"
    gcT f "array.new_default" "$pk"
    ls f "$s"
    blockE f "$d"
    loopE f "$go"
    lg f "$i"
    lg f "$n"
    ins f "i32.ge_u"
    brIf f "$d"
    lg f "$s"
    gcT f "ref.cast" "$pk"
    lg f "$i"
    lg f "$p"
    lg f "$i"
    ic f 8
    ins f "i32.mul"
    ins f "i32.add"
    mem f "i64.load"
    gcT f "array.set" "$pk"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    ls f "$i"
    br f "$go"
    endB f
    endB f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    lg f "$s"
    gcT f "ref.cast" "$pk"
    gcTF f "struct.set" "$hnd" 0
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    ic f 0
    gcTF f "struct.set" "$hnd" 1
    ic f 0
    endFn f
    // $hwget: one i64 word through the handle, wherever the data lives
    let f = beginFn m [ "$h"; "$i" ]
    localsDone f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    ins f "ref.is_null"
    ifV f "i64"
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 1
    lg f "$i"
    ic f 8
    ins f "i32.mul"
    ins f "i32.add"
    mem f "i64.load"
    elseB f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    gcT f "ref.cast" "$pk"
    lg f "$i"
    gcT f "array.get" "$pk"
    endB f
    endFn f
    // $hwset
    let f = beginFn m [ "$h"; "$i"; "$v" ]
    localsDone f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    ins f "ref.is_null"
    ifE f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 1
    lg f "$i"
    ic f 8
    ins f "i32.mul"
    ins f "i32.add"
    lg f "$v"
    mem f "i64.store"
    elseB f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    gcT f "ref.cast" "$pk"
    lg f "$i"
    lg f "$v"
    gcT f "array.set" "$pk"
    endB f
    endFn f
    // $hlen: word count
    let f = beginFn m [ "$h" ]
    localsDone f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    ins f "ref.is_null"
    ifV f "i32"
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 2
    elseB f
    lg f "$h"
    gcT f "ref.cast" "$hnd"
    gcTF f "struct.get" "$hnd" 0
    gcT f "ref.cast" "$pk"
    gci f "array.len"
    endB f
    endFn f

// ---- runtime: enumeration protocol and object identity helpers -------------
// Lists and arrays ARE seqs but carry no vtable: $iterNew wraps whichever
// representation arrives, $iterNext/$iterCur drive it.

let rtTypes9 (m : Mod) : unit =
    tyFunc m "$rt_ai2a" [ "anyref"; "i32" ] [ "anyref" ]
    tyFunc m "$rt_siii2a" [ "$str"; "i32"; "i32"; "i32" ] [ "anyref" ]

let rtDecls9 (m : Mod) : unit =
    declFn m "$isBuiltinSeq" "$rt_a2i"
    declFn m "$isArrayRep" "$rt_a2i"
    declFn m "$iterNew" "$rt_a2a"
    declFn m "$arrGetAny" "$rt_ai2a"
    declFn m "$iterNext" "$rt_a2a"
    declFn m "$iterCur" "$rt_a2a"
    declFn m "$hashvBoxed" "$v1"
    declFn m "$strPad" "$rt_siii2a"

let rtCore9 (m : Mod) : unit =
    // $isBuiltinSeq
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    ins f "ref.is_null"
    for ty in [ "$cons"; "$arr"; "$parr_i"; "$parr_f"; "$parr_s"; "$parr_l"; "$parr_h" ] do
        lg f "$v"
        gcT f "ref.test" ty
        ins f "i32.or"
    endFn f
    // $isArrayRep
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    gcT f "ref.test" "$arr"
    for ty in [ "$parr_i"; "$parr_f"; "$parr_s"; "$parr_l"; "$parr_h" ] do
        lg f "$v"
        gcT f "ref.test" ty
        ins f "i32.or"
    endFn f
    // $iterNew: mode 0 = list (cons chain), mode 1 = array (indexing)
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    ins f "ref.is_null"
    lg f "$v"
    gcT f "ref.test" "$cons"
    ins f "i32.or"
    ifA f
    ic f 0
    refNull f "any"
    lg f "$v"
    ic f 0
    gcT f "struct.new" "$iter"
    elseB f
    ic f 1
    lg f "$v"
    refNull f "any"
    ic f 0
    gcT f "struct.new" "$iter"
    endB f
    endFn f
    // $arrGetAny: one element of ANY array representation, boxed uniformly
    let f = beginFn m [ "$v"; "$i" ]
    localsDone f
    lg f "$v"
    gcT f "ref.test" "$arr"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$arr"
    lg f "$i"
    gcT f "array.get" "$arr"
    ret f
    endB f
    for ty, box_, get in
        [ "$parr_i", "$ofi", "array.get"
          "$parr_f", "$off", "array.get"
          "$parr_s", "$oss", "array.get"
          "$parr_l", "$ofl", "array.get"
          "$parr_h", "$ofi", "array.get_u" ] do
        lg f "$v"
        gcT f "ref.test" ty
        ifE f
        lg f "$v"
        gcT f "ref.cast" ty
        lg f "$i"
        gcT f get ty
        callf f box_
        ret f
        endB f
    ic f 0
    refI31 f
    endFn f
    // $iterNext
    let f = beginFn m [ "$st" ]
    local f "$it" "$iter"
    local f "$rest" "anyref"
    local f "$i" "i32"
    localsDone f
    lg f "$st"
    gcT f "ref.cast" "$iter"
    ls f "$it"
    lg f "$it"
    gcTF f "struct.get" "$iter" 0
    ins f "i32.eqz"
    ifA f
    // list: advance the cons chain
    lg f "$it"
    gcTF f "struct.get" "$iter" 2
    ls f "$rest"
    lg f "$rest"
    ins f "ref.is_null"
    ifA f
    ic f 0
    refI31 f
    elseB f
    lg f "$it"
    lg f "$rest"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 0
    gcTF f "struct.set" "$iter" 1
    lg f "$it"
    lg f "$rest"
    gcT f "ref.cast" "$cons"
    gcTF f "struct.get" "$cons" 1
    gcTF f "struct.set" "$iter" 2
    ic f 1
    refI31 f
    endB f
    elseB f
    // array: bump the index
    lg f "$it"
    gcTF f "struct.get" "$iter" 3
    ls f "$i"
    lg f "$i"
    lg f "$it"
    gcTF f "struct.get" "$iter" 1
    callf f "$lenv"
    gcAbs f "ref.cast" "i31"
    i31get f
    ins f "i32.ge_s"
    ifA f
    ic f 0
    refI31 f
    elseB f
    lg f "$it"
    lg f "$i"
    ic f 1
    ins f "i32.add"
    gcTF f "struct.set" "$iter" 3
    ic f 1
    refI31 f
    endB f
    endB f
    endFn f
    // $iterCur
    let f = beginFn m [ "$st" ]
    local f "$it" "$iter"
    localsDone f
    lg f "$st"
    gcT f "ref.cast" "$iter"
    ls f "$it"
    lg f "$it"
    gcTF f "struct.get" "$iter" 0
    ins f "i32.eqz"
    ifA f
    lg f "$it"
    gcTF f "struct.get" "$iter" 1
    elseB f
    lg f "$it"
    gcTF f "struct.get" "$iter" 1
    lg f "$it"
    gcTF f "struct.get" "$iter" 3
    ic f 1
    ins f "i32.sub"
    callf f "$arrGetAny"
    endB f
    endFn f
    // $hashvBoxed: `hash` as a VALUE
    let f = beginFn m [ "$v" ]
    localsDone f
    lg f "$v"
    callf f "$hashv"
    callf f "$ofi"
    endFn f
    // $strPad
    let f = beginFn m [ "$v"; "$w"; "$c"; "$left" ]
    local f "$n" "i32"
    local f "$r" "$str"
    local f "$off" "i32"
    localsDone f
    lg f "$v"
    gci f "array.len"
    ls f "$n"
    lg f "$n"
    lg f "$w"
    ins f "i32.ge_u"
    ifE f
    lg f "$v"
    ret f
    endB f
    lg f "$c"
    lg f "$w"
    gcT f "array.new" "$str"
    ls f "$r"
    ic f 0
    lg f "$w"
    lg f "$n"
    ins f "i32.sub"
    lg f "$left"
    ins f "select"
    ls f "$off"
    lg f "$r"
    lg f "$off"
    lg f "$v"
    ic f 0
    lg f "$n"
    arrCopy f "$str" "$str"
    lg f "$r"
    endFn f

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
    lg f "$v"
    gcT f "ref.test" "$boxl"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxl"
    gcTF f "struct.get" "$boxl" 0
    callf f "$printl"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxf"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxf"
    gcTF f "struct.get" "$boxf" 0
    callf f "$printf64"
    ret f
    endB f
    lg f "$v"
    gcT f "ref.test" "$boxs"
    ifE f
    lg f "$v"
    gcT f "ref.cast" "$boxs"
    gcTF f "struct.get" "$boxs" 0
    ins f "f64.promote_f32"
    callf f "$printf64"
    ret f
    endB f
    ic f 63
    callf f "$putc"
    endFn f

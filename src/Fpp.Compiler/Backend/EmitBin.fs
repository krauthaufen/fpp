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
      mutable PatchAt : int }

/// open a body: params get indices 0.., locals follow as they are created
let beginFn (m : Mod) (paramNames : string list) : Fn =
    let f = { M = m; B = m.CodeBody; LocalIdx = dictNew (); LocalTys = vecNew ()
              NParams = List.length paramNames; Labels = labelsNew (); PatchAt = 0 }
    f.PatchAt <- beginPatch m.CodeBody
    let mutable i = 0
    for p in paramNames do
        dictSet f.LocalIdx p i
        i <- i + 1
    f

/// a fresh named local of a given valtype name
let local (f : Fn) (name : string) (ty : string) : unit =
    dictSet f.LocalIdx name (f.NParams + vecLen f.LocalTys)
    vecAdd f.LocalTys ty

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

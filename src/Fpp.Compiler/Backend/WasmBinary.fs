module Fpp.Backend.WasmBinary

open Fpp.Prelude

// The BYTE WRITER for direct binary emission (PLAN.md: "skip the rope").
// `compileExpr` will append instructions here instead of returning strings:
// no intermediate text, no O(depth) copying, and the buffer IS the output.
//
// Everything in this file is plain compiler code in the F#/F++ common
// subset — a byte[] is packed i8 storage now, so growing one is cheap and
// the seam gains nothing.
//
// The three problems binary raises, and where they are solved here:
// - SIZE PREFIXES: function bodies and sections are LEB-length-prefixed and
//   the length is unknown until the scope closes. `beginPatch`/`endPatch`
//   reserve a PADDED 5-byte LEB and overwrite it in place — the spec
//   permits non-minimal LEBs, so nothing is ever moved or copied.
// - LABELS: text `br $done` becomes a RELATIVE DEPTH. `pushLabel`/`popLabel`
//   maintain the block stack and `labelDepth` resolves a name to its depth
//   at the branch site.
// - INDICES are the CALLER's job (a prepass over decls assigns them in
//   declaration order); this file only encodes what it is handed.

type Bytes =
    { mutable Buf : byte[]
      mutable Count : int }

let bytesNew () : Bytes = { Buf = Array.zeroCreate 1024; Count = 0 }

let private grow (b : Bytes) (needed : int) : unit =
    if needed > b.Buf.Length then
        let mutable cap = b.Buf.Length * 2
        while cap < needed do
            cap <- cap * 2
        let bigger : byte[] = Array.zeroCreate cap
        let mutable i = 0
        while i < b.Count do
            bigger.[i] <- b.Buf.[i]
            i <- i + 1
        b.Buf <- bigger

let emitByte (b : Bytes) (v : int) : unit =
    grow b (b.Count + 1)
    b.Buf.[b.Count] <- byte v
    b.Count <- b.Count + 1

let emitBytes (b : Bytes) (src : byte[]) : unit =
    grow b (b.Count + src.Length)
    let mutable i = 0
    while i < src.Length do
        b.Buf.[b.Count + i] <- src.[i]
        i <- i + 1
    b.Count <- b.Count + src.Length

/// A slice of the buffer appended again — how a memoized subtree is
/// re-mentioned without re-walking anything.
let emitSlice (b : Bytes) (start : int) (len : int) : unit =
    grow b (b.Count + len)
    let mutable i = 0
    while i < len do
        b.Buf.[b.Count + i] <- b.Buf.[start + i]
        i <- i + 1
    b.Count <- b.Count + len

/// Append TEXT bytes. The partial conversion runs the emitter in text-bytes
/// mode first: converted cases append directly, unconverted ones build their
/// string as before and append it here ONCE — so each converted ancestor
/// level removes one whole-subtree copy, and the same case structure then
/// carries the switch to opcode bytes.
let emitStr (b : Bytes) (s : string) : unit =
    grow b (b.Count + s.Length)
    let mutable i = 0
    while i < s.Length do
        b.Buf.[b.Count + i] <- byte s.[i]
        i <- i + 1
    b.Count <- b.Count + s.Length

let bytesToArray (b : Bytes) : byte[] =
    let a : byte[] = Array.zeroCreate b.Count
    let mutable i = 0
    while i < b.Count do
        a.[i] <- b.Buf.[i]
        i <- i + 1
    a

// ---- LEB128 ---------------------------------------------------------------

/// unsigned LEB128 (u32 domain; negative input is a caller bug)
let emitU32 (b : Bytes) (v0 : int) : unit =
    // arithmetic shift keeps a negative negative forever — and a negative
    // here is always a failed name lookup, so say so instead of spinning
    if v0 < 0 then failwith "emitU32: negative value (missing type/func/global index)"
    let mutable v = v0
    let mutable go = true
    while go do
        let low = v &&& 0x7f
        v <- v >>> 7
        if v = 0 then
            emitByte b low
            go <- false
        else emitByte b (low ||| 0x80)

/// signed LEB128 over 32 bits (i32.const immediates)
let emitS32 (b : Bytes) (v0 : int) : unit =
    let mutable v = v0
    let mutable go = true
    while go do
        let low = v &&& 0x7f
        v <- v >>> 7
        // arithmetic shift: v is 0 when done for non-negatives, -1 for
        // negatives once only sign bits remain
        if (v = 0 && (low &&& 0x40) = 0) || (v = -1 && (low &&& 0x40) <> 0) then
            emitByte b low
            go <- false
        else emitByte b (low ||| 0x80)

/// signed LEB128 over 64 bits (i64.const immediates)
let emitS64 (b : Bytes) (v0 : int64) : unit =
    let mutable v = v0
    let mutable go = true
    while go do
        let low = int (v &&& 0x7fL)
        v <- v >>> 7
        // the int and int64 comparisons are SEPARATE bindings: mixed in one
        // boolean chain, inference bleeds the operand types into each other
        // and the self-lowering lint gate flags a mismatch (bug noted in
        // PLAN.md; this shape is clearer anyway)
        let signClear = (low &&& 0x40) = 0
        let fin = if signClear then v = 0L else v = -1L
        if fin then
            emitByte b low
            go <- false
        else emitByte b (low ||| 0x80)

/// f64 as its 8 little-endian bytes
let emitF64Bits (b : Bytes) (bits : int64) : unit =
    let mutable i = 0
    while i < 8 do
        emitByte b (int ((bits >>> (i * 8)) &&& 0xffL))
        i <- i + 1

/// f32 as its 4 little-endian bytes
let emitF32Bits (b : Bytes) (bits : int) : unit =
    let mutable i = 0
    while i < 4 do
        emitByte b ((bits >>> (i * 8)) &&& 0xff)
        i <- i + 1

/// a length-prefixed byte vector (names, data segments)
let emitVec (b : Bytes) (payload : byte[]) : unit =
    emitU32 b payload.Length
    emitBytes b payload

// ---- patched size prefixes ------------------------------------------------

/// Reserve a PADDED 5-byte u32 LEB where a size will go, and remember where
/// the sized region starts. The spec allows non-minimal encodings, so the
/// patch never moves a byte.
let beginPatch (b : Bytes) : int =
    let at = b.Count
    emitByte b 0x80
    emitByte b 0x80
    emitByte b 0x80
    emitByte b 0x80
    emitByte b 0x00
    at

/// Write the size of everything emitted since the reservation into it.
let endPatch (b : Bytes) (at : int) : unit =
    let size = b.Count - (at + 5)
    let mutable v = size
    let mutable i = 0
    while i < 4 do
        b.Buf.[at + i] <- byte ((v &&& 0x7f) ||| 0x80)
        v <- v >>> 7
        i <- i + 1
    b.Buf.[at + 4] <- byte (v &&& 0x7f)

// ---- label resolution -----------------------------------------------------

/// The block stack of the function being emitted. `br` in binary wasm takes
/// how many enclosing blocks to break OUT of, counted from the innermost.
type Labels =
    { mutable Names : string[]
      mutable Depth : int }

let labelsNew () : Labels = { Names = Array.zeroCreate 64; Depth = 0 }

let pushLabel (ls : Labels) (name : string) : unit =
    if ls.Depth >= ls.Names.Length then
        let bigger : string[] = Array.zeroCreate (ls.Names.Length * 2)
        let mutable i = 0
        while i < ls.Depth do
            bigger.[i] <- ls.Names.[i]
            i <- i + 1
        ls.Names <- bigger
    ls.Names.[ls.Depth] <- name
    ls.Depth <- ls.Depth + 1

let popLabel (ls : Labels) : unit = ls.Depth <- ls.Depth - 1

/// Innermost binding of `name` wins, exactly as named labels shadow in text.
/// -1 means the label is not in scope — the caller reports it.
let labelDepth (ls : Labels) (name : string) : int =
    let mutable i = ls.Depth - 1
    let mutable found = -1
    while found < 0 && i >= 0 do
        if ls.Names.[i] = name then found <- ls.Depth - 1 - i
        i <- i - 1
    found

// ---- opcodes --------------------------------------------------------------
// The closed instruction set the emitter uses (inventoried from the emitted
// compiler itself). Plain ops encode as one byte; GC ops as 0xFB + sub-op.
// Cases call these by NAME through `opByte`/`gcByte`, so a typo is an error
// at emission, not a corrupt module.

let opByte (name : string) : int =
    match name with
    | "unreachable" -> 0x00
    | "nop" -> 0x01
    | "throw" -> 0x08
    | "drop" -> 0x1A
    | "select" -> 0x1B
    | "i32.eqz" -> 0x45 | "i32.eq" -> 0x46 | "i32.ne" -> 0x47
    | "i32.lt_s" -> 0x48 | "i32.lt_u" -> 0x49 | "i32.gt_s" -> 0x4A | "i32.gt_u" -> 0x4B
    | "i32.le_s" -> 0x4C | "i32.le_u" -> 0x4D | "i32.ge_s" -> 0x4E | "i32.ge_u" -> 0x4F
    | "i64.eqz" -> 0x50 | "i64.eq" -> 0x51 | "i64.ne" -> 0x52
    | "i64.lt_s" -> 0x53 | "i64.lt_u" -> 0x54 | "i64.gt_s" -> 0x55 | "i64.gt_u" -> 0x56
    | "i64.le_s" -> 0x57 | "i64.le_u" -> 0x58 | "i64.ge_s" -> 0x59 | "i64.ge_u" -> 0x5A
    | "f32.eq" -> 0x5B | "f32.ne" -> 0x5C | "f32.lt" -> 0x5D | "f32.gt" -> 0x5E
    | "f32.le" -> 0x5F | "f32.ge" -> 0x60
    | "f64.eq" -> 0x61 | "f64.ne" -> 0x62 | "f64.lt" -> 0x63 | "f64.gt" -> 0x64
    | "f64.le" -> 0x65 | "f64.ge" -> 0x66
    | "i32.add" -> 0x6A | "i32.sub" -> 0x6B | "i32.mul" -> 0x6C
    | "i32.div_s" -> 0x6D | "i32.div_u" -> 0x6E | "i32.rem_s" -> 0x6F | "i32.rem_u" -> 0x70
    | "i32.and" -> 0x71 | "i32.or" -> 0x72 | "i32.xor" -> 0x73
    | "i32.shl" -> 0x74 | "i32.shr_s" -> 0x75 | "i32.shr_u" -> 0x76
    | "i64.add" -> 0x7C | "i64.sub" -> 0x7D | "i64.mul" -> 0x7E
    | "i64.div_s" -> 0x7F | "i64.div_u" -> 0x80 | "i64.rem_s" -> 0x81 | "i64.rem_u" -> 0x82
    | "i64.and" -> 0x83 | "i64.or" -> 0x84 | "i64.xor" -> 0x85
    | "i64.shl" -> 0x86 | "i64.shr_s" -> 0x87 | "i64.shr_u" -> 0x88
    | "f32.abs" -> 0x8B | "f32.neg" -> 0x8C | "f32.ceil" -> 0x8D | "f32.floor" -> 0x8E
    | "f32.trunc" -> 0x8F | "f32.sqrt" -> 0x91
    | "f32.add" -> 0x92 | "f32.sub" -> 0x93 | "f32.mul" -> 0x94 | "f32.div" -> 0x95
    | "f64.abs" -> 0x99 | "f64.neg" -> 0x9A | "f64.ceil" -> 0x9B | "f64.floor" -> 0x9C
    | "f64.trunc" -> 0x9D | "f64.sqrt" -> 0x9F
    | "f64.add" -> 0xA0 | "f64.sub" -> 0xA1 | "f64.mul" -> 0xA2 | "f64.div" -> 0xA3
    | "i32.wrap_i64" -> 0xA7
    | "i32.trunc_f32_s" -> 0xA8 | "i32.trunc_f32_u" -> 0xA9
    | "i32.trunc_f64_s" -> 0xAA | "i32.trunc_f64_u" -> 0xAB
    | "i64.extend_i32_s" -> 0xAC | "i64.extend_i32_u" -> 0xAD
    | "i64.trunc_f32_s" -> 0xAE | "i64.trunc_f32_u" -> 0xAF
    | "i64.trunc_f64_s" -> 0xB0 | "i64.trunc_f64_u" -> 0xB1
    | "f32.convert_i32_s" -> 0xB2 | "f32.convert_i32_u" -> 0xB3 | "f32.convert_i64_s" -> 0xB4
    | "f32.demote_f64" -> 0xB6
    | "f64.convert_i32_s" -> 0xB7 | "f64.convert_i32_u" -> 0xB8 | "f64.convert_i64_s" -> 0xB9
    | "f64.promote_f32" -> 0xBB
    | "i32.reinterpret_f32" -> 0xBC | "i64.reinterpret_f64" -> 0xBD
    | "f32.reinterpret_i32" -> 0xBE | "f64.reinterpret_i64" -> 0xBF
    | "ref.null" -> 0xD0 | "ref.is_null" -> 0xD1 | "ref.func" -> 0xD2
    | "ref.eq" -> 0xD3 | "ref.as_non_null" -> 0xD4
    | _ -> -1

/// GC sub-opcodes (encoded as 0xFB + this as u32 LEB)
let gcByte (name : string) : int =
    match name with
    | "struct.new" -> 0 | "struct.new_default" -> 1
    | "struct.get" -> 2 | "struct.get_s" -> 3 | "struct.get_u" -> 4 | "struct.set" -> 5
    | "array.new" -> 6 | "array.new_default" -> 7 | "array.new_fixed" -> 8
    | "array.new_data" -> 9 | "array.new_elem" -> 10
    | "array.get" -> 11 | "array.get_s" -> 12 | "array.get_u" -> 13 | "array.set" -> 14
    | "array.len" -> 15 | "array.fill" -> 16 | "array.copy" -> 17
    | "ref.test" -> 20 | "ref.test_null" -> 21 | "ref.cast" -> 22 | "ref.cast_null" -> 23
    | "ref.i31" -> 28 | "i31.get_s" -> 29 | "i31.get_u" -> 30
    | _ -> -1

// memory ops carry align+offset immediates
let memByte (name : string) : int =
    match name with
    | "i32.load" -> 0x28 | "i64.load" -> 0x29 | "f32.load" -> 0x2A | "f64.load" -> 0x2B
    | "i32.store" -> 0x36 | "i64.store" -> 0x37 | "f32.store" -> 0x38 | "f64.store" -> 0x39
    | "i32.store8" -> 0x3A
    | "i32.load8_u" -> 0x2D | "i32.load16_u" -> 0x2F | "i32.store16" -> 0x3B
    | _ -> -1

// ---- types ----------------------------------------------------------------
// abstract heap types, as the SIGNED s33 the binary format wants
let heapByte (name : string) : int =
    match name with
    | "nofunc" -> 0x73 | "noextern" -> 0x72 | "none" -> 0x71
    | "func" -> 0x70 | "extern" -> 0x6F | "any" -> 0x6E
    | "eq" -> 0x6D | "i31" -> 0x6C | "struct" -> 0x6B | "array" -> 0x6A
    | _ -> -1

let valByte (name : string) : int =
    match name with
    | "i32" -> 0x7F | "i64" -> 0x7E | "f32" -> 0x7D | "f64" -> 0x7C
    | "i8" -> 0x78 | "i16" -> 0x77
    | "anyref" -> 0x6E | "funcref" -> 0x70 | "eqref" -> 0x6D
    | _ -> -1

/// (ref $t) / (ref null $t) with a CONCRETE type index
let emitRefType (b : Bytes) (nullable : bool) (tyIdx : int) : unit =
    emitByte b (if nullable then 0x63 else 0x64)
    emitS32 b tyIdx

/// (ref null any) etc — abstract heap type
let emitRefAbs (b : Bytes) (nullable : bool) (heap : string) : unit =
    emitByte b (if nullable then 0x63 else 0x64)
    emitByte b (heapByte heap)

// composite type headers for the type section
let emitFuncTypeHead (b : Bytes) : unit = emitByte b 0x60
let emitStructHead (b : Bytes) : unit = emitByte b 0x5F
let emitArrayHead (b : Bytes) : unit = emitByte b 0x5E
/// (sub $base ...) — non-final subtype with one supertype
let emitSubHead (b : Bytes) (baseIdx : int) : unit =
    emitByte b 0x50
    emitU32 b 1
    emitU32 b baseIdx
/// field: storage type + mutability
let emitField (b : Bytes) (mut : bool) (emitStorage : Bytes -> unit) : unit =
    emitStorage b
    emitByte b (if mut then 1 else 0)

// blocktype: empty, one valtype, or a type index (multi-result)
let emitBlockTypeEmpty (b : Bytes) : unit = emitByte b 0x40
let emitBlockTypeVal (b : Bytes) (v : int) : unit = emitByte b v
let emitBlockTypeIdx (b : Bytes) (tyIdx : int) : unit = emitS32 b tyIdx

// control opcodes (block/loop/if emit at OPEN, end at CLOSE)
let opBlock = 0x02
let opLoop = 0x03
let opIf = 0x04
let opElse = 0x05
let opEnd = 0x0B
let opBr = 0x0C
let opBrIf = 0x0D
let opReturn = 0x0F
let opCall = 0x10
let opReturnCall = 0x12
let opCallRef = 0x14
let opTryTable = 0x1F
let opLocalGet = 0x20
let opLocalSet = 0x21
let opLocalTee = 0x22
let opGlobalGet = 0x23
let opGlobalSet = 0x24
let opI32Const = 0x41
let opI64Const = 0x42
let opF32Const = 0x43
let opF64Const = 0x44
let opGcPrefix = 0xFB

/// one section: id byte, patched size, payload written by `fill`
let emitSection (b : Bytes) (id : int) (fill : Bytes -> unit) : unit =
    emitByte b id
    let at = beginPatch b
    fill b
    endPatch b at

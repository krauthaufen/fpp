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

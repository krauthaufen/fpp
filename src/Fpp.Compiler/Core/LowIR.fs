/// LowIR — a small machine-level IR shared by the linear/tagged backends
/// (the C backend over fpprt and the direct wasm-linear backend). It sits
/// below Core: lambda-lifted, match-compiled, with data layout made
/// explicit. There are NO tag/box/unbox primitives — Core lowers those to
/// shifts, allocations and loads, so LowIR is honest machine work and the
/// representation-aware optimisations (box elimination, alloc sinking, not
/// materialising a struct for a POD) finally have one place to live.
///
/// A value in LowIR is a machine word `W` (a tagged value or a raw pointer:
/// i32 on wasm-linear, intptr_t in C) or a wide payload (`I64`/`F64`) that a
/// box holds. A backend is instruction selection over this tree: the C
/// backend needs no register allocation (C locals are virtual registers), the
/// wasm-linear backend colours locals by liveness, and an eventual x64/arm64
/// backend slots in as one more selector with real register allocation.
module Fpp.Core.LowIR

/// Machine types. `W` is the tagged value / pointer word. `I64`/`F64` are the
/// wide payloads a box stores; `I8`/`I16` name narrow loads and stores.
type LTy =
    | W
    | I64
    | F64
    /// a SINGLE. float32 is its own primitive type, so it is its own machine
    /// type too: f32 locals, f32 arithmetic, and a 4-byte slot in memory.
    | F32
    | I8
    | I16

/// A local in a lowered function: a dense index plus its machine type. On
/// wasm these become local slots after liveness colouring; in C they are
/// plain declared locals.
type LReg =
    { Id : int
      RTy : LTy }

/// The ALU. Each op is named by its operation AND operand type, so a backend
/// maps one op to exactly one instruction (wasm) or one C operator with no
/// type inference of its own. `S`/`U` suffixes are signed/unsigned.
type LOp =
    /// branchless choose: operands are (then, else, condition) in the order
    /// wasm's `select` pops them. A conditional whose arms are both cheap and
    /// side-effect-free is this, not a branch — `Box3d.ExtendedBy` is six of
    /// them, and clang's wasm emits six `select` where we emitted sixteen
    /// branches.
    | SelV
    // word (i32 / intptr) integer ops
    | AddW | SubW | MulW | DivSW | RemSW
    | AndW | OrW  | XorW | ShlW  | ShrSW | ShrUW
    | EqW  | NeW  | LtSW | GtSW  | LeSW  | GeSW | LtUW | GeUW | GtUW | LeUW
    | DivUW | RemUW
    // 64-bit integer ops
    | AddL | SubL | MulL | DivSL | RemSL | DivUL | RemUL
    | AndL | OrL  | XorL | ShlL  | ShrSL | ShrUL
    | EqL  | NeL  | LtSL | GtSL  | LeSL  | GeSL
    | LtUL | GtUL | LeUL | GeUL
    // double ops
    | AddF | SubF | MulF | DivF | NegF | AbsF | SqrtF | TruncF
    | EqF  | NeF  | LtF  | GtF   | LeF | GeF
    // single ops — the same ALU one width down
    | AddS | SubS | MulS | DivS | NegS | AbsS | SqrtS
    | EqS  | NeS  | LtS  | GtS   | LeS | GeS
    // conversions between machine types
    | WToL | LToW | WToF | FToW | LToF | FToL
    // the UNSIGNED widenings. Without them `float 4000000000u` came out
    // negative and `int64 4000000000u` sign-extended — the signed op is not
    // a conversion for a value whose type says the top bit is a magnitude.
    | WUToL | WUToF | LUToF
    // float32 packing: an f32 never lives in a local (no F32 LTy) — it appears
    // only transiently on the operand stack. PromF widens a loaded f32 to the
    // f64 a float value rides in; DemF narrows for a 4-byte store. Bits2F/F2Bits
    // reinterpret an i32 slot as the f32 and back, so `float32` storage is a
    // plain 4-byte word with no new machine type.
    | PromF | DemF | Bits2F | F2Bits
    // the 64-bit pair: an i64 bit pattern as an f64, which is how a parsed
    // float is finally assembled
    | Bits2D
    /// the other direction: an f64's bit pattern as an i64. Without it
    /// `DoubleToInt64Bits` had to ALLOCATE a box, store the double and read
    /// the payload back as an integer — a heap allocation per float printed.
    | D2Bits

type LExpr =
    | LConstW of int
    | LConstL of int64
    | LConstF of float
    /// read a local's current value
    | LGet of LReg
    /// read a module global's current value
    | LGetGlobal of string
    /// load a value of the given type at (addr + byteOffset)
    | LLoad of LTy * LExpr * int
    /// a machine ALU op over its operands
    | LPrim of LOp * LExpr list
    /// bump-allocate n bytes, yield the pointer
    | LAlloc of LExpr
    /// direct call of a known function symbol
    | LCall of string * LExpr list
    /// indirect call: parameter types (for the wasm type index), the function
    /// pointer/closure, and the arguments
    | LCallIndirect of LTy list * LExpr * LExpr list
    /// call through the function table by index: the parameter count (which
    /// picks the call signature), the table-index expression, and the full
    /// argument list. Interface dispatch reads the index from a vtable.
    | LCallIdx of int * LExpr * LExpr list
    /// a sequence of statements evaluated for effect, then a result value —
    /// LowIR's let-region; binders are just LSet statements before the value
    | LDo of LStmt list * LExpr
    /// a SELF call in tail position: evaluates the arguments, then transfers
    /// to the named function via the wasm tail-call instruction. Never
    /// returns to the caller; under GC the emitter restores the shadow-stack
    /// pointer to the function's entry value first.
    | LTailCall of string * LExpr list

and LStmt =
    | LStore of LTy * LExpr * int * LExpr
    | LSet of LReg * LExpr
    /// evaluate a MULTI-VALUE call and store its results into these
    /// registers, in order. A struct returns its fields this way: the value
    /// never takes a heap slot on the way back.
    | LSetMany of LReg list * LExpr
    | LSetGlobal of string * LExpr
    /// evaluate an expression for its effect, discard the result
    | LEval of LExpr
    /// call a function that returns nothing (a void runtime routine); unlike
    /// LEval of LCall there is no result to discard
    | LCallVoidS of string * LExpr list
    /// fill `len` bytes at `dst` with a byte value — one bulk instruction in
    /// place of a per-element store loop. `Array.zeroCreate` of a million
    /// structs wrote every field of every element by hand before this.
    | LMemFill of LExpr * LExpr * LExpr
    | LIf of LExpr * LStmt list * LStmt list
    | LWhile of LExpr * LStmt list
    /// a labelled block; `LBreak` on the same label exits it. Match compiles
    /// to nested blocks that break out on a failed arm; C emits goto/labels,
    /// wasm emits `block`/`br`.
    | LBlock of string * LStmt list
    /// branch to the end of the named block when the condition is non-zero
    | LBreakIf of string * LExpr
    | LBreak of string
    /// unreachable — an exhausted match, a trap after failwith
    | LTrap
    | LReturn of LExpr
    /// throw an exception value (the operand) via the module's one tag
    | LThrow of LExpr
    /// exception handling: evaluate the body expression into the result
    /// register; if it throws, bind the caught value to the exn register and
    /// run the handler statements (which either assign the result and break to
    /// the done label, or fall through to a re-throw). Fields: body, result
    /// register, exn register, handler statements.
    | LTryStmt of LExpr * LReg * LReg * LStmt list

/// A lowered function ready for instruction selection.
type LFunc =
    { LName : string
      LParams : LReg list
      LResult : LTy
      LBody : LStmt list }

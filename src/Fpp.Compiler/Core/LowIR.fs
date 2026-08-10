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
    // word (i32 / intptr) integer ops
    | AddW | SubW | MulW | DivSW | RemSW
    | AndW | OrW  | XorW | ShlW  | ShrSW | ShrUW
    | EqW  | NeW  | LtSW | GtSW  | LeSW  | GeSW | LtUW | GeUW
    // 64-bit integer ops
    | AddL | SubL | MulL | DivSL | RemSL
    | EqL  | NeL  | LtSL | GtSL  | LeSL  | GeSL
    // double ops
    | AddF | SubF | MulF | DivF | NegF
    | EqF  | NeF  | LtF  | GtF   | LeF | GeF
    // conversions between machine types
    | WToL | LToW | WToF | FToW | LToF | FToL

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

and LStmt =
    | LStore of LTy * LExpr * int * LExpr
    | LSet of LReg * LExpr
    | LSetGlobal of string * LExpr
    /// evaluate an expression for its effect, discard the result
    | LEval of LExpr
    /// call a function that returns nothing (a void runtime routine); unlike
    /// LEval of LCall there is no result to discard
    | LCallVoidS of string * LExpr list
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

/// A lowered function ready for instruction selection.
type LFunc =
    { LName : string
      LParams : LReg list
      LResult : LTy
      LBody : LStmt list }

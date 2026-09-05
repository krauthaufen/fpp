// #30: THE uint16/int16 CONVERSION FUNCTIONS PRODUCE THE NARROW TYPE ITSELF.
// They used to share the int/uint32 conversion arm in Infer, so `uint16 x`
// TYPED as uint32 — a loud mismatch against any uint16 annotation, and no
// expression could produce a uint16 value at all (fpp.base's C3us/C4us
// colors were gated off on exactly this). The emitter masks (uint16) or
// sign-extends through bit 15 (int16), the same width discipline byte and
// sbyte already had.
module Core_narrowconv

let mutable ntests = 0
let mutable failures = 0
let eqi (name : string) (got : int) (want : int) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %d want %d" name got want

// from int: in range, truncating, and negative
eqi "u16 in-range" (int (uint16 40000)) 40000
eqi "u16 wrap" (int (uint16 65537)) 1
eqi "u16 neg" (int (uint16 -1)) 65535
eqi "s16 in-range" (int (int16 -1234)) -1234
eqi "s16 wrap" (int (int16 65535)) -1
eqi "s16 sign" (int (int16 32768)) -32768

// from float and int64
eqi "u16 of float" (int (uint16 3.9)) 3
eqi "s16 of float" (int (int16 -2.9)) -2
eqi "u16 of int64" (int (uint16 70000L)) 4464
eqi "s16 of int64" (int (int16 40000L)) -25536

// narrow -> narrow
let u : uint16 = uint16 300
let s : int16 = int16 u
eqi "u16 bind" (int u) 300
eqi "s16 of u16" (int s) 300

// the #30 shape: an annotated binding fed by the conversion
let r : uint16 = uint16 (200 * 300)
let q : int16 = int16 (100 - 40000)
eqi "u16 annotated" (int r) 60000
eqi "s16 annotated" (int q) (int (int16 -39900))

// arithmetic THROUGH narrow values
eqi "u16 add wraps" (int (uint16 60000 + uint16 10000)) (int (uint16 70000))

printfn "ntests=%d failures=%d" ntests failures

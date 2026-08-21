// Ported from dotnet/fsharp tests/fsharp/core/libtest/test.fsx — the
// Optimizations module's shift/bitwise section and the mod_float repro (BUG
// 868) — into the common F#/F++ subset. Test NAMES are the originals.
//
// The point of the shift cases is the COUNT: .NET masks it to the operand's
// width, so `1 <<< 32` is 1 again and `1 <<< 63` is `1 <<< 31`. A backend that
// passes the count straight to a wider instruction gets these wrong.
//
// DROPPED: the Checked.* conversion families and the decimal (`3.9m`) cases —
// no Checked module and no decimal type here (int32.fpp records the same).
module Core_shifts

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- constant folding must not change the answer ------------------------

test "opt.oi20c77u" (1 + 1 = 2)
test "opt.oi20c77i" (-1 + 1 = 0)
test "opt.oi20c77o" (1 + 2 = 3)
test "opt.oi20c77p" (2 + 1 = 3)
test "opt.oi20c77a" (1 * 0 = 0)
test "opt.oi20c77s" (0 * 1 = 0)
test "opt.oi20c77d" (2 * 2 = 4)
test "opt.oi20c77f" (2 * 3 = 6)
test "opt.oi20c77g" (-2 * 3 = -6)
test "opt.oi20c77h" (1 - 2 = -1)
test "opt.oi20c77j" (2 - 1 = 1)

test "opt.oi20c77uL" (1L + 1L = 2L)
test "opt.oi20c77iL" (-1L + 1L = 0L)
test "opt.oi20c77oL" (1L + 2L = 3L)
test "opt.oi20c77pL" (2L + 1L = 3L)
test "opt.oi20c77aL" (1L * 0L = 0L)
test "opt.oi20c77sL" (0L * 1L = 0L)
test "opt.oi20c77dL" (2L * 2L = 4L)
test "opt.oi20c77fL" (2L * 3L = 6L)
test "opt.oi20c77gL" (-2L * 3L = -6L)
test "opt.oi20c77hL" (1L - 2L = -1L)
test "opt.oi20c77jL" (2L - 1L = 1L)

// ---- shift COUNTS wrap to the operand width -----------------------------

test "opt.oi20cnq" (1 <<< 0 = 1)
test "opt.oi20cnw" (1 <<< 1 = 2)
test "opt.oi20cne" (1 <<< 2 = 4)
test "opt.oi20cnr" (1 <<< 31 = 0x80000000)
test "opt.oi20cnt" (1 <<< 32 = 1)
test "opt.oi20cny" (1 <<< 33 = 2)
test "opt.oi20cnu" (1 <<< 63 = 0x80000000)

test "opt.oi20cna" (1L <<< 0 = 1L)
test "opt.oi20cns" (1L <<< 1 = 2L)
test "opt.oi20cnd" (1L <<< 2 = 4L)
test "opt.oi20cnf" (1L <<< 31 = 0x80000000L)
test "opt.oi20cng" (1L <<< 32 = 0x100000000L)
test "opt.oi20cnh" (1L <<< 63 = 0x8000000000000000L)
test "opt.oi20cnj" (1L <<< 64 = 1L)
test "opt.oi20cnk" (1L <<< 127 = 0x8000000000000000L)

// right shift on a SIGNED operand is arithmetic — the sign bit floods in
test "opt.oi20cnza" (0x80000000 >>> 0 = 0x80000000)
test "opt.oi20cnxa" (0x80000000 >>> 1 = 0xC0000000)
test "opt.oi20cnca" (0x80000000 >>> 31 = 0xFFFFFFFF)
test "opt.oi20cnva" (0x80000000 >>> 32 = 0x80000000)

// ---- bitwise ------------------------------------------------------------

test "or.oi20cnq" (1 ||| 0 = 1)
test "or.oi20cnw" (1 ||| 1 = 1)
test "or.oi20cne" (1 ||| 2 = 3)
test "or.oi20cnr" (0x80808080 ||| 0x08080808 = 0x88888888)
test "or.oi20cnrL" (0x8080808080808080L ||| 0x0808080808080808L = 0x8888888888888888L)

test "and.oi20cnq" (1 &&& 0 = 0)
test "and.oi20cnw" (1 &&& 1 = 1)
test "and.oi20cne" (1 &&& 2 = 0)
test "and.oi20cnr" (0x80808080 &&& 0x08080808 = 0)
test "and.oi20cnrL" (0x8080808080808080L &&& 0x0808080808080808L = 0L)

test "xor.1" (0xFF ^^^ 0x0F = 0xF0)
test "xor.2" (0xFFFFFFFF ^^^ 0xFFFFFFFF = 0)
test "not.1" (~~~0 = -1)
test "not.2" (~~~0xFFFFFFFF = 0)

// ---- float modulo keeps the DIVIDEND's sign -----------------------------

let mod_float (x : float) (y : float) = x % y

test "mod_floatvrve" (mod_float 3.0 2.0 = 1.0)
test "mod_float3121" (mod_float 3.0 -2.0 = 1.0)
test "mod_float2e12" (mod_float -3.0 2.0 = -1.0)
test "mod_floatve23" (mod_float -3.0 -2.0 = -1.0)
test "mod_floatvr24" (mod_float 3.0 1.0 = 0.0)
test "mod_floatcw34" (mod_float 3.0 -1.0 = 0.0)

// the same rule for integers
test "mod_int1" (3 % 2 = 1)
test "mod_int2" (-3 % 2 = -1)
test "mod_int3" (3 % -2 = 1)
test "mod_int4" (-3 % -2 = -1)
test "mod_int64" (-3L % 2L = -1L)

printfn "DONE tests=%d failures=%d" ntests failures

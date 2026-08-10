// `Zero<float>.Zero` — a class MEMBER as the applied head of a dot
// chain — still compiles clean, stubs (`unknown field Zero`), and traps.
// The intended reading is Num's Zero at float (both segments resolve to
// the same member), and `Num<float>.Zero` / `Zero<float>` both WORK now;
// this double-name spelling threads a fourth resolution path that binds
// neither. Related hole: `(1.5).Bogus` and `r.Bogus` on known receivers
// are also still silent. DIAGNOSED, fix attempted and withdrawn: the
// forced dot pass concedes success unconditionally on a known receiver
// with NO candidate — `if force then (universal () || true) else false`
// in tryResolveDotCore's None arm. Changing `|| true` to plain
// `universal ()` made (1.5).Bogus and Zero<float>.Zero error correctly,
// but behavior then FLAPPED between builds (the same program parked its
// dot in one build and not the next) while widening the known-receiver
// set, and the session ended before the flap was understood. Start
// there, with the flap explained before shipping.
printfn "%s" (string (Zero<float>.Zero + 0.25))

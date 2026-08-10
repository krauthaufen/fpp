// `Zero<float>.Zero` — a class MEMBER as the applied head of a dot
// chain — still compiles clean, stubs (`unknown field Zero`), and traps.
// The intended reading is Num's Zero at float (both segments resolve to
// the same member), and `Num<float>.Zero` / `Zero<float>` both WORK now;
// this double-name spelling threads a fourth resolution path that binds
// neither. Related hole: `(1.5).Bogus` on a literal receiver is also
// still silent — the known-receiver check misses dots that never park.
printfn "%s" (string (Zero<float>.Zero + 0.25))

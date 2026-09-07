#!/usr/bin/env bash
# THE STANDALONE MODULE HAS NO ROOT TABLE.
#
# `fpp build --lowir` (`--linear`) emits a module with no collector: no
# `$roots`, no `$sp`, no witness area. Every mechanism that reads a witness —
# `typeName<'a>`, the class-parameter witnesses a method recovers off its
# receiver — belongs to the GC build alone, and reaching for the root table
# from the standalone one emitted a global the module never declares. The
# whole mode died on it, inside the PRELUDE (a Seq object expression's
# MoveNext), so no program at all could be built this way — including the
# empty one below. It surfaced as a bare NullReferenceException in the binary
# emitter with nothing but a stack trace (~/claude/fpp-base-snags.md #43).
#
# The lowir gates beside this one all use the mode, so they would have caught
# it too; this one holds the SHAPES that broke it, and it is fast.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module LowIRStandalone
// a generic CLASS: its methods are the ones that recover class-parameter
// witnesses off the receiver under GC
type Box<'a>(v : 'a) =
    member _.Value = v
    member x.Pair (o : 'a) : 'a list = [ x.Value; o ]
// the type-name primitive, at a concrete type and inside a generic body
let nameOf (x : 'a) : string = typeName<'a>
let bi = Box<int> 7
let bs = Box<string> "s"
let r1 = printfn "%d" (List.length (bi.Pair 8))
let r2 = printfn "%s" (String.concat "," (bs.Pair "t"))
let r3 = printfn "%s" (typeName<int>)
let r4 = printfn "%d" (List.sum (List.map (fun x -> x * 2) [ 1; 2; 3 ]))
// a sequence through the prelude's own object expressions, which is where
// the witness recovery was emitted
let r5 = printfn "%d" (Seq.length (Seq.filter (fun x -> x % 2 = 0) (Seq.ofList [ 1; 2; 3; 4 ])))
let r6 = printfn "%s" (nameOf 1.5)
FPP

"$fpp" build --lowir -o "$out/low.wasm" "$out/p.fpp"
"$wt" run "$out/low.wasm" > "$out/low.txt" 2>&1

# the typeName answers: a concrete type names itself, and a generic body
# STAMPED at float knows it is float — the standalone mode has no witness to
# ask, so a type parameter no stamp reached would answer obj
cat > "$out/want.txt" <<'EXP'
2
s,t
int
12
2
float
EXP
if diff -u "$out/want.txt" "$out/low.txt"; then
    echo "LOWIR-STANDALONE OK (generic class + typeName + seq, no root table)"
else
    echo "LOWIR-STANDALONE MISMATCH"; exit 1
fi

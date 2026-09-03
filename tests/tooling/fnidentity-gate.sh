#!/usr/bin/env bash
# A top-level function reified as a VALUE has STABLE IDENTITY here — `box f`
# twice is reference-equal — which F# does NOT guarantee (see DIVERGENCES.md).
# It is what makes `Effect.ofFunction f`-style value keying work. Not a
# conformance case: fsi disagrees, on purpose.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/.." && pwd)
fpp="${FPP:-$root/../src/Fpp.Cli/bin/Release/net10.0/fpp}"
wt="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
cat > "$out/f.fpp" <<'EOF'
let square (x : int) = x * x
let cube (x : int) = x * x * x
let apply (f : int -> int) (n : int) = f n
let go =
    let a = box square
    let b = box square
    printfn "%b %b %d" (System.Object.ReferenceEquals (a, b)) (System.Object.ReferenceEquals (box square, box cube)) (apply square 9)
EOF
"$fpp" build --strict -o "$out/f.wasm" "$out/f.fpp" >/dev/null 2>&1
got=$("$wt" run -W gc=y,exceptions=y "$out/f.wasm")
want="true false 81"
if [ "$got" = "$want" ]; then echo "FNIDENTITY OK (box f stable, distinct fns distinct, reified still calls)"
else echo "FNIDENTITY WRONG: want [$want] got [$got]"; exit 1; fi

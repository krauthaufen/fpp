#!/usr/bin/env bash
# The package pipeline, end to end: two libraries (mathlib, and geolib
# depending on it through a ^ range) are PACKED (both target flavors),
# PUBLISHED to a directory registry, then an app that names only geolib
# restores — the solver pulls mathlib transitively — and builds against the
# cached fppirs for BOTH backends. The printed answers are the assertion.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
reg="$work/registry"
mkdir -p "$reg"
export HOME="$work/home"   # an isolated ~/.fpp cache; the real one stays clean
mkdir -p "$HOME"

# ---- mathlib 1.2.0 --------------------------------------------------------
mkdir -p "$work/mathlib"
cat > "$work/mathlib/lib.fpp" <<'EOF'
module MathLib
let double (x : int) : int = x * 2
let scale (x : float) (f : float) : float = x * f
EOF
cat > "$work/mathlib/mathlib.fppproj" <<'EOF'
name mathlib
version 1.2.0
src lib.fpp
EOF
"$fpp" pack "$work/mathlib/mathlib.fppproj" -o "$work/mathlib-1.2.0.fpkg"
"$fpp" publish "$work/mathlib-1.2.0.fpkg" "$reg"

# ---- geolib 0.3.1, requires mathlib ^1.0 ----------------------------------
mkdir -p "$work/geolib"
cat > "$work/geolib/lib.fpp" <<'EOF'
module GeoLib
let perimeter (w : int) (h : int) : int = MathLib.double (w + h)
EOF
cat > "$work/geolib/geolib.fppproj" <<'EOF'
name geolib
version 0.3.1
registry REGDIR
package mathlib ^1.0
src lib.fpp
EOF
sed -i "s|REGDIR|$reg|" "$work/geolib/geolib.fppproj"
"$fpp" restore "$work/geolib/geolib.fppproj"
"$fpp" pack "$work/geolib/geolib.fppproj" -o "$work/geolib-0.3.1.fpkg"
"$fpp" publish "$work/geolib-0.3.1.fpkg" "$reg"

# ---- the app: names geolib only; mathlib arrives transitively -------------
mkdir -p "$work/app"
cat > "$work/app/main.fpp" <<'EOF'
module App
let a = printfn "%d" (GeoLib.perimeter 3 4)
let b = printfn "%d" (MathLib.double 21)
EOF
cat > "$work/app/app.fppproj" <<'EOF'
name app
registry REGDIR
package geolib ^0.3
src main.fpp
EOF
sed -i "s|REGDIR|$reg|" "$work/app/app.fppproj"

# no lock yet: the build must REFUSE with a pointer at restore
if "$fpp" build "$work/app/app.fppproj" -o "$work/app.wasm" 2> "$work/refuse.txt"; then
    echo "PKG FAILED: built without a lock"
    exit 1
fi
grep -q "fpp restore" "$work/refuse.txt" || { echo "PKG FAILED: refusal does not point at restore"; cat "$work/refuse.txt"; exit 1; }

"$fpp" restore "$work/app/app.fppproj"
grep -q "package mathlib 1.2.0" "$work/app/fpp.lock" || { echo "PKG FAILED: lock lacks the transitive pick"; cat "$work/app/fpp.lock"; exit 1; }

# wasm leg (HOME is redirected at the cache; wasmtime lives in the REAL one)
wasmtime=$(getent passwd "$(id -un)" | cut -d: -f6)/.wasmtime/bin/wasmtime
"$fpp" build --strict "$work/app/app.fppproj" -o "$work/app.wasm"
got=$("$wasmtime" run -W function-references=y,gc=y,exceptions=y "$work/app.wasm")
[ "$got" = "14
42" ] || { echo "PKG FAILED (wasm): got '$got'"; exit 1; }

# native leg
"$fpp" build "$work/app/app.fppproj" -o "$work/app.c"
gcc -O1 -I"$root/runtime" -I"$root/runtime/gc/api" \
    -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$root/runtime/gc/api/semi-attrs.h\"" \
    -DGC_EMBEDDER="\"$root/runtime/fpprt-embedder.h\"" \
    "$work/app.c" "$root/runtime/fpprt.c" "$root/runtime/fpprt-lang.c" \
    "$root/runtime/gc/src/gc-platform-gnu-linux.c" "$root/runtime/gc/src/gc-stack.c" \
    "$root/runtime/gc/src/gc-options.c" "$root/runtime/gc/src/gc-tracepoint.c" \
    "$root/runtime/gc/src/gc-ephemeron.c" "$root/runtime/gc/src/gc-finalizer.c" \
    "$root/runtime/gc/src/semi.c" \
    -I"$root/runtime/gc/src" -lm -lpthread -o "$work/appbin"
gotc=$("$work/appbin")
[ "$gotc" = "14
42" ] || { echo "PKG FAILED (native): got '$gotc'"; exit 1; }

echo "PKG OK (pack, publish, transitive restore, lock, both backends)"

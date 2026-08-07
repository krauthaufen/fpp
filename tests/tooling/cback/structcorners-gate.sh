#!/usr/bin/env bash
# Struct corners: FLAT arrays of STAMPED generic structs (uniform-
# conversion at the generic boundary), `arr.[i].F <- v` in place,
# mutable struct fields in plain records (lvalue writes, clone on
# read/assign/`with`-copy). Reference: dotnet fsi, pinned.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"$root/src/Fpp.Cli/bin/Release/net10.0/fpp" build -o "$out/m.c" "$here/structcorners.fpp"
rt="$root/runtime"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O2 -g -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    -c "$rt/fpprt-lang.c" -o "$out/fpprt-lang.o"
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/m.c" "$rt/build/mmc/fpprt.o" "$out/fpprt-lang.o" \
    "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/m"
"$out/m" > "$out/got.txt"
printf '42 2\n55 fiftyfive\n0\ntrue\nv42 x3\nv10 changed\n42 2\n42 77\n2 99\n' > "$out/want.txt"
if diff -u "$out/want.txt" "$out/got.txt"; then
    echo "STRUCT CORNERS OK (fsi-pinned, mmc)"
else
    echo "STRUCT CORNERS FAILED (mmc)"
    exit 1
fi

# the SHAKEOUT leg: semi moves EVERYTHING every collection — a missed
# frame-pod registration for a ref-holding stack struct dies here
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/semi-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/m.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
    "$rt/gc/src/gc-platform-gnu-linux.c" "$rt/gc/src/gc-stack.c" \
    "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
    "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/semi.c" \
    -lm -lpthread -o "$out/msemi"
FPP_HEAP_MB=2 "$out/msemi" 2>/dev/null > "$out/got-semi.txt"
if diff -u "$out/want.txt" "$out/got-semi.txt"; then
    echo "STRUCT CORNERS OK (fsi-pinned, semi shakeout)"
else
    echo "STRUCT CORNERS FAILED (semi)"
    exit 1
fi

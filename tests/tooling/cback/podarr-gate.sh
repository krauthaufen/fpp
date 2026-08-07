#!/usr/bin/env bash
# Flat struct arrays: blittable AND ref-holding elements stay flat; the
# array's type entry carries per-element ref offsets so the collector
# traces and updates them. Pod GLOBALS are static struct fields: reads
# copy, assignment copies, field-set mutates in place. Reference:
# dotnet fsi (the oracle boxes elements). Expected output pinned from fsi.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"$root/src/Fpp.Cli/bin/Release/net10.0/fpp" build -o "$out/p.c" "$here/podarr.fpp"
rt="$root/runtime"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O2 -g -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    -c "$rt/fpprt-lang.c" -o "$out/fpprt-lang.o"
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/p.c" "$rt/build/mmc/fpprt.o" "$out/fpprt-lang.o" \
    "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/p"
"$out/p" > "$out/got.txt"
printf '7\n100\n0\n5\nhi\n99\nchanged\n0\n124750\ntrue\ns123\nx9\n' > "$out/want.txt"
if diff -u "$out/want.txt" "$out/got.txt"; then
    echo "POD ARRAYS OK (fsi-pinned, mmc)"
else
    echo "POD ARRAYS FAILED (mmc)"
    exit 1
fi

# semi shakeout: everything moves every collection — a missed element
# ref in the array trace dies here
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/semi-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/p.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
    "$rt/gc/src/gc-platform-gnu-linux.c" "$rt/gc/src/gc-stack.c" \
    "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
    "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/semi.c" \
    -lm -lpthread -o "$out/psemi"
FPP_HEAP_MB=2 "$out/psemi" 2>/dev/null > "$out/got-semi.txt"
if diff -u "$out/want.txt" "$out/got-semi.txt"; then
    echo "POD ARRAYS OK (fsi-pinned, semi shakeout)"
else
    echo "POD ARRAYS FAILED (semi)"
    exit 1
fi

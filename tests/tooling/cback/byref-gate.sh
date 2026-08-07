#!/usr/bin/env bash
# TRUE byref aliasing, fsi-pinned: writes through a byref land in the
# original local/field/element, and byref reads observe direct-path writes
# MID-CALL. Runs mmc and the semi shakeout (views hold closures the moving
# collector must trace).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"$root/src/Fpp.Cli/bin/Release/net10.0/fpp" build -o "$out/b.c" "$here/byref.fpp"
rt="$root/runtime"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O2 -g -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    -c "$rt/fpprt-lang.c" -o "$out/fpprt-lang.o"
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/b.c" "$rt/build/mmc/fpprt.o" "$out/fpprt-lang.o" \
    "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/b"
printf '11\n13\n2\n9\n110\n105\n7\n103\n' > "$out/want.txt"
"$out/b" > "$out/got.txt"
diff -u "$out/want.txt" "$out/got.txt" && echo "BYREF ALIASING OK (mmc)"
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/semi-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/b.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
    "$rt/gc/src/gc-platform-gnu-linux.c" "$rt/gc/src/gc-stack.c" \
    "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
    "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/semi.c" \
    -lm -lpthread -o "$out/bsemi"
FPP_HEAP_MB=2 "$out/bsemi" 2>/dev/null > "$out/got2.txt"
diff -u "$out/want.txt" "$out/got2.txt" && echo "BYREF ALIASING OK (semi shakeout)"

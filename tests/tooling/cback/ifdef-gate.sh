#!/usr/bin/env bash
# Conditional compilation: `#if WASM` / `#if NATIVE` resolve from the build
# TARGET, so a dual-target program never compiles a branch that would trap —
# both legs build --strict (which refuses stubbed functions).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
rt="$root/runtime"
cat > "$out/dual.fpp" <<'SRC'
let describe () : string =
#if WASM
    "web"
#else
    "native"
#endif

#if WASM
let webOnly () =
    let d = Js.global_ "document"
    Js.set d "title" (Js.ofString "hi")
#endif

let go =
    print (describe ())
#if WASM
    print "js code present"
#endif
#if NATIVE
    print "no js compiled here"
#endif
    print "ok"
SRC
"$fpp" build --strict -o "$out/dual.wasm" "$out/dual.fpp"
"$fpp" build --strict -o "$out/dual.c" "$out/dual.fpp"
grep -q "js_global" "$out/dual.c" && { echo "IFDEF FAILED: js leaked into native"; exit 1; }
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null 2>&1
gcc -O1 -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/dual.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" "$rt/build/mmc/libwhippet.a" \
    -lm -lpthread -o "$out/dual" 2>/dev/null
got=$("$out/dual")
want=$(printf 'native\nno js compiled here\nok')
[ "$got" = "$want" ] || { echo "IFDEF FAILED: native output"; echo "$got"; exit 1; }
echo "IFDEF OK (target-conditional code, strict both legs)"

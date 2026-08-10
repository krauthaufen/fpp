#!/usr/bin/env bash
# Mobile proof-of-life: F++ -> C -> Android NDK clang -> static native
# ELF, for BOTH ABIs. The aarch64 binary is asserted to be a valid
# Android ARM executable; the x86_64 one is STATIC against bionic and
# runs directly on the host Linux kernel (syscall-compatible), so its
# real F++ output — unions, pattern matching, typeclasses, List pipeline
# — is the executable proof. iOS needs a Mac toolchain (recipe in
# MOBILE.md); this gate covers Android.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
rt="$root/runtime"

ndk=$(ls -d /opt/android-sdk/ndk/*/toolchains/llvm/prebuilt/*/bin 2>/dev/null | head -1)
if [ -z "$ndk" ] || [ ! -x "$ndk/aarch64-linux-android24-clang" ]; then
    echo "MOBILE SKIP (no Android NDK)"; exit 0
fi
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/m.fpp" <<'FPP'
module Mobile
type Tree = Leaf of int | Node of Tree * Tree
let rec sum (t : Tree) : int =
    match t with
    | Leaf n -> n
    | Node (l, r) -> sum l + sum r
let sq (x : 'a) : 'a when Num<'a> = x * x
let t = Node (Node (Leaf 3, Leaf 4), Leaf 5)
let r1 = printfn "%d" (sum t)
let r2 = printfn "%d" (sq 7)
let r3 = printfn "%s" "F++ native on Android"
let xs = [ 1 .. 10 ] |> List.map (fun x -> x * x) |> List.filter (fun x -> x % 2 = 1)
let r4 = printfn "%d" (List.sum xs)
FPP
"$fpp" build -o "$out/m.c" "$out/m.fpp"

sources=("$out/m.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
    "$rt/gc/src/gc-platform-gnu-linux.c" "$rt/gc/src/gc-stack.c" \
    "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
    "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/semi.c")
flags=(-O2 -static -w -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/semi-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" -lm)

"$ndk/aarch64-linux-android24-clang" "${flags[@]}" "${sources[@]}" -o "$out/m-arm64"
file "$out/m-arm64" | grep -q "ARM aarch64" \
    || { echo "MOBILE FAILED (aarch64 not an ARM ELF)"; exit 1; }
echo "MOBILE OK (aarch64 Android ELF built)"

"$ndk/x86_64-linux-android24-clang" "${flags[@]}" "${sources[@]}" -o "$out/m-x64"
got=$("$out/m-x64" 2>/dev/null)
want="12
49
F++ native on Android
165"
[ "$got" = "$want" ] || { echo "MOBILE FAILED (x86_64 output): $got"; exit 1; }
echo "MOBILE OK (x86_64 Android binary runs: unions, patterns, typeclasses, List)"

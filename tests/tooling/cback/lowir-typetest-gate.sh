#!/usr/bin/env bash
# Type tests on the wasm-linear backend. Every heap object carries a class-id
# descriptor at offset 0, so `:? T` and `:? T` patterns work against records
# and unions by reading that word. The wasm-GC oracle CANNOT type-test against
# a union ("not a class"), so this gate has no oracle to diff — it checks the
# --lowir output against the known-correct answer directly.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module TypeTest
type Shape = Circle of int | Square of int
type Point = { X : int; Y : int }
let name (o : obj) : string =
    if o :? Shape then "shape"
    elif o :? Point then "point"
    else "other"
let describe (o : obj) : int =
    match o with
    | :? Shape -> 1
    | :? Point -> 2
    | _ -> 0
let s = (Circle 5) :> obj
let p = { X = 1; Y = 2 } :> obj
let r1 = printfn "%s" (name s)
let r2 = printfn "%s" (name p)
let r3 = printfn "%d" (describe s)
let r4 = printfn "%d" (describe p)
FPP

"$fpp" build --lowir -o "$out/low.wasm" "$out/p.fpp"
"$wt" run "$out/low.wasm" > "$out/low.txt"
printf 'shape\npoint\n1\n2\n' > "$out/want.txt"
if diff -u "$out/want.txt" "$out/low.txt"; then
    echo "LOWIR TYPETEST OK (class-id descriptor: :? against records and unions)"
else
    echo "LOWIR TYPETEST MISMATCH"; exit 1
fi

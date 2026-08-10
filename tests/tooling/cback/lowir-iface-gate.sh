#!/usr/bin/env bash
# Interface dispatch on the wasm-linear backend. Every heap object carries a
# class-id header; a flat [class-id][slot] vtable holds each type's method
# implementations, and `x.Method args` reads the receiver's header, indexes the
# vtable, and call_indirects. `:? IFace` matches any implementor. Unlike union
# type tests, the wasm-GC oracle DOES do interface dispatch, so this diffs
# against it — one meaning across the two emitters.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module Iface
type IShape =
    abstract Area : unit -> int
    abstract Scaled : int -> int
type Circle(r : int) =
    interface IShape with
        member _.Area () = 3 * r * r
        member _.Scaled k = 3 * (r * k) * (r * k)
type Sq(w : int) =
    interface IShape with
        member _.Area () = w * w
        member _.Scaled k = (w * k) * (w * k)
type IShow =
    abstract Show : unit -> string
type Tag(s : string) =
    interface IShow with
        member _.Show () = "tag:" + s
let rec sumAreas (xs : IShape list) : int =
    match xs with
    | [] -> 0
    | h :: t -> h.Area () + sumAreas t
let shapes = [ (Circle 5) :> IShape; (Sq 4) :> IShape ]
let r1 = printfn "%d" (sumAreas shapes)
let r2 = printfn "%d" ((Circle 2 :> IShape).Scaled 3)
let r3 = printfn "%s" ((Tag "x" :> IShow).Show ())
let describe (o : obj) : string =
    if o :? IShape then "shape"
    elif o :? IShow then "show"
    else "other"
let r4 = printfn "%s" (describe (Circle 1 :> obj))
let r5 = printfn "%s" (describe (Tag "y" :> obj))
let r6 = printfn "%s" (describe (42 :> obj))
FPP

"$fpp" build --lowir -o "$out/low.wasm" "$out/p.fpp"
"$wt" run "$out/low.wasm" > "$out/low.txt"
"$fpp" build -o "$out/gc.wasm" "$out/p.fpp"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/gc.wasm" > "$out/gc.txt"
if diff -u "$out/gc.txt" "$out/low.txt"; then
    echo "LOWIR IFACE OK (vtable dispatch + interface type tests == wasm-GC oracle, $(wc -l < "$out/low.txt") lines)"
else
    echo "LOWIR IFACE MISMATCH"; exit 1
fi

#!/usr/bin/env bash
# The DIRECT wasm-linear backend (slice 1): `fpp build --linear` emits a
# wasm module over linear memory with NO C compiler and NO emscripten in
# the path. It runs under wasmtime with nothing but a wasm runtime, and
# its output must match the wasm-GC oracle for the same program — one
# meaning across two independent emitters. Covers the slice: integers,
# arithmetic, comparisons, let, top-level functions and recursion, while
# loops, mutable globals, string literals, int-to-string, concat, printfn.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module WasmLin
type Point = { X : int; Y : int }
type Shape = Circle of int | Rect of int * int | Dot
let area (s : Shape) : int =
    match s with
    | Circle r -> 3 * r * r
    | Rect (w, h) -> w * h
    | Dot -> 0
let rec fib (n : int) : int = if n < 2 then n else fib (n - 1) + fib (n - 2)
let rec fact (n : int) : int = if n <= 1 then 1 else n * fact (n - 1)
let gcd (a : int) (b : int) : int =
    let mutable x = a
    let mutable y = b
    while y <> 0 do
        let t = y
        y <- x % y
        x <- t
    x
let r1 = printfn "%d" (fib 15)
let r2 = printfn "%d" (fact 7)
let r3 = printfn "%d" (gcd 1071 462)
let r4 = printfn "%s" ("F++ " + "direct wasm-linear")
let mutable acc = 0
let loop =
    let mutable i = 1
    while i <= 100 do
        acc <- acc + i
        i <- i + 1
let r5 = printfn "%d" acc
let adder (n : int) : int -> int = fun x -> x + n
let apply (f : int -> int) (v : int) : int = f v
let twice (f : int -> int) (x : int) : int = f (f x)
let add10 = adder 10
let r6 = printfn "%d" (apply add10 5)
let r7 = printfn "%d" (twice (fun y -> y * y) 3)
let compose (f : int -> int) (g : int -> int) : int -> int = fun x -> f (g x)
let r8 = printfn "%d" ((compose (fun n -> n + 1) (fun m -> m * 2)) 20)
let counter (start : int) : int -> int =
    let mutable c = start
    fun step -> c + step
let pt = { X = 3; Y = 4 }
let r9 = printfn "%d" (pt.X * 100 + pt.Y)
let r10 = printfn "%d" (area (Circle 5) + area (Rect (6, 7)) + area Dot)
let swap (t : int * int) : int * int = let (a, b) = t in (b, a)
let r11 = printfn "%d" (let (a, b) = swap (2, 9) in a * 10 + b)
let lit = [| 10; 20; 30; 40 |]
let r12 = printfn "%d" (lit.[2] + lit.Length)
let sq : int[] = Array.zeroCreate 6
let fillsq =
    let mutable i = 0
    while i < sq.Length do
        sq.[i] <- i * i
        i <- i + 1
let mutable asum = 0
let sumsq =
    let mutable i = 0
    while i < sq.Length do
        asum <- asum + sq.[i]
        i <- i + 1
let r13 = printfn "%d" asum
let fa = 3.5
let fb = 2.0
let r14 = printfn "%f" (fa * fb + 1.5)
let sqf (x : float) : float = x * x
let r15 = printfn "%f" (sqf 4.0)
let r16 = printfn "%f" (10.0 / 4.0)
let r17 = printfn "%f" (0.0 - 2.25)
let r18 = printfn "%f" (float 7 + 0.5)
let big = 3000000000L
let r19 = printfn "%d" (int (big - 2999999900L))
let nums = [ 1; 2; 3; 4; 5; 6 ]
let r20 = printfn "%d" (List.sum (List.map (fun x -> x * 2) nums))
let r21 = printfn "%d" (List.length (List.filter (fun x -> x % 2 = 0) nums))
let r22 = printfn "%d" (List.fold (fun a x -> a + x) 0 nums)
let rec mysum (l : int list) : int =
    match l with
    | [] -> 0
    | h :: t -> h + mysum t
let r23 = printfn "%d" (mysum nums)
let classify (n : int) : string =
    match n with
    | 0 -> "zero"
    | 1 -> "one"
    | _ -> "many"
let r24 = printfn "%s" (classify 1)
let describe (o : int option) =
    match o with
    | Some v -> printfn "got %d" v
    | None -> printfn "nothing"
let r25 = describe (Some 7)
let r26 = describe None
FPP

# the direct linear module — no C toolchain touched
"$fpp" build --linear -o "$out/lin.wasm" "$out/p.fpp"
"$root/.wasmtime/bin/wasmtime" run "$out/lin.wasm" > "$out/lin.txt" 2>/dev/null \
    || "$HOME/.wasmtime/bin/wasmtime" run "$out/lin.wasm" > "$out/lin.txt"

# the wasm-GC oracle for the same program
"$fpp" build -o "$out/gc.wasm" "$out/p.fpp"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/gc.wasm" > "$out/gc.txt"

if diff -u "$out/gc.txt" "$out/lin.txt"; then
    echo "WASMLIN OK (direct linear == wasm-GC oracle, no C compiler, $(wc -l < "$out/lin.txt") lines)"
else
    echo "WASMLIN MISMATCH"; exit 1
fi

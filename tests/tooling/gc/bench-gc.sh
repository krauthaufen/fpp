#!/usr/bin/env bash
# Benchmark the GC (fpprt/Whippet) wasm-linear backend against C, the wasm-GC
# backend, and the standalone (bump, no-GC) lowir path. Warm best-of-N under
# wasmtime. Two workloads: a no-allocation integer loop (isolates the tagged-int
# representation cost from the GC) and an allocation-heavy list build (the GC's
# actual job, vs C malloc/free).
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"; wt="$HOME/.wasmtime/bin/wasmtime"
wm="$HOME/emsdk/upstream/bin/wasm-merge"; reactor="$HOME/projects/fpp/runtime/build/wasm/fpprt_reactor.wasm"
source "$HOME/emsdk/emsdk_env.sh" >/dev/null 2>&1
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

gcbuild(){ "$fpp" build --gc -o "$out/p.wasm" "$1" 2>/dev/null; "$wm" -all "$reactor" fpprt "$out/p.wasm" mutator -S -o "$out/p.wat" 2>/dev/null; wasm-tools parse "$out/p.wat" -o "$2"; }
bench(){ best=999999; for k in 1 2 3 4; do s=$(date +%s%N); r=$("$wt" run -W gc=y,exceptions=y "$1" 2>&1|tail -1); e=$(date +%s%N); ms=$(((e-s)/1000000)); [ $ms -lt $best ]&&best=$ms; done; printf "%-16s %5d ms  (%s)\n" "$2" "$best" "$r"; }

cat > "$out/int.fpp" <<'FPP'
module B
let go =
    let mutable acc = 0
    let mutable r = 0
    while r < 100 do
        let mutable i = 0
        while i < 1000000 do acc <- acc + i; i <- i + 1
        r <- r + 1
    printfn "%d" acc
FPP
cat > "$out/int.c" <<'C'
#include <stdio.h>
int main(int c,char**v){volatile int one=1;long acc=0;for(int r=0;r<100;r++)for(int i=0;i<1000000;i++)acc+=i*one;printf("%ld\n",acc);return 0;}
C
cat > "$out/alloc.fpp" <<'FPP'
module B
let go =
    let mutable total = 0
    let mutable r = 0
    while r < 30 do
        let mutable acc : int list = []
        let mutable i = 0
        while i < 200000 do acc <- i :: acc; i <- i + 1
        let mutable s = 0
        while (match acc with [] -> false | _ -> true) do (match acc with h :: t -> s <- s + h; acc <- t | [] -> ())
        total <- total + s
        r <- r + 1
    printfn "%d" total
FPP
cat > "$out/alloc.c" <<'C'
#include <stdio.h>
#include <stdlib.h>
typedef struct N{int v;struct N*next;}N;
int main(){long total=0;for(int r=0;r<30;r++){N*acc=0;for(int i=0;i<200000;i++){N*n=malloc(sizeof(N));n->v=i;n->next=acc;acc=n;}long s=0;for(N*p=acc;p;p=p->next)s+=p->v;total+=s;while(acc){N*t=acc->next;free(acc);acc=t;}}printf("%ld\n",total);return 0;}
C

emcc -O2 "$out/int.c" -o "$out/ic.wasm" -s STANDALONE_WASM -s PURE_WASI=1 2>/dev/null
"$fpp" build -o "$out/io.wasm" "$out/int.fpp" 2>/dev/null
"$fpp" build --lowir -o "$out/il.wasm" "$out/int.fpp" 2>/dev/null
gcbuild "$out/int.fpp" "$out/ig.wasm"
echo "=== integer loop (100M data-dependent adds, no allocation) ==="
bench "$out/ic.wasm" "C (emcc -O2)"; bench "$out/io.wasm" "F++ wasm-GC"
bench "$out/il.wasm" "F++ lowir noGC"; bench "$out/ig.wasm" "F++ --gc/fpprt"

emcc -O2 "$out/alloc.c" -o "$out/ac.wasm" -s STANDALONE_WASM -s PURE_WASI=1 2>/dev/null
gcbuild "$out/alloc.fpp" "$out/ag.wasm"
echo "=== allocation (6M cons cells built+summed, real GC vs malloc/free) ==="
bench "$out/ac.wasm" "C malloc/free"; bench "$out/ag.wasm" "F++ --gc/fpprt"

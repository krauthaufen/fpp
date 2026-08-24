#!/usr/bin/env bash
# Every perf benchmark, in C and in F++, both compiled to wasm and run under
# wasmtime — plus the .NET build where an F# twin exists.
#
# WARM, best of three: wasmtime caches a module's compilation on disk, so the
# first run of a fresh binary pays the whole Cranelift compile and reads 3-6x
# slower than every run after it. One cold run has been reported as a 400 ms
# "regression" before. The RESULT is printed beside the timing: a module that
# fails to build exits in milliseconds and looks like a spectacular win.
#
#   ./bench.sh              # every benchmark
#   ./bench.sh vertices     # one
set -u
cd "$(dirname "$0")"
root=$(cd ../../.. && pwd)
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
wt="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
only="${1:-}"

source /opt/emsdk/emsdk_env.sh >/dev/null 2>&1

# best of three, in milliseconds; echoes "<ms> <result>"
bestof3 () {
    local best=999999 res=""
    for _ in 1 2 3; do
        local s e ms
        s=$(date +%s%N)
        res=$("$@" 2>&1 | tail -1)
        e=$(date +%s%N)
        ms=$(( (e - s) / 1000000 ))
        [ "$ms" -lt "$best" ] && best=$ms
    done
    echo "$best|$res"
}

printf "%-10s %10s %10s %10s   %s\n" bench C F++ ratio result
for f in *.fpp; do
    b="${f%.fpp}"
    [ -n "$only" ] && [ "$b" != "$only" ] && continue
    [ -f "$b.c" ] || continue     # gpubench has no C twin

    emcc -O2 "$b.c" -o "$out/$b.c.wasm" -s STANDALONE_WASM -s PURE_WASI=1 >/dev/null 2>&1 \
        || { echo "$b: emcc failed"; continue; }
    dotnet run --no-build -c Release --project "$root/src/Fpp.Cli" -- \
        build -o "$out/$b.f.wasm" "$f" >/dev/null 2>&1 \
        || { echo "$b: fpp build failed"; continue; }

    # a cold run first so the measured three are all warm
    "$wt" run -W gc=y,exceptions=y "$out/$b.c.wasm" >/dev/null 2>&1
    "$wt" run -W gc=y,exceptions=y "$out/$b.f.wasm" >/dev/null 2>&1

    cr=$(bestof3 "$wt" run -W gc=y,exceptions=y "$out/$b.c.wasm")
    fr=$(bestof3 "$wt" run -W gc=y,exceptions=y "$out/$b.f.wasm")
    cms="${cr%%|*}"; fms="${fr%%|*}"
    fres="${fr#*|}"
    ratio=$(awk -v c="$cms" -v f="$fms" 'BEGIN { if (c > 0) printf "%.2fx", f / c; else printf "-" }')
    printf "%-10s %9sms %9sms %10s   %s\n" "$b" "$cms" "$fms" "$ratio" "$fres"
done

#!/usr/bin/env bash
# The benchmarks as a NO-REGRESSION gate.
#
# Three things are checked, and only one of them is a timing:
#
#   1. the ANSWER. Every twin prints a checksum and they must agree with the
#      recorded one. This is the cheap half and it never flakes — it catches
#      a benchmark that stopped computing what it used to.
#   2. the BOUNDS CHECKS each program still emits. A static count, stable to
#      the instruction, and the thing that would silently rot if the proof
#      pass lost a rule. Read the EMITTED count: a proven access takes the
#      fast path and never reaches the counter.
#   3. the TIME — ONLY with --timing, and never inside run-gates.sh.
#
# On (3): the gate suite runs eight jobs at once, and under that load these
# numbers trebled — avl went from 1990ms to 6553. A timing check cannot
# share a machine with a build farm, so the default run does (1) and (2)
# only, which are load-independent and catch the regressions that actually
# happened here: a checksum change means the program stopped computing what
# it did, and a rise in emitted checks means the proof pass lost a rule (the
# sqrt wrapper, worth 2.1x, would have shown up as neither — see below).
#
# Run --timing yourself on a quiet machine. Its ceiling is 1.5x of the
# recorded baseline, loose enough to ignore the 10-20% this box drifts and
# tight enough to catch a 2x.
#
#   ./regress.sh            # answers + bounds-check counts (the gate)
#   ./regress.sh --timing   # ... and times, on a QUIET machine
#   ./regress.sh --record   # rewrite baseline.txt
set -u
cd "$(dirname "$0")"
root=$(cd ../../.. && pwd)
wt="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
base=baseline.txt
record=0
timing=0
[ "${1:-}" = "--record" ] && record=1
[ "${1:-}" = "--timing" ] && timing=1

out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
fail=0
results=""

for f in *.fpp; do
    b="${f%.fpp}"
    [ "$b" = "gpubench" ] && continue

    stats=$(FPP_BOUNDS_STATS=1 "$fpp" build -o "$out/$b.wasm" "$f" 2>&1 >/dev/null | grep -oE "BOUNDS: [0-9]+" | grep -oE "[0-9]+")
    [ -z "$stats" ] && stats=0
    if [ ! -f "$out/$b.wasm" ]; then
        echo "FAIL  $b: did not build"
        fail=1
        continue
    fi

    # warm the module cache, then best of three if anyone is timing
    ans=$("$wt" run -W gc=y,exceptions=y "$out/$b.wasm" 2>&1 | tail -1)
    best=0
    if [ "$timing" = 1 ] || [ "$record" = 1 ]; then
        best=9999999
        for _ in 1 2 3; do
            s=$(date +%s%N)
            "$wt" run -W gc=y,exceptions=y "$out/$b.wasm" >/dev/null 2>&1
            e=$(date +%s%N)
            ms=$(( (e - s) / 1000000 ))
            [ "$ms" -lt "$best" ] && best=$ms
        done
    fi
    results="$results$b $ans $stats $best"$'\n'

    if [ "$record" = 0 ]; then
        want=$(grep "^$b " "$base" 2>/dev/null)
        if [ -z "$want" ]; then
            echo "FAIL  $b: no baseline (run --record)"
            fail=1
            continue
        fi
        wans=$(echo "$want" | awk '{print $2}')
        wchk=$(echo "$want" | awk '{print $3}')
        wms=$(echo "$want"  | awk '{print $4}')
        if [ "$ans" != "$wans" ]; then
            echo "FAIL  $b: answer $ans, baseline $wans"
            fail=1
        elif [ "$stats" -gt "$wchk" ]; then
            # TWO causes, and the SHAPE tells them apart: a rise on one or
            # two benchmarks is the proof pass losing a rule, which is the
            # one worth chasing. The same rise on EVERY benchmark is a new
            # prelude function getting linked, carrying checks of its own —
            # rebaseline that one after confirming the answers held.
            echo "FAIL  $b: $stats bounds checks emitted, baseline $wchk — proof rule lost, or (if all of them moved) a newly linked prelude function"
            fail=1
        elif [ "$timing" = 1 ]; then
            ceil=$(( wms * 3 / 2 ))
            [ "$ceil" -lt 20 ] && ceil=20      # a 10ms benchmark is all noise
            if [ "$best" -gt "$ceil" ]; then
                echo "FAIL  $b: ${best}ms against a ${wms}ms baseline (ceiling ${ceil}ms)"
                fail=1
            fi
        fi
    fi
done

if [ "$record" = 1 ]; then
    printf '# benchmark answer bounds-checks ms — rewritten by ./regress.sh --record\n' > "$base"
    printf '%s' "$results" >> "$base"
    echo "PERF: baseline recorded for $(printf '%s' "$results" | wc -l) benchmarks"
    exit 0
fi

n=$(printf '%s' "$results" | wc -l)
if [ "$fail" = 0 ] && [ "$timing" = 1 ]; then echo "PERF: $n ok (answers, bounds-check counts, times under 1.5x baseline)"
elif [ "$fail" = 0 ]; then echo "PERF: $n ok (answers and bounds-check counts; --timing for the clock)"
else echo "PERF: regressions above"; fi
exit $fail

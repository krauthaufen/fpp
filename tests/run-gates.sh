#!/usr/bin/env bash
# Parallel gate driver. Every gate script is hermetic (mktemp sandbox, no
# rebuild, read-only use of the Release fpp binary), so they run
# CONCURRENTLY up to the core count instead of one after another.
#
#   ./run-gates.sh            # all tooling gates + conformance (~fastest)
#   ./run-gates.sh --full     # also fixpoint, fixpoint self, unit suite —
#                             # the three heavyweights, started FIRST so the
#                             # small gates fill in around them
#   ./run-gates.sh name ...   # just the named gates (basename, no .sh)
#
# The compiler is NOT built here: build once, then gate. A failed build
# leaves the old binary in place — check the build's own error count.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
logs=$(mktemp -d); trap 'rm -rf "$logs"' EXIT
jobs=$(nproc 2>/dev/null || echo 4)

full=0
only=()
for a in "$@"; do
  case "$a" in
    --full) full=1 ;;
    *) only+=("$a") ;;
  esac
done

# name|command — conformance counts as one gate (its own runner is serial
# but cheap per suite; the heavy oracle side is cached in expected/)
gates=()
for g in "$here"/tooling/cback/*-gate.sh; do
  gates+=("$(basename "$g" .sh)|$g")
done
gates+=("hkt-gate|$here/tooling/hkt-gate.sh")
gates+=("pkg-gate|$here/tooling/pkg-gate.sh")
[ -x "$here/tooling/jsinterop/jsinterop-gate.sh" ] && gates+=("jsinterop-gate|$here/tooling/jsinterop/jsinterop-gate.sh")
[ -x "$here/tooling/gc/cleanup-gate.sh" ] && gates+=("cleanup-gate|$here/tooling/gc/cleanup-gate.sh")
gates+=("conformance|$here/conformance/run.sh")
gates+=("conformance-neg|$here/conformance/neg.sh")
if [ "$full" = 1 ]; then
  # heaviest first, so they overlap the whole small-gate tail. The unit
  # suite's sequenced adaptive test (an 8-minute in-process compile) runs
  # as its OWN job: FPP_GATE_SKIP_ADAPTIVE skips it in the main run and
  # the filtered job runs only it.
  # the two fixpoint modes share GetTempPath()/fpp-fixpoint — give each
  # its own TMPDIR so they can run concurrently
  mkdir -p "$logs/tmp-self" "$logs/tmp-corpus"
  mkdir -p "$logs/tmp-linself"
  gates=("fixpoint-linself|TMPDIR=$logs/tmp-linself dotnet fsi $root/tests/bootstrap/fixpoint.fsx linear self"
         "unit-adaptive|dotnet run -c Release --no-build --project $root/tests/Fpp.Tests -- --filter-test-list 'adaptive suite'"
         "unit-suite|FPP_GATE_SKIP_ADAPTIVE=1 dotnet run -c Release --no-build --project $root/tests/Fpp.Tests"
         "fixpoint-lincorpus|TMPDIR=$logs/tmp-corpus dotnet fsi $root/tests/bootstrap/fixpoint.fsx linear"
         "${gates[@]}")
fi

if [ ${#only[@]} -gt 0 ]; then
  filtered=()
  for g in "${gates[@]}"; do
    n=${g%%|*}
    for o in "${only[@]}"; do [ "$n" = "$o" ] && filtered+=("$g"); done
  done
  gates=("${filtered[@]}")
fi

running=0
pids=()
names=()
start=$(date +%s)
for g in "${gates[@]}"; do
  n=${g%%|*}; cmd=${g#*|}
  while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do wait -n || true; done
  ( bash -c "$cmd" >"$logs/$n.log" 2>&1; echo $? > "$logs/$n.rc" ) &
  pids+=($!); names+=("$n")
done
wait

pass=0; fail=0
for n in "${names[@]}"; do
  rc=$(cat "$logs/$n.rc" 2>/dev/null || echo 99)
  if [ "$rc" = 0 ]; then
    printf 'OK      %-22s %s\n' "$n" "$(tail -1 "$logs/$n.log")"
    pass=$((pass+1))
  else
    printf 'FAIL    %-22s (rc=%s)\n' "$n" "$rc"
    tail -5 "$logs/$n.log" | sed 's/^/        /'
    fail=$((fail+1))
  fi
done
echo "GATES: $pass ok, $fail failed in $(( $(date +%s) - start ))s (jobs=$jobs)"
[ "$fail" = 0 ]

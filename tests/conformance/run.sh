#!/usr/bin/env bash
# Differential conformance gate (docs/WASMLIN-SELFHOST-STATUS.md §6 item 5).
#
# Each suites/<name>.fpp is a self-checking test file in the COMMON F#/F++
# subset (the stdlib/dotnet.fpp discipline): it prints per-failure lines and
# ends with `DONE tests=N failures=0`. The ORACLE is `dotnet fsi` — its
# stdout is cached in expected/<name>.out (regenerate with --regen after
# editing a suite; fsi startup is seconds per file, the cache keeps the gate
# fast and hermetic). The gate compiles each suite with `fpp build --gc`,
# runs it under wasmtime, and diffs stdout against the oracle byte for byte.
#
#   ./run.sh                 # gate every suite
#   ./run.sh letrec          # gate one suite
#   ./run.sh --regen [name]  # refresh expected/ from dotnet fsi
#
# skip.txt lists `name: reason` lines for suites known not to fit the subset.
set -u
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
fpp="${FPP:-$root/src/Fpp.Cli/bin/Release/net10.0/fpp}"
wt="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

regen=0
if [ "${1:-}" = "--regen" ]; then regen=1; shift; fi
only="${1:-}"

pass=0; fail=0; skipped=0
for f in "$here"/suites/*.fpp; do
  b=$(basename "$f" .fpp)
  [ -n "$only" ] && [ "$b" != "$only" ] && continue
  if grep -q "^$b:" "$here/skip.txt" 2>/dev/null; then
    skipped=$((skipped+1)); continue
  fi
  if [ "$regen" = 1 ]; then
    # the fsi copy drops the `module M` header (a script treats the rest as
    # top-level; a named top-level module is not script syntax) — the same
    # transform the stdlib oracle tests use
    sed '0,/^module /{/^module /d}' "$f" > "$out/$b.fsx"
    if ! timeout 180 dotnet fsi "$out/$b.fsx" >"$out/$b.exp" 2>"$out/$b.fsierr" </dev/null; then
      echo "FSIERR  $b"; sed -n '1,5p' "$out/$b.fsierr"; fail=$((fail+1)); continue
    fi
    if ! grep -q "failures=0$" "$out/$b.exp"; then
      echo "FSIFAIL $b (oracle run did not end failures=0)"; tail -3 "$out/$b.exp"; fail=$((fail+1)); continue
    fi
    cp "$out/$b.exp" "$here/expected/$b.out"
    echo "REGEN   $b ($(grep -c . "$here/expected/$b.out") lines)"
    continue
  fi
  if [ ! -f "$here/expected/$b.out" ]; then
    echo "NOEXP   $b (run --regen first)"; fail=$((fail+1)); continue
  fi
  if ! "$fpp" build --gc -o "$out/$b.wasm" "$f" >"$out/$b.buildlog" 2>&1; then
    echo "BUILDERR $b"; sed -n '1,5p' "$out/$b.buildlog"; fail=$((fail+1)); continue
  fi
  # 128 MB heap: the ported originals allocate at .NET scale (forexpression
  # builds ~500k cons cells live), and the default 16 MB is a self-host
  # tuning choice, not a language limit
  if ! timeout 180 "$wt" run -W gc=y,exceptions=y --env FPPRT_HEAP_MB=128 "$out/$b.wasm" >"$out/$b.act" 2>"$out/$b.trap"; then
    echo "TRAP    $b"; tail -4 "$out/$b.trap"; fail=$((fail+1)); continue
  fi
  if diff -q "$here/expected/$b.out" "$out/$b.act" >/dev/null; then
    echo "OK      $b"
    pass=$((pass+1))
  else
    echo "DIFF    $b"
    diff "$here/expected/$b.out" "$out/$b.act" | head -10
    fail=$((fail+1))
  fi
done
echo "CONFORMANCE: $pass ok, $fail failed, $skipped skipped"
[ "$fail" = 0 ]

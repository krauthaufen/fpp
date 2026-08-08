#!/usr/bin/env bash
# The pick comparison: the compiler prints every instance selection it
# made over concrete arguments, and check-picks.py re-derives each winner
# with none of the compiler's code. Any disagreement fails. Needs the
# Release build (dotnet build -c Release).
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fail=0
total=0
for f in \
    tests/tooling/hkt.fpp tests/tooling/hktns.fpp tests/tooling/clsmem.fpp \
    tests/tooling/exist.fpp tests/tooling/hktgadt.fpp \
    playground/classes.fpp stdlib/dotnet.fpp
do
    out=$(cd "$root" && dotnet run -c Release --no-build --project src/Fpp.Cli -- picks "$f" 2>/dev/null | python3 "$here/check-picks.py")
    rc=$?
    echo "$f: $out"
    total=$((total + 1))
    [ $rc -ne 0 ] && fail=1
done
[ $fail -eq 0 ] && echo "pick check: all $total programs agree"
exit $fail

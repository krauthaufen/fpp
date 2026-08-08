#!/usr/bin/env bash
# Bounded model checks of the class-resolution rules (DESIGN.md,
# "Typeclasses: The rules"). Two lemmas must be theorems (UNSAT: the
# solver searched every program in the bounded universe and found no
# counterexample) and two must have witnesses (SAT: the solver
# rediscovers, by search, the two bugs that were first found by hand).
# A flip either way is a rules regression, not noise.
set -u
here=$(cd "$(dirname "$0")" && pwd)
if command -v clingo > /dev/null; then
    clingo () { command clingo "$@"; }
elif [ -x "$HOME/.venvs/clingo/bin/python" ]; then
    clingo () { "$HOME/.venvs/clingo/bin/python" -m clingo "$@"; }
else
    echo "clingo not found (install: python3 -m venv ~/.venvs/clingo && ~/.venvs/clingo/bin/pip install clingo)" >&2
    exit 2
fi

fail=0
check () { # file expected(SAT|UNSAT)
    local f=$1 want=$2
    clingo --quiet=1 $scope 1 "$here/$f" > "$here/.last.out" 2>&1
    # pyclingo exits 0 either way: read the verdict from the output
    local got
    if grep -q '^UNSATISFIABLE' "$here/.last.out"; then got=UNSAT
    elif grep -q '^SATISFIABLE' "$here/.last.out"; then got=SAT
    else got=ERROR; sed -n '1,12p' "$here/.last.out"
    fi
    if [ "$got" = "$want" ]; then
        echo "ok   $f: $got  ${scope:-(base scope)}"
        if [ "$want" = SAT ]; then
            grep -A1 '^Answer' "$here/.last.out" | tail -1 | fold -s -w 78 | sed 's/^/       /'
        fi
    else
        echo "FAIL $f: expected $want, got $got"
        fail=1
    fi
}

# Scope A — the base scope: two atoms, unary list, depth 2, 3 files
scope=""
check l1-ground-coherent.lp   UNSAT
check l2-orphans-needed.lp    SAT
check l3-eager-commit.lp      SAT
check l4-specificity-order.lp UNSAT
# Scope B — wider signature: a second user-declared atom and a BINARY
# constructor (incomparability shapes unary cannot express), 4 files
scope="-c with_mine2=1 -c with_pair=1 -c dmax=1 -c nfiles=4"
check l1-ground-coherent.lp   UNSAT
check l2-orphans-needed.lp    SAT
check l3-eager-commit.lp      SAT
check l4-specificity-order.lp UNSAT
# Scope C — deeper and bigger: depth 3, 4 files, 4 instances
scope="-c dmax=3 -c nfiles=4 -c ninsts=4"
check l1-ground-coherent.lp   UNSAT
check l2-orphans-needed.lp    SAT
check l3-eager-commit.lp      SAT
check l4-specificity-order.lp UNSAT
rm -f "$here/.last.out"
exit $fail

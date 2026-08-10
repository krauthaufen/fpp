# Known issues

One directory, one file per open bug, each the SMALLEST program that still
shows it. They are not part of any gate — a gate that is allowed to fail
teaches nothing — but every one of them is a real, reproducible defect, and
the diagnosis at the top of the file is what the next person needs.

Run one with:

```bash
dotnet run -c Release --project src/Fpp.Cli -- build -o /tmp/x.wasm \
    tests/known-issues/<name>.fpp
~/.wasmtime/bin/wasmtime run -W gc=y,exceptions=y /tmp/x.wasm
```

* `let-rec-and-group-self-host.fpp` — a `let rec ... and` group inside the
  `lower` function miscompiles under SELF-HOST only. Not reproduced in
  isolation; the note records exactly what was ruled out. Kept as the
  record of a shape to avoid, not a live defect.

Fixed and removed (see git history for the repros):
`member-applied-dot-chain` (the forced dot pass conceded success on any
known receiver with no candidate — `universal () || true` — so every
misspelled member sailed through check and stubbed; the concession now
extends to the universal object members alone, and a member name known
NOWHERE errors at check naming the receiver's type — `(1.5).Bogus`,
`r.Bogus`. A name known SOMEWHERE, `Zero<float>.Zero` included, is left
to the by-name binder, which the port's arity-split sibling shape
legitimately needs; tightening that means fixing same-name member
registration across the arity split first),
`generic-instance-operator-body` and `instance-body-second-context-var`
(both faces of one arc: parked field reads resolved AFTER numeric
defaulting, so the guess ran before the information and ground a generic
instance's variable to int, freezing its member template at int layouts;
and the dynamic arithmetic helpers covered int-and-f64-on-plus only, so
everything else unboxed a float as an int — dots now resolve first,
dropped per-stamp constraints pull their result variables along, and
+,-,*,/ dispatch on the boxes at run time),
`generic-class-through-interface` (the Enumerator shape: the enclosing
member is not layout-dependent, so its call classified CANON and ran the
template, whose inner construction canonicalized against packed fields — a
class member called at a concrete non-uniform instantiation now STAMPS,
and the ctor family it constructs specializes with it; regression lives in
`tests/tooling/genericenum.fpp`),
`use-new-in-match-arm` (a match-arm body starting with `use` fell out of
the clause — the arm-body gate now accepts every statement keyword a block
does; regression lives in `tests/tooling/usearm.fpp`),
`member-body-early-pick` (a class member body froze its instance pick to
its own file's best candidate — a named use whose constraint still holds
a variable now rides the stamp marker and is resolved per copy against
the whole program's instances),
`cross-module-specificity` (a generic let binding in an earlier file
committed its constraint to the general instance before a later file's
more specific one existed — an OPEN instance match in a let body now
defers to the stamp, where the table is the whole program's; type and
instance bodies still commit eagerly, see DESIGN.md rule 5),
`print-class-polymorphic` (class-polymorphic print converted as int) and
`user-type-shadows-prelude-type` (a user type merging with a prelude type
of the same name) both pass as of the adaptive-port arc.

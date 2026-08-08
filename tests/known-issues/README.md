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

* `generic-class-through-interface.fpp` — a generic class constructed
  inside another generic class' member (the .NET `Enumerator<'a>` shape)
  canonicalizes the inner instantiation and traps reading `Current`. The
  diagnosis at the top of the file still holds. One fix is PAID FOR and
  reverted: running Link's layout passes (transitive marking → vtable
  propagation → ctor forcing) to a shared fixpoint repairs this repro, but
  the repro NEEDS the second generation — the enclosing member must stamp
  before its constructor argument is concrete — and second-generation
  forcing cascades into classes whose instances also arrive canonically. A
  generic `static let` value (`CountingHashSet.trace.tempty`) is evaluated
  ONCE, so its construction cannot stamp, and a newly-stamped accessor
  casting that canonical object traps ("[ASet] reduce group",
  `Store <- ComputeDelta_int`). A layout-variant-field guard does not save
  it either: the cascade is required by this repro and fatal to those
  singletons whatever the fields look like. The mechanism that actually
  closes it is canonical code constructing the RIGHT STAMP dynamically —
  descriptor-carried constructors — which is runtime work, not another
  analysis pass.
* `let-rec-and-group-self-host.fpp` — a `let rec ... and` group inside the
  `lower` function miscompiles under SELF-HOST only. Not reproduced in
  isolation; the note records exactly what was ruled out. Kept as the
  record of a shape to avoid, not a live defect.

* `member-body-early-pick/` — needs two files, so it is a directory:
  `fpp build a.fpp b.fpp`. A class MEMBER body that needs an instance at
  the class's own type variable picks from the instances visible in its
  own file, and the pick is baked into every later copy of the class —
  so `Box<Mine>.Same` answers 1 where B's `SE<Mine>` says 999. The same
  program with `Box` replaced by a plain generic `let` answers 999,
  because a let's requirement rides its type to each use. This is the
  corner DESIGN.md rule 5 documents; the fix is giving member bodies the
  same ride.

Fixed and removed (see git history for the repros):
`cross-module-specificity` (a generic let binding in an earlier file
committed its constraint to the general instance before a later file's
more specific one existed — an OPEN instance match in a let body now
defers to the stamp, where the table is the whole program's; type and
instance bodies still commit eagerly, see DESIGN.md rule 5),
`print-class-polymorphic` (class-polymorphic print converted as int) and
`user-type-shadows-prelude-type` (a user type merging with a prelude type
of the same name) both pass as of the adaptive-port arc.

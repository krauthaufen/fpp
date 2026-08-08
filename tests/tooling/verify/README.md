# Searching every small program for rule-breaking cases

`run.sh` (needs clingo; `python3 -m venv ~/.venvs/clingo &&
~/.venvs/clingo/bin/pip install clingo`). Sub-second, deterministic.

The instance rules in DESIGN.md ("Typeclasses: The rules") make claims of
the form "no program can do X". You cannot unit-test a claim like that —
a test suite only tries the programs someone thought of. What you can do
is hand the claim to a solver together with a SIZE LIMIT, and let it try
**every** program under that limit: every way of placing instances, type
declarations and a call across ordered files. Four checks, and the
expected outcome of each is part of the gate:

* **l1-ground-coherent — must find nothing.** Claim: once a call's types
  are fully spelled out (no type variables left), the instances visible
  in the files so far give the same winner as the whole program would.
  The search finds no program where they differ — provided the no-orphans
  rule holds and every type is declared before it is used. This is the
  fact that makes "wait and decide later" safe: once the types are
  concrete, waiting longer changes nothing.
* **l2-orphans-needed — must find an example.** Drop the no-orphans rule
  and the search immediately builds the bad program: one class, one type,
  two answers depending on which file asks. That is the bug we first
  found by hand (its compiled twin: ClassTests "an orphan instance is
  rejected").
* **l3-eager-commit — must find an example.** No-orphans alone is not
  enough: a generic function that picks its instance in its OWN file,
  before later files exist, picks wrong. The search reconstructs exactly
  the cross-module bug that motivated the compiler change (ClassTests "a
  later file's more specific instance wins at the stamp").
* **l4-specificity-order — must find nothing.** "More specific" here
  means "accepts strictly fewer types". The search confirms that
  relation never loops or contradicts itself, so "the unique most
  specific match" is a meaningful phrase. (This one is really a check on
  the model's own encoding: if a later edit makes "more specific" stop
  meaning "accepts fewer", it fails loudly.)

## Why a size limit is not a blank spot

"Nothing found" is only exhaustive up to the limit. Two things carry it
further:

* **Any big bad program contains a small one.** A violation of l1 needs
  just one instance: not yet visible at the call, yet good enough to win.
  The no-orphans rule forces that instance's file to declare a type its
  shape names; the way matching works, every type its shape names must
  appear in any call it can win; and declare-before-use puts all the
  call's types at or before the call. One instance, one type, three file
  positions — strip anything else from a large bad program and a small
  bad program remains. The two atoms are what is left after stripping.
* **The verdicts do not move when the limit does.** run.sh re-runs all
  four checks at three sizes grown along different axes — a second
  user-declared type, a two-slot type shape (a pair, which one-slot
  shapes cannot imitate), deeper nesting, more files, more instances.
  Same outcomes everywhere. The "must find an example" checks need no
  such argument at all: an example is proof, whatever its size.

## What no size limit can see

The model decides "does this instance fit / which fits better" by
LISTING the types each shape accepts. The compiler decides it by WALKING
the two shapes side by side (`matchTy` in Classes.fs). Bugs that live in
the walking are invisible here at any size — and they are real: the same
variable used twice in one instance (`P2<'a,'a>`, "both arguments the
same type") was mishandled by the walking code while the model, which
cannot even express the mistake, stayed green. Poking that blind spot by
hand found and fixed it (ClassTests "a repeated variable in a head only
matches equal arguments"). The counterpart gap earlier was `sameType`
missing the applied-variable case. The answer for that side is not a
bigger search but the comparison harness next to this file:
`check-picks.sh` has the compiler print every selection it made over
concrete arguments (`fpp picks <files>`), and `check-picks.py`
re-derives each winner — its own parser, its own matcher, its own
"accepts fewer types", none of the compiler's code — and fails on any
disagreement. A concrete `deferred` fails outright: waiting is only for
arguments still holding a variable, and a concrete wait was exactly the
repeated-variable bug's shape. Corrupting a pick line flips the check
red, so its green means something.

Also deliberately outside the model: picking an instance to make
progress on inference when only one candidate is left (file-order
sensitive by design, like the inference it serves); `when` conditions on
instances (they never influence the pick — rule 7 — so they cannot
change a winner); associated types; and the early pick inside type and
instance bodies — that one is a real, open wrong-answer corner, recorded
as `tests/known-issues/member-body-early-pick/`.

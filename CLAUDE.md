# Working in this repo

## A diagnostic names the sub-expression that is wrong

`let x : int = "s"` used to be reported at `x`, which is correct as written —
the string is the problem. Every position now blames the offending
sub-expression, and the column matches F#'s on all fourteen shapes checked
(annotation, argument, record field, list/array/tuple element, if branch,
match arm, return, assignment, range bound, while condition, unbound value,
unknown member).

Two things make it work, and both are easy to undo by accident:

* an offset captured BEFORE the arms that shadow it. In the binary-operator
  branch `r` is rebound to a result TYPE, so `nodeOff op.Offset r` inside
  those arms does not compile — `lOff`/`rOff` are taken where the operand
  nodes are still in scope.
* CASCADE SUPPRESSION. A tuple element reports at the element, and then the
  ascription would report the whole tuple as well: two errors for one
  mistake, the vaguer one first because diagnostics sort by offset. The
  ascription checks whether the body already added a diagnostic and, if so,
  ties the types without reporting.

Not everything should blame an operand. `1 + "s"` reports `no instance
Add<int, string>` AT THE OPERATOR, where F# blames the right operand — the
failure really is that the operator has no instance for that pair, and
naming one operand would misdescribe it.

## Each boxed scalar has its OWN class id

`box true :? int` was true, `box true :?> int` handed back 1, and — the part
that mattered — `1 :> obj` compared EQUAL to `true :> obj`, because every
32-bit scalar shared one class id. The id is `CID_BOX_BASE + kind` now, one
per scalar type, and the payload stays a single word at HDR.

Two attempts failed first, and both are worth not repeating:

* storing the kind as a SECOND word in the box. It works, but it moves the
  payload to HDR+4, and the hash of a boxed value then covers the kind too —
  so `hash (box true)` stopped matching F#. A separate id per type keeps the
  object one word and the hash the payload's.
* writing the literal-suffix decoder with `System.Char.IsDigit` and
  `ToLowerInvariant`. This file is compiler SOURCE: both stubbed, and stage-1
  trapped the moment anything boxed a literal. Bisecting blamed the type test
  three times before the real cause showed — when a backend change breaks the
  self-host but not the .NET build, suspect the SUBSET before the logic.

The kind comes from `rawScalarNameOfExpr`, which mirrors `refKindOfExpr`'s
RKRaw paths so a box always knows what it holds — including the literal
suffix, since `3uy` is a byte and boxing it as an int made `box 3uy :? byte`
false.

## A boxed 32-bit scalar is a real object

`box 1` and `1 :> obj` allocate a box with its own class-id header (CID_BOXW),
exactly as float, int64 and string are boxed. Before, an `obj` holding an int
WAS the raw int, and the scalar type test read its low bit as a tag that the
raw-i32 arc had removed — so `box n :? int` answered true only for ODD n,
`:?>` trapped on the rest, and a large or negative value was dereferenced as
a pointer. `box true` and `box 'a'` passed by accident: 1 and 97 are odd.

Four places have to agree, and a name in one list but not another is a value
that tests true and then unboxes as a pointer: `lowTypeTest`, the `:?>`
unwrap, the `:? t as v` binder (test FIRST, then bind the payload — unboxing
a non-box reads rubbish), and `coerceToParams` at a call. `boxedScalarName`
is the single list.

Restrict every one of these to `obj`. A blanket "the target is not a raw
scalar" test boxed float16, which IS a raw word but is not in
`rawScalarName` — three float16 unit tests caught it.

The C backend TAGS its scalars, so there `$box`/`$unbox` are the identity.
That is why the coercion is a Core PRIM rather than something the middle end
resolves: it says "coerce to obj" and each backend answers in its own model.

## Never ship a silently wrong answer

Documentation is for MISSING things. A construct this compiler accepts and
then answers incorrectly is not a known issue to write down — it is a defect
to FIX, or a construct to REJECT with a diagnostic. `tests/known-issues/`
may hold the first kind and never the second.

Three went out under that rule the day it was written:

* `decimal`. The `m` suffix was accepted and computed in binary, so
  `0.1m + 0.2m` answered 0.30000000000000004. There is no base-ten type
  here, so the suffix is a compile error now.
* units of measure. `[<Measure>]` declared an ordinary empty type and the
  `<m>` on a literal was PARSED AND DISCARDED — no part of the compiler
  ever knew the word — so `1.0<m> + 2.0<s>` answered 3 where F# rejects it,
  and `5.0<zzz>` was fine with zzz declared nowhere. Both halves are errors
  now, at the attribute and at the literal.
* integer `/` and `%` by zero. wasm's `div_s` TRAPS, and a trap is not
  catchable, so `try 1/0 with _ -> ...` ran its handler in F# and killed the
  program here. Guarded and raised now, like a bounds failure, so the same
  `with` sees it. A non-zero literal divisor skips the guard.

The shape to watch for is syntax that PARSES and is then ignored. It reads
as support, and the wrong answer arrives with no diagnostic anywhere. When
adding a feature, prefer rejecting the surface you have not implemented over
accepting it and doing something approximate.

F++ is a compiler that compiles itself. That single fact sets almost every
rule below: a change that looks fine and passes the unit tests can still be
wrong, because the compiler has to be able to build *its own source* and get
the same bytes twice.

## The gates

Run all three before claiming anything works. They take about twelve minutes
together, and they have each caught things review did not.

```bash
dotnet build -c Release                      # ~30 s
dotnet run  -c Release --project tests/Fpp.Tests      # ~4 min, 692 tests
tests/conformance/run.sh                              # 76 suites, fsi oracle
dotnet fsi  tests/bootstrap/fixpoint.fsx              # ~2 min, corpus
dotnet fsi  tests/bootstrap/fixpoint.fsx self         # ~7 min, THE gate
./tests/run-gates.sh --full                           # ~9 min, all 32, parallel
tests/tooling/perf/regress.sh --timing                # perf, on a QUIET box
```

There is ONE backend: wasm-linear over the fpprt/Whippet reactor (the C
backend shares its middle end). The wasm-GC backend — `BinDriver.fs`, the
`--wasmgc` flag, and the source maps that only it could emit — was deleted
once every gate ran on the linear one. `fixpoint.fsx` still accepts the
`linear` argument and ignores it.

`fixpoint.fsx self` is the real one: the compiler compiles its own sources,
and stage-1's output must equal stage-0's **byte for byte**. It has caught
bugs the unit suite missed — a `List.init` that counted down, an equality that
compared tree shape instead of contents. If you change the backend and only
the unit tests pass, you have not tested your change.

**A `let rec ... and` group inside `lower` miscompiled under SELF-HOST**
while the .NET build and every unit test passed. It looked for a long time
like the group's SHAPE — its size, its position among the surrounding
`let`s — and it was not. The cause was a FORWARD reference: the first
binding of a group calling a later one got a throwaway type variable, so
`(payload k).IsSome` written above `and payload ... : int option` never
learned its receiver was an option. The member stayed unresolved, Lower
emitted a bare field, and the backend answered `unreachable` — silent under
every diagnostic, `--strict` included. Fixed in Infer (`forwardVars`), and
`tests/conformance/suites/letrecand.fpp` covers the shapes.

The lesson that outlives it: a program that compiles clean and traps is an
inference gap reaching emission, not a backend bug. Dump the Core
(`FPP_CORE_DUMP=1`) and look for an access that did not lower — a `.M` still
sitting in the tree is a member the type never resolved.

Three details that will bite:

* **The prelude is an embedded resource.** Editing `stdlib/prelude.fpp` does
  nothing until you rebuild. A "green" run against a stale prelude is the
  oldest trap here — and a FAILED build leaves the old binary in place, so
  `dotnet run --no-build` afterwards happily runs the previous prelude. Read
  the build's error count, do not just pipe it to `grep -c`.
* **F# builds SIGSEGV (exit 139) under the sandbox.** Run with sandboxing
  disabled.
* **The dogfooding gate infers every `*.fs` in the repo with an empty
  prelude** and demands zero diagnostics. So compiler source has to be
  F++-inferable with NOTHING resolved — no prelude, no union cases. That is
  harsh on purpose: it is how a false positive in inference gets caught. It
  found the pattern-binder bug below.

## A synthetic local must not live in the source's PATH

Lower mints helper bindings at `<a node's offset> + <a bias>` in the file being
lowered, and the biases are small — 1000, 50000, 600000, 670000. The backend
keys its function table by `path:offset`. So in a source LONGER than the bias
the synthetic local lands on a real top-level function and is taken for one.

The interface eta parameter `_eta0` at offset 223,642 met `YieldFrom` at
893,642 in the 917 KB adaptive port. It was eta-expanded to that function's
arity, and the closure that came out read a FREE variable as its second
argument — so `cmp.Compare(key, n.Key)` answered on garbage and MapExt built a
tree that was not ordered. `containsKey` on the largest key was false at every
size, six of a hundred adaptive tests failed, and there was no diagnostic
anywhere.

Everything about it misleads. It is invisible below the bias, so no small
repro reproduces it — the same code in a 40-line file is correct. ANY edit
near the site moves every later offset and the collision disappears, which
makes a `printfn` probe "fix" the bug and reads exactly like a memory or GC
fault. It is not one: `FPP_GC_LOG` shows no collection, and the heap size
changes nothing. And the C backend is correct, because this eta-expansion is
the wasm backend's own.

They all live in `synPath` now, which is no file's path, so the collision
cannot happen at any size. If you add a synthetic binding, put it there —
never in `path`.

The tool that cracked it was `FPP_LAM_DUMP=$blamN`, which printed a lifted
lambda whose body was `(λ$e47. (_eta0 $e46 $e47))` — an inner lambda, with
`$e46` free. When a closure's dump names a variable nothing binds, look for
who else owns its key.

## The let-pattern classification lives in TWO files

Whether `let <pat> = e` is a simple binding or a DESTRUCTURE is decided by a
list of pattern kinds — and that list exists twice, once in Infer and once in
Lower. `ArrayPat` was in neither, so `let [| a; b |] = arr` typed as a simple
binding (a := the whole array) while lowering destructured it. The two
disagreed, and the symptom depended on the arity: one element gave a wrong
VALUE, two gave a type error at the next USE, nowhere near the binding.

Fixing one side alone is worse than fixing neither — that is the state where
inference and emission disagree. The comment above each list names the shapes
it covers; keep them identical.

## A qualified case pattern was a WILDCARD

`match c with Colour.Red -> .. | Colour.Green -> ..` took the FIRST arm for
every value. The type-qualified lookup in `recordQualifiedCase` was gated on
`idents.Length > 2` — written for `Inner.Colour.Green`, it never saw the
two-segment `Colour.Green`, where the type IS the whole prefix. Nothing was
recorded, so lowering found neither a binder nor a case and emitted `PWild`:
an irrefutable pattern. Every value took the first clause, silently.

The unknown-case diagnostic had the same hole — it covered the BARE
uppercase name only, so `Colour.Purple` on a type with no such case was
accepted and swallowed everything. It now reports through the same `missing`
channel whenever the prefix names a type that declares cases.

Worth generalising: this file's "Qualification, and the first-identifier
trap" section is about the same family, and the pattern side had been missed.
When a lookup for a dotted name is guarded by a SEGMENT COUNT, check the
smallest case — two segments is the common one, and it is the one an
arity-style guard tends to exclude.

## null is not the empty string, and the compare knew it was

String `=` lowers to `$str_cmp` (`ShStr` in structEqW), and both it and
`$streq` — which string PATTERNS compile to — began by loading the length
word from `ptr + 4`. For a null pointer that reads address 4, where a 0
happens to sit, so a null matched the EMPTY string: `("" = null)` answered
true and a null fell into a `| "" ->` clause. Both now test for null before
any load, and order null below the empty string the way .NET does.

`$eqv`, the generic structural walker, had it right all along — "a tagged
scalar, a null, or anything not addressable is equal only to itself". Only
the string-specialized paths skipped the check. When a specialization and a
general walker disagree, the specialization is usually the one that forgot
something.

`Unchecked.defaultof<string>` was a related miss: the `defaultof` token keys
`memberSites`, but there the entry is the TARGET type, not an owner — so the
string-member router turned it into a `$str.defaultof` primitive that does
not exist. Its own branch already answered null correctly; it just never ran.

And `isNull` used as a VALUE (`List.filter isNull`) hit the trap CLAUDE.md
already describes for `string`/`int`: emitted at its APPLICATION, so a bare
name reached the backend as an unknown and trapped. It eta-expands now, in
both Infer and Lower — the same two lists that note warns about.

## The seq widening compares NAMES, so check the arguments

`isSupertypeOf` answers on constructor names alone: `list` widens to `seq`
whatever the element types are. `unifyArg` then unified the arguments only
when they already fit, and DROPPED the mismatch otherwise — so
`String.concat "," [ 1; 2; 3 ]` type-checked and rendered three EMPTY
strings where F# rejects the call.

The mismatch is now a diagnostic, but only for the built-in container
widenings (`list`/`array`/`seq` into `seq`), where the element passes
straight through and so MUST pair. Two things it must NOT catch, both found
by the gates rather than by reasoning:

* a class widening to an interface — the `IOpReader` shape, where the class'
  own parameter is the ELEMENT and the interface's is the DELTA. They cannot
  pair, and the declared instantiation carries the real mapping.
* a NESTED widening — `array<array<string>>` reaching `seq<seq<'a>>` needs
  the inner array to widen too, which plain unification refuses. That case
  now recurses through `unifyArg` instead of erroring.

Report it directly with `vecAdd diags`, not by unifying the two whole types:
that path re-enters the same name-based widening and succeeds, so it says
nothing.

## A chosen constructor may live in ANOTHER file

Inference picks a constructor project-wide and records the WINNER'S OFFSET
(`ctorSites`). Lower resolved that offset through `defsAt`, which covers only
the file being lowered — so a prelude class' secondary constructor resolved
to nothing and the call quietly fell back to the primary. `ResizeArray<int>
([1;2;3])` type-checked, ran, and answered an EMPTY list: the argument was
simply dropped, with no diagnostic and no trap.

`foreignCtors` (Lower) indexes the project-wide member table by the `new`
keyword's offset — Resolve already keys an explicit constructor as
`Owner.new@<offset>` — and the lookup falls back to it.

The shape to remember: an OFFSET is only meaningful together with its file.
Any table keyed by a bare offset and consulted from another file's lowering
has this bug latent in it. The tell here was that the same class worked
verbatim in user code and failed in the prelude — when that happens, suspect
a cross-file table before suspecting the feature.

`new (args) as x = <delegate> then <body>` is what exposed it. That form now
DESUGARS in the parser to `new (args) = let x = <delegate> in (<body>; x)`,
which every later stage already handled — Resolve binds the let, Infer types
x from the delegate, Lower emits an `ELet`. Nothing downstream knows the form
existed. Parser-level desugaring is the cheap route for a construct that is
only sugar; the synthesized tree follows `apChain`'s conventions, including
`<bigconstant> + realOffset` for synthetic tokens, and the binder's
DEFINITION keeps the real token so hovers still point at the source.

## `inline` is real: the body is copied to every call site

`let inline` and `member inline` were parsed and DISCARDED — the exact
"parses and is then ignored" shape this file forbids. The marker now rides
a `DExport (v, "$inline")` beside the function's `DLet` (the `$jsimport`
precedent: no new IR case, and the package serializer carries it for free),
and `Optimize.inlineCalls` honors it: an inline-marked candidate bypasses
the SIZE threshold and the caller's growth budget, because the writer asked
for the copy. SRTP is deliberately out of scope — copy-to-call-site is the
half of the keyword that exists here.

What it does NOT bypass: the soundness guards. A body that crosses an obj
boundary, binds a type variable, is a stamped clone, or names itself is
wrong to copy no matter what the writer asked. Two spellings are rejected
outright because the keyword could only be a silent no-op: `let rec inline`
(the body would be copied into itself) and `abstract inline` (no known body
to copy).

Three consumers had to learn the marker is a NOTE, not an export: Link's
DCE roots (pinning it kept every fully-inlined body alive), the uncurry
shim's pin set, and WasmLin's export section. DCE also drops the marker
when its function dies, so no pass meets a DExport naming nothing.
`suites/inlinefn.fpp` pins the semantics; `FPP_INLINE_DBG=1` shows the
sites.

## byref-as-stack-offset is COMPLETE: every payload, and the two bugs

The final slice added "#r" — ANY reference or generic payload, one uniform
word. The slot lives on the SCANNED shadow stack (`$roots + $sp`), so the
collector traces it and REWRITES it when the pointee moves: this is the
fpprt_frame_pod idea one level up, and it is what makes a byref of a
ref-holding struct (a heap object here) sound on the stack. Better: a
mutable REF local is SLOTTED already — its value lives in a persistent root
slot kept current by every write-through — so `&refLocal` passes the
local's OWN slot address, no spill, no reload, and the aliasing is exact.

FORWARDING ships too: eligibility is a FIXPOINT (start from every
byref-payload param, drop what fails under the current set, repeat), so
`deep -> incTwice -> bump` rides one offset end to end — a forwarded param
is already a cell, a view or an offset, all of which the receiver
dispatches on, so forwarding needs no spill. Forwarded payloads are
VERIFIED equal (a mismatch would be silent memory corruption; the receiver
is demoted on conflict). Two hard-won keys: `BrParamPay` is keyed PER
FUNCTION because stamped clones share param VarIds — one flat dict let a
canonical clone's "#r" overwrite its float sibling's "#f64"; and the
tagged offset is unambiguous because byref params never otherwise receive
odd words.

TUPLED callees are covered: the byref is a PATTERN BINDER
(`λ_arg. match _arg with (b, p) -> ...`) and the caller passes a literal
tuple the backend spreads — the prepass recognizes the destructure lambda,
keys entries by ELEMENT index, and rewrites eligible elements inside the
ETuple argument. Tuple-FORWARDING (a binder passed on inside another
tuple literal) stays conservative: the body walk sees the bare binder
inside the ETuple and declines eligibility. Non-inlined tupled struct
byref: 135 ms / 31 B-per-call -> 55 ms / 0 B (inlined stays 9 ms).

The two bugs the finishing pass found, both the silent kind:

* **the statement-position dispatch.** `coreToLowS` has its own EIf arm,
  so a write dispatch followed by ANY statement bypassed the expression
  path's interception and lowered the ORIGINAL cell code — which, against
  a tagged offset, stored through an odd address into nowhere. The write
  VANISHED; a write in final-expression position worked. Every callee
  until then happened to end with its write, so gates were green. The
  statement path now delegates the marked shapes to the expression path.
  When an interception lives in one lowering path, audit the OTHER paths
  that can meet the same Core shape.
* **the stale alias on the else path.** A byref param is ROOTED: its reads
  go through a shadow-stack slot the collector updates, while its raw
  register goes stale across safepoints. The interception's alias copied
  the REGISTER, so the cell/view arm could store into a moved-from cell —
  e.g. when the write's own rhs allocated. The alias now registers as
  Slotted at the SAME address, and the tagged test reads through
  `brParamVal`. Pinned by a churn-through-array-element case in the
  byrefs suite under the semi shakeout.

## byref-as-stack-offset: the noalloc promise for byref calls

`&local` to a non-escaping callee involves no GC object at all now: the
caller spills the local's register to an `$ssp` scratch slot around the
call, passes the slot's address TAGGED AS A SCALAR — odd, so the collector
neither traces nor moves it, which is the whole GC story in one move — and
the callee's dispatch has a third arm doing raw loads and stores at the
untagged address. `noalloc-gate` asserts EXACTLY 0 bytes across a 1M-
iteration two-byref-call loop, beside the struct shapes.

`brOffPrepass` (WasmLin, Core level, BEFORE `cellScan` — dropping the view
before the scan is what keeps the local out of a cell) does both halves:

* a CALLEE param is eligible when its scheme is `ByRefCell` of an
  int-family payload and its every use is one of the two dispatch shapes
  Lower emits (`brReadShape`/`brWriteShape`). Anything else — stored,
  captured, returned, forwarded — keeps the heap paths, which stay sound
  for escapes.
* a CALLER'S hoisted view over an UNCAPTURED local converts when every use
  is a direct argument at an eligible position of a different function.
  The view binding is dropped entirely; each converted argument becomes a
  `$broff:` marker the backend lowers to reserve+spill+tagged-address,
  with the reload and `$ssp` release riding `ctx.BrPost` to run after the
  call (drained by the known-call arm, scoped so nested calls drain their
  own).

Traps met and designed around, worth keeping:

* the ELSE arm of the callee dispatch must re-lower the ORIGINAL shape —
  recursing on the same node re-fires the interception arm forever. The
  param is ALIASED to a fresh register first; the alias's key carries no
  `BrParamPay` entry, so the arm cannot match it.
* a view used under a NESTED LAMBDA would become a capture of the local
  after substitution — the exact cell-ification the rewrite exists to
  avoid. Rejected by checking the view var itself against every `ELam`.
* self-tail calls never return, so there is no frame to reload into — the
  prepass skips calls where the callee is the enclosing function.
* stamped clones SHARE param VarIds, so a key marked for one clone is seen
  in siblings — harmless: their tagged test is false for every cell and
  view (even words), so the raw arm is dead code there, never wrong code.

Payloads: the int family ("#w" — the slot holds the uniform word, both
arms agree with no conversion), the wide scalars ("#f64"/"#i64"/"#f32" —
the read JOINS ON A TYPED REGISTER with one flatBox after the LDo; box-elim
pushes through LDo, so an arithmetic consumer cancels it and the read
allocates nothing — joining on the word register instead re-boxes inside
the branch, where the peephole cannot see the pair), and BLITTABLE STRUCTS
(field chains are one typed load at the leaf's offset — `brFieldSpine`
joins the dotted path structAbiOf names leaves in; the write scatters via
lowStructBind, which peels the lets a computed literal arrives wrapped in;
a bare whole-struct read materialises, as .NET boxes a struct entering a
uniform context). Ref-holding structs next: they ride the runtime's
existing POD-frame root mechanism (`fpprt_frame_pod` — the C backend
already registers stack structs with `refoffs`-guided tracing).

THE INLINED CALLEE IS THE OTHER HALF, and it was found by measuring, not
predicted: with the callee inlined there is no call, so the offset
machinery never fires — the dispatch shapes operate on the view var IN THE
CALLER, and every Get materialised the payload (31 B per access on a V3).
Dispatch on a KNOWN view beta-reduces: the view IS `{Get=λ.tv; Set=λv.tv<-v}`,
so the read is `tv` and the write is an assignment. Three traps inside
that one fix, each costing a debugging round:

* the inliner binds the parameter as an ALIAS (`let b = _brl1`), so the
  reduction must follow the alias CLOSURE, not just the view var;
* the dead alias-lets must then be dropped, or they keep the view alive;
* a view whose every use REDUCED (total = 0) must still be DROPPED — a
  `total > 0` guard kept it, its lambdas kept capturing the local, and
  cellScan put the local in a heap cell after all: same 31 B, two layers
  further down.

Measured end to end (5M-iteration V3 extend loop, tupled callee):
135 ms / 31 B-per-call -> **9 ms / 0 B** — identical to writing the
mutation by hand. Non-inlined curried calls: 0 B via the slot path. The
int loop: 405 -> 118 ms, 0 B (plain-call floor 56 ms). `noalloc-gate`
pins both int and struct byref loops at EXACTLY zero. Both fixpoints
byte-exact with the pass converting sites inside the compiler itself.
`FPP_BROFF_DBG=1` prints each rewritten body.

## Why byrefs are not on the shadow stack, and what `&x` costs

The question is fair — the by-value struct ABI lives on the raw `$ssp`
stack, why not byrefs? Three reasons, each structural:

* **`$ssp` is unscanned and the collector MOVES.** The struct ABI is legal
  there because `structAbiOf` is all-scalar BY CONSTRUCTION and the slots
  are copies, never retained. A `byref<'T>` is a RETAINABLE reference and
  `'T` can be a heap type — an unscanned slot holding a heap pointer is an
  untraced edge, and under mmc a stale one even when the pointee lives.
* **a pointer into `$ssp` in a uniform argument register gets TRACED** —
  the collector would walk it as a heap object. Stack byrefs need a RAW
  parameter ABI, which byref-as-`'a` (accepted here) cannot have.
* **escapes are legal here, deliberately** (see the divergence above). A
  stack slot dies with its frame; keeping the escapes sound is exactly why
  the byref is a heap cell. Stack placement would need F#'s full escape
  analysis — adopted in order to LOSE a feature.

What `&x` actually cost was something else: a `ByRefView` (record + two
closures) built PER USE — 47 bytes per call in a loop passing `&acc`, all
three objects aliasing the same captured cell every iteration. `fixAddrs`
hoists the view to the LOCAL'S BINDING now: every view over one local is
the same closure pair over the same cell, so one copy serves every use
under it (an inner REBINDING of the name shadows and gets its own).
Measured: 47 -> 0 bytes per call; aliasing, the byref gate, and the
fsi-pinned suite all unchanged. `&field` / `&arr.[i]` still build per use —
the receiver and index differ per use, so there is nothing to share.

## byref escapes are sound, and the READ side had two holes

A byref here is a heap CELL, not a stack pointer, so every escape F#'s
safety analysis exists to forbid — a lambda receiving one, a return out of
the defining frame — is sound: the collector keeps the cell. Probing that
claim (rather than asserting it) found two real gaps on the READ side:

* **a byref-typed LOCAL did not dereference on read.** The `$deref` marker
  was gated on `byrefParams` — parameter DEFINITIONS only — so
  `let r : byref<int> = f ()` read back the cell object while `r <- v`
  wrote through it. The registration now covers a `let` with a WRITTEN
  `byref`/`outref` annotation, the same declaration-driven rule (and the
  only sound one: `ref<'a>` is the SAME ByRefCell type, and `let r = ref 5`
  must keep reading as the cell — the type cannot drive this, only the
  declaration can). F# rejects this binding outright (FS3226), so the
  behavior is a recorded DIVERGENCE, pinned by the tooling byref gate.
* **numeric printf holes accepted ANY type.** `%d` is polymorphic so every
  integer width fits and the recorded kind decides at expansion — but a
  type outside the family fell through every kind to the "?" renderer:
  `printfn "%d" cell` printed a question mark. Judged after inference now,
  the nullSites pattern: a hole whose settled type is a TCon outside the
  int family (or float family for %f/%e/%g) is an error; a still-variable
  type stays lenient for generic callers.

The pattern-match trap in the hunt: the binder registration matched
`vecToList before` against `GNode bp :: _` — but `before` STARTS with the
`let` keyword TOKEN, so the arm never fired and nothing said so. When a
registration has no visible effect, check the spine you matched against.

## The wrongly-accepted programs, second pass (2026-09-02)

Ten more rules from triaging the upstream corpus, every one verified to be
accepted-and-broken BEFORE the fix, not just accepted:

* **or-alternatives must agree on a binder's type.** `| x, 0.0 | 0, x ->`
  bound x at int in one arm, float in the other — each occurrence got its
  own fresh variable — and `string x` on input (3, 0.0) printed "0". A
  WRONG ANSWER, not a trap. In a match clause the binder's NAME now keys
  the type (`inClausePat` + a `$bind:` slot in the clause's pvars), so the
  alternatives unify. Parameters stay out: `let f (x : int) (x : string)`
  is legal shadowing.
* **`null` is not a value of a union, record, struct or scalar.** `let x :
  DU = null` built and trapped at the first match. Every null literal
  records its variable (`nullSites`) and is judged AFTER inference, so
  annotation and context still flow through it; a null at string/obj/class
  stays legal.
* **a union case must start uppercase.** Not just fidelity: this compiler
  reads a lowercase identifier in a case pattern as a BINDER whenever the
  case is out of scope, so a lowercase case silently stops matching the
  moment an `open` is missing.
* **extensions**: on a BUILTIN type (`type string with` — the member
  resolved to nothing and the statement USING it was dropped whole: ran,
  printed nothing, exit 0); a `let` in an extension (silently discarded,
  effects included); an `override` in an extension (dispatch never sees
  it, the original kept answering).
* **structs**: no abstract members (no vtable), no `inherit` (no base
  object), no INSTANCE `let` (the constructor body was dropped whole —
  `static let` stays legal, the adaptive port's CountingHashSet uses it),
  no field of the struct's own bare type (no finite size — `S option`
  stays legal, the option is a heap reference).

Three more from the follow-up sweep, same standard:

* **a member may not take a record FIELD's name.** `member r.Name = r.Name`
  resolved its own body's `r.Name` to the MEMBER and the program HUNG in
  the recursion at run time. Caught in `registerField`, where the field's
  entry (`DefKey = None`) is right there to ask.
* **an active pattern's return type is checked at the DEFINITION.** The
  parser spells `(|A|B|)` as the binder `$ap$A$B`, so the let walk knows
  the case count and partiality: total multi-case must answer
  ActiveChoiceN, partial an option, a single total case its payload (no
  constraint). Left to the uses, an unused bad definition was accepted
  outright and a used one failed far from the mistake.

All fifteen have neg-conformance cases with the fsi oracle behind them.
Upstream corpus: 254 accepted at the session's start, 220 after. What
remains is dominated by structurally-N/A areas (byref-as-heap-cell,
quotations, AttributeUsage, accessibility-on-override) and generalization
subtleties that are permissive rather than wrong.

## A slot that nothing fills is a trap, and the declaration must say so

Two rules, both found by triaging the upstream NEGATIVE corpus, and both of
the kind this compiler refuses to ship — accepted at compile time, dead or
wrong at run time.

* **an abstract slot a concrete class never fills.** The row stays 0,
  `$novt`, and the call traps when reached. `Derived` inheriting an
  `[<AbstractClass>] Base` without implementing `Speak` built clean and
  trapped. Now reported at the derived class.
* **two abstract members of ONE name on an interface.** A row is keyed by
  (interface, member), so the second takes the first's slot and one of them
  is unreachable. The class-member side of this rule was already enforced;
  this is the interface side.

The unimplemented-slot check is the one with false positives waiting, and
each exemption below was a real gate failure, not a precaution:

* an INTERFACE inheriting an interface inherits slots it does not fill —
  the implementing class does. `IOpReader\`2 : IAdaptiveObject`.
* a TYPE EXTENSION (`type X with ...`) is not a declaration of X: it has
  members and a base and reads as a concrete type to every other test.
* `abstract` paired with `default` is already filled, so a derived class
  need not override. `concreteMembers` records what each type supplies a
  BODY for — default, override, or a plain member — and the walk clears a
  slot when any nearer ancestor supplies one.
* `[<AbstractClass>]` opts out — but `abstractTypes` is keyed by the token
  as WRITTEN while the walk carries the ARITY-DECORATED name, so an
  abstract class at a second arity (`AbstractReader\`2`) looked concrete.
  Ask under both.

The chain is walked, not just the direct base, so a slot introduced two
levels up is still caught; a visited set and a fuel counter keep a cyclic
`inherit` from hanging the walk.

## An inherited interface needs its OWN vtable row

A vtable row is keyed by interface NAME. F# requires a class implementing
`IDer` (which inherits `IBase`) to implement every inherited member in that
one `interface IDer with` block, so the functions were all there — but
nothing was filed under `IBase`, and a cast to it dispatched through table
index 0, which is `$novt`. The cast type-checked and the trap named only the
helper.

Two halves, and both were needed:

* `isSupertypeOf` checked a class' implemented interfaces with a flat
  `List.contains`, so it never stepped into an interface's own bases. An
  interface's `inherit` is recorded in `bases`, so recursing into each
  implemented interface reaches it.
* `ifaceRowsFor` (Lower) now expands one block into a row per inherited
  interface, sharing the same lifted functions — a table slot, not a copy.
  Both producers of rows have to call it: explicit `interface ... with`
  blocks AND object expressions, which build their own synthetic class. The
  class half alone left `{ new INamedShape with ... } :> IShape` trapping.

`use` had a related hole. An interface implementation is not an ordinary
member — `r.Dispose ()` on a class that merely implements IDisposable is a
compile error in F#, and lookup here agrees — but `use` is exactly the
construct that reaches through the interface anyway. It looked up Dispose as
a plain member, found nothing, and lowering quietly emitted a plain `let`.
The resource was never disposed and nothing was said, `--strict` included.

Both are the same lesson as the parked queues below: when a lookup fails,
check what the fallback DOES. Silently emitting the unadorned construct is
how these stay invisible.

## The two parked queues must advance TOGETHER

Inference parks what it cannot yet place: `pendingDots` for a member whose
receiver has no type, `pendingIndex` for an index whose receiver is not yet
known to be an array. They used to drain one after the other, dots first,
because an index's receiver often takes shape through a parked dot.

The dependency runs BOTH ways, and the other direction had no path. Adding a
second `string.Split` overload was enough to expose it: overloaded, the call
parks, so `lines` has no type, so `lines.[0]` parks, so the `.Trim()` on it
finds no receiver — and by the time the index pass ran, every dot retry was
already behind it. The member reached emission unlowered and the backend
answered `unreachable`. **`--strict` said nothing**, because nothing was
recorded as missing; the tell was a Core dump still showing
`(lines.[0].Trim ())` as a bare member instead of `$str.Trim`.

They now advance to a joint fixpoint (`indexProgress`, called inside the dot
loop). The final index pass still owns the diagnostics for receivers that
genuinely cannot be indexed, and skips what the fixpoint already named —
naming a site twice would file a second `arrKindsRaw` entry for it.

Worth remembering as a shape, not just a bug: adding an OVERLOAD to an
existing member is never local. It moves that member from the eager path to
the parked one, and anything downstream that needed its result type
immediately now needs it later. The regression showed up in `.TrimEnd`,
whose overloads nobody had touched.

A related trap from the same change: intercepting a member BY NAME in Lower
(`String.Join`) also grabbed the prelude's own list-taking `String.Join` and
forced its argument to an array. Only the `System.`-qualified spelling needs
the interception — that is the one whose `System` never resolves.

## Every binding solves the WHOLE pool, so a blocked constraint must say so

The wanted pool is one FILE-level list, and `solveWanted` runs from ten
sites — every binding, every clause with givens, every member. So a
constraint that cannot yet be discharged is re-selected once per binding
for the rest of the file, and the cost is quadratic in bindings without
anything looking quadratic. Measured on a fpp.base build: **3.49M constraint
visits for 171K useful selections**, one file alone walking 1.64M.

A pass' outcome is decided by three things, and each is cheap to compare, so
a deferral now RECORDS them (`WEntry`) and is skipped while they hold:

* the pruned ARGUMENTS, which can only move by binding a variable the
  attempt was left blocked on — an unbound `Link` on every one of them is
  the test;
* the class-table GENERATION (`Classes.instGeneration ()`), since a derived
  or newly registered instance turns `NoInstance` into a match;
* the ambient givens AND the givens seated at the constraint's offset, both
  immutable lists only ever replaced wholesale, so identity is the compare.
  The seat is not redundant: a constraint raised LATER at the same offset
  seats givens if none were, and `byGiven` would then discharge this one.

Only an outcome that changes nothing may mark — a deferral, an ambiguity or
a missing instance that is not yet ground. Anything that unifies, improves
or reports has had an effect, and re-running it is not a no-op. The
`seenKey` duplicate and the budget cutoff must NOT mark, having never been
attempted.

Worth 3.49M visits -> 202K and 25.7 s -> 20.9 s on the transform build,
17.8% on the library, with the emitted wasm byte-identical either way. A
pool-level guard was tried first and is the wrong granularity: 94% of calls
failed it because ONE new constraint invalidates the whole pool, which is
exactly the re-scan being paid for.

The profile after it is flat — emit 7.2 s, inference 6.1 s (the expression
walk, not the solver), lowering 4.0 s. There is no single next hotspot.

## An application types its argument ONCE

The member path takes a `dotDemand` before typing the head, and that needs the
argument's type. It used to type the argument again in the argument loop, so
every member application did the work twice. A computation expression nests
once per `yield` and each level's argument IS the whole remaining tail, so it
doubled per level: eight yields took 8 s, and the adaptive port's own CE test
module never finished inferring. The demand's result is kept and reused —
eight yields now take 34 ms, thirty-two take 180 ms.

Do not "fix" this by taking the demand only for overloaded members. That was
tried: it scales the same and breaks the OUT-PARAMETER view, which is built
from the demand too (`real.TryGetTarget()` stops typing). The duplication was
the bug, not the demand.

## What actually makes struct code slow: the CALL, and nothing else

Measured, same machine, same engine, 20M `Box3d.ExtendedBy` calls:

    native C                     36 ms
    C -> wasm, inlined           39 ms      <- the floor a wasm program can reach
    .NET (Aardvark.Base)         56 ms
    F++ hand-inlined             78 ms
    F++ via the call            152 ms
    C -> wasm, NOT inlined      166 ms      <- clang, same shape, SLOWER than us

Two conclusions, both of which contradict what the ratios suggested. The
wasm sandbox is NOT the problem — C through wasm beats .NET on this loop. And
our by-value struct ABI is not the problem either: with the call left in
place, clang pays 166 ms where we pay 152. What separates 152 from 39 is that
clang and .NET INLINE a small struct method and we do not.

So a benchmark ratio against .NET is mostly a statement about inlining. Before
blaming the ABI, the collector or the engine, build the C twin with
`__attribute__((noinline))` and compare against THAT.

The other half of the gap was an allocation nobody had looked for: reading a
struct out of an array (`pts.[i]`) built a heap object per element, 32 bytes
and 20M times. `lowStructBind` reads the leaves straight out of the element
now — worth 183 ms -> 78 ms on the hand-inlined loop, and it is what
`noalloc-gate.sh` would have caught had it covered arrays. It does now.

## The wasm-hosted compiler can read the ENVIRONMENT now

`System.Environment.GetEnvironmentVariable` answered null inside stage-1,
because `System` reaches the backend unresolved. That is not a small gap: it
means an env-gated pass RUNS in stage-0 and does nothing in stage-1, so the
fixpoint reports a byte mismatch that means nothing — which is exactly the
warning this file gives about `FPP_UNROLL`, and it cost a wrong diagnosis
once already (a "fixpoint failure" that was only the gate being invisible to
stage-1).

WASI gives the reactor a real environment, so the fix is libc's `getenv`:
`fpprt_env_get` takes the name as UTF-16 out of linear memory (env names are
ASCII, so the low byte of each unit is the name) and answers the value's
length, and `fpprt_env_byte` reads it back a byte at a time — no buffer
crosses the boundary in either direction. `EnvOps.Get` in the prelude assembles
the string, and Lower routes `System.Environment.GetEnvironmentVariable` to it
the same way it routes `System.String.Join`.

So an env-gated pass is now testable end to end, and a fixpoint mismatch under
one is a REAL mismatch. The C backend shares the prelude and gets the same two
builtins over plain getenv.

## A stamped clone specialized its SIGNATURE and not its BODY

`substScheme` rewrote a clone's declared type at its instantiation and left
every binder inside the body alone — so a function stamped at `int` still bound
`'a` locals, and a `'a` local rides the UNIFORM word. That is where a concrete
program's boxing comes from: not from calls, but from values crossing between
the raw and uniform representations, and an unspecialized binder is a
permanent crossing point in the middle of specialized code.

`substBinderTypes` (Link) now applies the same substitution to lambda
parameters, `let`s and pattern binders. `FPP_MONO_CENSUS=1` counts what is
left: 113 of 233 top-level functions bound a type variable before, 98 after.

**Only SCALAR instantiations are substituted.** Specializing a binder to a
reference type changes no representation — both ride the uniform word — while
it does change how a typeclass witness is chosen, and four adaptive-suite
tests (typeclass materialization, derived instances, generic contexts) failed
on exactly that. The scalar case is the one that turns a boxed word into a raw
register, and it is the only one taken.

It is NOT env-gated, deliberately: `GetEnvironmentVariable` answers null inside
the wasm-hosted compiler, so an env-gated pass makes stage-0 and stage-1
disagree and the fixpoint reports a byte mismatch that means nothing. If a pass
is worth having, take the gate off and let the fixpoint check it.

## What still boxes, and why it is not the call

Measured with `GC.AllocatedBytes ()`:

    int array   36 B/elem      int list   32 B/elem      float list  47 B/elem

A concrete call boxes NOTHING — struct arguments and returns ride registers,
scalars ride raw, and `noalloc-gate` holds that at zero across four million
struct calls. What boxes is a value entering a UNIFORM CONTAINER: the int list
costs one cons cell and no box (a small int rides tagged), the float list costs
a cons cell plus a box per element, because a float does not fit a tagged word.

So the remaining boxing is a CONTAINER REPRESENTATION question, not a calling
convention one. POD arrays already store raw elements — that is why `pts.[i]`
costs nothing — and the same has to be done for unions: stamp the payload
representation per instantiation, so `float list` holds an f64 rather than a
pointer to one. That is the last piece of "no boxing anywhere", and it is a
feature, not a fix.

## Inlining is OPT-IN, and what it is worth

`FPP_INLINE=1` (threshold `FPP_INLINE_THRESHOLD`, default 120) turns on
`Optimize.inlineCalls` for the linear backend, which nothing used before —
`optimize` never called it, and the linear path skipped `optimize` entirely.
Measured against .NET on the fpp.base benchmarks: rot-transform 1.30x -> 0.90x,
rot-compose 1.33x -> 1.00x, transform-trafo 4.25x -> 1.86x, transform-m44
3.27x -> 2.15x, ray-triangle 4.58x -> 4.24x.

Two things had to be fixed before it was worth anything, and both are the
kind that make a pass measure as a REGRESSION rather than as a bug:

* **an inlined tupled call builds a tuple.** The inliner binds arguments as
  `let`s, so `f (a, b)` becomes `let t = (a, b) in match t with (x, y) -> ...`
  — and `fuseTuples`, the pass written for exactly this, only matched a tuple
  LITERAL scrutinee, never the let-bound variable the inliner produces. Every
  inlined tupled call therefore allocated: 886 MB on ray-triangle, which read
  as "inlining made it 40% slower".
* **`freshenBinders` returned the body UNCHANGED when it had no binders.**
  The second walk is what gives the copy fresh nodes, and the lambda lift
  keys a closure by node REFERENCE — two copies sharing one `ELam` get one
  lifted function with one set of captures.

Four more guards were needed, and each was a boundary the copy silently
crossed. A candidate must have a fully CONCRETE signature; no parameter or
result may be `obj` (widening to it is a box the boundary performs, so
`let returnsObjOf (v : int) : obj = v` inlined to `let v = 5 in v` and the
`:?> int` after it unboxed a value that was never boxed); every binder in the
body must be monomorphic (`[ 3 .. -1 .. -3 ]` inlined put a raw -2 in a list
and comparing it read -2 as a pointer, wasm address 0xfffffffe); and a
COMPILER-SYNTHESIZED function (`$ordD@…`) is never inlined, because its stamp
is context it only has by being its own function — inlined, `compare` on a
`uint32` payload fell back to the structural walker. The copy also keeps its
original binders rather than renaming them, since decisions taken during
inference are keyed by the variable the SOURCE bound; a callee is inlined at
most once per caller so a key cannot be bound twice, and never when its
binder keys collide with the caller's (monomorphized clones share VarIds).

With all of that, all 93 conformance suites and all 60 negatives pass with
`FPP_INLINE=1`. It stays opt-in for one thing that remains: the CORPUS
fixpoint traps — the compiler compiled with inlining miscompiles itself
somewhere the suites do not reach. Until that is found, this is a flag.

The first symptom found was `let xs = [ 3u; 1u; 2u; 4000000000u ]` sorted and
printed, faulting at wasm address 0xee6b2800 — 4000000000 itself, read as a
pointer because an even word is a pointer in the uniform model. That one is
fixed (it was the concrete-signature guard). It was NOT the bounds proof:
`FPP_NO_PROOF=1` (emit every check, trust nothing the proof pass marked)
trapped identically, which is what that flag exists to tell you.

## Measure, do not reason

Almost every performance intuition recorded in this repo's history was wrong,
including several in a row. The vertex benchmark went from 3615 ms to 149 ms
against C's ~62 ms, and the causes were never where they looked:

* "the field read is slow" — reads were ~5 ns; the *fill* loop was being
  counted as read time
* "it is the boxing" — the peephole already cancelled it
* "it is `ref.cast`" — measured at ~2 ns in isolation
* the thing that actually cost 3 seconds was a GC struct allocated per
  element *while a 12 MB array was live*, which neither ingredient shows on
  its own (allocating against a small array: 289 ms; writing without
  allocating: 210 ms; both: 3246 ms)

What worked, every time, was replicating the loop in hand-written wasm
(`wasm-tools parse`) and bisecting there. If a hand-written replica of the
same instructions runs 12x faster, the instructions are not the problem.

**Always print the program's result next to the timing.** A module that fails
to compile exits in milliseconds and looks like a spectacular win. That
mistake was made three times in one session, once reported as a 27x speedup
that was really a validation error with stderr piped to `/dev/null`.

**The benchmarks gate, but only their stable half.** `perf-regress` checks
every benchmark's ANSWER against a recorded checksum and the number of
bounds checks it still emits — both load-independent. It does NOT check the
clock: the gate suite runs eight jobs at once and under that load these
numbers trebled (avl 1990ms -> 6553). Timing is `regress.sh --timing`, run
by hand on a quiet machine, with a 1.5x ceiling. `--record` rewrites
`baseline.txt`.

The static half is not a consolation prize — a checksum change means the
program stopped computing what it computed, and a rise in the emitted-check
count means the proof pass lost a rule, which is the failure most likely to
creep in unnoticed.

Read the SHAPE of a count rise before chasing it. The count is a floor plus
the program's own checks, so linking one more prelude function raises EVERY
benchmark by the same amount — adding `List.toArray` to a `StringOps` member
put all nine up by exactly one, via `Array.ofList`, whose `r.[i] <- x` is
in range only if two separate `for _ in xs` traversals of the same list
agree in count. Nothing in the domain expresses that, and `Array.ofList` is
in no hot loop, so the answer there is `--record`, not a new rule. A rise on
ONE or TWO benchmarks is the real signal.

Benchmarks that compare against C live in `tests/tooling/perf/`;
`tests/tooling/abi/` checks struct layout against emscripten.

**Every twin manages memory, and there is a Rust column.** The C twins for
`avl` and `trees` used to be bump ARENAS — one never freed, the other
dropped a whole tree by resetting a pointer — and against that the collector
looked 2.9x slow while measuring something no real program can do. They
malloc/free now, with refcounts for `avl` because the tree is persistent and
each insert shares most of its nodes with the version before it.

Rust builds to the same `wasm32-wasip1` under the same engine, with bounds
checks ON, which makes it the useful third point: C says what UNCHECKED
manual memory costs, Rust what CHECKED manual memory costs, F++ what a
collector costs on top. Read as of this writing:

    allocation   avl    F++ 1827  Rust 1796   — within 2%
                 trees  F++ 900   Rust 1137   — F++ ahead by 26%
    bounds       sort   F++ 1501  Rust 1472   — within 2%, and Rust cannot
                                                elide the partition scans
                                                either
    streaming    read/vertices/shapes         — F++ ~1.25x Rust
    float        nbody  F++ 389   Rust 305    — 1.28x, the widest gap left

So the collector is not the problem it looked like, and the bounds checks
cost what Rust's cost. What is left is array streaming and float-heavy code.

A Go twin was tried as "a mature GC" and dropped: `GOOS=wasip1` works and
answers correctly, but Go's wasm port runs ~10x its native speed (trees
8902ms against 1409), so the column measured the port. For the record its
NATIVE numbers against the old arena C were avl 2.51x and trees 4.45x, both
worse than F++ manages inside a sandbox.

**Measure WARM.** wasmtime caches module compilation on disk: the first run
of a fresh binary pays the whole Cranelift compile and reads 3-6x slower
than every run after it. A 433 ms "regression" on the read benchmark was a
cold cache; warm, the same binary beat C. Best-of-three, never first-of-one.

The 2026-08 pass found three real wastes, each visible only in a profile
(`perf record -k 1` + `--profile jitdump` + `perf inject -j`):
`Array.zeroCreate` of a POD struct spent a quarter of the benchmark seeding
zero fields into an `array.new_default` that was already zero (the seeding
is for CLASS-shaped elements, which need instances in the slots); every
statement answered with a boxed unit that its context immediately dropped
(`pushUnit`/`dropU` cancel the pair positionally, like the box/unbox
peephole); and a store into a hoisted-base POD array still called the
`$hwset` runtime helper whenever ANYTHING in the program pinned that
element kind — float formatting does — so the pin test is now inlined on
the hoisted storage, mirroring the read path. After all three: vertices
149 ms vs C 62, add 65 vs 67, read 88 vs 103 (both now BEAT C), shapes 686
vs 248. What remains on vertices/shapes is per-access bounds checks and no
SIMD — wasm-GC array.get has no unchecked or vector form, so that gap
belongs to the engine and the spec, not to emitted-code waste.

## Optimisations, and what they are worth

There is no global optimisation switch. `St.Opt` does not exist — that was
the deleted wasm-GC driver, and the paragraph describing it outlived the
backend it described. Treat a claim in this file as suspect until you have
grepped for the thing it names; several were stale by a whole backend.

On by default: POD array bases are hoisted out of loops (`hoistE`); a
literal-valued top-level `let` is emitted as its literal; the
pinned/unpinned test is dropped for types the program never pins; a record
literal stored into a POD array is written field-by-field rather than via a
materialised struct; `let v = arr.[i]` splits the element into unboxed
locals (the last two are the same fix from opposite sides — never
materialise a GC struct for a POD element); one-instruction class wrappers
are inlined at their call sites; and a loop's exit test is the guard
NEGATED rather than `cond; i32.eqz`, which is worth 8-10% on a tight
streaming loop (read 49 -> 45 ms, vertices 58 -> 52).

## Unrolling and strength reduction: BOTH implemented, BOTH off

`FPP_UNROLL=1` and `FPP_STRENGTH=1`, in WasmLin over LowIR. They are off
because they were measured, not because nobody got to them:

    bench      base   unroll  strength   both
    read       43ms     44ms     43ms     42ms
    vertices   52ms     52ms     53ms     54ms
    shapes    247ms    239ms    240ms    241ms
    matmul    103ms    131ms    103ms    101ms     <- unroll 27% WORSE
    nbody     392ms    397ms    389ms    390ms
    sort     1495ms   1494ms   1495ms   1538ms
    avl      1812ms   1812ms   1815ms   1801ms
    trees     897ms    898ms    898ms    898ms

Nothing outside the noise, and unrolling costs matmul 27%. Strength
reduction is a wash for a reason the emitted code shows plainly: the
multiply it takes out of the address (`i*12` — get, const, mul, add) is
replaced by a bump beside the counter (get, const, add, set), so the body
gets LONGER by two instructions. Wasm has no addressing mode to fold an
index into, which is why the trick pays on a native target and not here.

Unrolling is innermost-only and capped at 60 nodes for a reason worth
keeping: unrolling a loop that contains another copies the inner one too,
and copies multiply as 3^depth.

THE FIXPOINT CANNOT VALIDATE EITHER FLAG. `GetEnvironmentVariable` answers
null inside the wasm-hosted compiler (`System` is one of the roots that
reach the backend unresolved), so with `FPP_UNROLL=1` stage-0 unrolls and
stage-1 does not, and the fixpoint reports a byte mismatch that means
nothing. Check these passes with the CONFORMANCE suite instead — all 76 are
green under unroll, strength and both.

VERIFY THE PASS FIRES BEFORE BELIEVING A NULL RESULT. The first measurement
of both showed "no change" because the wiring matched only a top-level
`LDo`, which a function body rarely is — the passes ran over nothing and
still reported a clean build, which looks exactly like an honest zero. Check
the emitted wat (loop count for unrolling, the address shape for strength
reduction), not the wall clock.

### The profiler over-attributes `getenv` — check it with an experiment

`dotnet-trace` blamed `GetEnvironmentVariableCore` for 1.68 s of a 21 s
build (6.7%), spread over the lowering and emission inner loops, which
reads as an obvious win: hoist every probe gate to a module-level value.
Done — all 35 of them, in WasmLin and Optimize — the build measured
20882 ms against 20873 ms. NOTHING. The reads are a managed dictionary
lookup over a cached environment block, not a syscall.

So the hoist was reverted rather than kept with a false rationale, and the
`consCheckOn ()` function position stays. Its comment's REASON is stale
(it names the wasm-GC self-host, which is gone, and `boundsOn`/`noProof`
beside it are module-level values across the fixpoint) but the shape is
harmless, and changing it buys nothing.

The general lesson: a sampling profiler is a hypothesis generator, and a
P/Invoke boundary is where its samples pile up. Confirm with an A/B that
toggles the suspect and rebuilds — which is also the only way to know a
change is worth its risk.

### Two more that were measured and REVERTED

Inlining `$toi` everywhere, and caching `i * stride` across an element's
fields (the engine already does that one). Do not re-add either without a
number.

### Bounds checks: emitted, then proven away

Every element access carries one — a single UNSIGNED compare against the
length word, which rejects a negative index in the same test — and it
raises rather than traps, so a program can catch it. What keeps that from
costing anything is the proof pass (`provenWalk`, WasmLin), which runs over
the Core body BEFORE lowering and marks the accesses it can show are in
range. Six sources of proof, and they compose:

* a counted loop's own guard — `for i in 0 .. a.Length - 1`, `for v in a`,
  and the hand-written `while i < n` where `n` is the length `a` was
  CREATED with (module-level `Array.zeroCreate n`, literal or binding);
* a DERIVED index inside such a loop: `a.[i - k]` appeals to the same fact
  as `a.[i]` when the counter starts at k or above, which is the sliding-
  window idiom. The other direction does NOT hold — `a.[i + k]` needs an
  upper bound tighter than the loop's, so it stays checked;
* a check that already ran on the same (array, index) pair earlier in the
  same straight-line region;
* a PRECONDITION on a parameter, established by the function's CALLERS —
  see below;
* a FLATTENED 2D index — `m.[i * cols + j]` over `Array.zeroCreate (rows *
  cols)`, in range when i is under ROWS and j under COLS. Neither bound is
  the array's own length, so the length is kept as a PRODUCT of its factors
  and the index checked against them. Worth 2x on matmul: 218 ms to 103,
  which is C's 100;
* a guard the PROGRAM wrote. `&&` short-circuits, so the right operand runs
  only where the left holds: `while i < n && a.[i] < p do ...` proves its
  own access, and does not then pay for a check as well;
* nothing crosses a branch join or a lambda boundary, and a loop's guard is
  read with only what survives the body's own writes. That last one matters:
  walking the guard with the richer pre-loop state "proved"
  `while a.[i] < p do i <- i + 1`, which is exactly the access nothing can
  prove — i's upper bound is gone the moment it is incremented.

### Preconditions: what the CALLERS establish

`a.[lo + (hi - lo) / 2]` inside a recursive partition cannot be proven from
the function's own body: `lo` and `hi` are whatever the callers passed. The
fixpoint assumes every (parameter, array) pair is in range, then drops the
ones a call site fails to support, and repeats. The assumption is discharged
by induction on the execution trace — a call is supported by its caller's
facts, which held when the caller's activation began.

For quicksort that closes: `qsort 0 (n - 1)` is the base (n is a literal, so
the array is known non-empty), `qsort lo j` has j <= hi because j only FALLS
from hi, and `qsort i hi` has i >= lo because i only RISES from lo. Which is
why the domain tracks the two halves separately — a counter that only
decrements keeps its upper bound while losing its lower one, and collapsing
them into one "in range" fact loses exactly the half that survives.

Facts key on the PARAMETER, not its position: the bodies the fixpoint walks
are pre-transform, the ones emission lowers are not, and node identity does
not survive lifting and stamping. A callee named but not applied (passed as
a value) loses every precondition, since nothing constrains what reaches it.

Three shadowed match arms cost hours here, all the same mistake: `x < y`
must apply BOTH the "x inherits y's bounds" reading and the "y is some
array's length" one; `n - 1` must try both "offset from an in-range index"
and "last index of a non-empty array". Written as alternatives, the first
arm silently swallowed the case the second existed for.

The pass is compiler SOURCE, so it lives in the self-hosting subset like
everything else here. A nested `[ for x in xs do for y in ys -> ... ]` in
it built and passed every unit test, then died at the CORPUS fixpoint with
"not lowerable: list comprehension" — stage-1 compiling this very file.
`List.collect` instead. The tell that it was not the bounds work at all:
`FPP_NO_BOUNDS=1` failed the same way.

An access that is proven emits EXACTLY the code it did before checks
existed, register bindings included: binding the base defeats the hoist
that lifts it out of a loop, and that cost is real whether or not a check
is there to pay for it. That is why each site branches on
`boundsGuardPeek` rather than always taking the guarded shape.

Measured, best-of-five interleaved, checks on against `FPP_NO_BOUNDS=1`:
add, read, shapes, vertices are FREE (fully proven), and every benchmark
sits at the same prelude floor of emitted checks except `sort`, which keeps
exactly the two its partition scans need. `sort` pays 18% (1493 ms against
1258), all of it in that scan —
`while a.[i] < p do i <- i + 1` — which is in range because `p` is an
ELEMENT of the array, so the scan stops at it. That is a property of the
array's CONTENTS, not of any guard or arithmetic, and no compiler proves
it. `a.[lo + (hi - lo) / 2]` beside it IS derivable, and now is — see the
precondition section below.

Writing that guard yourself is NOT worth it, which is worth knowing before
anyone reaches for it. Guarding both quicksort scans elides every check in
qsort — measured, sg_on 1656 ms against sg_off 1661, so the checks really
do cost nothing there — and the whole benchmark still runs SLOWER than the
unguarded one with its checks left in (1656 against 1490). The guard is not
a comparison saved, it is a comparison MOVED: same test, but `&&` makes it
a second control-flow diamond in the tightest loop, and the engine handles
the check's shape better. Leave the check in.

A WARNING about reading these numbers. The stronger analysis emits 124
checks against the weaker one's 135 and does strictly less work at run
time, yet measures 1493 ms against 1410. The emitted qsort is
instruction-identical between the two; only the local NUMBERING differs,
because eliding an access skips its temporaries. That 6% is Cranelift
allocating differently, not work. Compare check COUNTS when judging the
analysis, and treat a single benchmark's milliseconds as the noisy signal
they are here.

### The check's real cost was the HOIST, not the compare

Worth knowing before optimising the compare. Measured on sort, the check
overhead split almost evenly: 238 ms for the compare and its loads, 271 ms
for the throw. But the two were not independent — the inline throw
ALLOCATES, `hoistStmts` refused to hoist loop-invariant global loads out of
any loop containing a safepoint, and so the array pointer was re-read from
its GC root slot (four instructions) on every single access.

The fix is a refinement to the hoist, not to the check: a safepoint on a
branch that always THROWS, traps or returns cannot make a hoisted pointer
stale for a later iteration, because there is no later iteration
(`escapesS`/`hasSafepointH`). That took sort from 1771 ms to 1407, and it
helps any loop with a `failwith` branch, not just bounds checks.

Two shapes measured WORSE and are recorded so they are not retried. Calling
one shared thrower instead of inlining: 1771 -> 2132 ms, because an untaken
call still makes the engine spill live registers around it every iteration.
Branching to one throw per function: wrong, not just slow — it leaves an
enclosing `try`'s scope before throwing, so the handler never sees it.

`FPP_BOUNDS_STATS=1` prints how many checks a build emitted and elided.
Read the EMITTED count, not the percentage: a proven access takes the fast
path and never reaches the counter, so "0% elided" with the emitted count
at the prelude floor means everything of yours was proven.

`for i in 0 .. arr.Length - 1` already evaluates the bound once: the loop
body contains zero `array.len`. That one was checked, not assumed.

## Emitting wasm

* **Declaration order must match body order.** The function section and the
  code section are positional; declaring `$hlen` third and emitting it fifth
  produces "unknown local" errors far from the cause.
* **Bodies are NOT emitted twice.** `Fn.Replay` is initialised to -1 and
  set nowhere, so the scratch/replay path is dead — locals are declared
  first (`local`, then `localsDone`), then instructions, then `endFn`, in
  one pass. It was the wasm-GC driver that replayed, and that backend is
  gone. If you resurrect a two-pass scheme, both passes must allocate
  locals identically: any cache that lets the second skip a `freshLocal`
  desynchronises them.
* `wasm-tools validate -f all out.wasm` gives a far better message than the
  runtime does.

## The prelude snapshot, and the two traps it hit

The prelude is parsed, resolved, inferred and lowered on EVERY invocation,
and it is the same work every time: 1.34 s of a hello-world's 2.89 s, 47% of
the build. `PreludeCache` writes the INFERRED state (schemes, fields, class
tables, the resolver's bindings, `InferResult`) to
`~/.cache/fpp/prelude-<key>.sx` and reads it back. Small builds go 2.93 s ->
2.39 s, ~18%. `FPP_NO_PRELUDE_CACHE=1` disables it, `FPP_CACHE_DIR` moves it.

Four rules hold it together, and three of them are load-bearing:

* **variable ids are preserved, INCLUDING the supply the run ended on.**
  Class and operator markers name a variable by id inside a STRING
  (`$class:Num:One:#4`) — the same fact the package format has to work
  around by re-numbering and rewriting markers. A snapshot is one run's
  state, so it keeps the ids; and `Types.reserveIds` puts the counter back
  where the prelude left it, or the next PROJECT variable is minted with an
  id the prelude already used. This is what makes a cached build's wasm
  byte-identical to an uncached one, which is the only acceptance test that
  matters here.
* **fields are tagged, not positional.** `ShowTypes` beside `StrTypes`,
  `OrdDerive` beside `ShowDerive` — a positional format swaps those
  silently, and the round-trip check below cannot see a symmetric swap.
* **it is verified before it is written.** `decExpr` answers `ELit LUnit`
  for a node it does not recognise, so a codec gap does not fail, it
  replaces code with unit. `encodePrelude` decodes what it just encoded,
  re-encodes that, and refuses to write unless the two texts match.
* the snapshot is keyed by the COMPILER BINARY (path, size, write time) and
  the DEFINE SET, and carries a hash of the prelude source it was built
  from. Nothing weaker is honest: it holds inferred types, so any change to
  inference invalidates it.

Adding a field to `InferResult`, `FieldInfo`, `InstanceDef`, `ClassDef` or
`BindResult` BREAKS THE BUILD, because the decoder constructs those records
and F# demands every field. That is deliberate — it is the only thing
stopping a new field from silently falling out of the cache.

### Both traps were the self-host, and only the fixpoint saw them

* **file IO in the compiler library trapped stage-1 at module init.** A host
  API the self-hosted build does not implement becomes a STUB, and a stub
  takes its whole enclosing function with it — reading the cache from
  `Workspace.fs` was enough to kill the module initializer. Every byte of
  IO now lives in `Fpp.Cli`, which is not in the corpus; the library only
  ever sees `PreludeCache.input`/`.output` as TEXT. Guarding the call site
  is not enough on its own, but it is also done.
* **building a snapshot nobody stores ran the self-host out of memory.**
  Stage-1 always misses and can store nothing, yet it still encoded 2.4 MB
  (three times, for the round-trip check) against wasm32's 2 GB. It failed
  with `weird: we have the space but mmap didn't work`, a `linit` trap and
  no diagnostic anywhere else. `PreludeCache.wanted` is off unless the host
  will actually keep the result.

### What it is NOT worth on a large build

Measured: hello-world 18%, the 20 s fpp.base benchmark builds a WASH
(19.4 s against 19.7 s, inside the noise). The prelude is a fixed 1.3 s, so
its share vanishes as the project grows, and roughly half of what is saved
goes back into decoding a 2.4 MB snapshot. This is a fix for small and
interactive builds — `fpp dev`'s watch loop — not for the benchmark suite.

The prelude's LOWERING is deliberately not cached, though it is another
406 ms. `Lower.lower` is handed the PROJECT-WIDE tables (`r.Members`,
`r.Fields`, `r.Schemes`), so its output is not a function of the prelude
alone and a snapshot of it would be poisoned by whichever project wrote it.

### The s-expression reader allocated one string PER CHARACTER

Independent of the cache, and worth more than it: `Serialize.parse` built
every string literal by appending one single-character string per character
and concatenating the lot — 429 ms of the 502 ms a snapshot took to read,
and every `.fppir` package load paid it too. A literal with no escape in it
IS a slice of the input. The writer had the identical shape. Fixed both.

## The vtable build was quadratic in classes

`slotImpl` answers "which function implements this slot for this class",
and it did so by scanning the whole `classDecls` LIST at every step of the
inheritance chain — inside `for each class do for each vtable slot`. So it
cost O(classes^2 x slots): **1.34 s of a 21 s fpp.base build, 19% of the
entire emission phase**, for lookups that are a dictionary.

It is indexed by name now, and `chainOf` / `subclassesOf` are memoized.
Two details the index must preserve, or it changes the program:

* a name maps to a LIST of declarations, not one. Two can share a name (a
  stamped clone beside its origin) and the walks are `tryPick` — the first
  that ANSWERS wins, which is not the same as the first that MATCHES, so
  keeping only the first declaration silently drops the second's answer.
* `subclassesOf` returns declaration order, and falls back to `[n]` for a
  name that is not a class at all (an interface). Filing each class under
  every ancestor, in order, reproduces both.

Emission went 6.96 s -> 5.87 s with the wasm byte-identical. Worth looking
for the same shape elsewhere: a `List.tryPick`/`List.filter` over a whole
declaration list, called from inside a loop over that same list.

## The .NET collections, and the two rules that shaped them

`ResizeArray`, `Dictionary`, `MutableHashSet` and `StringBuilder` live in
the prelude and are exercised by `stdlib/dotnet.fpp`. That file is a MANUAL
check, not a gate: nothing in `run-gates.sh` runs it, and running it under
`dotnet fsi` needs shims for `print` and for `MutableHashSet` (F# spells
that one `HashSet`). It prints 142 lines as of this writing — an earlier
version of this paragraph said 111 and asserted a gate that does not exist. Two limits decided their shape, and both
will bite anyone extending them:

* **A generic class that implements an interface is monomorphized.** A
  vtable member keeps the canonical all-anyref signature, so it is never
  specialized and would read a packed `int[]` field as uniform. Each
  instantiation is therefore a SUBCLASS carrying its own vtable, and the
  class' constructor is forced into stamping so there is somewhere to hang
  it. Two traps if you touch this: an instantiated subclass must not claim
  ownership of its base's field names, and a member's quantified variables
  are NOT the class' — find the class' parameters positionally, through the
  receiver type.
* **A user type whose name matches a prelude type MERGES with it.** That is
  why the mutable set is `MutableHashSet`: the acceptance corpus ports a
  `HashSet` of its own.

Extra members exist that .NET does not have (`Reserve`, `SlotOf`, `Rehash`,
`KeyArray`) because there is no working `member private` convention here.
They are implementation, not surface.

## A library must ship its TABLES, or it is only good for functions

`.fppir` carried exports, schemes and decls. That is enough for a plain
function and nothing else, because everything that makes a TYPE usable lives
in tables the consumer never received:

* a class declared in the library (`class Real<'a>` in fpp.base) put its
  instances in the producer's class table, so the consumer met
  `$class:Real:Pi:float` — a marker naming an instance member — with no
  instance to resolve it against. The backend stubbed the enclosing
  function, and the program trapped at whichever global initializer touched
  it first. `--strict` named it; an ordinary build did not.
* `fields` is where a type MEMBER is found, so `a.Dot b` on a library V3d
  had nowhere to resolve either.

`fppir2` carries classes/instances, fields, ifaces, bases, impls, implTys,
structTypes, ctors and aliases; `fppir1` still loads with the old limits.
Three rules the producer and consumer have to keep:

* the producer ships only what the LIBRARY declared. `ProjectResults` is
  project-wide and holds the prelude's entries too — shipping those has a
  consumer overwrite its own prelude with re-numbered copies of itself. The
  prelude snapshot's key set is exactly what to subtract, EXCEPT for
  instances, which are filtered by their own `Path`: a library may add
  instances to a PRELUDE class, and those are precisely the ones a consumer
  cannot rediscover.
* the consumer merges tables only where the key is FREE, so a project still
  wins over its libraries — the same precedence it had when the library was
  referenced by source. Instances are the exception again: they REGISTER,
  because a class may be extended by library and project both and selection
  ranks the whole candidate list.
* a list section is VARIADIC (`(d decl decl ...)`) and a table section is
  not (`(fields <map>)`). One accessor for both, unwrapping a single child,
  silently splices a one-decl library's decl children in place of the decl —
  which presented as a one-function package failing to resolve its own name.

Two traps in writing it, both self-host and both invisible to the .NET
build: `{ emptyLib () with ... }` — copy-and-update over a CALL — is not in
the subset, and reaches Lower as an unresolved `BraceExpr` ("not lowerable:
computation/sequence body", naming no line). Spell the record out. And a
record that must be built in full is the only thing stopping a new table
from silently not shipping.

The playground referenced fpp.base as 22 SOURCE files because of all this.
It references `lib/fpp.base.fppir` now: 16.6 s against 19.8 s, `--strict`
clean, same output.

## A package's IR names type variables by the PRODUCER's ids

A class or operator marker spells its variable by ID, inside a NAME —
`*@#1`, `$class:Num:One:#1`. That is TEXT, not a `Type` node, so decoding an
`.fppir` rewrote the schemes (`varById` hands out fresh ids) and left every
marker naming ids that belong to nothing at the consumer. The stamper's
substitution then had no entry: a packaged
`let sq (x : 'a) : 'a when Num<'a> = x * x` kept `*@#1`, and `sq 3` answered
0 while `sq 1.5` answered 1.5 — the same two files built as ONE project were
right, which is what made it look like a package-system bug rather than a
naming one. `Serialize.remapDeclMarkers` rewrites them with the same mapping
`varById` used.

The shape to remember: a type variable that appears inside a STRING is
invisible to every pass that rewrites types. Two bugs in this file are that
same shape (see the class-constant section below), and both were found by
dumping Core and reading a `#` that should not have survived.

## An explicit type argument on a static member was DROPPED

`V3<int>.ZeroV` stamped at `$ref` and trapped, while `let z : V3<int> =
V3.ZeroV` worked. The static-access path finds its owner with `headIdent`,
which walks `Comparer<int>.Instance` down to the type TOKEN — and keeps only
the name. The class parameters were then freshened, the specialization demand
recorded those fresh variables, and the stamper settled them at `$ref`.

The written arguments are read off the head's `TyParams` node now and used
for the demand DIRECTLY. Using them to pin the substitution is not enough:
that substitution is keyed by the FieldInfo's parameters, while the demand is
built from the definition scheme's quantified variables — a different set, so
the pin was invisible to it.

## A member and its `when` may be written in either order

`member v.Dot (o : V3<'a>) : 'a when Num<'a>` parsed; `static member ZeroV
when Num<'a> : V3<'a>` did not, and reported "unexpected token at top level"
four times for one member. The signature parser took the ascription once,
then the constraints, and stopped — so a return type written AFTER the
constraints was left for the top-level loop. The two alternate now.

## The CLASS spelling of a struct is a value type too

`[<Struct>] type V3(x, y, z : float)` is the other way F# writes a value type,
and its storage IS the constructor's parameters — the generated constructor
body already builds an `ERecord` of exactly those fields. But the inline
layout was computed for records only, guarded by "not a class", so a
struct-class never got a `RecPod`, `structAbiOf` answered None, and the whole
by-value ABI was unreachable for that spelling: every construction allocated,
64 bytes an iteration where the record spelling allocates none. That was the
whole of its ~10x (1723 ms -> 495 ms on its benchmark, KNOWN-ISSUES #11).

It joins on STRICTER terms than a record, and each condition was learned by
breaking something:

* **no type parameters, no base, no interface implementations.** A
  ref-carrying or dispatched struct-class reaches the runtime as an interned
  SHAPE rather than a class instance, and an interface call on it then finds
  no vtable row — the adaptive suite failed with `no vtable entry (tid …)`.
* **every field a scalar**, for the same reason: the shape a ref field
  produces is what the dispatch lands on.

The flag is decided in Lower, where the declaration is still visible, because
it also decides SHAPE INTERNING for the type everywhere — setting it in the
backend's layout pass alone is not enough, and setting it unconditionally
breaks dispatch. `noalloc-gate.sh` covers the shape.

## Defaulting a constraint DECIDES its associated type

Numeric defaulting skips constraints that mention a declaration-level
variable — a type's own parameter is settled per stamp, never by a guess. The
test read `c.Args` only, and that is not where the decision lands.

`Zero - One` inside a `when Num<'a>` body is `Sub<'z,'o>` whose RESULT is
`'a`. Its ARGUMENTS are ordinary inner variables, so the constraint did not
look declaration-level; defaulting ground them to int, the instance
`Sub<int,int>` then fixed its Result — and that Result was the type's `'a`.
Deciding the constraint decided its projection.

The damage travelled sideways, which is what made it hard to see: a
`member v.Sign` calling a constrained generic let froze the parameter for
EVERY member, so the unrelated `member v.Length when Floating<'a>` rendered
`Floating:sqrt:int` and trapped on any receiver, and deleting `Sign` made
`Length` correct again (KNOWN-ISSUES #2). `declLevel` now reads the
associated types as well as the arguments.

The rule to keep: **a constraint is declaration-level if deciding it would
decide a declaration variable** — through its arguments or through anything
it projects.

## prune's PATH COMPRESSION was invisible to the trial log

`prune` re-pointed each variable it walked straight at the representative, and
the note beside it argued this needed no undo record: the compression aims a
variable at the SAME representative it already had, so a rollback leaves it
pointing where it should either way.

That holds only when no rollback happens in between, and overload resolution
rolls back constantly. The sequence that breaks it:

    v3 -> v1                     an ordinary tie (a parameter to its annotation)
    trial: v1 -> X               RECORDED in the trial's undo log
    prune v3  =>  v3 -> X        compression, recorded NOWHERE
    undoTrial: v1 restored free  the log knows only about v1

`v3` still points at `X`, so the tie between `v3` and `v1` is gone — severed
by a write the undo log never saw. Nothing looks wrong from any angle the
obvious probes take: no link-changing entry in the trail, no variable copied,
no scope entry rewritten, one `inferLet` call, one `namedVar` creation.

What it cost: a binding's PARAMETER and its own RETURN ANNOTATION were the
same variable when its body started and two different variables when it
ended. The scheme then quantified both, and
`let f (t : 'a) : 'a when Num<'a> when OfInt<'a> = t * t * (OfInt 3 - OfInt 2 * t)`
stamped `$float$int` with its operators substituted through the wrong
variable to the bare INTEGER defaults (KNOWN-ISSUES #3's second half).

Compression is gone; `prune` follows the chain. It costs nothing measurable —
the full gate suite runs in the same time — because these chains are short.

Two lessons worth more than the fix. A union-find with an undo log has
exactly one rule: **every write to a link is recorded, including the ones that
"cannot matter"**. And when a measurement is impossible under your model of
the code (a variable pruning two ways with nothing writing to it), the model
is missing a writer — look for the write that is deliberately not logged.

## A class constant baked its marker BEFORE the variable was unified

`t * (One - One * t)` in a `when Num<'a>` body trapped, while the same body
with the constant bound first — `let one : 'a = One in t * (one - one * t)` —
answered correctly. Two spellings of one thing disagreeing, and the working
one is the longer.

The stamped clone kept `$class:Num:One:#4`. The constant is typed with a FRESH
variable that unifies with `'a` only afterwards, so the marker string was
rendered before the two became one, and neither spelling the substitution
knows (`prunedId qv` and `qv.Id`) matches `#4`. `typeConName` prunes, so this
is not a missing prune — it is a string baked at the wrong moment.

The leftover is now mapped at stamping by the marker's CLASS: the scheme says
which variable `Num` applies to, and that variable's position picks the
instantiation. Two things about the rule, both learned by breaking something:

* never map by POSITION or by "there is only one type parameter". A body can
  nest a generic lambda whose variables are its own, and mapping those to the
  instantiation left a vtable slot unresolved in the adaptive suite (`no
  vtable entry (tid 228 slot 795)`).
* every constraint for the class must AGREE on the variable, not be unique. A
  body mentioning a constant repeatedly carries one constraint per occurrence
  until they merge, so demanding exactly one left the NESTED spelling
  (`One - (One - (One - One * t))`) unresolved.

`tooling/classconst-gate.sh` pins it — a gate rather than a conformance suite
because there is no oracle: F# has no `Num` typeclass, so `dotnet fsi` cannot
type-check the file at all.

The TWO-type-parameter shape (`when Num<'a> when OfInt<'a>`, stamped
`$float$int`) works as well: `classconst-gate` covers it among its twelve
cases, and `t / OfInt 2` answers 1.5 at float and 1 at int — the division
that would expose integer defaults. This paragraph recorded it as broken;
re-checked 2026-09-02.

## `string x` honours an overridden ToString — for a record

`string x` lowered straight to the Show class' `str`, which prints the
structural form, so a type that overrides `ToString` printed its record shape
from `string x` while `x.ToString ()` beside it answered correctly. Two
spellings of one thing disagreeing is the shape to watch for. The override is
an ordinary member, so the project member index finds it by owner
(`tn + ".ToString"`) and the call goes there instead.

A CLASS with an override answers correctly too, as of the member-index work
— `string c` on a class overriding ToString renders through the override.
(This paragraph used to record it as broken; re-checked 2026-09-02.)

## A nested [<AutoOpen>] module opens with its parent

`open Base` injected only Base's DIRECT members: the injection skips any name
whose remainder still contains a dot, so `Base.Ops.dot` from a nested
`[<AutoOpen>] module Ops` was never brought in and the consumer file reported
`dot` unbound. The attribute worked within its own file and nowhere else.

The auto-opened module is recorded in the EXPORTS table under an `"autoopen "`
prefix — the way `"type "` already keys type definitions there — because
module-level state would be shared by two workspaces type-checking at once.
`open` then injects the members of every auto-opened submodule as well.

## Qualification, and the first-identifier trap

`Impl.Node(k, v)` must mean what `Node(k, v)` means. It did not: constructor
overload selection searched the head for the FIRST identifier, which on a
dotted name is the MODULE, so a qualified call never reached selection and
took the primary constructor whatever its arity — and the mismatch surfaced
far from the call.

The rule: a dotted head is named by its LAST segment. Infer and Lower must
agree on which token they key by, or inference chooses one constructor and
emission calls another.

The same mistake hid in two places, and the second needed BOTH sides fixed:
a static member through a qualified type (`Inner.Box.Make`) bound in
inference but emission still built a closure over it, so it type-checked and
trapped. If you change one side, change the other.

**A type name declared at several ARITIES is now split** the way .NET splits
it: `IOpReader<'D>` and `IOpReader<'S,'D>` are `IOpReader` and `IOpReader`2`.
The first arity seen keeps the plain name; a use's WRITTEN type arguments
pick the variant, a bare constructor call chooses by argument fit across all
variants, and Lower learns a decl's decorated name via a `$tyname:` marker.
Same-name-same-arity across MODULES still merges — the port renames those
when private (see DIVERGENCES.md).

**A constructor scheme quantifies its DECLARED parameters first.** freeVars
order is encounter order, and `H<'S, 'D>(x : voption<W<'D>>, ...)` meets 'D
first — while the explicit application `H<'S, 'D>(...)` pins positionally
against scheme order. Crossed pins collapsed 'S into 'D, every History
constructor read Traceable<'a, 'a>, and NOTHING errored at the declaration —
it surfaced as "no constructor accepts these arguments" at every call.

**Types are keyed by BARE NAME**, so `IVal` and `IVal<'T>` share one entry.
`and IVal<'T> = inherit IVal` therefore recorded a type as its own base, and
the member walk never ended — a SHALLOW stack at 100% CPU, because the
recursion is a tail call. Both the record and the walk now refuse a cycle.
The same conflation still merges a nested private `Traceable<'T>` with a
global `Traceable<'S,'D>`; keying by name AND arity is the real fix.

**The extension-on-an-alias remap must not fire for the abbreviation's own
declaration.** Abbreviations are pre-registered before declarations are
walked, so `type MultiSetMap<'k,'v> = HashMap<'k, HashSet<'v>>` found ITSELF
in the alias table, took the name `HashMap`, and re-registered the alias
under it — after which every `HashMap<K, V>` in the project expanded with a
HashSet around its value type. Sixty-five diagnostics from one poisoned
entry, and none of them pointed anywhere near it. The tell was a HOVER on a
parameter disagreeing with its own written annotation — when those disagree,
suspect the alias table first.

The remaining 35 `List.tryFind (fun t -> t.Kind = Ident)` lookups in Infer
and Lower were audited as a group: all safe. Each is a binder/declaration
head (unqualifiable), an IdentExpr-guarded site (a dotted head parses as
DotExpr and takes a tryLast path), or a TypeDecl name. Two invariants carry
that conclusion, so guard them: `tokensOf` reads DIRECT children only —
switching a site to the recursive `Green.tokens` re-opens the trap — and
the parser collapses a dotted type-declaration name
(`type System.Threading.Interlocked with`) to its last segment, which is
the single point protecting every TypeDecl site.

## Overload resolution, and why it cannot be approximated

Selection unifies each candidate against what the call asks for and UNDOES
the attempt (`Types.unifyTrial`). Two things make that answer correctly, and
both were missing while two rounds of heuristics were tried in their place:

* the undo log is **threaded through the unifier**, never module state. Two
  workspaces type check at once under Expecto, and a trial that recorded —
  then undid — another thread's ordinary unifications corrupted both. It
  presented as five unrelated tests failing differently on every run, and as
  passing when reproduced alone.
* a type parameter a binding WRITES is **rigid** inside its body. The body
  must work for every instantiation, so a candidate may not decide that `'K`
  is `Cmp<'K>` to make itself fit. The flag is consulted only inside a trial.

An overloaded MEMBER is chosen at the application, with the arguments typed
first: that is the only moment the caller's parameters are still rigid, and
by the time an application has constrained the result the binding has been
generalized. The demand informs the CHOICE only — the chosen member is still
unified through the path that widens arguments, or `hs.UnionWith [ 5; 6 ]`
stops accepting a list where a seq is declared.

If you are tempted to approximate this again: the test is a call whose
argument types are still VARIABLES. Every candidate looks equally good there,
and that is the whole problem.

## Pattern identifiers

An identifier in a CASE pattern that starts with an uppercase letter names a
union case; it never binds. F# technically binds it (with warning FS0049) if
no case resolves, and this compiler's own source did exactly that once — a
list pattern `[ inner; GNodePat ]`. That is the shape to avoid: name pattern
binders in lowercase.

The strict rule applies only in match/try clauses. A `let`, a parameter or a
`for` still binds whatever name it is given, uppercase included.

## F# shape that keeps biting

`| None -> <rest>` swallows everything after it. Twice this silently moved
shared tail code into one branch — once skipping a type conversion, once
failing to advance a loop and hanging the compiler. Parenthesise a `match`
whose arms are statements and whose result continues below.

`if c then match ... with ... else e` is the same trap wearing a hat: the
`else` lands inside the last arm. The .NET build accepts it and the SELF-HOST
traps, which is a long way to travel for a missing bracket. Write the match
LAST — `if not c then e else match ...` — rather than parenthesising it.

**A builtin conversion is emitted at its APPLICATION.** `string` and `int`
are not functions in the emitted code, so `List.map string xs` used to leave
the bare name for the backend to stub — green build, trap when reached. It
now eta-expands: inference records the SOURCE kind at the bare identifier
(the same channel an application uses) and Lower wraps it in a lambda.

The conversion NAMES are a hand-copied list, and there are FOUR copies of it
— bare-value and applied, in each of Infer and Lower. A name added to three
of them types and then reaches the backend as an unknown. This is why the
alias spellings are canonicalized (`canonTypeName`) rather than appended:
`double` is `float` before any list sees it, so no list grew.

**A scalar's two spellings are ONE type, and a DIAGNOSTIC uses the one you
wrote.** `int`/`int32`, `float`/`double`, `float32`/`single`, `byte`/`uint8`,
`sbyte`/`int8`, `uint32`/`uint`. Each spelling used to become its own nominal
type, so `let (b : byte) = (a : uint8)` was a type error, `let n : int32 = 1`
annotated a type no backend knows, and `int32`/`uint`/`double`/`single` were
unbound as CONVERSIONS.

The alias SURVIVES inference and is canonicalized at the BOUNDARY, which is
`Types.typeConName`/`instConName` — every consumer downstream (stamping,
class ids, layouts, the marker strings in InferResult) names a type through
those, so one change covers all of them. Canonicalizing earlier, where a
written name becomes a type, is the obvious-looking place and it is wrong:
messages then name a type that is nowhere in the reader's file. fsc echoes
the written spelling (`'int32'`, `'double'`, `'uint8'` — checked), and now so
does this.

Three things have to agree that the spellings are equal, and a miss in any
one is silent:

* `Types.unify`'s `TCon`/`TCon` case, and the widening guard beside it —
  otherwise `byte` and `uint8` simply do not unify;
* `Classes.fs`'s three head matchers (`sameType`, `matchTy`, `compatible`) —
  instance dispatch is by name, so `Mul<double, float>` found no instance;
* the bare `TCon (n, _) -> n` cases in the InferResult block, which build a
  marker string WITHOUT going through `typeConName`. Those left
  `$class:Show:str:double` to reach emission as an unknown, and a `%s` of a
  `double` compiled clean and trapped.

The CONVERSION functions are value names, not types, so they are normalized
where the name is read (`canonTypeName t.Text`) rather than by growing the
list — see the four copies noted above.
`tests/conformance/suites/typealiases.fpp` pins all six pairs across
annotation, signature, element, cast and test;
`tests/conformance/neg/alias-spelling-in-message.fpp` pins the wording.

## An interpolated string IS a printf format

`$"a{e}b"` is not sugar for concatenation, and two things follow that were
both wrong and neither said so. A `%d` before a hole BINDS to that hole —
`$"n=%d{x}"` lowers to `sprintf "%d" x`, which is what makes the specifier
format AND type-check — and `%%` is one literal percent. Left alone, the
specifier printed itself (`%d42`) and the escape stayed a pair (`100%%42`).

Order matters between the two: the specifier scan counts the run of `%` to
tell `%d` from an escaped `%%d`, so collapsing the pairs FIRST turns a
literal `%d` into one that reads as a specifier and eats the hole.

## `a[i]` is indexing, `f [i]` is application

F# 6 dropped the dot. Adjacency is the whole rule and the only thing
separating the two, so the parser takes `[` as an index when it touches the
expression before it, and synthesizes a `.` so the tree is IDENTICAL to the
`a.[i]` form — nothing downstream learns the spelling exists. `[|` and `[<`
are excluded, being an array literal and an attribute list.

F# additionally REFUSES `expr1[expr2]` in argument position as ambiguous
(FS3369); this compiler indexes it. That divergence is deliberate: the
reading it picks is the one the writer meant.

## What a PATTERN may bind, and what an active pattern may be called

Two rules that were missing, both of which had accepted programs answering
for themselves:

* a name binds ONCE per pattern. `match (1, 2) with (x, x) -> x` answered 2
  — the second binder silently won — where nobody means "the last one".
  The check is its own walk, not part of the type walk, because
  or-alternatives share their binder table BY DESIGN (`| A x | B x ->` must
  bind `x` on both sides). There is no OrPat node: `|` is a TOKEN between
  sibling patterns, and it appears parenthesised INSIDE a pattern as readily
  as at the top of a clause — this compiler's own source has
  `(EVar (v, hsch) | EVarI (v, hsch, _))`. So `|` starts a branch, and
  duplicates are an error within one branch only. A record pattern's field
  LABEL is an identifier too, and `{ a = a }` names field and binder alike:
  only what follows an `=` binds.
* `(|A|B|_|)` is not a pattern. A total one answers WHICH case and rides a
  Choice; a partial one answers WHETHER it matched and rides an option; no
  return type is both. Accepted, its cases rode a Choice while every caller
  read an option.

## Anonymous records are a SYNTHESIZED nominal type

`{| X = 1; Y = "s" |}` is F#'s structural record and everything here is
nominal, so the lexer expands it — the same token-level trick interpolation
uses — into an ordinary record of a type it synthesizes, one per distinct
field-name set, declared once after the module header:

    ({ X = 1; Y = "s" } : $anon$X$Y<_, _>)
    type $anon$X$Y<'anon0, 'anon1> = { X : 'anon0; Y : 'anon1 }

GENERIC, so the same labels at different value types stay different types the
way F# has them. SORTED, so writing the fields in another order does not make
a second type. The ASCRIPTION is load-bearing: a record literal resolves by
field-name SET, so a nominal `type Same = { X : int; Y : string }` in the
same program would otherwise capture the literal, and the expected-type rule
is what pins it. The synthesized name contains `$`, which also keeps it out
of the by-label candidate list.

`{| r with X = 7 |}` gets NO ascription, because copy-and-update takes its
type from the base — which meant teaching the owner rule to ASK the base
first. It did not, so `{ r with X = 7 }` was resolved from the written labels
alone and any other record declaring an X could capture it. That was a
latent bug for nominal records too.

Three things about synthetic tokens, each of which cost a debugging round:

* they are laid out by TEXT LENGTH, not one apart. `Name<int>` only reads as
  type arguments when the `<` TOUCHES the name;
* but a GAP is needed after each expansion's closing `)`, or that `)` is
  adjacent to the next expansion's `(` and `f {| .. |} {| .. |}` becomes the
  first argument APPLIED to the second;
* the type form `{| N : int |}` anchors its brackets to the offset of the
  `{` it replaces, rather than living past EOF like the rest.
  `looksLikeTypeArgs` refuses a `<...>` whose tokens are not all on one line,
  and every past-EOF offset reports the file's LAST line — so mixing
  synthesized brackets with the user's own type tokens read as less-than
  everywhere except the last line of a file.

## The upstream NEGATIVE corpus, and what its number is worth

dotnet/fsharp has 473 `E_*` tests; we compile 244 of them. Measured, not
sampled — but the number badly overstates the gap, and every category opened
so far has discounted:

* 3 expect a WARNING, which this compiler does not emit at all;
* 102 carry no inline `Expects` tag, so they are unclassified rather than
  known-bad;
* whole areas are non-applicable by design. All 13 ByrefSafetyAnalysis cases
  are a byref escaping into a DU field or a list, unsound in F# because a
  byref is a stack pointer and fine here because it is a heap CELL;
* some are accepted only because the offending definition is never USED —
  the active-pattern return-type cases compile until something matches on
  them, and then they are rejected at the use;
* the 23 AccessibilityAnnotations cases are not the missing rule they look
  like: basic `private` IS enforced, and they are all the narrow edge of an
  accessibility modifier on an override.

So triage before porting, and prefer the areas where accepting means
ANSWERING WRONGLY rather than merely being permissive. Pattern matching is
that area — it has produced three silent-wrongness bugs here (the qualified
case that lowered to a wildcard, the uppercase binder, and the duplicate
binder above). Its cluster went 32 accepted to 25 on the two rules above.

The corpus is at 227 accepted, from 244. Three rules did that, and the
CHEAPEST by far was the computation-expression one: eleven upstream cases are
a single check, and DataExpressions went from 13 accepted to 2. Look for the
cluster that is one rule before looking for the interesting bug.

## `[<RequireQualifiedAccess>]` is enforced at the USE, not the binding

The attribute used to be parsed and ignored: `let x = Red` compiled on a type
that forbids exactly that, and with TWO such types declaring `Red` the bare
name bound to whichever was declared LAST — silently, at the wrong type.

The obvious fix is to bind the cases QUALIFIED ONLY, the way enum members
already are. It was tried and BACKED OUT, twice over: the bare name still
resolved (something later finds it by name anyway), and worse, QUALIFIED
matching broke — `match c with Colour.Red -> .. | Colour.Green -> ..`
answered the first arm for every value, because the qualified-case path
resolves THROUGH the bare binding.

So the cases stay bound bare and the USE is refused instead. `rqaCaseKeys`
records the case DEFINITIONS (path and offset, not names — another type may
legitimately declare a case of the same name) and `tryRecord` reports a bare
one through `AccessErrors`, the channel that always surfaces because the use
resolved and the declaration merely forbids it. Both positions are covered:
expression and pattern.

PATTERN position is a deliberate DIVERGENCE, and the fsi oracle is what
found it — F# ACCEPTS a bare case there, reading it as a fresh binder, so
the arm is irrefutable and every later rule is dead (warning FS0026). This
compiler has no such reading available: an uppercase identifier in a case
pattern names a case and never binds. Resolving it to the case instead would
give the same program a different meaning than F# without saying so, so it
is refused. DIVERGENCES.md carries it; `neg/rqa-bare-expr.fpp` carries the
expression half, which both compilers reject.

## A control construct needs its builder method

A computation expression is a REWRITE into calls on the builder, so `for`
becomes `builder.For(...)` and means nothing when the builder has no `For`.
F# rejects that (FS0708). Here the rewrite emitted the call regardless: it
compiled clean and the module TRAPPED when the construct was reached — a
compile-time diagnostic arriving at run time, and only on the lines that ran.

The check has to live in Desugar, which is the only pass that knows which
constructs a CE used. It cannot live where missing members are normally
reported, because that diagnostic is gated on `offset < 30000000` and the
rewrite's own tokens sit above 500000000 — deliberately, since blaming a
position the author never wrote is worse than saying nothing. So `CeBuilder`
carries the CE's OWN offset (`At`) plus a general `Has`, and the error lands
on the source.

`unknownBuilder.Has` answers TRUE for everything. A builder that could not be
typed is one the probe failed on, and guessing the other way turns a file
that does not yet type check into a pile of missing-method errors that vanish
once it does.
By contrast the `:?` cluster is permissiveness: `match (x : int) with :?
float` answers "no", which is the sensible reading of a test F# declines to
allow at all.

## The browser workflow lives in Web.fs

`fpp new` / `dev` / `bundle` / `npm` — see WEB.md for the surface. Three
things about it are worth knowing before touching it:

* it depends on NOTHING new. `HttpListener` and `FileSystemWatcher` are BCL,
  and a project without npm packages needs no Node at all, because browsers
  resolve ES modules natively. Node enters only for a bare specifier, which a
  browser cannot resolve, and then only as `npm` and `esbuild`.
* the two attributes are the whole boundary, and BOTH failure modes are
  quiet. Without `[<JsImport>]` an extern is the C import (module "env") and
  the browser refuses to instantiate — the error names `env`, not your
  function. Without `[<Export>]` a top-level function is missing from the
  exports and the page fails at the CALL, long after the module ran. The
  scaffold uses both, and `web-gate.sh` asserts they survive in the emitted
  module.
* the dev server's watcher ignores `.wasm`. The build's own output lands
  under `web/`, so watching it rebuilds forever.

`sprintf` is not usable for the file templates: a multi-line triple-quoted
format string silently collapses to its first specifier (F# warns it is a
partially-applied function), so the generated project file was the project
NAME alone. They are plain strings with `$NAME$` substituted.

## An unexplained adaptive-gate failure, and what was done about it

One full-gate run failed BOTH adaptive jobs with five type errors
(`AggNode<'a> vs Option<AggNode<'a>>`) on the generated 900 KB suite. It has
not recurred in six full runs since, nor in 36 targeted iterations — twelve
of them run concurrently with a full gate suite, which was the condition it
appeared in. Ruled out, so nobody repeats the work:

* the port driver is DETERMINISTIC — three regenerations are md5-identical,
  so both jobs were compiling the same bytes;
* the compiler has no parallelism (the `Parallel` hits in Desugar are the
  LANGUAGE's feature, not the compiler's execution);
* the same concatenation compiles clean by hand, in both the wasm and the C
  configuration — the gate uses `-o suite.c`, so it is the NATIVE defines,
  which is worth knowing before reaching for `-o .wasm` to reproduce.

What actually blocked the diagnosis was `trap 'rm -rf "$out"' EXIT`: the only
copy of what the compiler had been given was deleted on the way out, and
regenerating afterwards produced a clean build. The gate now KEEPS its
directory when it fails and prints the path. If it happens again there will
be something to look at, which is the whole reason this section is short.

A second finding from the same investigation: a `wasmtime` running this
suite had been spinning a core for 8.6 DAYS, because nothing bounded it. The
Expecto helper called `ReadToEnd` before `WaitForExit`, and `ReadToEnd`
blocks until the pipe closes — so a child that hangs WITHOUT printing never
reaches the wait, and a timeout on the wait could not have fired either. The
reads are async now and the wait is bounded, in the shell gate too.

## The by-value struct ABI reads its fields back from REGISTERS

A plain function's struct parameter is passed as its fields, in registers,
the way .NET passes one. Two kinds of field had no support in the paths that
read those registers back, and each failed in a way that named nothing
useful. Both came from the fpp.base port (`~/claude/fpp-base-snags.md`).

* **a float32 field.** The register is an f32 LOCAL, and the read had arms
  for F64 and I64 only — an F32 fell through to "read it as a word". The
  consumer then took that word for a boxed-float pointer and emitted an
  `f64.load`, so the module failed VALIDATION with the error pointing at a
  load instruction rather than at the parameter. `storBox` already knew the
  answer for a float32 slot (promote, then box); the register read simply had
  no arm. Every `*f` type in fpp.base — V3f, M44f, Box3f — was excluded from
  its build for this.
* **a field that is itself a struct.** Rebuilding the WHOLE value walked the
  top-level fields and demanded a scalar storage type for each, which a
  nested struct does not have: the compiler died with `optGet: None` instead
  of compiling. `structAbiOf` already flattens nested structs into dotted
  leaves with absolute offsets, and is what the field map is keyed by — so
  the rebuild reads those leaves now, not the top-level fields.

* **a generic class instantiated at a struct.** The constructor and the
  members must be stamped at the SAME instantiation, or the object's storage
  and its accessors disagree about the layout. The specialization demand at a
  construction was gated on `explicitCtorTypes`, which is filled while
  inferring a type DECLARATION and therefore holds only classes declared in
  the file being inferred — while that same arm serves the prelude's, whose
  `ctors` entry is project-wide. So `ResizeArray<V>` built its backing as a
  REF array while the stamped Add/Item/ToArray read it packed, and the first
  read came back as a pointer made of a double's bits. A class element or a
  float worked, which made it look like a ResizeArray bug rather than a
  stamping one.

  The demand is now recorded whenever the instantiation carries a STRUCT,
  whatever file declared the class. Recording one for EVERY generic
  construction is too much — that asks for stamps nothing can supply, and the
  adaptive suite trapped.

`suites/structabi.fpp` pins all three. Note the second one's original repro is not
valid F#: it captures the struct RECEIVER in a closure inside a member, and a
struct receiver is a byref (FS0406). What was fixed is a compiler crash on a
program fsc rejects; the same capture over a struct PARAMETER is legal in
both languages and is what the suite uses.

## A MODULE does not shadow a VALUE of its own name

F# keeps the two in different namespaces, and a value-position use finds the
VALUE — which is why `V3d.length` is an ERROR there rather than a call: `V3d`
is the let-bound function, and a function has no member `length`.

The module used to overwrite the value binding in `walkDecl`, so the F#
constructor-function idiom (`let V3d (x,y,z)` beside `module V3d`) resolved
its own calls to the TYPE: `V3d (3.0, 4.0, 0.0)` built a zero record and every
length came out 0, with no diagnostic. fpp.base's generator writes exactly
that shape (KNOWN-ISSUES #6).

The rejection needs BOTH halves. Keeping the value binding alone left
`V3d.length` unlowered and the module trapped at the access, with `--strict`
the only thing that mentioned it — so a member access on a FUNCTION receiver
is now a diagnostic, at the same line and column fsc reports.
`neg/value-shadows-module.fpp` pins it.

## The struct-return stack sat INSIDE the collector's root table

A by-value struct result is written through a destination on a raw region the
collector never scans. That region's address was a compile-time constant in
the MUTATOR's own layout (`ConstNext + 65536`, growing down) — and once the
reactor is merged in, the two modules share one linear memory, where the
runtime's 8 MB `g_wasm_roots` array happens to live. Measured: roots at
0x2310, `$ssp` starting at 459,788, which is slot 112,698 of that array. So
every struct return wrote its fields over shadow-stack root slots, and the
next collection traced a double's bit pattern as a pointer and died deep
inside the collector with a backtrace naming nothing.

That is KNOWN-ISSUES #20, and it is why struct-heavy loops had to run at a
1 GB heap. The region is runtime-owned now (`fpprt_wasm_sstack_top/base`,
beside the root table and the tid map), with a bounds check per call so
exhausting it traps instead of quietly corrupting whatever follows.

Two things about the hunt are worth keeping:

* **`FPP_CONSCHECK` degrades to a no-op under mmc.** `gc_dbg_live` exists
  only in `semi.c` and is declared WEAK, so under the default collector the
  check silently answers "always live". It found nothing for an hour because
  it was not running. Use the semi reactor for it — and note that the semi
  reactor is `fpprt_reactor.wasm`, with no suffix.
* **`FPPRT_ROOTCHECK=1`** (fpprt-embedder.h, wasm only) validates every
  range root before it is traced — the header word must be an odd
  `(tid<<1)|1` for a registered tid — and prints the slot index, the slot's
  ADDRESS and the value. That address is what identified the overlap; the
  value (`0x410efb88`, a double's high word) is what proved it was not a
  stale pointer but raw data.

## "No collection happened" is not "nothing allocated"

The heap GROWS rather than collecting when it can, so a loop that allocates
per iteration can run to completion with no collection at all. A gate built
on that proxy passed while 236 MB went by, and three separate measurements in
one session were read as "zero allocation" when they were nothing of the
kind.

`GC.AllocatedBytes ()` is the runtime's lifetime allocation counter, exposed
for exactly this. It is the only honest answer to "did that loop allocate?",
and `noalloc-gate.sh` asserts it is EXACTLY zero for the by-value struct
shapes. Prefer it to reading collection logs, and prefer both to reading the
emitted wat — a hand scan for one allocation shape missed the `$fpalloc` call
sitting beside it.

## A struct is a struct — it is NEVER re-boxed as a fallback

The design says so in three places (REPRESENTATION.md, PLAN-STACK.md,
docs/INLINE-VALUES.md) and the backend had two fallbacks that quietly said
otherwise. Both are gone; the only boxing left that anyone accepts is a
struct passed as `obj`.

* **a TUPLED parameter.** The tupled signature was built with `abiTy` per
  element, which hands a struct a POINTER — so `add (a, b)` boxed both
  arguments AND its result while the curried twin passed registers. 20M calls
  allocated 1.6 GB and ran 574 ms against the curried 329. Each struct
  element expands to its fields now, with the parameter plan the CALLER
  already knew how to honour. Both call shapes needed it: a literal tuple
  argument, and a tuple VALUE — that second path walked `paramTys`
  positionally and would read past the tuple once the signature grew.
* **a SIZE CAP.** `structAbiOf` gave up above 4 leaves, so `Box3d`
  (`{ Min : V3d; Max : V3d }`, six doubles) fell off the by-value ABI and
  every `ExtendedBy` heap-allocated its 48-byte result. The tell was that the
  benchmark ratios tracked the SIZE of the returned struct — 3.4x for a
  three-leaf V3d, 10.4x for a six-leaf Box3d — rather than the arithmetic. A
  ratio that tracks size is a fallback, not a cost. There is no number there
  now; `ok` still gates the walk, but that is a question of SHAPE (a field
  with no inline layout) and not of size.

Four more fallbacks were found the same way and are gone. A struct now
crosses a call in registers in every shape `tests/tooling/gc/noalloc-gate.sh`
covers, and that gate asserts **zero bytes allocated** over four million
struct calls.

* **an ARGUMENT that is a literal with computed fields.** The spelled-out
  arm never fired, because Core lifts the field expressions into `let`s and
  the literal arrives wrapped in them. Arguments go through `lowStructBind`
  now, which peels those.
* **a nested field given as a VARIABLE.** `{ B | Min = { X = a; Y = b } }`
  is lifted to `let _rf0 = { X = a; Y = b } in { B | Min = _rf0 }`, so the
  literal walk met a variable where it wanted a record and gave up. `_rf0`'s
  leaves are already registers; `litLeafOk`/`litLeafRaw` read them.
* **a struct GLOBAL passed BY VALUE.** A single field of one was a global
  read; the whole value was not, so it was rebuilt on the heap per use.
* **a scalar leaf of a struct EXPRESSION** — `(mk x y).X`, and through a
  nested struct `(nest v).Max.X`. The receiver was lowered as a VALUE, which
  for a call means building the object whose fields the callee had just
  written out and reading one back. Order matters here: the "nested chain
  over an ordinary object" arm matches the same shape and must come AFTER,
  or it takes the nested case and materialises the base.

The sret destination is now RECORDED by the call (`ctx.SretDst`) instead of
being recovered by scanning the lowered statements for a `$ssp` reservation.
That scan cannot be right: argument setup sits in the same statement list, so
once a struct argument could itself be a struct-returning call, "the first
reservation" named the ARGUMENT's destination. `(v3d (1,2,3)).Normalized`
answered `(1,2,3)` — silently, and only in programs where an argument needed
a scratch. Taking the LAST reservation instead is not a fix either; it is the
same guess. `neg`-style coverage for it is in `suites/structabi.fpp`.

One more trap in that path, which cost an afternoon: having found the
destination, do NOT flatten every `LDo` layer to collect the statements. The
object the call built for a one-value context is the TAIL, and flattening
descends into it — so its allocation was kept while its pointer was
discarded, and the fix measured as no change at all. Stop at the layer that
reserves the destination.

## Conventions

Commit subjects are one line, ≤ 80 chars, no AI attribution. Release notes in
`RELEASE_NOTES.md` are append-only — nothing ever rolls off.

Comments explain *why*, and are worth their space when they record a fact
someone would otherwise have to rediscover — a measurement, a trap, the
reason a slower-looking path is the correct one. They are not narration of
the code below them.

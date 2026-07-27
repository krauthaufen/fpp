# F++ — Implementation Plan

Stages are strictly ordered by architectural risk, not feature glamour. Each
stage ends with something running in CI. Status legend: `[ ]` open,
`[~]` in progress, `[x]` done.

## Stage 0 — Skeleton & infrastructure
- [x] Repo, solution layout, CI-able test runner (Expecto)
- [~] Golden/snapshot test infrastructure
- [ ] Oracle harness: run a `.fs`-subset program under dotnet and under F++,
      diff stdout (activates end of Stage 4)

## Stage 1 — Lexer, lossless trees, LSP shell
- [x] Trivia-preserving lexer for the F# subset (round-trip property:
      concat of token texts == input, byte-for-byte)
- [x] Green/red lossless syntax tree infrastructure
- [x] Error-tolerant parser: modules, `let`, expressions, DUs, records,
      matches, offside rule, class/interface bodies, members (incl. static
      abstract + associated types), for/while, or-patterns, tuple lets;
      gate: zero diagnostics on the repo's own sources (CE bodies and
      record exprs remain lossless brace-soup, structured later)
- [x] Query engine core (Salsa-style: memoized queries, dependency tracking,
      invalidation on edit, early cutoff)
- [x] LSP server v0 as first query-engine client: diagnostics (syntax),
      document outline (`src/Fpp.Lsp`); `fpp check` CLI as second client
- Exit: open a `.fpp` file in an editor, see live syntax errors; parser
  round-trips the whole compiler's own source — REACHED (editor wiring
  is a client-side config away: `dotnet run --project src/Fpp.Lsp`)

Deliberate departures from F# are recorded in DIVERGENCES.md, each with
its reason. The oracle gate cannot arbitrate them, so each carries a test
asserting our own semantics ("deliberate divergences from F#" in
EmitTests).

## Stage 2 — Names & types (the long one)
- [x] Name resolution (modules, opens, shadowing) as queries — env-threading
      pass with module paths, exports/imports, `open`, qualified spine
      resolution; cross-file go-to-def; gate: whole compiler project (fsproj
      order) resolves + typechecks with zero diagnostics
- [~] HM inference core — v0 done: unification with levels (Rémy),
      let-generalization, schemes keyed by def-offset (resolver solves all
      scoping), DU/GADT constructor schemes, generic type params, same-file
      abbreviation expansion, ascriptions, literals/apps/ops/match/if/lists;
      typed hover; gate: ZERO type diagnostics on own sources. Open:
      deferred constraints (overloads/classes), records, member types,
      cross-file
- [ ] Overload resolution as its own specced algorithm
- [x] Nominal subtyping, interfaces, classes — receiver-directed member
      binding (inference parks each dot-access and retries to fixpoint, so
      member names need not be unique); classes with constructor state,
      `let` fields incl. `mutable`, properties, methods, statics; explicit
      interface implementations; single inheritance with prefix field
      layout; `abstract`/`default`/`override` virtual dispatch; object
      expressions (anonymous classes whose captures become fields);
      `:>`/`:?>`/`:?`. Every class instance carries a descriptor
      {classId, vtable} in a hidden first field — that is what makes
      dispatch and checked casts work without knowing the concrete type.
      Gate: six oracle programs byte-exact against dotnet fsi.
      Generic classes monomorphize: a member use instantiates the member's
      own scheme, so `Buf<V2d>` and `Buf<int>` stamp separate copies, and
      stamped clones are alpha-renamed so per-parameter backend state cannot
      leak between specializations.
      Property accessors (`member x.P with get() = ... and set v = ...`)
      lower to a reader `P` and a writer `set_P`; a generic base is
      instantiated through its `inherit` clause, so inherited members type
      correctly on a derived receiver; a constructor parameter becomes a
      field only when a member reads it (F#'s own storage rule).
      Open: `member val`, `static let`, operators as members, interface
      inheritance, `AbstractClass`.

### Measured against the acceptance target
Running the real `HashCollections.fs` (4501 lines) through the front end:
**the first 3167 lines now parse and typecheck with zero diagnostics**, and
lowering reports only 18 gaps in them, all of one kind (assignment to a
`val mutable` field). The first error was line 24 when this measurement
started; it has moved 24 -> 184 -> 530 -> 855 -> 3168.

That covers the hash-mixing helpers, the whole node class hierarchy, and
the set/map node implementation: generic inheritance, property accessors,
packed uint32 tag bits, the NodeKind enum, null-terminated chains,
IEqualityComparer dispatch, struct tuples, and implicit upcasts.

On the acceptance target: the ported file (4130 lines) **parses with zero
diagnostics, has 3 type errors, and lowers with 11 notes**.

`EmitProgram` returns early on those, so to find the REAL remaining set the
emitter was run directly (`emitforce` in the scratch harness). It reported
**87 errors** at first measurement; after the class layer, the resolver
fixes and the widening work it is **6 diagnostics / 17 emit errors**, nearly
all member overloading. The split at first measurement:

- [x] a TYPE and a MODULE may share a name — done. Types have their own
      namespace, a dotted spine that resolves qualified IS qualified, and a
      bare expression name prefers the type (a module is never a value).
      119 -> 87 errors.
- [ ] type tests and downcasts against BUILTIN collections: `:? array<'K>`,
      `:? list<'K>` need a runtime representation test, not a class id (12)
- [x] MEMBER overloading — instance AND static. Overloads register under
      ordinal keys ("HashMap.CopyTo#2", declaration order, resolver and
      inference assigning the same ordinals). Selection happens in the
      parked-dot retry — which runs after the whole file is typed, so the
      call's argument shape is visible through the access's result var — by
      a non-committing structural test, EXACT fits ranked above ones that
      need the supertype allowance (or Equals(obj) always wins). An
      uninformative set stays parked; a final forced pass breaks true ties
      in declaration order. Statics park with a synthetic receiver. The
      chosen ordinal rides to Lower in the MemberSites owner tag
- [x] `f<T> x` nests as `(f<T>) x` — Lower strips the pure type application
      so its builtin/member special cases see their shape (zeroCreate fell
      into the C-ABI extern path)
- [x] `.Length` where the element type is not statically known called a
      runtime helper that was never DEFINED — any module reaching it failed
      validation. `$lenv` now exists
- [x] ctor arguments widen to a declared base, including inside the
      argument TUPLE (unifyArg now recurses into tuple components)
- [x] explicit type application in expressions: the lookahead accepts
      `struct(...)` types, and the written arguments pin the callee's
      freshened instantiation vars — `Array.zeroCreate<struct('K * 'V)>`
      types without a downstream use
- [x] `Array.zeroCreate`, lowered to wasm's `array.new_default` (numeric
      zeros, null refs — the zero fill IS the default fill)
- [x] a nested local no longer exports over a module-level binding of the
      same name; qualified expression spines prefer a TYPE over a module
      sharing its full name (constructor calls through `Impl.MapLinked`)
- [x] the enumerator protocol. `for x in e` is STRUCTURAL, as in F#: any
      GetEnumerator/MoveNext/Current shape enumerates, no interface needed.
      The desugar creates three member accesses at SYNTHETIC offsets
      (30/40/50M + the loop's own), parks them with everything else, and the
      lowering derives the same offsets and reads what they bound to —
      interface members dispatch through the vtable, concrete ones call the
      lifted function. `IEnumerator`/`IEnumerable` are prelude interfaces
      and `seq` aliases IEnumerable, so a seq parameter enumerates without
      knowing the concrete type. Lists walk their cons cells; arrays keep
      the indexed loop; both accept destructuring binders. Fixed on the way:
      `new X<T>(args)` typed as a fresh variable (every new-built enumerator
      was opaque), and "no such member" during the MAIN pass silently
      unbound members declared later in the same class — the fields table is
      only complete once the retries run
- [x] arrays of TUPLES (a uniform-reference element) index as plain $arr —
      previously unnameable, so `for (k, v) in pairs` over an array of
      pairs could not lower
- [x] ofSet/toSet dropped by the port script: they bridge to FSharp.Core's
      Set, a type that lives outside the file being ported

### Acceptance: ONE error left in the whole file
Type tests landed: `:? list`/`:? array`/`:? string` are representation
tests (null MATCHES `:? list` — nil is a null reference; noted with the
other representation decisions), an INTERFACE test is a class-id check
over its implementors, and every class-id read is guarded — a non-object
answers false instead of trapping (`(box 5) :? HashSet` was a crash).
Downcasts to interfaces/builtins check the same way. The 36 emit errors
collapsed to ONE: most "unknown field" errors were downstream of type
tests failing earlier in the same member.

The occurs corruption is FIXED, and it was a beauty: `let (k, v) = e`
parses as one FLAT ParenPat (no TuplePat node, just a comma), and every
phase treated it as a SIMPLE binding named k — v never bound, the tuple
type silently mis-unified, and in the acceptance file that corrupted the
class-level 'V across members until an occurs check finally tripped three
members later. All three phases now detect the flat-paren destructure.

The mscorlib interfaces are settled BY KIND: the read contracts
(IReadOnlyCollection, IEquatable, ISet's query side) are prelude
interfaces — genuinely meaningful for immutable collections — and the
mutation interop (ICollection, ISet's ExceptWith family, the non-generic
System.Collections enumerators) is dropped by the port script, which also
flattens .NET's interface inheritance by injecting ISet's Contains/Count
forwards. Fixed alongside, each pinned:
- F#'s HIGH-PRECEDENCE APPLICATION: `C(1).Get()` — the parser never chained
  a postfix dot past a call, and both Lower and Infer then treated
  `C(args).M` as a STATIC access, silently dropping the receiver (compiled
  clean, read garbage at runtime)
- a static member used ABOVE its declaration in the same class parks on
  the owner type until the fields table is complete
Emit tail: 30 -> 23 — the remainder sits in HashSet's overloaded
SetEquals/IsSubsetOf family (forward statics inside overloaded members)
plus valueTupleGetter/KeyValuePairDebugFriendly corners; the minimal
repros of each ingredient pass individually.

### Acceptance emit status after the stdlib layer
61 -> 36 emit errors. Lists and arrays are genuine seqs AT RUNTIME: the
IEnumerable/IEnumerator dispatch sites pre-test the representation and
route to a built-in iterator ($iter walks cons chains and indexes any
array kind), so a list literal flows through a lazy Seq pipeline and into
String.concat. The tail: type tests against BUILTIN collections
(`:? list`/`:? array`/`:? ISet`, 12 — a designed feature, representation
tests not class ids), a resolution corner where `HashSet.OfSeq` inside the
class's own ISet impl fails to bind, and array-write specialization in two
generic bodies.

### ACCEPTANCE MILESTONE: the whole file front-ends clean
`reference-HashCollections.ported.fs.txt` (4130 lines): **0 diagnostics,
0 lowering notes**. First error line 24 at the start; the journey ran
24 -> 184 -> 530 -> 855 -> 3168 -> clean. What remains is the EMIT phase:
61 errors, all stdlib surface (`sprintf`, `String.concat`,
`Object.ReferenceEquals`) plus array-write specialization in generic
bodies — "compiling and running" now means the backend tail, not the
language.
- [x] the genuine stdlib, done as CORE (the prelude, auto-opened):
      * `string x` for every primitive kind, .NET spellings; number-to-
        string builders (ltoa/ftoa/ftoa6/hex/octal) are the primary
        implementations and the printers print their result
      * the printf family as COMPILE-TIME expansion — %d %i %u %s %c %b
        %x %X %o %f %A, %%, width and 0/- flags, byte-exact against F#;
        %e/%g refused rather than approximated; partial application
        expands to a lambda (`Seq.map (sprintf "%A")`); %A quotes strings
        and chars, and dispatches on the runtime representation at a
        statically-unknown hole
      * `Seq`: lazy map/filter/truncate/take over the enumerator protocol
        (object expressions), eager exists/forall/fold/iter/length/toList
      * `String`: length/concat/replicate/init/exists/forall/iter/iteri/map
      * `KeyValuePair` (a struct class), `KeyNotFoundException` as an exn
        case (the port script rewrites the .NET nullary ctor to carry
        .NET's own message)
- [ ] string INSTANCE members (s.Substring, s.Contains, ...) need extension
      members on a builtin type — a language feature, not stdlib
- [x] two capture bugs the lazy Seq surfaced: a nested object expression's
      construction read captured vars RAW even when they were fields of the
      enclosing anonymous class, and each member lift CLEARED currentSelf
      instead of restoring it — any object expression inside a member
      poisoned everything after it
- [x] pipes widen: `xs |> Seq.length` decomposes the function type first,
      so a list flows into a seq parameter, as in application position

So: stdlib alone would NOT make this compile. It is roughly a 1:6 split in
favour of compiler work.

Two real bugs found by pushing on this file, both fixed:
- `open M` did not bring M's NESTED modules into scope, because an open was
  recorded as a bare name instead of being resolved relative to where it
  appears;
- a cast or type test named its target by the LAST identifier of the type,
  so `x :?> MapLeaf<'K, 'V>` tried to downcast to `V` (68 errors).

### HKT — follows directly from the class layer
Design: DESIGN.md ("Higher-kinded types"), syntax now consistent with the
class decisions. The class machinery is kind-agnostic, so HKT adds:
- kinds declared by shape (`'m<_>`), checked at application — a small pass,
  no kind inference
- constructors as type arguments; unification decomposes the OUTERMOST
  application only, which is what keeps it first-order. No type-level
  lambdas; partial application is a trailing `_` run only
- monomorphization unchanged in character: a known constructor stamps, a
  variable one takes the dictionary — the same Stamp/Canon split

### Typeclasses — the numeric hierarchy is the first client
Design: DESIGN.md ("Numeric classes and operators"). Decided:
- operators are two-parameter classes with an associated `Result`, the Rust
  `Mul<Rhs> { type Output }` shape; the member is named `(*)`, not `Mul`
- knowingly overloading rather than law-carrying algebra, for operators only
- coherence: one instance per `(a, b)`, plus an orphan rule
- a constraint is a CLASS APPLIED TO TYPES, Haskell-style:
  `when Fractional<'a>`, never `'a : Fractional`. The latter reads as
  subtyping and has no reading for a two-parameter class
- constraints must be able to equate an associated type (`Result = 'a`) —
  this is what closed classes use to pin operators to closure
- a CLASS is not a type: no values, no subtyping, no boxing, no `I` prefix.
  Declared with `class`, which is free (F#'s `type X() = class end` is not
  part of F++); instances with `instance`
- a class NEVER stands where a type goes (`Matrix<Fractional>` rejected):
  it hides whether two positions share a scalar and breaks down the moment
  a function needs two different ones. Type variables are always named and
  implicitly quantified, as in F#
- closed classes (`Fractional<'a>` etc.) carry superclass constraints, so
  generic math annotates with ONE name and projections reduce from the
  constraint rather than from a concrete type
- constraints are INFERRED, and projections may appear in inferred results
  (requiring them to reduce would be grounding by another route). The
  readability problem is solved by PRESENTATION: one symbol maps to one
  class, so `Add<'a,'b>.Result` renders as `'a + 'b` and an inferred type
  mirrors the expression that produced it. Pure sugar: defined only for a
  class with one associated type and one operator member, never affects
  inference, degrades to the nominal form (unlike `Matrix<Fractional>`,
  which had a cliff). Display first, source syntax later
- constraint sets are simplified: duplicates collapse, superclass-entailed
  constraints are dropped
- instance reduction must be decreasing, or type-level evaluation can loop
- errors name the operator application and its operand types, never the
  accumulated chain
- instances are free-standing (Haskell-style); `static member (+)` is sugar
  for the homogeneous case
- one operator symbol maps to exactly one class
**Built.** The numeric tower is real and runs. What landed:
- [x] `class` / `instance` declarations, operator member names (`(+)` fuses
      into one identifier token, and the lexer carves `(*)` out of the
      block-comment rule as F# does), `when` constraints on classes,
      instances and `let` bindings
- [x] a class member IS a constrained scheme — so associated types never
      enter `Type`, and unification was not touched at all. The solver is a
      store of wanted constraints run to fixpoint next to the existing HM
- [x] one-way instance matching, improvement when exactly one candidate
      survives (including on the ASSOCIATED TYPE, which is what keeps
      `a + b + 1` at `int -> int -> int`), superclass entailment from a
      declared `when`, numeric defaulting to int
- [x] Add/Sub/Mul/Div/Rem plus Num/Fractional/Integral with Zero/One, and
      an instance of each for int, int64, uint32, float, float32 (`+` for
      string). Primitive instances declare no bodies: the backend emits the
      machine instruction, which is the design's "the instance is known
      statically and inlined" spelled out
- [x] `Ordered<'a>` (`< > <= >=`, homogeneous, always bool, no associated
      type) and `Neg<'a>` (unary minus). `=`/`<>` are deliberately NOT a
      class: structural equality is total. String ordering is ordinal
      (`$strcmp`, byte-wise), oracle-checked against F#
- [x] class members are qualifiable: `Num.Zero`, `Add.(+)`. A primitive
      instance gains a generated wrapper function so a NAMED use denotes
      something callable while `a + b` stays a machine instruction
- [x] user instances with bodies, homogeneous and heterogeneous
      (`Mul<float, V2d>`) — an instance member is an ordinary top-level
      function
- [x] a body left generic over its operand type is STAMPED per
      instantiation, reusing the layout-dependent machinery. This fixed a
      real bug: `let add a b = a + b` used at float emitted `i32.add` and
      trapped
Open:
- [ ] the operator-notation sugar (`'a + 'b` for `Add<'a,'b>.Result`) —
      contexts are inferred and stored, but printed nominally
- [ ] constraint-set simplification (dedup, drop superclass-entailed) before
      display
- [ ] the orphan rule and the coherence check are not enforced; two exact
      matches currently refuse to choose rather than being rejected at
      declaration
- [ ] the decreasing-instance check for termination
- [ ] a heterogeneous instance reached from inside a generic body: the
      stamped operator carries one operand type, so only the homogeneous
      case resolves there
- [x] the math surface: `Abs`, `MinMax`, `Floating` (sqrt, truncate, exp,
      log, sin, cos, tan, sinh, cosh, tanh, asin, acos, atan, atan2, pow),
      `%` on floats. `sqrt`/`abs`/`truncate` are machine instructions; the
      transcendentals are written in F++ in the prelude, because wasm has no
      libm under it — accurate to ~1e-15 but not bit-identical, so they are
      tested to a tolerance (DIVERGENCES.md)
- [x] `Ordered` is ONE operation (`compare : 'a -> 'a -> int`); `<`/`>`/
      `<=`/`>=` are notation for a test on its result wherever the instance
      is not primitive. `MinMax` deliberately does NOT require `Ordered`, so
      a vector can have a componentwise min without a total order
- [x] a named class member used inside GENERIC code (`compare key k` on a
      generic key, which the MapExt port needs) resolves after stamping —
      the member and its type travel in the IR until the copy is concrete
- [x] a real bug this surfaced: stamping decisions did not walk match/try
      GUARDS, so a generic operator in a `when` clause was invisible to
      specialization. Pre-existing — it applied to array ops too

### Tooling: projects and editors
Docs: editors/README.md.
- [x] `*.fppproj` manifests: an ordered source list, libraries, output. No
      globbing — the compile order is semantic, and a directory listing
      would hide the one fact the file exists to state
- [x] `fpp check <proj>` / `fpp build <proj>` take the manifest
- [x] the LSP server finds the manifest by walking up from the opened file,
      so an editor never has to be told where it is; it works in filesystem
      paths, with URIs only at the protocol edge
- [x] hover shows the generalized scheme WITH its class context
- [x] VS Code extension (editors/vscode): client, TextMate grammar covering
      class/instance/operator members, build command
- [x] Rider/IntelliJ via LSP4IJ — configuration only, documented
- [ ] Visual Studio needs a VSIX implementing ILanguageClient; buildable
      only on Windows with the VS SDK, so not written
- [ ] completion, references, rename, semantic tokens
- [ ] a real cross-file bug this surfaced and fixed: a generic binding used
      from ANOTHER file recorded no specialization demand, so its body was
      dropped as a template and the call was unbound. Every generic
      arithmetic function hit this once operators became class members

### Numeric tower
- [x] int, int64, float, float32, uint32: literals, arithmetic, comparison,
      bitwise and shifts, conversions between them, packed struct fields,
      structural equality and hashing. Conversions dispatch on the type
      INFERENCE resolved, not the backend's kind analysis — the latter
      cannot see through a global.
- [x] float16. wasm has no f16 either, so a half is its 16-BIT PATTERN in an
      i31 — allocation-free, like an int — and every operation widens to f32,
      works there, and rounds back ONCE. That single rounding is correct:
      double rounding is innocuous at 2p+2 bits and f32's 24 is exactly the
      bound for f16's 11, so arithmetic is bit-identical to native hardware.
      Conversion from DOUBLE goes straight to f16 ($f2h64) rather than
      through f32, which would round twice and is observably different at
      the bottom of the subnormal range. Checked against System.Half.
- [x] float16 ARRAYS are packed: `(array (mut i16))`, 2 bytes per element,
      reads via `array.get_u`. The size win the type exists for.
- [ ] a half FIELD still stores as i32 — packing it means `struct.get_u`
      at every field-read site for a per-field saving that rarely matters;
      do it if a struct-of-halves ever shows up hot
- [ ] uint64, and the smaller widths (int8/16, byte). No demand yet.
- [ ] `decimal` — DEFERRED, deliberately. wasm has four numeric types and
      none of them is decimal, so it would be a software bignum: a 96-bit
      mantissa with a scale, 96x96->192 multiply, long division, and
      round-half-to-even, to be bit-exact with .NET. That is a few hundred
      lines for a type this language's users are unlikely to reach for.
      Cheap to reverse: the class layer makes it purely additive — a type
      plus `Add`/`Num`/`Ordered`/`Fractional` instances, no compiler change.
      Revisit if something real needs exact base-10 money.

### Identity: hash and equals — in progress
Contract and semantics: DESIGN.md ("Identity"), divergences: DIVERGENCES.md.
- [x] DUs and tuples compare and hash structurally (they were compared by
      REFERENCE: `Box 3 <> Box 3`). Sound because case tags are globally
      unique and `$tupN` is one wasm type per arity.
- [x] arrays hash by length — stable under element mutation
- [x] descriptors on every reference type. Records compare and hash
      structurally and soundly: differing descriptors mean differing types,
      which a shape test cannot establish (wasm-GC canonicalizes
      same-shaped structs into ONE heap type — a 2-field record used to
      canonicalize with `$cons` and was compared as a list cell, giving the
      right answer by luck).
- [x] generated per-type equals/hash in vtable slots 0 and 1; a
      user-declared `Equals`/`GetHashCode` fills the slot instead.
- [x] per-OBJECT identity hash for classes: a word in the object header,
      handed out on first use. Records and structs do not carry it.
- [x] `Equals`/`GetHashCode` overrides work on ANY type — records and
      unions too, not just classes. A union has no descriptor field, so its
      identity dispatches through a table indexed by case tag, which is a
      DU's equivalent of a vtable. `GetHashCode()` is written with a unit
      argument, so its arity is adapted to the slot.
- [x] `$boxi` was `(struct (field i32))` and so was `$du0` — the SAME heap
      type after canonicalization, so a nullary union case was hashed as a
      boxed int. `$boxi` is now mutable, which separates them.
- [ ] `$hashv`/`$equal` still exist as the dynamic entry points. They are
      now thin — primitives, then descriptor dispatch — but the remaining
      shape tests (cons, tuple, DU) could move behind descriptors too.

### Generic structs — DONE
A generic struct is stamped per instantiation, so its fields carry a real
representation instead of being boxed: `Pair<float,float>` gets f64 fields,
`Pair<int,int>` gets i32, and arrays of them are packed. Struct tuples get
this for free, being ordinary generic structs. Reference types are NOT
stamped: their fields are uniform whatever they hold, so splitting them
would buy nothing.

How: a type's name carries its instantiation, bracketed so nesting stays
unambiguous (`Pair$<int.Pair$<int.int>>`); Infer records that name wherever
the backend identifies a type by name (array element, field owner, record
literal, struct-tuple pattern); Link stamps a DRecord per used name after
monomorphization; and a record name still mentioning a type variable makes
its function layout-dependent, so the function is stamped and the name
substituted.

Two latent bugs surfaced and were fixed:
- a recursive self-call carries no instantiation (a function is monomorphic
  inside its own body), so a stamped clone kept calling the template that
  specialization had already removed;
- synthetic `_arg` binders reused their definition's own offset, so a
  parameter and its function shared one identity and any table keyed by
  VarId confused them.

Earlier items, now done:
Earlier items, now done:
- [x] struct tuples: NOT a concept in the core. `struct(a, b)` builds the
      prelude's generic struct `StructTuple2<'a,'b>`, in expression,
      pattern and type position — so every struct rule applies to it
      unchanged, and improving generic-struct layout improves it for free.
- [x] nominal subtyping: an argument may be a subclass of the parameter, or
      a class implementing the expected interface. F# inserts the upcast
      and the representation is identical, so unification widens instead
      of failing.
- [x] `IEqualityComparer<'a>` in the builtin prelude, satisfiable with an
      object expression. Fixed a real bug on the way: a generic interface
      (`IEqualityComparer<int>`) was registered under its type ARGUMENT,
      so every generic interface implementation was misfiled.
- [x] null as empty: `null` was lowering to unit — a real value, silently
      wrong. It is now `ref.null`, with `isNull`, null patterns, and
      `$equal` treating null as equal only to null.
- [x] `uint32`: literals (`1u`, `0xABCDu`), the type, unsigned ops
      (`/ % < > <= >= >>>` emit `i32.*_u`), `int`/`uint32` conversions as
      bit-preserving primitives, unsigned printing. Same i32 payload as
      `int` — only the operations differ. Bitwise operators are now
      same-type rather than int-only, and shifts keep their operand's type.
- [x] `downcast` / `upcast`: the target comes from the context, so the
      site parks during inference and reads its resolved type back after
      solving — the same deferral member binding uses.
- [ ] multi-entry attribute lists `[<AllowNullLiteral; AbstractClass>]`
      and `AbstractClass` itself
- [x] enums (`| Leaf = 0uy`): an enum value IS its integer, the cases are
      constants, and `NodeKind.Leaf` resolves through the type name.
- [ ] null-as-empty (`AllowNullLiteral`): empty case as `ref.null`,
      test as `ref.is_null`
- [ ] O(1) `toHashSet` via the prefix layout that now exists
- [ ] GADT mode: per-case schemes, match refinement, existentials,
      escape diagnostics
- [ ] Kinds + HKT: `'m<_>` params, bare-constructor type args,
      `when 'm : Monad` constraints, spine unification, trailing-`_` sections
- [ ] Typeclass resolution: definition-site instances, conditional
      instances, associated types + injectivity
- [ ] LSP grows: hover types, go-to-def, find-refs
- Timebox rule: ship an ugly-but-honest solver first (annotations required
  in more places than ideal), reach running programs, then iterate inference
  quality against the oracle suite
- Exit: compiler's own source (common subset) typechecks

## Stage 3 — Typed core
- [x] Small typed core IR (`Core/Core.fs`) — binders/ctors carry schemes;
      dictionaries and GADT coercions arrive with the typeclass layer
- [x] Elaboration surface → core (`Core/Lower.fs`) for the v1 emission
      subset (functional core + records/DUs); out-of-subset constructs
      produce notes, never failures
- [x] Core linter (`Core/Lint.fs`): independent re-typecheck; gate:
      lint-clean on all sample programs AND on everything lowered from the
      compiler's own sources
- [x] REPRESENTATION.md: boxed/unboxed, structs, arrays, generics — the
      uniform-slot baseline + specialization plan (user requirement)
- Exit: REACHED — sample programs lower 100% note-free and lint-clean;
  next stop is the wasm-GC emitter consuming Core.Ir

## Stage 4 — First backend: wasm-GC
- [x] Core → wasm-GC lowering (`Backend/EmitWasm.fs`): uniform anyref repr,
      i31 ints, GC structs for records/DU cases/tuples/closures, $cons
      lists, i8-array strings via passive data, known-call fast path +
      curry wrappers, pattern compilation with br-chains, structural $equal
- [x] Runtime shims in emitted WAT: WASI fd_write putc/printi/prints,
      printval, equal, append, applyc
- [x] `fpp build -o out.wat` CLI; end-to-end tests run wasmtime and assert
      stdout (hello/factorial, DUs+closures+records+lists+equality,
      guards/tuples/negatives)
- [x] Oracle harness ACTIVE: programs run under dotnet fsi AND fpp+wasmtime,
      outputs diffed byte-exact — first catch: i31 overflow on fact 13,
      fixed by the box-spill
- [x] int32 box-spill ($ofi/$toi, normalize-on-box; full int32 wraparound
      semantics verified by the oracle)
- [x] tail calls (return_call in tail positions; oracle: 1M-deep loop)
- [ ] inner let rec, match-body tail positions, more oracle programs

## Stage 4.5 — Expanded mandate (user directive: "all of it")
- [~] More F# surface area end-to-end: while/range-for/mutables/assignment
      SHIPPED (EWhile/EAssign in core, for desugars to while, oracle-checked).
      Arrays SHIPPED: [| |] literals, a.[i] get/set, .Length on
      arrays+strings, int[] types, oracle-verified incl. for-loop sum.
      NUMERIC TOWER SHIPPED: float/float32/int64 typed prims (Infer OpKinds
      per operator -> suffixed core ops -> typed wasm instrs), boxes
      $boxf/$boxs/$boxl, exact printers, oracle-verified.
      STRUCTS SHIPPED: [<Struct>] records emit unboxed typed fields
      (V2d = two raw f64s); index element typing; V2d array-sum oracle.
      EXCEPTIONS SHIPPED: failwith/raise -> wasm throw, try/with ->
      try_table + clause chain + rethrow; builtin exn/Failure;
      oracle-verified (wasmtime -W exceptions=y; Chrome ships EH).
      Open: general for-in over collections, string ops beyond concat,
      printf formatting, CE bodies, try/finally
- [~] Linker: fat-IR .fppir format DONE (Core/Serialize.fs s-expr:
      exports + schemes + decls), `fpp lib -o x.fppir` + `fpp build`
      accepting .fppir DONE (cross-lib resolution, typing, direct calls),
      demand-closure DCE at link DONE (Core/Link.fs). Open: tier-1
      instantiation stamping (needs per-use instantiation types recorded
      in Infer), symbol dedup across libs
- [~] C FFI (user vision: SEAMLESS — include a header / link a .so, done):
      `extern let name : type` SHIPPED — typed foreign imports, i32 C-ABI
      boundary wrapping, cross-module linking via wasmtime --preload
      (the exact shape clang --target=wasm32 emits). Open:
      Zig-@cImport model — libclang-parsed headers materialize extern
      declarations at compile time (fits the plugin architecture: a
      binding generator IS a declaration-emitting plugin); C++ via
      extern "C" boundaries only (full C++ interop is a non-goal v1);
      wasm: host imports; native: direct C ABI, blittable structs
- Exit: hello world through real programs run — REACHED

## Stage 4.9 — Compiler plugins (TAST -> TAST)
- [x] `Core/Plugins.fs`: `Plugin = { Name; PerFile : Decl list -> Decl list;
      WholeProgram : Decl list -> Decl list }`, registered in project config
      (NO source annotations), run in order after lowering / at link
- [x] Core linter validates every plugin's output — a broken plugin is a
      compiler error naming it, never a miscompilation
- [x] Shipped plugins: `constFold` (TAST rewrite) and `deriveShallowEquals`
      (emits per-type shallow equality for every record; DCE drops unused,
      which is what makes annotation-free derivation free)
- [ ] Load third-party plugins from assemblies/config; expression-level
      plugin blocks (`myplugin { ... }`) consuming the lossless token span

## Stage 5 — Stdlib & dogfood
- [~] `stdlib/array.fpp`: Array module (length/get/set/fold/iter/exists/
      forall/contains/tryFind/tryFindIndex/toList/isEmpty/sum/max/min +
      init/map/filter/rev/copy/append/sort in int and float flavours);
      generic element types await tier-1 specialization
- [~] `stdlib/check.fpp`: **Check** — property/fuzzing library in F++
      (seed-threaded generators: int/bool/elem/list/pair; `forAll` runner
      reporting failure count + reproducible seed). Replaces hand-rolled
      LCG loops; the basis for porting Adaptive's FsCheck properties
- [~] `stdlib/mapext.fpp`: **Map = MapExt** (AVL tree: height/count cached,
      rebalance, add/remove/alter/change/update/tryMin/tryMax/fold/foldBack/
      map/mapValues/filter/choose/exists/forall/partition/union/unionWith/
      intersect/intersectWith/difference/choose2/map2/keys/values/toList/
      ofList) + **Set** on the same tree; tests: per-function edges, AVL
      invariants, ordering, laws, and a 400-op randomised differential
      against an assoc-list model — 62 assertions, all matching F#
- [~] `stdlib/hashmap.fpp`: **HashMap + HashSet** core (patricia trie) with
      the same operator vocabulary as Map/Set (add/remove/alter/change/
      update/tryFind/containsKey/findOr/fold/map/mapValues/filter/choose/
      exists/forall/partition/union/unionWith/intersect/intersectWith/
      difference/choose2/map2/keys/values/toList/ofList); 44 assertions
      incl. a 500-op randomised differential against an assoc-list model over the patricia trie
      (add/remove/tryFind/containsKey/fold/toList/ofList; Set union), all
      oracle-verified against F#
- [~] `stdlib/list.fpp`: List module written IN F++ (length/rev/map/filter/
      fold/sum/exists/tryFind/append/init), oracle-verified against F#
- [ ] Prelude reimplemented in F++ (the bootstrap seam closes)
- [ ] Core collections, string, IO; Functor/Monad/Collection hierarchy
      proves out or gets revised
- [ ] Generic `monad<'m>` CE builder as the HKT showcase test

## Stage 6 — Self-host flip
- [ ] Compiler source compiles under itself (stage 2 binary)
- [ ] Fixpoint: stage2-compiled compiler recompiles source → byte-identical
      stage3; test pinned in CI forever
- Exit: dotnet becomes optional for development

## Stage 7+ — Native backend & beyond
- [ ] LLVM or Cranelift native backend, MMTk (Boehm to start)
- [ ] Monomorphization/unboxing optimization pass over uniform baseline
- [ ] Plugin (type-provider successor) declaration-IR + query endpoint API
- [ ] Scoped given-imports iff definition-site coherence proves too tight

## Standing decisions (see DESIGN.md for rationale)
- Query-based incremental compiler; LSP is client #1
- Written in the F#/F++ common subset; runtime touchpoints behind `Prelude`
- No type-level lambdas; kinds capped ~rank 2; associated types not fundeps;
  no orphans; uniform representation baseline

### ACCEPTANCE MILESTONE 2: the whole file EMITS and RUNS
`reference-HashCollections.ported.fs.txt`: **0 diagnostics, 0 lowering
notes, 0 emit errors** — 330KB of wat that wasmtime validates, instantiates
and runs to exit 0. The journey: 87 -> 61 -> 36 -> 23 -> 14 -> 5 -> 0.
What broke the tail, in dependency order:

- **The full value restriction.** A parameterless binding whose RHS is
  expansive stays monomorphic. `let a = Array.zeroCreate n` had every use
  instantiating fresh variables, so the stamper could not tie the array's
  element type to the enclosing instantiation.
- **Assignments now unify.** `lt <- rt` typed both sides and unified
  NOTHING; `inner <- Some e` constrained nothing and the payload stayed
  unknown forever. Now argument-style (a list still widens into a seq cell).
- **Union by level.** Var-var unification kept whichever variable was on
  the right; re-pointing a class-level variable at a member-level one made
  every scheme quantifying it miss its substitution at instantiation, and
  the first concrete use grounded the raw variable for the whole class
  (HashMap.OfList became `list<'a * int>` because a DELTA member used
  `HashMap<'K, int>`). The shallower variable is now always the
  representative. This subsumed an earlier ordering fix in property-setter
  typing and is the root fix for the whole "silently int-only" family.
- **Written type args in expression position** (`HashMap<'K, int>(...)`)
  resolved in a FRESH scope, disconnecting 'K from the member's 'K —
  a tyScope now carries the enclosing binding's named variables.
- **Cross-file/same-class instantiation demands**: qualified uses of
  another file's generics, statics resolved through the PARKED path, and
  `static let`s all lost their instantiation lists, so layout-dependent
  callees had their templates removed and nothing stamped. All three now
  record demands (in the defining scheme's variable order).
- **`and`-groups**: sibling types now pre-bind in Resolve AND pre-register
  primary-ctor schemes in Infer, so `HashSet`'s members can build the
  `HashMap` declared after them.
- Stamp names disambiguate when two top-level functions share a bare name
  (Array.rev / Seq.rev both stamped to `rev$int` and one clobbered the
  other in the stamped-clone dict).
- `$str` sentinel: string CHAR access no longer collides with arrays whose
  ELEMENTS are strings; boxed element types fall back to the uniform $arr.
- Enum cases named through their type (`NodeKind.Inner`) survive an
  unrelated type also answering to the case's name.
- struct-tuple PATTERNS in lambdas and match arms destructure through a
  synthetic binder; single-payload constructors work as first-class
  functions (`|> Some`, `update >> ValueSome`).

### Stdlib: List, Array, Seq as real modules
Full everyday F# core surface, written in F++ in the prelude: `List` (~40
functions incl. stable merge sort, splitAt, zip/unzip, sum/max under class
constraints), `Array` (same surface, bottom-up stable merge sort, copy/sub/
fill/blit, ofSeq/toList round-trips), `Seq` extended (append/collect/choose/
mapi/skip/init/singleton/replicate/sortWith/rev/toArray + eager folds).
Operator sections `(+)` parse, type with the operator's class constraints,
and lower to a lambda over the same resolution an infix use gets.

### Next: the collections must WORK, not just run
A smoke test appending real HashSet/HashMap usage compiles clean but traps
at runtime: `IsLeaf` (a bit-packed base-class member) cast-fails when
called from a stamped `addInPlace$int` clone. Minimal repros of the
inheritance + stamped-builder shape pass, so the failing ingredient is
still unisolated. Also parked: `HashMap [ ... ]` (ctor overloads from seq),
top-level `let x, y = ...` destructure lowering ("top-level let shape"),
inline `let ... in` destructure + index corner.

### Solver termination and the suite clock
Three non-termination bugs in constraint solving, all found by reading after
a stack sample: numeric defaulting re-picked the SAME non-ground constraint
forever when its defaulting unification failed (a tuple arg vs int — this
alone was 8.5M solver calls on Workspace.fs); a failed IMPROVEMENT re-queued
its unchanged constraint inside the same pass; and an instance context could
grow the queue unboundedly (now deduped per pass + budgeted). The structural
walkers (unify, occurs, freeVars, adjustLevels, typeString, instantiation
copies) are DAG-aware now — types legitimately share sub-graphs, and a tree
walk over them is exponential. The prelude is analyzed ONCE per process and
copied per project (the suite paid it per test), and the type-var id supply
is process-wide so cached and fresh variables can never collide. Suite:
54s, 349 green.

### KNOWN OPEN: self-application regressed to red (4 tests)
Today's semantic changes surface ~318 diagnostics on the compiler's OWN
sources (the F# self-application gates): union-by-level shifted which
variable id survives a merge and id-keyed substitutions elsewhere now miss
in places the old direction happened to satisfy; the defaulting fix REPORTS
mismatches it previously looped on (`Ordered<string * string>` from sortBy
with tuple keys — tuple Ordered instances do not exist yet); and Types.fs
now contains `struct (Type * Type)` in generic args, which the F++ parser
cannot parse. The assignment unification is restricted to plain-identifier
targets (dot targets can resolve to setter shapes the dot machinery still
mistypes). These four tests fail FAST now — before the fixes they hung the
suite outright. The 4130-line acceptance file remains 0/0/0 and runs.

### Self-application back from 322 to green (3 of 4 gates)
The 300-diagnostic regression had ONE cause: making the type-var id supply
process-wide (a theory-driven "fix" during the perf hunt, never validated —
per-file inference relies on per-run id spaces). Reverted; the prelude cache
never needed it. The rest of the tail: `Ordered` on tuples is structural now
(the builtin instance demands orderedness componentwise), .NET's List<'a>
widens to seq, one comprehension and one peephole line rewritten into the
typeable subset. Parser/project/inference self-application: ZERO diagnostics
again. Still red: the LOWERING gate — 27 lint errors in the lowered core of
Infer/Lower/EmitWasm/Workspace, all from constructs added today; each is a
small lowering-imprecision hunt.

### Self-application fully green: the lowering gate closed
The last 28 lint errors came from three causes, not 28.

**Curried lambda parameters were collapsed into one tuple (16 sites).**
`fun i (f, k) -> ..` lowered to `fun _arg -> match _arg with (i, (f, k)) -> ..`:
`paramBinds` gives up on ALL binders as soon as ONE parameter is structured,
and the lambda case then tupled them. Every `List.mapi`/`iteri`/`foldBack`
with a destructuring parameter therefore had the wrong arity, which is
exactly what the lint reported (`int vs 'a * (string * string)`).
`paramBindsCurried` now lowers per parameter: simple ones stay binders,
structured ones destructure their own synthetic `_arg` inside the body, so
the arity survives. This is a real elaboration fix, not a source rewrite.

**The lint monomorphized top-level bindings (9 sites).** After checking a
`DLet` it stored the decl's instantiated type in `env`, so every later use in
the same file shared ONE monotype: `BuiltinCache.copyDict` unified with
`Dict<string, Definition>` at its first use and every other use of the nine
cached dicts failed. Uses of an already-checked top level now re-instantiate
its scheme (`generalized` set); recursive uses inside the decl's own body
stay monomorphic, as before.

**`dict.[k] <- v` lowers as an ARRAY index-set (2 sites).** The core IR has no
dict-index form, so the memo tables in `Types.InstantiateC` and
`Infer.substVars` demanded `int` keys. Rewritten into the subset as
`dictSet memo p r` — the Prelude call the rest of the compiler already uses.

All four self-application gates now pass at zero: parse, project, inference,
and lowering (283 decls, lint-clean). Acceptance unchanged: 0 diagnostics /
0 notes / 0 emit errors, and the emitted wasm still runs. Suite 353/353.

### The collections WORK: acceptance file runs, pinned as a test
The trap was four independent bugs, each hidden behind the last, all found
by bisecting the real file rather than growing repros:

- **Static creators were never a specialization demand.** The eager
  single-candidate path for `Type.Member` recorded the member site but no
  instantiation, so `HashSet.OfList` lowered to a bare `EVar` naming a
  layout-dependent template that stamping had already removed ("unbound
  variable OfList"). The parked overload path already did this; the eager
  one now does too.
- **Struct-tuple expressions were named too early.** `instName` ran at
  inference time, freezing a type variable that later unification linked
  away — so the clone's substitution missed it. They defer through
  `pendingRecords` now, exactly like struct-tuple patterns.
- **The stamper substituted whole names only.** A variable nested in a
  composed name (`StructTuple2$<bool.SetNode$<#42>>`) survived into the
  clone, which then named a record nobody declares; the emitter silently
  fell back to another record with an `Item1` field and read the WRONG
  slot. `substName` now substitutes every `#n` in the name.
- **A wildcard in `struct(_, n)` shifted the field indices.** Binders were
  collected from ident tokens, so `n` was read as `Item1`. Destructuring is
  positional now: one slot per element, empty for wildcards.
- **A downcast trapped on null.** `x :?> T` read the descriptor
  unguarded; null now casts to null and a non-object raises InvalidCast
  instead of trapping the module.

The smoke program (18 assertions over `OfList`/`Add`/`Remove`/`Contains`/
`IsSubsetOf`/`IntersectWith`/`Filter`/`Fold`/`Map`/`SetEquals`/`Overlaps`)
prints the right answers and exits 0; it is pinned as an Expecto test that
compiles the 4130-line reference file plus usage and diffs wasmtime's
output. Suite 354 green. Still parked: `HashMap [ (1, "a") ]` seq-ctor,
top-level `let x, y = ...` destructure.

### Next: stage-0/stage-1 bootstrap harness
The self-application gates prove the front end ACCEPTS its own sources; they
do not run the result. The next step is a harness that takes the
dotnet-built compiler and emits wasm for a growing prefix of its own files —
starting with the leaves that need no .NET interop (`Prelude`, `Tokens`,
`Tree`, `Lexer`), each file gated on "emits 0 errors AND the emitted module
instantiates". Files that need host services (file IO in `Workspace`,
`Project`) come last and need an import surface decided first. Full
bootstrap (stage-1 compiling stage-2) is NOT in scope until every file emits.

### The prelude is a real source file now
`stdlib/prelude.fpp` (1492 lines of actual F++, editor support and all),
embedded into Fpp.Compiler as a resource at build time; `Builtin.source`
reads the resource. Analyzed once per process (the cache), copied per
project. Precompiling to a serialized form stays unnecessary while the
one-time cost is ~250ms.

### Backlog: binary wasm emission
The backend emits .wat text — debuggable, and wasmtime takes it directly.
Browsers only take binary .wasm, so before F++ output meets the web either
a binary section-writer (LEB128 + type/func/code sections) or a wat2wasm
assembly step must land.

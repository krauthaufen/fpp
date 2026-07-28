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

### Stage 0 lands: the lexer compiles itself and runs
The harness exists and the first prefix is green. `stdlib/bootstrap.fpp` is
the F++ half of the bootstrap seam — the same surface `src/Fpp.Compiler/
Prelude.fs` gives .NET (Vec, Dict, the string and char helpers), written in
F++ over arrays: Vec is a doubling array, Dict an open-addressed index over
insertion-ordered entry arrays, so `dictPairs` is deterministic. The prefix
substitutes it for `Prelude.fs` and adds `Tokens.fs`, `Tree.fs`, `Lexer.fs`;
all four emit with zero errors and the module runs under wasmtime.

Emission alone is a WEAK gate — dead-code elimination drops what nobody
calls, so an unused file "passes" having emitted almost nothing. The gate
that counts is a driver: `tests/bootstrap/lexdrive.fpp` lexes a source
string with the emitted lexer and prints kinds, texts, offsets, trivia
counts and the round-trip witness; the Expecto test compares that output
against the SAME program run by the dotnet-hosted lexer. They agree.
`tests/bootstrap/preludedrive.fpp` does the same for the seam itself.
`tests/bootstrap/frontier.fsx` grows the prefix file by file and reports
where it stops.

Four gaps closed on the way:
- **`a.[i] <- v` never constrained the element type.** Assignment only
  unified through a plain variable target, deliberately, because a dot
  target can be a member setter whose shape would poison the value's type.
  An ARRAY index is not that case: the target type IS the element type. The
  index inference now marks array-receiver sites, and assignment ties them.
  Without it every generic container written in F++ (`v.Items.[i] <- x`)
  emitted "array write needs a statically known element type".
- **No string slice.** `String.sub` is a primitive (`$strsub`, one
  `array.copy`-style loop) rather than a library function, because building
  a slice out of concatenation is quadratic and the lexer lives on it.
- **No `Set`.** The prelude has one now: comparison-ordered like F#'s, but a
  sorted array with binary-search membership instead of a tree — persistent
  either way, `add`/`remove` copy. The compiler only ever asks it for
  `ofList` and `contains`.
- **List comprehensions do not lower** (7 sites compiler-wide). `Tree.fs`'s
  `Red.children` was rewritten into the explicit accumulation it desugars
  to; the remaining six are in `Link.fs` and `EmitWasm.fs`. Lowering
  comprehensions properly — `for`/`if`/`yield` into a Vec accumulation — is
  the better fix and is still open.

**The parser stage needs closures with CELLS.** `tests/bootstrap/
parsedrive.fpp` (parses a source string with the emitted parser, prints a
paren/dot shape fingerprint of the tree, the round-trip witness and the
diagnostics, and does it again for deliberately broken input) does not emit
yet — it does now. It was 102 errors from exactly two causes, and both are
fixed.

- ~~**Mutually recursive functions.**~~ FIXED, and it was never only about
  locals: `let rec even ... and odd ...` was broken at the TOP level too, so
  the theory that globals resolve by name regardless of order was wrong.
  `and` binds a GROUP and nothing put the group in scope, so a forward
  reference resolved to nothing — silently, because an unresolved name is not
  a diagnostic; it only surfaced as an `EUnknown` at emission. Three parts:
  `andGroupBindings` in `Resolve` now covers `let` groups as well as the
  `type ... and ...` groups it already handled, and `walkLet` counts `and` as
  recursive, so every member's body sees every member's name; `Lower` counts
  `and` as recursive too, so each member reaches the emitter as a recursive
  binding; and the emitter ties the knot for a GROUP, giving each member a
  freshly allocated marker (distinct identity under `ref.eq`), building every
  closure over those markers, then replacing each marker with the closure it
  stood for via `$patchmark` — the generalization of the single-binding
  `$selfmark`/`$patchself` trick.
- ~~**`let x = e in body` scoping.**~~ FIXED, found while closing the group
  work. Everything after `=` is a child of the same node, but the two halves
  are not in the same scope: the `in` body sees the binding (and not its
  parameters), the right-hand side does not. `walkLet` walked them alike, so
  five uses in `Parser.fs` — every `(let n = s.Peek 1 in n.Kind = ...)` —
  resolved to nothing.
- ~~**Local let-polymorphism was monomorphized in the lint.**~~ FIXED. The
  same bug that was fixed for TOP-LEVEL bindings, one scope down: `ELet`
  stored the binding's monotype and discarded its scheme, so a local generic
  helper used at two types was pinned by its first use. It stayed invisible
  while the group fix was missing — `local (fun () -> walkLet env n)` in
  `Resolve` had an unresolved `walkLet`, so that use demanded nothing of
  `local`'s `'a`; the moment forward references resolved, `local` was used at
  both `Env` and `unit` and the lowered core stopped type-checking. A
  ten-line repro (`let apply (g : unit -> 'a) : 'a = g ()` applied at `int`
  and `string`) reproduces it away from the compiler entirely. Inference was
  never wrong here — only the core the lint checks.
- ~~**A captured mutable local.**~~ FIXED. Mutable locals are wasm locals and
  closure conversion copies free variables BY VALUE, so a closure used to
  write to a copy ("assignment to unknown acc"). A local that is let-bound,
  assigned, and mentioned inside a lambda is now a one-field `$cell`:
  allocated in the frame, read and written through `struct.get`/`struct.set`,
  and captured AS the cell, so the frame and every closure over it write the
  same slot. The decision is per binding, so all uses agree; a top-level
  function's own parameter lambdas do not count as a capture boundary (its
  body compiles into a wasm function whose locals really are locals), which
  is what keeps unboxed float loops unboxed. Pinned by four tests: a counter
  that outlives its frame, two closures over one cell, a lambda handed to
  `List.iter`, and a cell-count baseline for the uncaptured case.

Minimal repros for both, ready to grow into tests, are 12 lines each:
`let rec even k = if k = 0 then true else odd (k - 1) and odd k = ...` and
`let counter n = let mutable acc = 0 in let bump k = acc <- acc + k in ...`.

The parser is now gated the way the lexer is: `tests/bootstrap/parsedrive.fpp`
parses a source string with the EMITTED parser and prints the diagnostics, a
paren/dot shape fingerprint of the tree, the round-trip witness and node
counts, then does it all again for deliberately broken input; the Expecto test
compares that against the same program run by the hosted parser. They agree,
byte for byte, on both inputs. `Parser.fs` has joined the gated prefix.

**Next up, `Analysis/Resolve.fs`.** It emits (file 6 of 20), and
`tests/bootstrap/resolvedrive.fpp` is written and parses — it runs the emitted
resolver over a program containing the shapes this stage fixed (an `and` group
referencing forwards and backwards, a shadowed name, a one-line `let ... in`)
and prints the definitions and resolutions. It is NOT gated yet: emission
reports `unbound variable resolve`, i.e. the use resolved to a definition the
emitter has no top-level slot for. A qualified cross-file call through a
namespace prefix is fine in isolation (`Thing.compute` from another file emits
and runs), so the suspect is narrower: `Fpp.Analysis.Resolve.resolve` is a
VALUE whose name matches its own MODULE, and module-versus-value spines are
exactly where that has bitten before. One minimized probe should settle it.

Layout note found while writing that driver: deeply nested multi-line
arguments (`print (String.concat " "` with the list on following lines) hit the
v0 offside rule and parse as top-level junk. Flat helper bindings work. The
driver is written in that flat style; whether the offside rule should accept
the nested form is a separate question.

### The reference-identity seam, and the frontier at 13 files
`Analysis` used to reach past the seam straight into
`System.Collections.Generic`: `Types.fs` alone had a reference comparer
feeding three `HashSet<Type>` visited sets, a pair comparer for `unifySeen`
and a `Dictionary<Type, Type>` memo; `Infer.fs` spelled the same memo
`HashIdentity.Reference`; `Format.fs` used `List<Seg>` and a
`StringBuilder`. Eleven sites, now all behind `RefSet` / `RefPairSet` /
`RefMap`, name-for-name in both halves.

These are not an optimization. A pruned type is a GRAPH — a variable solved
once and read many times is one node on many paths — so a walker without a
visited set is exponential, and IDENTITY is what it must key on: two
structurally equal types that are different objects are different nodes, and
hashing a cyclic one structurally would not terminate.

**Hash shallowly, compare by identity.** The .NET half builds on
`Object.ReferenceEquals`, the F++ half on the `refEq` primitive over an
open-addressed table; the hash is the CALLER's, and reads only immutable
fields — a variable's id, a constructor's name and arity. Stability is the
constraint that forces this: `unifySeen` rewrites `Link` while its visited
set is live, and a hash that looked at a link would strand its entry in the
wrong bucket. Any hash consistent with identity is otherwise legal, since
identity-equal values are the same object. That is what lets this work
without an identity-hash primitive at all — wasm-GC exposes no address, and
the emitter's identity numbers live in a hidden field on CLASS instances
that a DU value does not have.

`Format.fs` needed no new machinery: `Vec<Seg>`, and a `Vec<string>` joined
once with `String.concat ""` where a builder would have been (repeated `+`
is quadratic).

Gated by `tests/bootstrap/refdrive.fpp`: the same program — distinct but
structurally equal keys, a mutation of a non-hashed field, 40 entries in one
bucket to force rehashing, update semantics, pair order — run by BOTH halves
and diffed.

Three gaps fell out on the way:

- **`fst`/`snd` and `List.distinctBy`/`distinct` were missing** from the F++
  prelude. Added; `distinctBy` keeps F#'s first-occurrence-wins order.
- **A for-in whose source type was still unknown when the loop was typed**
  recorded no marker at all, so lowering had nothing to walk. Late sources
  are now remembered and promoted at finalization — but ONLY if they turn
  out to be a list or an array, because the enumerator protocol needs member
  accesses parked DURING the walk, and promoting one of those would emit an
  array walk over a class.
- **A QUALIFIED case pattern was named by its FIRST segment.**
  `Classes.Improve inst` typed off the MODULE name `Classes`, so the
  constructor was never instantiated, the payload binder `inst` had no type,
  and everything read out of it stayed unknown — which is why
  `for ctx in inst.Context` could not tell it was walking a list. The parser
  was innocent (it builds the right `AppPat`); resolution recorded the use
  on the prefix, and lowering read the name from the prefix too. All three
  layers now take the LAST segment, which is where the case actually is.

Then two more, and the frontier reached 14:

- **`for c in s` over a string** now walks by index like an array. Inference
  records the `"$str"` sentinel the emitter already reads for a string
  receiver, so the existing array lowering does the rest — no backend
  change.
- **`System.Text.StringBuilder` in `Serialize.fs` and `Link.fs`** joined the
  other builders behind the seam as a `Vec<string>` concatenated once.

### List comprehensions, arrow form
`[ for x in src -> e ]` lowers now. The loop itself takes the ORDINARY path
— range, cons walk, indexed array or enumerator protocol, whichever applies
— and the only change is that its body conses onto an accumulator instead of
running for effect; the list is built by prepending and reversed once at the
end. The sink is consumed on entry to the body, so a loop NESTED inside the
yielded expression is an ordinary loop again (pinned by a test: the inner
loop must accumulate nothing).

### The statement form, and a `yield` that escaped its `if`
`[ for x in xs do ... yield e ... ]` lowers now too, including `yield!`.
The sink turned out not to need a syntax-directed transformation at all: it
is DYNAMIC. `compAcc` is set while the comprehension's loop is lowered by
the ordinary rules, and the interception happens at `yield` itself, wherever
the lowering reaches it — inside an `if`, a `match` arm, a nested loop, a
`let` continuation. Those constructs already lower their sub-expressions the
normal way, so they carry the sink without knowing about it. `yield!` walks
the spliced list and pushes each element, which keeps the single reversal at
the end correct.

Refused deliberately: a comprehension whose body contains NO explicit yield.
F# would read a bare non-unit expression as an implicit yield; lowering one
as a statement would silently produce `[]`, so it stays a note.

Finding it needed a PARSER fix first. `yield` was a block item but not an
expression start, so `if cond then yield y` parsed with an EMPTY then-branch
and the yield became a SIBLING of the loop — which would have yielded
unconditionally. `then`, `else` and match-arm bodies accept `yield`/`return`
as a body start now. That is a silent-wrongness bug that existed
independently of comprehensions.

`Option` (map, bind, filter, forall, exists, iter, isSome, isNone,
defaultValue, toList) and `id` joined the prelude on the same push — 45
`Option.map` and 27 `Option.bind` sites across the compiler were waiting on
them.

### Where the frontier stands, and the next decision
14 of 20 files: `bootstrap`, `Tokens`, `Lexer`, `Tree`, `Parser`, `Resolve`,
`Types`, `Format`, `Classes`, `Infer`, `Core`, `Lower`, `Lint`, `Serialize`.

`Core/Link.fs` is the wall, and past the comprehension it is not a bug but a
DECISION. The remaining files call the .NET string API directly — 88 sites:
26 in `Link.fs`, 55 in `EmitWasm.fs`, 6 in `Project.fs`, 1 in `Workspace.fs`
— `Substring`, `StartsWith`, `EndsWith`, `IndexOf`, `Contains`, `Replace`,
`Split`, `Trim`. F++ models a string as a primitive `$str` with `.Length`
and indexing through the `"$str"` sentinel and no members beyond that, so
every one of those calls parks unresolved. (That is also why `Link.fs` still
reports a for-in: `for c in inner` where `inner = name.Substring ...` — the
source type never becomes known, so the loop cannot be walked.)

Two ways, and they should not be mixed:

1. **Give F++ string members.** `name.StartsWith p` keeps working verbatim,
   at the cost of teaching the type system and the emitter a member surface
   on a primitive.
2. **Route the 88 sites through the seam** as ordinary functions
   (`startsWith s p`, `indexOfFrom s p i`, …) added to `Prelude.fs` and
   `stdlib/bootstrap.fpp` together. Mechanical, in house style, and it makes
   the seam explicit — but it is 88 edits, and each one can slip a semantic
   (`IndexOf` returning -1, `Split` on empty, `Replace` overlapping).

**Decided: (1), builtin string members.** The self-hosting goal is F#
compatibility, and `s.Substring` IS the F# surface; rewriting 88 idiomatic
sites away from it moves the sources in the wrong direction, so the fix
belongs in the compiler. The surface was derived from the survey, not
guessed: `Substring` (1 and 2 argument), `StartsWith`, `EndsWith`,
`Contains`, `IndexOf` (char, string, string-from-index), `LastIndexOf`,
`Split` (char), `Replace`, `Trim`, `TrimEnd`. They register in Infer's
`fields` table under `"string.X"` — the ordinal mechanism carries the
overloads, so `Substring#2` is chosen by the shape the use site was
constrained to, exactly like a user-declared overload set — and emit through
`$str` primitives (`$strFind`, `$strStarts`, `$strEnds`, `$strSplitChar`,
`$strReplace`, `$strTrim`, `$strTrimEndChars`, alongside the existing
`$strsub`/`$strcat`/`$strcmp`).

Pinned by oracle tests against dotnet fsi on exactly the cases where a
hand-rolled implementation drifts: empty needles (found at 0), missing ones
(-1), `Split` keeping trailing empty pieces, and `Replace` not overlapping
itself. The set is CLOSED and that is a divergence — recorded in
DIVERGENCES.md, along with the fact that general extension members on
builtins remain an open language feature.

Two smaller things fell out of the same push:

- A late loop source that resolves to a STRING is promoted like a list or an
  array now (`for c in name.Substring ...`); a string can never have been
  the enumerator protocol, so the sentinel is safe to add after the walk.
- **Array PATTERNS do not exist.** `[| a; b; c |]` in pattern position
  parses as a list pattern and types as a list, so `Link.fs`'s one use was
  rewritten into a length test plus indexing. Typing it as an array without
  a matching IR node would silently lower a list match against an array
  value, so the honest fix is a new `Pat` case — worth doing when a second
  site wants it.

### The frontier reaches 17 of 20, and stops on the stamper
`Link`, `Plugins` and `EmitWasm` — the whole backend — emit now. Four more
gaps closed on the way:

- **`for _ in 1 .. n`** — a wildcard binder in a range loop. The loop still
  needs a counter, so the binder gets a synthetic variable; before, the
  range branch only matched a named binder and the loop fell through to "no
  GetEnumerator". Four sites in `EmitWasm` alone.
- **`box`/`unbox`** are type-level here: every value is already a reference,
  so both lower to their argument. `obj` was already the top type in the
  subtyping check; it is a real type in the prelude now.
- **The core lint had to learn `obj`.** Once `box` typed properly, the lint
  read `string` against `obj` as a mismatch — the unifier has no subtyping.
  Allowed at that one place rather than weakening unification.
- **`Option`** (map, bind, filter, forall, exists, iter, isSome, isNone,
  defaultValue, toList) and **`id`** joined the prelude.

**Fixed: tuple type arguments specialize as canon.** A tuple is a uniform
reference — the conclusion arrays already reached, where a tuple element
makes the array a plain `$ref` array whatever it holds — so every tuple
instantiation of a generic SHARES one body, and one name is what says so.
`typeConName` and the instantiation-site naming give `TTuple` (and `TFun`)
the name `$ref`; the stamper then classifies them like any other reference
type. `Dict<string * string, _>` and `Dict<int * bool, _>` compile to the
same code and stay independent tables.

**Fixed: an instantiation the stamper cannot perform is now REPORTED.** The
silence had a specific cause. Errors were suppressed inside a *template* —
the unstamped body of a layout-dependent generic — because a symbolic demand
there legitimately resolves per clone. But a class member that touches such
a field BECOMES a template, so its failure was suppressed too, and since a
template is never emitted, the member simply vanished: the module linked and
every use was unbound. The rule is finer now. A demand carrying a `#id`
resolves in a clone and stays suppressed in a template; a demand with NO
NAME can never be resolved by substitution, so it is an error wherever it
occurs. Both paths — top level and class field — are pinned by tests, the
class-field one guarding a MISSING function rather than a wrong answer.

(Since every `Type` case now names itself, the nameless path is unreachable
from source today. It stays as the rule that keeps it that way: the next
type form that forgets to name itself gets an error instead of a hole.)

**`obj.Equals (a, b)`** joins `ReferenceEquals` as an intercepted static: it
is .NET's structural comparison, which is what `=` already means here —
including on arrays, where both compare by reference.

With those, `Query.fs` and `Project.fs` emit, and
`tests/bootstrap/querydrive.fpp` is wired into the suite: the emitted query
engine memoizes, invalidates on edit and cuts off early, agreeing with the
hosted engine run over the same script. **The frontier is 19 of 20.**

**Superseded — the original diagnosis, kept for the record:** A generic
function cannot be specialized at a TUPLE type argument. Eight lines:

    let table : Dict<string * string, obj> = dictNew ()
    let a = dictSet table ("s", "a") (box 1)

gives "cannot specialize 'dictNew': element layout is not statically known
here". `Db` holds exactly that — `Dict<QueryKey, Entry>` with
`QueryKey = string * string` — so the query engine cannot be stamped.

Two things to fix, and the second is the worse one:

1. A tuple has no static layout name, so it cannot drive specialization.
   Arrays already solved this: a tuple element is a UNIFORM reference and
   the array is `$ref` whatever it holds. The same answer should work for a
   type argument — stamp one shared copy for all tuple instantiations —
   but it is a stamper design decision, not a patch.
2. **Inside a CLASS the same failure is silent.** At top level it reports
   the three errors above; as a class field it emits nothing at all and the
   class's members simply vanish ("unbound variable Db", "unbound variable
   SetInput"). A specialization that cannot be done must say so wherever it
   occurs — a missing function that nobody warned about is how a
   self-hosted compiler miscompiles quietly.

`tests/bootstrap/querydrive.fpp` is written and waiting: it drives inputs,
memoized queries, dependency tracking, invalidation and early cutoff through
the emitted engine. It is not wired into the suite yet because the file does
not emit.

### The host-import surface (APPROVED, then implemented)
Decided: **synchronous, process-global, result-style.**

- Four externs, module-level wasm imports: `readText`, `exists`, `listDir`,
  `canonicalize`. That is everything `Workspace` and `Project` actually
  need — no writing, no process, no network — and it should stay that small.
- `readText` returns `option<string>`. **No exceptions cross the FFI
  boundary**: a missing file is `None` and the CALLER reports it, which
  keeps the error surface in the compiler where diagnostics already live.
- Process-global. wasm imports are module-scoped anyway, and `Workspace`
  state stays inside the module regardless.
- **Not async.** A browser host satisfies the imports from a preloaded
  in-memory map; making the compiler async would infect every call path to
  accommodate a host that can preload.

The mechanism is the existing one: `extern` lowers to an import from module
`env`, which `FfiTests` already covers end to end with wasmtime supplying
the implementation as a preload module.

**Implemented.** The raw imports are over STRINGS ONLY — `readTextRaw`
answers null for a missing file, `listDirRaw` a newline-separated list — so
that any host can satisfy them without building F++ data structures. The
wrapping into `option` and `string[]` happens in the SEAM, on both sides, so
the compiler-facing API is `hostReadText : string -> string option`,
`hostExists`, `hostListDir : string -> string[]`, `hostCanonicalize`.

Path arithmetic — combine, directory, file name, stem — is PURE and lives in
the seam as ordinary functions. It needs no host and does not belong in the
import surface, which is how the surface stays at four.

`Project.fs` and `Workspace.fs` are rewritten onto it and both emit;
`Project.read` on a missing file now returns a LoadResult carrying
"cannot read project file", which is the error surface staying in the
compiler exactly as decided. Pinned by `FfiTests`: the wasm side declares
all four imports against module `env`, and the .NET side — the runnable
half — is asserted against real files, including that a missing one is
`None` and a missing directory lists empty.

Two more things fell out on the way: `List.truncate` (the prelude only had
the `Seq` one, and `errs |> List.truncate 3` is a for-in source), and
`lazy`/`.Force ()` in `BuiltinCache`, replaced by an explicit memo cell —
F#'s `lazy` adds thread safety a single-threaded cache does not need, and it
is not in the subset.

### Or-patterns that bind, and what `Workspace.fs` still needs
Removing the last lowering note let emission run over all 20 files for the
first time, and it reported 153 errors that the note had been MASKING. The
largest single cause was one bug: **an or-pattern's alternatives each bound
their own variable.** `| A n | B n -> n` wrote two different `n` identities,
and the body — which resolves to the LAST alternative, since each shadows
the previous — read a local the matching alternative never wrote. The
alternatives are aligned by NAME now, onto the last one's identity. By name
and not by position, because the compiler's own use swaps sides:
`| TVar v, other | other, TVar v ->`. Both shapes are oracle-tested against
F#. That alone took 153 errors to 109.

**Read the census correctly: these are not `Workspace.fs`'s gaps.** The
errors are attributed to functions in `Resolve`, `Lower`, `Infer` and
`Link` — files that pass on their own. They pass because dead-code
elimination drops what nothing calls, and `Workspace` is the file that
finally CALLS everything. So the 109 are the whole compiler's remaining
gaps becoming reachable at once, and looking for them inside `Workspace.fs`
will find nothing. Expect the same effect at every later stage: the moment a
driver exercises a path, its gaps appear.

### The long tail closes, and one decision is left
Everything in the census above is done except the last item. What each turned
out to be:

- **`Map` is a TREE, and that is what made `Map.empty` work.** The census
  called for a sorted array like `Set`'s, but `Resolve.fs` writes
  `let mutable env : Env = Map.empty` — a generic VALUE, which the full value
  restriction only generalizes for a SYNTACTIC value. A record literal over
  two empty arrays is not one; a nullary DU case is. So the prelude's Map is
  the AVL tree `stdlib/mapext.fpp` already exercises, ported over, with
  `empty = MapEmpty`. The cost argument agrees: the resolver rebuilds the
  environment by `add` on the way down every scope, and a copying insert is
  quadratic over a file where a tree insert shares all but the spine.
- **`option.IsSome`/`IsNone`/`Value` are BUILTIN members**, registered in
  Infer's `fields` table beside the string ones and lowered to the match they
  mean. Declaring them on the prelude's `Option` DU also works and reads
  better — but a member on a generic DU is stamped per instantiation, and
  `option` is instantiated at nearly every type in the compiler. These three
  are properties of the TAG, identical at every element type, so a stamp per
  type is pure waste. `Value` was not cosmetic either way:
  `(dictTryFind d k).Value` had been resolving to *`KeyValuePair`'s* `Value`
  slot, reading the wrong field of the wrong type. Silent, and now correct.
- **The small gaps**: `char` (one entry in each of the three conversion
  lists — Infer's kind capture, Infer's typing, Lower's dispatch — since a
  char IS its code point and the emitter's generic conversion case already
  handles the rest), `defaultArg`, `List.take`, `List.tryFindIndex` and
  `findIndex`. `dictRemove` and `vecToArray` joined BOTH halves of the seam;
  the F++ `dictRemove` shifts the survivors down and rebuilds the index
  rather than leaving a tombstone, because `dictSlot` probes until it finds
  an empty slot and `dictPairs` order is what makes emission reproducible.
  `System.Char.IsDigit` became the seam's own `isDigit`, `Link.substName`'s
  StringBuilder became a `Vec<string>` and a join, and `Project.fs`'s
  `IndexOfAny` became two `IndexOf` calls.
- **The or-pattern bug was in EMISSION, not in the alignment.** Lowering was
  already correct — the alternatives shared one identity per name. But the
  emitter expanded a `POr` only when it sat at the TOP of a case pattern, so
  `(EVar (bv, _) | EVarI (bv, _, _)), [ pa ]` — an alternative nested inside
  a TUPLE — reached `compilePat`'s `| POr _ -> ()`, which bound nothing and
  tested nothing. Hence "unbound variable bv" and a cast trap at runtime.
  `Core.expandOr` now takes the product over positions at any depth, and the
  `compilePat` no-op is an error, so the next missed shape is loud instead of
  silent.
- **The nameless array read was a late-typing shape**, exactly as suspected
  of `.IsSome`: `(s.Split ':').[0]` indexes the result of a PARKED dot, so
  the receiver was still a variable when the walk reached the index site and
  nothing was recorded. Index sites park too now, and are retried after the
  dot fixpoint — which also ties the read's result to the element type
  instead of leaving it free.
- **`[ a .. b ]` as a value** lowers to a downward cons walk, so nothing has
  to be reversed, with both ends bound first so each is evaluated once.

Two things fell out that are worth writing down:

- **`Ordered` has no instance at a TUPLE type.** `List.sortBy (fun d ->
  d.Line, d.Col)` in `Workspace.fs` reaches emission as
  `$class:Ordered:compare:$ref` and finds nothing, because tuples canon-name
  to `$ref` and no instance names that. Inference ACCEPTS the constraint, so
  the gap only shows at emission. The site is spelled out with `sortWith`
  instead; giving `$ref` an `Ordered` instance would make every reference
  type comparable, which is a language decision and not a patch.
- **An unused prelude global is still emitted.** `Map.empty` is the first
  top-level VALUE the prelude has ever had, and it costs every program one
  global plus `$init0` even when nothing mentions `Map`. Dead-code
  elimination drops unused prelude FUNCTIONS but not this. Small, but it
  moves the emitted bytes of every program, which matters to the fixpoint.

### The next wall: the compiler has never actually emitted itself
Fixing the census tail revealed that every previous measurement of "the
20-file emit" was measuring an INCOMPLETE program. Both the 109-error and the
49-error censuses contain `unbound variable emit`, `unbound variable infer`,
`unbound variable builtinInstanceWrappers` and `unbound variable
instanceFunctions` — the whole backend and the whole inference engine were
ABSENT from the module. The output was ~8.2k lines of wat for an 18k-line
compiler, which is the same tell.

So the numbers to carry forward are not what they looked like:

| state | errors | time | peak RSS | wat |
|---|---|---|---|---|
| before this milestone | 109 | 115s | 0.62 GB | 8245 |
| tail fixed, `IsSome` still failing | 49 | 115s | 0.62 GB | 8342 |
| `IsSome` resolving | ? | >30 min, killed | ~29.9 GB, twice | — |

The moment `IsSome` resolves, `infer` and `emit` become reachable for the
first time, and monomorphizing them does not fit. It plateaus at ~29.9 GB and
makes no further progress; two independent runs stopped at the same figure.

**This is not about how the option members are implemented.** DU members and
builtin members blow up identically, because the cause is REACHABILITY, not
the members: they were simply the last thing holding the backend out of the
module.

**It is ONE function, and it is `EmitWasm.emit` — the emitter emitting
itself.** Instrumenting the pipeline localizes it exactly:

| phase | cost |
|---|---|
| lowering all 20 files | 2.4s, 0.36 GB |
| `monomorphizeWith` + `stampRecords` + `deadCodeEliminate` | 0.1s, no growth |
| emitting functions 1..216 (~51k core nodes) | 0.4s, 0.42 GB |
| emitting function 217, `emit` (15,099 nodes) | >15 min, ~30 GB, no result |

So the cost is superlinear in a SINGLE function's size by a factor no
quadratic term explains: 216 functions totalling 51k nodes cost 0.4s, and one
function of 15k nodes costs more than fifteen minutes. `emit` is the largest
binding in the compiler (23% of its 66,282 core nodes); `infer` at 12,302 and
`lower` at 10,157 are next, and they emit fine, so the cliff sits between
10k and 15k nodes.

Three suspects have been TESTED AND ELIMINATED, which is worth recording so
nobody pays for them twice:

- **The stamper is not involved.** Its work queue holds 184 entries and the
  longest instantiation name is 17 characters; the whole of monomorphization
  runs in 0.1s. This was the first theory and it was wrong.
- **`expandOr` is not involved.** Instrumented to report any match whose case
  count grows by more than 8 under or-expansion: it never fires, anywhere in
  the compiler.
- **Memoizing `kindOf` does not fix it.** `kindOf` recurses into both arms of
  an `EIf`, which looked like the exponential; caching it on reference
  identity changes nothing.

What remains is the cost model of `compileExpr` itself — something in it
walks or emits a subexpression more than once per node. That is a backend
question, and it should be answered before any more emission gaps are
chased: the remaining errors are a short list, and closing them changes
nothing if the result cannot be built.

**What is also left: `Builtin.source`.** `Workspace.fs` reads `stdlib/prelude.fpp`
out of the assembly with `GetManifestResourceStream`, and a wasm module has
no such thing. This is the one remaining item that touches the APPROVED
four-function host-import surface, so it is a decision and not a patch: a
fifth extern, a seam function layered over `hostReadText` (which needs the
compiler to learn where stdlib lives), or a generated string constant in
`stdlib/bootstrap.fpp` — the direct analogue of what the .NET half already
does, and the only one that keeps a browser host from needing a filesystem.

### A note on the weak gate, since it has now bitten three times
"File N emits" has meant three different things at three different moments,
and the difference matters more each time:

1. It LOWERS without notes — but emission never ran, because a lower note
   returns early. `Workspace.fs` sat here for a long time, and clearing its
   last note revealed 153 emission errors that had been masked.
2. It EMITS without errors — but dead-code elimination dropped most of it,
   because nothing calls it. `Parser.fs` and `Resolve.fs` both passed this
   way at stage 0 while emitting almost nothing.
3. A DRIVER runs it and its output matches the hosted compiler. Only this
   one is evidence.

The frontier script reports (1) and (2) and says so in its header; the
drivers in `tests/bootstrap` are the only (3). When the count of emitting
files goes up, check which kind of "emits" moved.

### Superseded design notes (the questions, and how they were answered)
The last two files need services no wasm module has: reading a file, listing
a directory, resolving a project path. This is deliberately NOT implemented
yet — the surface is a contract between the compiler and every host that
will ever run it (wasmtime, a browser, a build server), and it outlives any
one of them.

What the two files actually need, from reading them: read a file's text,
test existence, list a directory, and canonicalize a path. Nothing else —
no writing, no process, no network. That is a small surface, and it should
stay small.

The mechanism already exists and should be reused rather than invented:
`extern` lowers to a wasm import from module `env` (`FfiTests` covers it
end to end, with wasmtime supplying the implementation as a preload module).
So the design is a prelude module of externs — `hostReadFile : string ->
string`, `hostFileExists : string -> bool`, `hostListDir : string ->
string[]`, `hostFullPath : string -> string` — plus the .NET half of the
seam implementing them over `System.IO` so the dotnet-hosted compiler keeps
working unchanged.

Open questions that need answering BEFORE the first line is written, since
each changes the signatures: how a missing file is reported (an option, an
exception, or a sentinel — `Project.fs` currently leans on .NET exceptions);
whether the host surface is per-Workspace state or process-global; and
whether a browser host, which cannot do synchronous IO, forces the whole
surface to be async, which would reshape `Workspace` far beyond these four
functions. That last one is the reason to decide it deliberately.

### Next: stage-0/stage-1 bootstrap harness
The self-application gates prove the front end ACCEPTS its own sources; they
do not run the result. The next step is a harness that takes the
dotnet-built compiler and emits wasm for a growing prefix of its own files —
starting with the leaves that need no .NET interop (`Prelude`, `Tokens`,
`Tree`, `Lexer`), each file gated on "emits 0 errors AND the emitted module
instantiates". Files that need host services (file IO in `Workspace`,
`Project`) come last and need an import surface decided first. Full
bootstrap (stage-1 compiling stage-2) is NOT in scope until every file emits.

### Phase 2 harness: the fixpoint is wired, and what it is waiting on
The stage-0/stage-1 comparison is built and its plumbing is PROVEN; only
stage-1 itself is missing, and it is missing for one reason (below).

- `tests/bootstrap/fixpoint.fsx` — stage-0 emits both the expected answer
  (its own .wat for a corpus) and stage-1 (the 20 sources plus the driver).
  Stage-1 runs under wasmtime, compiles the same corpus, and its stdout must
  match byte for byte. A difference is bisected to the first differing byte,
  with its line, column, and the emitted function it falls inside.
  `... fixpoint.fsx stage0` stops after the expected answer, which costs
  seconds instead of the minutes and gigabytes stage-1 emission costs.
- `tests/bootstrap/compiledrive.fpp` — the driver. It carries the corpus
  PATHS, never the text: a driver holding the source could let the two
  stages compile different bytes and still agree, which is the weak gate
  this phase exists to close.
- `tests/bootstrap/fixcorpus.fpp` — a self-contained corpus (generics and
  stamping, a class with inheritance, a DU, a record, a struct tuple, a
  downcast, a comprehension). The drivers cannot serve as the default
  corpus: each is a FRAGMENT that only compiles beside the compiler's own
  sources, so using one would drag `Parser.fs` into every fixpoint run.
  Stage-0's answer for it is 151300 bytes.
- `tests/Fpp.Tests/FixpointTests.fs` — gated off by default and says so;
  `FPP_FIXPOINT=1` runs it. Gated because one run is a wasmtime execution of
  a module the size of the compiler, and that is measured before trusted.

**How the corpus reaches stage-1, measured rather than assumed.** A preload
module CAN satisfy the string-typed host imports: the imports are
`anyref -> anyref`, and the emitted `$str` is `(array (mut i8))` outside any
rec group, so a host declaring the same array type is structurally identical
and its arrays survive the `ref.cast`. Verified end to end — a generated host
serving a file map answers `hostReadText` for two files, `None` for a miss,
and a module reading a 1576-byte corpus through it echoes it back byte for
byte. `generateHost` in the harness is that generator, and it is what a
browser host looks like from the module's side.

**Blocked on `Builtin.source`.** Stage-1 is `Workspace` running in wasm, and
`Workspace` reads the prelude through `System.Reflection` — which is not in
the subset. The measurement above answers the open question: make it a SEAM
function. .NET keeps the embedded resource (the single self-contained binary
stays), the F++ half reads `prelude.fpp` through `hostReadText`, and the
harness already serves that file to stage-1 alongside the corpus. No new
import, no second copy of the prelude to drift.

**Also measured:** all 20 files LOWER with zero notes in 3.3s, so nothing is
parked at the front end. Whole-program emission of all 20 is the expensive
part — it had not finished after 8 minutes and ~6GB, which is the number
that decides whether the fixpoint test can ever come off its gate.

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

### The emission wall: four duplication bugs, not the stamper
Emitting all 20 compiler files used to take >15 min and ~30 GB and never
finish; the largest single function (`EmitWasm.emit`, 15k core nodes) was
where it died. Three separate investigations blamed monomorphization; the
stamper was innocent (184 queue entries, 0.1s, longest instantiation name 17
chars). The cost was in the emitter, as four independent duplications that
multiply through nesting:

- **Closure environments were cons chains.** Reading capture k emitted k
  nested `struct.get`s, so a function's text grew with captures squared.
  Environments are now ONE flat array with an indexed read. The two
  knot-tying runtime routines (`$patchself`, `$patchmark`) walked the same
  chain and were rewritten to scan the array — missing that broke every
  mutual-recursion test until the drivers caught it.
- **Or-pattern bodies were duplicated per alternative.** `| A n | B n -> e`
  emitted `e` once per alternative, compounding through nesting. Now each
  alternative gets a TEST block branching to one shared body. The binders
  must then write ONE slot: `compilePat` reuses a per-position slot map, or
  the matching alternative writes a local the body never reads (it printed
  garbage for the first alternative — exactly the silent-wrong-answer class).
- **Operator operands were thunks** (`fun () -> unwrapI32 (recur a)`) used up
  to 14 times per case, re-walking the subtree on each use: 13^depth.
- The general form: **twenty emitter cases mention `recur x` more than
  once**. Fixed at the root by memoizing emission per (locals-map, node,
  tail) on REFERENCE identity — structural hashing would re-walk the tree
  per lookup, and the locals map must be part of the key because a lambda
  body compiles against a fresh one.

Result: the whole compiler emits in ~2 min inside a 10 GB cap, 4.96 MB of
wat, 104 remaining emission errors (a real list, no longer a wall). Suite
402/402 with the lowering-lint gate green again.

### Compile speed: the peephole was 97% of the time
Whole-compiler compile was 110s; the phase split said parse 0.5s,
resolve+infer 1.8s, lower 0.4s, link+emit 108s. The cost was one line in
the peephole: every box/unbox cancellation rebuilt the ENTIRE module string
(`before + arg + after`) and then restarted its search from position zero,
so a multi-megabyte module with ~100k cancellations copied hundreds of
gigabytes. It now marks deletions during one left-to-right scan and compacts
once, looping only while a pass still finds something. 108s -> 1.2s, and the
whole compiler compiles in 3.8s. (The output differs from the old pass by
0.03%: both are fixpoints, reached in a different order — the pass is an
optimization, and the oracle tests agree on behaviour.)

### The prelude families completed, and four bugs behind them
`List`, `Array` and `Seq` now carry the same standard surface rather than the
slice the compiler happened to call: the two-collection family (iter2,
forall2, exists2, fold2), the position-aware combinators (indexed, scan,
pairwise), unfold, skip/take/truncate, windowed, chunkBySize,
distinct/distinctBy, except, sortDescending/sortByDescending.

Four compiler bugs surfaced while doing it:
- **`{ v with f = v }` was unimplemented.** It lowered as a plain record and
  silently dropped every field the literal did not mention. Now lowers to
  ERecordExt with a plain-record emission (copy each unmentioned slot), and
  the closure capture walk covers ERecordExt — its base and field values are
  ordinary uses, and skipping them lost captures.
- **Monomorphic functions were deleted as templates.** The rule removed any
  layout-dependent function, but only a GENERIC one is unreachable by
  construction (every use is stamped). A monomorphic one has no
  instantiation, so removing it deleted a function its callers still name:
  `infer`, `emit`, `builtinInstanceWrappers`, `instanceFunctions` all
  vanished. This also explains a false measurement — with those four gone,
  the errors INSIDE them were never counted, so "12 errors remaining" was
  really 154.
- **Nested arrays did not work at all.** Element naming unwrapped one level
  too far (`int[][]` emitted as a packed int array, trapping on the cast).
  Every arrKinds site now records the ARRAY type, so the reader unwraps
  exactly once and a nested array names its element `$ref`.
- **`a.[i].Length` collided with itself**: the index site and the length site
  keyed their element kind by the same first-token offset, so one silently
  overwrote the other. Length sites key by their member token.

`Builtin.source` moved behind the host seam (Prelude.preludeSource /
bootstrap's preludeSourceRaw), so Workspace.fs contains no .NET at all.

### Element kinds are keyed per SITE, not per expression head
Three bugs, one cause: an array operation recorded its element kind under the
first token of the expression, so operations sharing a head silently
overwrote each other. `a.[i].Length` (index site vs length site) and
`a.[i].[j]` (two index sites) both read the wrong layout and trapped. Length
sites key by their member token; index sites key by the first token of their
own bracket group — and ALSO under the head token, because a later
dot-resolution records the RESOLVED element type there while the early record
is still a type variable. Lowering prefers whichever name is not symbolic.
The bootstrap drivers caught the first attempt at this (bracket-only keying
lost the resolution and broke every generic container in the seam), which is
what those drivers are for.

### Host services as FAMILIES, and the count that follows
The .NET surface still reachable from compiler source was closed as coherent
seam families rather than call-by-call: **Builder** (four operations; .NET
aliases StringBuilder, F++ joins a chunk vector once — repeated `+` on a
growing string is the quadratic the peephole already taught us), **character
classes and ordinal comparison**, and **literal parsing** (integers in any
base, culture-independent floats, UTF-8 byte length, IEEE half bits). The
emitter's memo tables moved onto the seam's own RefMap with a shallow
constructor-tag hash. Function composition `>>` / `<<` became real operators
(typed like a pipe, lowered to `fun x -> g (f x)`), and `float16Bits` a
language primitive so source can name a half's BIT PATTERN — the runtime
representation already is those bits, so it is the identity.
Whole-compiler emission errors this session: 124 -> 66 -> 42 -> 33, with the
suite at 407/407 and the acceptance file 0/0/0 at every step.

### The remaining 18 (whole-compiler emission), individually
No longer families — each is its own puzzle. Measure with
scratchpad/dbg/phases.fsx (parse/infer/lower/emit split plus the error list):

- **13x `missing field X in Cached (asked for ?)`** — the record literal in
  Workspace's BuiltinCache.compute lowers with owner "?" , i.e. inference
  recorded no type for that literal, so every field is "missing". NOT
  reproducible with a small record in a nested/private module, with many
  fields, or multiline (all probed clean) — the real one has 14 fields whose
  types come from four different modules. Suspect the pendingRecords
  resolution not firing when the literal is the last expression of a function
  whose return type is only known through it.
- **2x `unbound variable dictNew`** (in infer, in emit) — a generic seam
  function losing its instantiation at a call site that passes it directly as
  an argument (`compilePatWith (dictNew ()) ...`).
- **`unknown field IsEmpty`** — `.IsEmpty` on a list. Wants the builtin-member
  treatment `string` already has (register under "list.X"), together with
  `.Head`/`.Tail`/`.Length` for the same reason.
- **`unknown field GetBytes`** — the last Encoding call; the seam has
  utf8Length, this needs the bytes themselves (utf8Bytes).
- **`$class:Ordered:compare:$ref`** — sorting at a tuple key. Still the open
  design question: giving `$ref` an Ordered instance would make every
  reference type comparable.

### The 13 were one bug, and not in Workspace.fs at all
`{ Classes.MPath = path; ... }` in `Infer.infer` — a record label QUALIFIED by
its owning module, which F# allows. Both Infer and Lower read the label as the
first `Ident` token of the field node, so they saw `Classes`, not `MPath`. The
literal then matched no record, lowered with owner `?`, and emission's
fallback ("pick the record owning the first known label") landed on `Cached`,
whose only shared field is `Classes` — hence thirteen "missing field X in
Cached" for a record literal in a different file entirely. The label is now the
last identifier BEFORE the `=` in both halves. 18 -> 5 errors.

### MILESTONE: the whole compiler emits with ZERO errors
All 20 files, 6.2 MB of wat, 4.5s, no emission errors — from 124 at the
start of the session. The last three:

- **Qualified record labels named the qualifier.** `{ Classes.MPath = p }`
  read its label as `Classes`, so no candidate record covered the label set
  and the literal's owner came out "?" — every field then read as missing.
  Taking the LAST identifier before the `=` fixed 13 errors at once. (Small
  reproductions all passed because they never wrote a qualified label.)
- **Ordering on tuples is structural.** `compare` at a uniform reference
  routes to the runtime's structural comparison, and $cmpv gained
  lexicographic tuple cases beside the equality ones it already generated.
  This is deliberately NOT `instance Ordered<$ref>`, which would make every
  reference type comparable.
- **"Template" now requires genericity.** A layout-dependent MONOMORPHIC
  function was treated as a specialization template, so symbolic type slots
  inside it were deferred to clones that never come, and the use kept naming
  a function specialization had removed (`dictNew`, twice). Outside a generic
  template an unobserved slot stamps uniformly: nothing will ever resolve it
  and nothing observes its layout.

Also this stretch: utf8Bytes in both halves, `list.IsEmpty/Length/Head/Tail`
as builtin members (lowered to the match they mean, like Option's), and
`byte`/`sbyte` conversions — which the seam's own UTF-8 encoder needed and
which the language did not have (byte 300 = 44, sbyte 200 = -56, as F#).

### Stage-1 RUNS: the compiler as wasm, and where it stops
The bootstrap now gets deep. In order, each wall cleared:

1. **Class `do` blocks were never type-checked.** `inferTypeDecl`'s member
   loop handled let/member/interface but had no case for a `do` block, so
   constructor code was never typed and its dot-accesses never resolved —
   `do db.SetInput ...` reached emission as an unknown field, and only once
   something made it reachable. Ten-line repro, one-line fix.
2. The harness predated the fifth host import: it now serves `preludeSourceRaw`
   — deliberately the SAME prelude text stage-0 compiled against, which is
   what makes the two stages comparable rather than merely similar.
3. **A pipe deadlock in the harness**, not the compiler: it drained stdout to
   the end before reading stderr, so stage-1 blocked once the stderr buffer
   filled (153s elapsed, 9s of CPU — the signature of a block, not slowness).
   Both pipes are read concurrently now.
4. wasmtime's default 1 MB wasm stack is not enough for a recursive-descent
   compiler; stage-1 runs with 64 MB.

**THE FIXPOINT CLOSES.** Stage-1 — the compiler compiled to wasm by stage-0 —
compiles the corpus and reproduces stage-0's answer BYTE FOR BYTE (156255
bytes). Everything below is the record of what stood in the way, because each
was a real compiler bug that the ordinary test suite could not see.

### Seven bugs between "stage-1 traps" and "stage-1 agrees"

Six were miscompilations, one was a divergence between the two halves of the
seam. Every one is now covered by a test in `EmitTests.fs`.

1. **A late-resolved `.Length` bound to a like-named record field.** The
   eager dot path answers `.Length` on an array itself; the PARKED path (used
   when the receiver only takes shape through another parked dot, as in
   `(s.Substring 1).Split ':'`) had no array case, so it fell through to a
   by-name field lookup and found whatever record in scope declares a
   `Length` — silently, since a field WAS found. `parts.Length` in the
   monomorphizer read field 5 of `Definition`. This was the cast failure.
2. **A store into a record field did not constrain its value.** Assignment
   only unified through variable and array-index targets; a dot target was
   excluded because it might be a setter. So `m.MapSlots <- Array.zeroCreate n`
   (`MapSlots : int[]`) built a UNIFORM array — nothing pinned the element
   type — and every later read cast it to `$parr_i` and trapped. Record
   fields are as safe as variables: their type IS the declared field type.
3. **`int s` was the identity.** The conversion table's catch-all is right
   for the int-shaped sources and wrong for a string, so the string itself
   reached an integer context. All of `int`/`int64`/`uint32`/`byte`/`sbyte`/
   `float`/`float32`/`float16`/`char` now parse, over new `$atoi`/`$atol`/
   `$atof` runtime helpers, and any remaining string source is REPORTED.
4. **A conversion's kind was unknown to `kindOf`**, so a nested one
   (`int64 s |> int`) took the identity path one level up and left an i64 box
   where an i32 was expected.
5. **`byte` and `sbyte` were missing from the operator suffix table**, so
   `<@byte` went looking for an instance member and found the GENERATED
   `compare` — whose body is that very comparison. Infinite recursion. Both
   are int-shaped and now spell the integer operator. A wrapper can also no
   longer resolve into itself, whatever the type.
6. **Every string literal was unescaped as if it were `"..."`.** A triple-
   quoted one kept two quotes at each end (and still processed backslashes);
   a verbatim one kept its doubled quotes. The emitted runtime blob grew a
   stray `""`.
7. **Source is BYTES, and .NET was reading it as UTF-8 text.** Char offsets
   and byte offsets diverge after the first non-ASCII character: fifteen em
   dashes in the prelude's own COMMENTS moved an object expression's
   generated name by twelve, and the two stages then disagreed about a type
   name. The .NET seam now reads source Latin-1 (the identity byte->char
   map), `utf8Length`/`utf8Bytes` became `byteLength`/`stringBytes` with no
   re-encoding at all, and the emitted runtime blob is ASCII — a literal in
   the compiler's own F# source is compiled by dotnet as UTF-16 and by F++ as
   bytes, so it must not contain anything where those differ.

Two guards were added along the way and stay, because both failure modes are
silent: `requestWrappers` reports an arity conflict instead of dropping it,
and emission reports two definitions that mangle to one wasm symbol instead
of producing a module the assembler rejects thousands of lines later.

### Ruled out during the hunt (do not re-chase)
- **Wrapper arity conflicts.** Now reported; none fires in the self-compile.
- **Wrapper self-consistency.** w0 builds `cons(a, env)` and w1 reads it
  back; the only producer of a `.w1` closure is w0.
- **Capture-env slot numbering.** `innerFree` assigns index i to freeList[i]
  and the flat array is built in the same order.
- **Knot-tying** was a real bug and IS fixed: `$patchself`/`$patchmark`
  scanned only the flat array, so a recursive function reached through a
  partial application kept its own marker. It was not this trap.

### SELF-HOSTING: the compiler compiles itself, byte for byte

    corpus: bootstrap.fpp, Tokens.fs, ... Workspace.fs, compiledrive.fpp
    stage-0 answer: 6238872 bytes
    stage-1:        6238872 bytes of wat
    FIXPOINT: stage-1 reproduces stage-0 byte for byte (6238872 bytes)

97 seconds, against ~2 seconds for the same job natively. Two bugs stood
between the single-file fixpoint and this one:

1. **Only the NAMED character escapes were decoded.** `'\000'` came out as
   the digit zero, so the compiler compiled its own lexer's end-of-input
   guard (`peek (pos + 1) <> '\000'`) into a test against '0' — and stage-1
   then rejected every char literal in its own sources, 473 errors deep. The
   emitter now decodes `\DDD`, `\xHH`, `\uXXXX`, `\UXXXXXXXX` and
   `\a \b \f \v`, with code points above ASCII encoded as UTF-8 bytes.
2. **`String.concat` folded left.** `acc <- acc + sep + x` copies the whole
   accumulator every step, so joining n chunks of total length L costs
   O(n*L). `sbText` is exactly that fold over the emitter's chunks, and the
   emitted module is six megabytes: the first full self-host ran 50 minutes
   without finishing. As a pairwise merge it is O(L log n) — the four-file
   probe went 248s -> 25s, and the whole compiler finished in 97s.
   `String.replicate`, `String.init` and `stringOfChars` had the same shape
   and were fixed with it.

The lesson worth keeping: the .NET half of the seam gets `StringBuilder` and
`Dictionary` from the host, so an O(n^2) stdlib routine in the F++ half is
invisible until the compiler runs on ITSELF. Native speed proves nothing
about the hosted build.

### Stage 3: the compiler as its own corpus
`dotnet fsi tests/bootstrap/fixpoint.fsx self` makes the corpus the COMPILER —
its twenty sources plus the driver, under the same served names stage-1 was
built from. Stage-0's answer for that corpus therefore IS stage-1's own text,
so the run asks one question: does the compiler, running as wasm, reproduce
itself byte for byte? That is self-hosting; the single-file corpus only ever
showed that the two stages agree on a program neither of them is.

Source names are SERVED names (basenames) on both sides now. A file's name
reaches the .wat through diagnostics and symbol prefixes, so naming a source
by absolute path in stage-1 and by basename in the host made the two stages
differ for no reason — and it made the emitted compiler depend on where the
checkout lives.

### Debug information for the emitted module (not started)
wasm carries debug info in CUSTOM SECTIONS, and there are three levels. The
`name` section is already effectively present — wat identifiers become
function names, which is why a wasmtime backtrace reads
`g773_4262_mapExpr.w1` rather than `<wasm function 812>`. Above that:

- **`sourceMappingURL`** — one string naming a JS-style `.map` file. Browsers
  show F++ source instead of wat. Every node already carries a byte offset,
  so the map is bookkeeping rather than new analysis; this is the cheap win,
  and it wants binary emission first.
- **DWARF in `.debug_*` sections** — line AND variable info, consumed by
  lldb and Chrome's C/C++ DevTools extension. Much heavier, and only worth it
  once someone actually needs to step through F++ in a debugger.

### Self-hosting speed: 97s -> 43s, and where the rest goes
Profiled with `perf` + wasmtime's `--profile=perfmap` (the in-process guest
profiler walks the whole stack per sample and made a 70s run take over ten
minutes — unusable on a deeply recursive compiler).

The first profile said the job was 42% GARBAGE COLLECTION —
`CopyingHeap::forward`, `scan_field`, `collect_increment`. Two fixes:

1. **The emitter's memo hashed on the constructor tag alone.** `RefMap` only
   requires a hash that is stable and reads immutable fields, and a tag
   satisfies that — but twenty-eight values across the tens of thousands of
   subexpressions in one function turned open addressing into a linear scan
   of a single cluster that grows with the function. `exprTag` now mixes in
   offsets, names (bounded — a string literal can be the whole runtime blob)
   and child arity. This helped the DOTNET build too: `RefMap` there is a
   HashSet with the same comparer, so both stages were paying it.
   `localsTag` stays constant on purpose — that dictionary IS mutated while
   it is a key, so a content hash would strand its entries.
2. **The bootstrap sizes the GC heap.** A compiler is a batch job: it
   allocates hard and keeps almost nothing, so the default heap collects
   constantly. One gigabyte up front took the wasm side 63s -> 36s and
   changes nothing about the answer.

    97s  ->  73s   (memo hash; stage-0's own emit got faster too)
    73s  ->  43s   (GC heap sizing)

After both, GC is 12% and nothing dominates. What is left, in order:

- **`strcat` 9.3%** — `compileExpr` returns STRINGS, so every parent
  reconcatenates its children's whole text. The fix is a rope or builder
  through the emitter rather than `string`, which touches every `recur a +
  "..."` site in EmitWasm.fs. Biggest single win available, biggest refactor.
- **`toi`/`ofi` 10.3%** — every integer is `anyref` in the emitted code, so
  it is tagged and untagged constantly. Neither allocates (i31 covers the
  range); this is pure call frequency. The emitter already carries unboxed
  `f64`/`f32`/`i64` through `sigKinds`/`kindOf` — extending that to `i32` is
  the natural next step and is a real project, not a peephole.
- `addv` 3.3%, `equal` 3.0%, `compareOrdinalAt` 2.8%, then a long tail.

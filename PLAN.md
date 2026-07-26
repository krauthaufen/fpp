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
emitter was run directly (`emitforce` in the scratch harness). It reports
**87 errors**, and the split matters: a minority are missing stdlib surface.
The rest are compiler gaps:

- [x] a TYPE and a MODULE may share a name — done. Types have their own
      namespace, a dotted spine that resolves qualified IS qualified, and a
      bare expression name prefers the type (a module is never a value).
      119 -> 87 errors.
- [ ] type tests and downcasts against BUILTIN collections: `:? array<'K>`,
      `:? list<'K>` need a runtime representation test, not a class id (12)
- [ ] MEMBER overloading (constructors are done; methods are not)
- [ ] the enumerator protocol so `for e in <seq>` lowers at all: `seq`/
      `IEnumerable`/`IEnumerator` as prelude interfaces, arrays and lists
      implementing them, `for-in` desugaring to GetEnumerator/MoveNext
- [ ] then the genuine stdlib: `Seq.*`, `sprintf`, `String.concat`,
      `Array.zeroCreate`, `KeyValuePair`

So: stdlib alone would NOT make this compile. It is roughly a 1:6 split in
favour of compiler work.

Two real bugs found by pushing on this file, both fixed:
- `open M` did not bring M's NESTED modules into scope, because an open was
  recorded as a bare name instead of being resolved relative to where it
  appears;
- a cast or type test named its target by the LAST identifier of the type,
  so `x :?> MapLeaf<'K, 'V>` tried to downcast to `V` (68 errors).

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
- a projection reduces by a concrete type or a constraint in scope, and
  never survives into a generalized signature; failures name the operator
  application, not the constraint chain
- instances are free-standing (Haskell-style); `static member (+)` is sugar
  for the homogeneous case
- one operator symbol maps to exactly one class
Open: `static member (+)` in member position needs parser support — the same
work serves user-defined operators and instance declarations.

### Numeric tower
- [x] int, int64, float, float32, uint32: literals, arithmetic, comparison,
      bitwise and shifts, conversions between them, packed struct fields,
      structural equality and hashing. Conversions dispatch on the type
      INFERENCE resolved, not the backend's kind analysis — the latter
      cannot see through a global.
- [ ] uint64, and the smaller widths (int8/16, byte). No demand yet.

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

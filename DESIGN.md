# F++ — Design

F# without .NET. A language keeping F#'s syntax and semantics — including the
full overload/module/static-member zoo, nominal OOP, and computation
expressions — compiled ahead-of-time to native and wasm with no JIT and no CLR,
the way OCaml is its own language. Extended with GADTs, higher-kinded types,
and typeclasses via static interface members. Tooling is first-class from day
one, not a retrofit.

Slug: `fpp`. Source extension: `.fpp` (plain `.fs` accepted for the shared
subset during bootstrap).

## What is kept from F# unchanged

### Shadowing (explicit requirement)

F#'s shadowing semantics survive **in full**. The name environment is
temporal: whatever entered scope last wins.

- `let` bindings shadow earlier bindings of the same name, always.
- `open` injects the opened module's exports into the environment *at that
  point* — shadowing earlier `let`s and earlier `open`s; later `let`s shadow
  the opened names in turn.
- When a (possibly qualified) reference like `A.B.Foo` has multiple
  candidates through different opens, the **last** `open` wins.
- Colliding modules/namespaces **merge** (explicit requirement): with
  `Foo.A.bar` and `Blubb.A.boing` both in scope via opens, `A.bar` and
  `A.boing` both resolve — the containers union their contents. Only when
  the *same full name* exists in both does last-open-wins apply.
  (Implementation: qualified lookup resolves each full path independently
  against every open, so merging is the natural behavior.)


- Syntax, offside rule, modules, `let` bindings, DUs, records, structs,
  pattern matching, active patterns.
- The whole overload / static member / extension member zoo. Overload
  resolution gets re-specced as a self-contained algorithm (today it is
  entangled with .NET metadata quirks: `op_Implicit`, `params`,
  optional/named args) but keeps the left-to-right type-directed flavor.
- Nominal OOP: classes, interfaces, inheritance, object expressions.
- Computation expressions, verbatim. They are pure syntactic lowering onto
  builder members and cost nothing. With HKT a generic `monad<'m>` builder
  falls out for free, but the ad-hoc mechanism (CustomOperation,
  MergeSources, Run/Delay/Quote) stays the primitive.

## What is removed

- The CLR: no JIT, no reflection, no `System.*`. Own stdlib + C FFI only.
- Every semantic that silently assumes the runtime — reified `typeof`,
  `System.Object` identity/hashing, CLR exceptions model, tasks — gets an
  explicit keep/redefine/drop verdict in the spec (tracked in SPEC/ as it
  develops).
- Type providers in their current form (see Plugins below).

## GADTs

Per-case constructor signatures on DUs. **The header binds no type
parameters** — the generic parameter lives on the constructor, not the type.
`type Expr<_>` declares arity/kind only; each case signature is its own
closed, implicitly generalized scheme:

```fsharp
type Expr<_> =
  | Lit  : int -> Expr<int>
  | Pair : Expr<'a> * Expr<'b> -> Expr<'a * 'b>
  | If   : Expr<bool> * Expr<'a> * Expr<'a> -> Expr<'a>
```

- Named params in the header = ordinary DU, ordinary inference/variance.
  `_` in the header = GADT mode: per-case return types required, matches
  refine under an annotated scrutinee. The mode is declared, never inferred.
- Binders appearing only left of the arrow are existentials
  (`| Thunk : (unit -> 'r) * ('r -> string) -> Expr<string>`). Escaping
  existentials get first-class error messages — it is the first confusing
  thing every GADT user hits.
- GADT constructors force polymorphic recursion, so whole-program
  monomorphization (MLton/Rust style) is impossible. A uniform boxed
  representation fallback is required; monomorphization is an optimization,
  never the semantics.

## Higher-kinded types

Kinds are declared by shape in the type-parameter list: `'m<_>` is a
constructor of one argument, `'t<_<_>, _>` takes a constructor and a type
(monad transformers). Kinds capped at rank ~2 in v1 for the sake of error
messages.

```fsharp
type Functor<'f<_>> =
    static abstract Map : ('a -> 'b) * 'f<'a> -> 'f<'b>

type Monad<'m<_>> =
    inherit Functor<'m>
    static abstract Return : 'a -> 'm<'a>
    static abstract Bind   : 'm<'a> * ('a -> 'm<'b>) -> 'm<'b>
```

- Bare unapplied constructors become legal type arguments:
  `interface Monad<Option>`. Kind-checked (`Option : * -> *`).
- Constraint form mirrors the existing constraint family: `when 'm : Monad`.
  Statics on type variables use the F# 7 generic-math call form `'m.Bind(...)`.
- **No type-level lambdas** (keeps higher-order unification decidable;
  inference unifies on constructor spines only). Partial application is a
  trailing run of `_` only: `Result<'e, _>` yes, `Result<_, 'e>` no.
- Quantified constraints (`forall 'a. 'm<'a> :> seq<'a>`) are out of v1;
  express the same thing as a superclass interface providing a view.

## Typeclasses

Interfaces with static abstract members, implemented at the type's definition
site. Compiled by **implicit dictionary passing** — not SRTP-style mandatory
inlining, whose misery is an artifact of erasure-era .NET. Monomorphization
happens only as an optimization when the instantiation is visible. Real
separate compilation, sane error messages.

- **Coherence for free**: instances live only at the definition site of the
  implementing type. Resolution = look at the head constructor's interface
  list, then discharge `when` clauses. No backtracking; overlapping instances
  are unrepresentable. No orphans. If retrofitting types you don't own hurts
  in practice, Scala-style scoped given-imports are the *later, additive*
  escape hatch — global orphans can never be walked back.
- **Conditional instances**: an implementation may carry constraints and
  compiles to a dictionary-to-dictionary function:

  ```fsharp
  type Compose<'f<_>, 'g<_>, 'a> = Compose of 'f<'g<'a>>
      interface Functor<Compose<'f, 'g>> when 'f : Functor and 'g : Functor with
          static member Map (h, Compose x) = Compose ('f.Map('g.Map h, x))
  ```

- **Associated types, not fundeps** (Haskell's type families — the
  *associated* kind only). `static abstract type` members on interfaces;
  dictionaries carry them; resolution stays syntax-directed. Open top-level
  families are rejected (type-level orphans); closed families are out of v1
  (type-level programming swamp; GADTs + associated types cover practice).
  **Injectivity annotations** (`static abstract type Elem (injective)`) are
  in — the default non-injectivity surprises everyone and the check is local.

  ```fsharp
  type MonadState<'m<_>> =
      inherit Monad<'m>
      static abstract type State
      static abstract Get : unit -> 'm<State>
      static abstract Put : State -> 'm<unit>
  ```

## Plugins (type providers, principled)

Compiler plugins produce declarations the compiler lowers as if written in
source — but:

- Plugins never touch the TAST (most churn-prone structure in any compiler).
  They emit a small **versioned declaration IR** (or surface syntax) that
  flows through normal checking.
- Laziness is preserved by making the plugin a **query endpoint**: the
  compiler asks "members of `Db.Customers`?", the plugin answers on demand,
  the incremental engine memoizes. Million-type provided spaces never
  materialize.
- Plugins must be deterministic functions of declared inputs (schema files,
  snapshots) — required for incremental correctness and reproducible builds.

## Type system reference points

- **Scala 3 / DOT** — the one shipped, sound combination of GADTs + HKT +
  nominal subtyping + intersection. Closest prior art for the checker.
- **OCaml** — GADT inference pragmatics, compilation model, uniform
  representation.
- **MoonBit** — closest existing analog of the whole undertaking (ML-family,
  native + wasm-GC, tooling-first, small team). Study its backend choices.
- Inference degrades gracefully by design: GADT matches need annotations,
  HKT instantiation sometimes does. F#'s left-to-right inference culture
  already accepts this.

## Compiler architecture (non-negotiables)

- **Query-based and incremental from the first commit** (Roslyn /
  rust-analyzer / Salsa style). The LSP server is the *first* client of the
  query engine; the batch CLI is the second. Never a batch compiler with an
  IDE bolted on later — that retrofit is the mistake F# itself (FCS) can
  never finish paying for.
- Error-tolerant parser producing **lossless syntax trees** (red/green).
  Concatenating the leaves reproduces the source byte-for-byte.
- Constraint-based inference (generate then solve, with deferral) — not
  Algorithm W. Overloads, subtyping, classes, and GADT equalities all need
  constraints that outlive the use site.
- Elaboration into a small **typed core** (explicit dictionaries, explicit
  GADT coercions, kinds) à la GHC Core, with a linter that re-typechecks
  core after every pass.
- Backends: **wasm-GC first** (host GC solves the hardest runtime problem;
  runs in wasmtime/node/browsers), then LLVM or Cranelift native with MMTk
  (Boehm acceptable to start). Value representation: uniform boxed baseline,
  monomorphize/unbox as visible-instantiation optimization (forced by GADTs,
  see above).

## Bootstrap strategy

The compiler is written in the **common subset of F# and F++** from the first
line: no reflection, no fancy BCL surface; every runtime touchpoint (strings,
maps, IO) behind one small `Prelude` module reimplemented later in the F++
stdlib. Self-hosting is then a flip, not a rewrite — the same tree compiles
under dotnet today and under itself later, keeping full .NET tooling and
debugging throughout development.

**The oracle trick**: because the shared subset is real F#, every semantics
test executes twice — under `dotnet` and under the F++ pipeline — and outputs
are diffed. A machine-checked conformance suite for the entire inherited
surface, for free. The self-host fixpoint (stage2 compiles source →
byte-identical stage3) runs in CI forever after the flip.

## Identity: hashing and equality on every type

Every value can be hashed and compared. Today that is a runtime walk
(`$hashv`/`$equal`) that sniffs representations with `ref.test` chains —
which is the runtime dispatch this design rejects everywhere else, and is
unsound besides: wasm-GC canonicalizes same-shaped struct types into one
heap type, so the walk cannot always tell two types apart. It goes away.

**Generated, not discovered.** The compiler emits `equals` and `hash` for
every type, structurally, recursing into components. This is a TAST plugin
(the mechanism already exists). A user-declared `Equals`/`GetHashCode`
member replaces the generated one.

**Semantics follow F#, with one deliberate exception.**

| kind | equality |
| --- | --- |
| struct, record, DU, tuple | structural |
| class | reference identity, unless it overrides |
| **array** | **reference identity — F# says structural; we do not** |

Classes being reference-equal is not only faithful, it is what keeps
structural equality total: a cyclic object graph would otherwise not
terminate.

Arrays are the one place we break with F# on purpose, because their
contents may change while their identity stays the same. The reasoning,
and the rules governing any future departure, live in DIVERGENCES.md —
including that the oracle gate cannot arbitrate such a case and each one
needs a test asserting our own behaviour.

**Dispatch splits along the boxing line.**

- A struct, or any statically-known type, gets a direct call to its
  stamped function. No boxing, no dispatch — monomorphization already
  provides this.
- A reference type reached from generic (`Canon`) code dispatches through
  a slot in its descriptor.

**Every reference type therefore carries a descriptor.** Classes already
do. DUs get theirs for free — the case tag indexes a descriptor table, so
no word is added. Records take one extra word per instance; that is the
accepted cost of uniform identity, and anything needing density should be
`[<Struct>]`, which pays nothing. The rule is: *boxed things carry a
descriptor; value types are known statically.*

`IEqualityComparer` remains the path for CUSTOM equality — dictionary
passing, exactly as in the typeclass design — and is what the collections
take explicitly.

## The library boundary: Fable's subset as the specification

The set of FSharp.Core and BCL surface we implement is Fable's subset. Not
its implementation — its *list*. It is the already-drawn and validated line
between F# and .NET, it is documented and finite (so it is testable), and
it matches what F# users targeting non-CLR hosts already expect.

In scope: `List`, `Array`, `Seq`, `Option`, `Result`, `Map`, `Set`,
`String`, `Printf`, and a thin `System` surface.

Out of scope, explicitly: reflection, LINQ/IQueryable, `Task`/async
(we design our own concurrency later), globalization and culture.

Where we must diverge from Fable: it *maps* onto JS built-ins — its `seq`
is a JS iterator, its string a JS string. We have no host library, so every
shim is ours. That is an advantage: the stdlib is written in F++ itself,
continuous with `stdlib/*.fpp`, and every function is oracle-tested against
fsi. Only a minimal primitive floor stays as emitter intrinsics — string
bytes, math, memory.

`seq` is the hard one, being lazy and interface-based. It becomes a real
interface (`IEnumerable`/`IEnumerator`) dispatched through the vtable
machinery, with compiler-provided implementations for arrays and lists,
and `for x in xs` desugaring to `GetEnumerator`/`MoveNext`/`Current`.

### Order of work

1. Descriptors on all reference types — the universal identity mechanism.
2. Generated `equals`/`hash`; user overrides win.
3. Delete the `$hashv`/`$equal` runtime walks.
4. The stdlib proper, scoped by the Fable list, written in F++.
5. `seq`/`IEnumerable` as a real interface plus `for-in` desugaring.

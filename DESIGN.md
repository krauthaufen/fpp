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

## Numeric classes and operators

SRTP is removed, so operators and math functions get their polymorphism
from typeclasses. The numeric hierarchy is the first serious client of
that layer, and it is deliberately shaped unlike Haskell's.

**A class is not a type.** It has no values, no subtyping and no boxing —
you can never hold something of type `Fractional`. C# puts static abstract
members on interfaces, which look like types you could hold and are not;
that confusion is designed out here with a distinct keyword. `class` is
free: F#'s verbose `type X() = class ... end` form is not part of F++. And
since these are not interfaces, they carry no `I` prefix.

**Operators are overloading, not algebra.** Each operator is a two-parameter
class whose result is an associated type — the shape Rust uses for
`Mul<Rhs> { type Output }`, not the shape Haskell uses for `Num`:

```
class Mul<'a, 'b>
    type Result
    static (*) : 'a -> 'b -> Result

instance Mul<M44d, V4d>
    type Result = V4d
    static (*) m v = ...
```

The member is named `(*)`, not `Mul`, so an instance reads as an operator
definition and lines up with F#'s `static member (+)` syntax.

`Num` forces `(*) : a -> a -> a`, and almost nothing in linear algebra is
closed like that: `M * v`, `s * v` and `M * M` all leave the type. Making
the result an associated type — determined by the operand pair, not a free
third parameter — is what makes matrix·vector the ordinary case instead of
a special one.

**This is knowingly not what typeclasses are for.** A class like
`Mul<'a,'b>` carries no laws, and no generic algorithm can be written
against it alone; it exists to overload notation. Haskell would not do
this. We do it because the alternative — modelling `Apply`, `Compose`,
`Scale` and componentwise product as separate law-carrying structures — 
forces renaming operations that have universally understood spellings, and
because the ambiguity argument does not survive contact with the domain:
`V3d * V3d` componentwise is standard in computer graphics, not a mistake
to be prevented. The trade is taken for OPERATORS specifically.

Classes that do carry laws stay principled and single-parameter:
`Floating<'a>` for `sin`/`exp`/`log` (closed and homogeneous — a `V3d`
is never asked for a sine), `Ordered<'a>` for comparison, and the
Functor/Monad layer of the HKT design. Two flavours of class coexist, and
which is which should be stated rather than assumed.

**Closed classes carry the genericity; operator classes carry the
notation.** Overloaded operators alone would make generic math unwritable:
`a + b` yields `Add<'a,'b>.Result`, and without something to pin it, an
unannotated numerical routine infers a chain of unreduced projections that
is unreadable — the failure mode that makes F#'s SRTP errors notorious.
The fix is nominal superclass constraints:

```
class Fractional<'a>
    when Add<'a,'a> with Result = 'a
    when Mul<'a,'a> with Result = 'a
    when Div<'a,'a> with Result = 'a
    static Zero : 'a
    static One  : 'a
```

**A constraint is a class applied to types**, Haskell-style, not a
membership test on a variable. `when Fractional<'a>`, never
`'a : Fractional`. The latter reads as subtyping — the very confusion the
`class` keyword removes — and it has no sensible reading at all for a
two-parameter class: in `'a : Mul<'a,'b>` neither parameter is the
subject. The same spelling then serves superclass constraints, use-site
constraints and instance contexts:

```
let solve (m : Matrix<'a>) (b : Vector<'a>) : Vector<'a>
    when Fractional<'a> = ...

instance Add<V3d, V3d> when Fractional<float>
    type Result = V3d
    static (+) a b = ...
```

Where a class has exactly one associated type, `Add<'a,'a> = 'a` is
shorthand for `Add<'a,'a> with Result = 'a`.

**A single-parameter class may stand where a type goes**, and that is how
generic math is written:

```
let solve (m : Matrix<Fractional>) (b : Vector<Fractional>) : Vector<Fractional> = ...
```

`Fractional` there introduces an implicitly quantified type variable
constrained by the class. The rule that makes this useful rather than
misleading: **the same class name means the SAME type within one
signature.** C++'s `auto` and Rust's `impl Trait` in argument position
introduce a fresh variable per occurrence, so `Matrix<Fractional>` and
`Vector<Fractional>` would not share a scalar — which for numerical code is
exactly backwards. When two distinct instances of a class are genuinely
wanted, name them: `when Fractional<'a>` and `when Fractional<'b>`.

The sugar applies to single-parameter classes only; nobody writes
`x : Mul`, and the two-parameter operator classes appear in `requires`
clauses rather than type positions.

Either way the projection reduces: `x + y` at `'a` produces
`Add<'a,'a>.Result`, and the `requires` equality in scope rewrites it to
`'a` at once. The user writes one readable name; closure comes from the
class, not from grounding.

**The projection rule.** A projection must reduce either by a known
concrete type or by a constraint in scope, and may never survive into a
generalized signature. If it cannot reduce, that is an error naming the
failing operator application and its two operand types — never an
accumulated constraint chain. Error shape is a requirement here, not a
nicety: dumping the chain is exactly what makes SRTP diagnostics
unreadable.

This is also what makes associated-type EQUALITY in constraints
load-bearing rather than speculative: `with Result = 'a` is the mechanism.

In practice generic numeric code is generic over the SCALAR, not the
containers — `Matrix<'a>`/`Vector<'a>` operations are written concretely
and constrained by `when Fractional<'a>`, while heterogeneous instances like
`Mul<Matrix<'a>, Vector<'a>>` are declared once per container rather than
inferred per call. So the two-parameter classes stay near-ground and the
closed classes do the abstracting. (nalgebra's `T: RealField` is the same
split.)

**Instances are free-standing.** A two-parameter class has no natural
owner — `Mul<M44d, V4d>` belongs to neither operand more than the other —
so instances are declared Haskell-style rather than inside a type, as in
the example above. `static member (+)` on a type stays as sugar for the homogeneous case
`Add<T,T> with Result = T`, because that is what F# code in the wild
writes.

**One operator symbol, one class.** `a + b` must resolve by a single
lookup keyed on the class and the operand pair. If several classes could
define `+`, resolution becomes a search with ambiguity that is
unresolvable in principle, not merely slow.

**Coherence matters more here, not less.** With no laws to constrain
instances, the only thing keeping resolution well-defined is: exactly one
instance per `(a, b)` pair, globally, and an orphan rule — an instance must
live in the module defining one of the two types. Without it two libraries
can each declare `Mul<float, V3d>` and linking is ill-defined.

**Consequence for the constraint language.** Generic numeric code needs to
say that an operation stays in its type: `sum` over `'a` requires
`when Add<'a,'a> with Result = 'a`. So constraints must be able to
equate an associated type, not merely require a class.

**Sequencing.** `sin`/`cos`/`exp` ship monomorphically on `float` and
`float32` first — that is how they are overwhelmingly used, and F# itself
defaults `sin` to float. Those functions become the instance bodies when
the class layer lands, so nothing is wasted. Operators on primitives are
already resolved statically by inference and emitted as machine
instructions; under the class formulation that is not a special case but
the instance being known statically and inlined.

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

**The contract is total.** Every value has `equals` and `hash`. There is no
type for which they are unavailable, and no call that can fail to resolve
one — a structural definition where the type has one, reference identity
everywhere else. Nothing "does not support hashing".

| kind | equality and hash |
| --- | --- |
| primitive, string, struct, record, DU, tuple | structural |
| class | reference identity, unless it overrides |
| function / closure | reference identity |
| **array** | **reference identity — F# says structural; we do not** |
| anything else without a definition | reference identity |

Reference identity is the floor, not a failure case. Classes being
reference-equal is faithful to F# and is also what keeps structural
equality total: a cyclic object graph would otherwise not terminate.

**Identity hashing needs a number, and wasm-GC has no address-of.** The
obligation is only `a = b` implies `hash a = hash b`, so for a
reference-equal value any stable function of the object is legal; quality
is a separate question from correctness.

- classes: a lazily-assigned identity word in the object header, alongside
  the descriptor. Paid only by types that are reference-equal — a record is
  structural and never carries one, a struct never does.

  There is no alternative: wasm-GC exposes no address, no identity number
  and no ordering on references, because a moving collector would
  invalidate anything address-derived. `ref.eq` compares two references but
  does not number one. `i31ref` looks like a counter-example and is not —
  an i31 is a 31-bit immediate tagged as a reference, so `i31.get_s`
  recovers the VALUE it encodes, which is exactly why primitives need no
  stored word. A struct reference has no such projection. The JVM and .NET
  store the same word for the same reason.
- arrays: the length. Stable (our arrays are fixed-length), cheap, and
  unaffected by element mutation — which is precisely the property that
  made structural hashing incoherent for them.
- closures: a constant until something needs better. Legal, and honest
  about being poor.

Anything wanting real hash quality on a reference-equal type passes an
`IEqualityComparer`, which is the custom-equality path already.

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

# WasmLin `--gc` self-host — status & resume brief

Goal: the WasmLin (wasm-linear) backend self-hosts the F++ compiler byte-exactly
under `--gc`. The probe path compiles `module M\nlet a = 1`, runs the whole
compiler to completion at the **default 16 MB** heap through real collections,
emits, and `cmp`s `/tmp/oracle.wasm` (77860 bytes) byte-exact.

Standing rules: root-cause, never mask ("measure, do not reason"). WasmLin
changes must keep **fixpoint-self** (wasm-GC / BinDriver backend) byte-exact —
WasmLin and BinDriver share `Link`/inference but emit independently.

---

## 1. What's done + committed

**Architecture — inline values, no boxing, .NET-parity layout, value-witness ABI.**
Scalars (`int`/`bool`/`char`/`uint32`) are RAW inline i32 words (even, untagged),
never boxed. Aggregates use a per-type layout engine computing `{size, align,
refMask}` with .NET-parity field packing. A generic element's raw-vs-ref shape is
carried at runtime by a **value witness** `{size, align, refMask}` (offsets
0/4/8); `refMask=0` raw, `1` ref. `ctx.Witness : Dict<tvarId,reg>` maps a type
var to its witness register.
- `b93bb84` .NET-parity inline-value layout engine (size/align/refMask)
- `a49bd31` int/bool/uint32 inline raw scalars (GC-safe records/arrays)
- `019593c` docs: inline-values GC path (runtime refoffs map)
- `d264cd4` / `784049e` / `15fc463` FK_STRUCT ref-maps for concrete
  tuples/unions/cells/globals, concrete-element list cons, closure envs
- `4726ae8` witness-driven refoffs for generic records/tuples/unions/closures
- `10a2026` / `2799af5` value-witness ABI for generic list cons; witness args
  from recorded `inst`; Canon calls keep the witness ABI
- `b354ba4` witness class type params so `'k` compare/hash skip `$cmpv`/`$hashv`
- `defc475` class-field cell of a scalar reads RAW (excluded from aggregate scan)
- `edefbcc` vtable-method impls keep a uniform sig (no funSigOf specialization)

**Collector (Whippet semi-space, growable, `runtime/gc/src/semi.c`).** Precise
moving GC. Forwarded tag word is EVEN (new addr, bit0=0); a live header is
`(tid<<1)|1` (ODD). On wasm, released regions stay mapped, so a **stale pointer
reads old data** rather than faulting — the failure mode behind the rooting
class. Growth mmaps a new region at a new base. Shadow-stack scanner SKIPS odd
and null words, so only genuine even-nonzero pointers may be pushed; a raw even
int on the shadow stack (or in an FK_TAGGED slot) is mis-traced.

**Dictionary / enumeration.**
- `a9065eb` array enumeration routed to a built-in iterator; array tids mapped to
  `CID_ARRAY` in the t2c table (the real bug — not the iterator).
- `6d08ce8` isBuiltinSeq recognizes FK_STRUCT cons via cid; literNext raw bool.

**Rooting class — CLOSED (general liveness pass).** Stale-but-valid pointers not
kept live across a safepoint. Closed comprehensively, not per-instance, by
`ActiveGen` + `rootActiveGen`: every pointer-typed value live across ANY
safepoint is pushed/reloaded through the shadow stack, generic vars gated by
their witness refMask.
- `08231b2` root closure env on shadow stack; ETry `$sp` restore
- `7c73223` root all live pointer values across GC safepoints (8 categories)
- `4d811bf` root generic (`'a`) locals across safepoints via witness-conditional
  slots (the general pass that subsumed the categories)

**Classification class — CLOSED for all resolvable forms (type-driven witnesses).**
A RAW scalar sitting in a ref-marked / FK_TAGGED slot mis-traces. Closed by
threading an element witness to every generic aggregate construction site so
`lowObjR`/cons/tuple resolve the precise-refoffs path; the FK_TAGGED tag-scan is
the fallback only for genuinely-unresolved slots.
- `60162b1` classify `arr.[i]` cons head by element kind
- `36cb3ee` preserve source cons tid in `$lappend`; array-index element witness
- `163b65d` resolve generic cons-head ref-kind through call inst / if-match
- `1dcb24a` classify a record field read by its field type
- `01466ee` thread element witnesses to generic aggregate slots
  (constant / inst / witness) — `genWits` carries witness `LExpr`s
- `b10562d` **resolve generic slot witnesses by result type** — applied lambda →
  its body; builtin (`EUnknown`) → its name (`int#`→raw, `string#`/`$str.`/
  `$cellof`→ref); prim → its result (`::`/`@` ref, comparison/unary raw). Drops
  unresolved slots **482 → 15**.
- `b99030b` **record a stamped instance's own type-vars as constant witnesses**
  — tier-1 monomorphic instances (`add_..$int`) leave their type-var free with no
  witness; record the own-Quantified→inst map. Drops **15 → 6**.

**#2 (receiver-instance-witness for `x.f` where `f:'a`) — measured NOT needed.**
Instrumenting the unresolved slots by form showed **zero EField cases**; the gaps
were all EApp/EPrim/EUnknown/EVar (value results, not receiver field reads). Do
not spend effort here.

Validation at HEAD (`b99030b`): **698 unit tests pass**, corpus byte-exact
(84579), fixpoint-self byte-exact (2712515). WasmLin changes are provably
invisible to BinDriver (`stampedClassWits` is read only by WasmLin).

---

## 2. Current self-host landing point

Self-host runs the **entire lexer** and is **deep in the parser** (`Parser.fs`,
around `IsKw`). It traps in the collector on **tid-236**: `pkind=5`
(`FPPRT_EMB_KIND_TAGGED` = FK_TAGGED), `pnrefs=1`, no name — a tagged object
whose payload slot holds a RAW even word (observed values 2164 / 5656 / 40108
across runs; parent header decodes to string data) that the tag-scan mis-traces
as a heap ref. Every raw-slot class **except** this one is closed.

---

## 3. The residual 6 raw slots — single root cause

6 generic slots still resolve to no witness → FK_TAGGED. tid-236 is one of them
(the raw `int` key of a `dictSlotH` construction). Measured breakdown post-fix:
3 × `EVar TVar` (ids 5489/5491/5636), 2 × EApp, 1 × other — all inside stamped
**Dictionary** members (`dictSlotH$int$list<…>`).

**Root cause — monomorphizer type-var id-provenance mismatch.** The witnesses
*are* recorded, but under the **template scheme's Quantified ids** (`224`=int,
`225`=list — verified via the `stampedClassWits` dump). The stamped member's
**body** references those same logical types under **different fresh ids**
(`5489`/`5491`/`5636`). So `ctx.Witness` is seeded with keys 224/225 while the
body looks up 5489/… → miss → FK_TAGGED → the raw `int` one mis-traces (tid-236).
This is the `CLAUDE.md` trap: "a member's quantified variables are NOT the
class' — find the class' parameters positionally, through the receiver type."

**Two candidate fixes (Link, fixpoint-fragile — DO NOT start without a steer):**
1. **Substitute** the stamped body's type-vars to the scheme's Quantified ids
   consistently at stamp time (so the body carries 224/225).
2. **Key the recorded witness by the id the body carries** — derive the map from
   the member's receiver args (the `classMapOf` approach, `Link.fs:1048`), and
   make the queue-drain recording (`Link.fs` ~992–996) not overwrite it with the
   enclosing canonical ids.

Both touch `Link.monomorphizeWith` (the documented-fragile path). Guardrail:
`stampedClassWits` is WasmLin-only, so a correct fix cannot alter BinDriver
output — fixpoint-self must stay byte-exact; if it moves, the change leaked into
shared `Link` state, which is the bug.

---

## 4. Reproduction + instrumentation recipes

**Self-host build/run (probe path):**
```bash
cd ~/projects/fpp-lowir
dotnet build -c Release
# compile the whole compiler via WasmLin.gc -> /tmp/selfhost_a.mod.wasm
dotnet fsi /tmp/gchost.fsx                       # prints "selfhost: N bytes, 0 errors"
# reactor (fpprt + Whippet, imported reactor) -> /tmp/bigreactor/
bash tests/tooling/gc/build-reactor.sh
cp ~/projects/fpp/runtime/build/wasm/fpprt_reactor.wasm /tmp/bigreactor/
# merge + run
WM=~/emsdk/upstream/bin/wasm-merge; wt=~/.wasmtime/bin/wasmtime
$WM -all /tmp/bigreactor/fpprt_reactor.wasm fpprt /tmp/selfhost_a.mod.wasm mutator -S -o /tmp/sh.wat
wasm-tools parse /tmp/sh.wat -o /tmp/sh.wasm
$wt run -W gc=y,exceptions=y,max-wasm-stack=536870912 --env FPPRT_HEAP_MB=16 /tmp/sh.wasm
# oracle for the final cmp: /tmp/oracle.wasm (77860 bytes)
```
`wasm-merge` names merged globals `$global$110` etc. (NOT numeric index) — use
`$global$N` in any shadow-stack walk.

**Gates:** `dotnet fsi tests/bootstrap/fixpoint.fsx` (corpus),
`… fixpoint.fsx self` (fixpoint-self, byte-exact),
`dotnet run -c Release --project tests/Fpp.Tests` (698 tests, ~8 min contended),
`tests/tooling/gc/run-gc.sh /tmp/<t>.fpp` (ra/denum/gcstress/closrec/gcnest).

**`unresolvedGen` / slot-form instrument** (WasmLin.fs, `genWitsOf` None branch):
```fsharp
| RKGen -> (match slotWitness ctx e with Some w -> Some (base_+j, w) | None ->
    (if not (isNull (System.Environment.GetEnvironmentVariable "FPP_GEN2")) then
       match e with
       | EVar(_,s)|EVarI(_,s,_) -> eprintfn "GEN2 EVar %A" (prune s.Body)
       | EApp _ -> eprintfn "GEN2 EApp" | EPrim(o,_) -> eprintfn "GEN2 EPrim %s" o
       | _ -> eprintfn "GEN2 other"); None)
```
Correlate with `FPP_FUNC_DUMP=1` (prints `FUNC $f… = key | Name` before each
body). Do NOT use `[for KeyValue … in dict]` comprehensions in the probe — they
aren't dogfood-inferable and break the self-compile.

**`stampedClassWits` dump** (WasmLin.fs, the `constWits` `match`): print
`v.Name`, `pairs |> List.map (fun (vid,nm) -> string vid+"="+nm)` for names
starting `dictSlotH` — this is what showed the 224/225-vs-body-id mismatch.

**Collector `visit()` external-edge logging** (`runtime/gc/src/semi.c`; struct
`fpprt_type_intern {size;kind;nrefs;refoffs;name}` is already visible via
`embedder-api-impl.h` — do NOT redefine it):
```c
static uintptr_t g_cur_parent = 0;                 // add above copy()
// in scan(): g_cur_parent = gc_ref_value(grey);  before gc_trace_object
// in visit() else-branch (non-from-space, non-forwarded), before visit_external_object:
{ uintptr_t a=gc_ref_value(ref), ph=g_cur_parent?*(uintptr_t*)g_cur_parent:0;
  struct fpprt_type_intern *pt = ph? &fpprt_types_[ph>>1] : 0;
  fprintf(stderr,"EXT ref=%lu pkind=%u pnrefs=%u pname=%s\n",
    (unsigned long)a, pt?pt->kind:999, pt?pt->nrefs:999, pt&&pt->name?pt->name:"?");
  fflush(stderr); }
```
`pkind` maps the mis-trace to its object class (5=FK_TAGGED). Revert with
`git -C ~/projects/fpp checkout gc/src/semi.c`, then rebuild the reactor.

**Fast cycles:** `FPP_PRELUDE_TRUNC=<n>` shrinks the prelude so the self-host
reaches a trap in seconds instead of compiling the whole compiler.

---

## 5. What's beyond tid-236

Honest scope: tid-236 is the last known raw-slot blocker in the **parser**. Past
it, the self-host still has to run **inference, lowering, and emission** to
completion and then `cmp` byte-exact — each may surface new instances of the same
two classes, or a new class entirely. The two closed classes are the templates:
- **Rooting** (stale valid pointer): find the safepoint it crosses, root it
  through the shadow stack. General mechanism: `ActiveGen`/`rootActiveGen`.
- **Classification** (raw scalar in a ref/FK_TAGGED slot): resolve the element
  witness at the construction site (`slotWitness`/`genWitsOf`); if the witness
  genuinely can't be resolved from any source, it's an ABI gap — STOP and report,
  as with the current monomorphizer id-provenance mismatch.

Diagnose every new trap with the `visit()` `pkind`/`pname` dump first (which
class?), never guess.

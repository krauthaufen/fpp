// A CANONICAL (all-obj) CLASS INSTANCE HAS NO VTABLE ROW: its members were
// only ever stamped at the CONCRETE instantiations, so the row names a stamp
// nobody made and the dispatch traps in `$novt3`.
//
// THE fpp.dom TRAP THIS FILE WAS WRITTEN FOR WAS NOT THIS (2026-09-08). It
// was a WILDCARD UPCAST taking type arguments independent of its class:
// `C<'T>(v) :> IBox<_>` left the interface's argument free, so
// `AVal.constant (Some x)` fitted a parameter declared `aval<seq<_>>`, the
// wrong Yield overload was chosen on that lie, and the OPTION was enumerated
// at run time — reaching a row nothing fills. The upcast now takes its
// arguments from the class' own declaration (`suites/upcastargs.fpp`,
// `neg/upcast-wildcard-argument.fpp`), and fpp.dom's ce gate passes with all
// six formerly blocked cases. There is no program left that reaches an empty
// row.
//
// WHAT REMAINS OPEN is the row itself: a class CONSTRUCTED canonically still
// has no implementation to dispatch to. Nothing known reaches one, so this
// is a missing mechanism rather than an observable defect — kept here for
// the diagnosis, which is otherwise expensive to re-derive.
//
// THIS FILE IS NOT THE REPRO — it cannot be, and that is the point. Every
// small program stamps every instantiation it uses, so every row is filled.
// The shape needs a program where a generic class is BOTH stamped at concrete
// types and constructed canonically (a value that reaches a `'a`-typed field,
// an `obj` container, a reader's output). The recipe that USED to trap:
//
//   cd ~/projects/fpp.dom && cp -r . /tmp/domx && cd /tmp/domx
//   # tests/gen-ce-tests.py: BLOCKED = set()
//   python3 tests/gen-ce-tests.py
//   cat ~/projects/fpp.adaptive/src/adaptive.fpp src/dom/events.fpp \
//       src/dom/attribute.fpp src/dom/domnode.fpp src/dom/builders.fpp \
//       src/dom/frontend.fpp src/updater/updater.fpp tests/t-ce.fpp > /tmp/ce.fpp
//   fpp build --strict -o /tmp/ce.wasm /tmp/ce.fpp
//   wasmtime run -W gc=y,exceptions=y --env FPPRT_HEAP_MB=256 /tmp/ce.wasm
//
// It printed its cases and then trapped inside `$novt3` under `Seq.ofSeq`,
// on the `avalatt` case (`div { AVal.constant (Some (Dom.Id "opt")) }`, the
// AttributeMap.OfOptionA path) — that was #48, and it passes now.
//
// WHAT IS KNOWN, so the next session does not re-derive it:
//
//   * the failing dispatch is IEnumerable.GetEnumerator, slot 802 of the
//     row, whose k is 1 — the call passes (self, unit, element witness).
//   * `FPP_VTDBG=1` prints every row. The rows that stay empty are the BASE
//     (unstamped) classes: ResizeArray, Dictionary, MutableHashSet, HashSet,
//     ChangeableHashSet, ChangeableHashMap, ChangeableIndexList — "MISS-func
//     GetEnumerator". Their implementation is the shared TEMPLATE, and the
//     template is not among the emitted functions: monomorphization stamped
//     the concrete uses and nothing kept the template alive, so a value whose
//     class-id is the canonical one has nothing to dispatch to.
//   * a STAMPED class whose own stamp is missing now falls back to its base's
//     template when the widths agree — that filled 893 rows in this program,
//     including MapExt$obj$obj's. It does not reach the base classes above,
//     which have no base of their own to borrow from.
//   * every unfilled row is now the trap of ITS SLOT'S WIDTH ($novt/$novt3/
//     $novt4). Before that they were 0 — index 0, `$novt`, which takes two
//     arguments — so a slot passing witnesses failed the call_indirect TYPE
//     CHECK first and the engine said "indirect call type mismatch" with
//     nothing to name. That is why this looked like a mystery for so long.
//   * a row whose filler takes a different number of witnesses than its slot
//     passes is reported at build time now ("stubbed vtable row …"); twelve
//     of them exist in that program, and none is the one that traps.
//
// WHAT IT NEEDS: the template must survive for a class that is still
// CONSTRUCTED canonically — either by keeping it as a DCE root whenever the
// canonical class-id is reachable, or by stamping the canonical
// instantiation like any other. The fix belongs in Link, beside the stamping
// decisions, not in the backend.
module CanonicalClassVtableRow

// what the shape looks like in the small (this one WORKS — the stamp exists)
type Holder<'T>(items : 'T list) =
    member x.Items = items
    interface System.Collections.Generic.IEnumerable<'T> with
        member x.GetEnumerator () = (List.toSeq items).GetEnumerator ()

let h = Holder [ 1; 2; 3 ]
let t = printfn "%d" (Seq.length (h :> System.Collections.Generic.IEnumerable<int>))

# Inline values — never boxed, .NET-parity layout

The WasmLin backend is moving off the *uniform-boxed baseline* (DESIGN.md:92)
to a representation where **no value is ever heap-boxed to be carried**. A value
lives inline — in a local, on the wasm stack, or in the bytes of the container
that holds it — and generics are served by a runtime **value-witness** rather
than by boxing every `'a`. This is the "option C" direction: kind-per-slot,
layout-driven, closest to true monomorphization without duplicating code.

This note is the contract the codegen stages build against. Stage 1 (this
commit) is only the **layout engine** — pure, additive, consumed by nobody yet.

## Layout descriptor

```fsharp
type Layout = { Size : int; Align : int; RefMask : uint64; Generic : bool }
```

- `Size` / `Align` — bytes the value occupies inline, and its alignment.
- `RefMask` — bit *i* set ⇒ word *i* (4 bytes) of the value is a GC pointer the
  collector must trace. Every other word is raw scalar bytes it skips. This
  replaces the low-bit word tag: the GC scans by the container's layout, so an
  `int` in a slot is never mistaken for a pointer and never needs a tag bit —
  hence full 32 bits, no box, no truncation.
- `Generic` — the layout is not known statically (a type parameter, or a struct
  with a type-parameter field). A runtime witness supplies it; `Size`/`Align`/
  `RefMask` are meaningless when this is set. `layoutOf` never guesses.

`> 64 words`: `RefMask` is a `uint64`, so a value wider than 64 words cannot
represent its high ref-words. No such type exists today; the reconciliation
stage must widen the mask (or fall back to a per-type ref-map) before that can.

## Struct storage follows .NET layout

Structs lay out **sequentially, exactly as .NET/CLR does**: declaration order,
each field on its natural alignment, the whole padded up to the struct's
alignment. This is the same rule the ABI parity harness (`tests/tooling/abi/`)
pins against a real C compiler via emscripten — `layoutOf` agrees with those
numbers by construction:

| type                         | .NET / C (abi harness) | `layoutOf` |
|------------------------------|------------------------|------------|
| `V3f {float32×3}`            | 12                     | 12         |
| `V2d {float×2}`              | 16                     | 16         |
| `Mixed {float; byte}`        | 16 (byte@8, pad to 16) | 16         |
| `C3b {byte×3}`               | 3                      | 3          |

Primitives at their .NET widths: `byte`/`bool` = 1, `char`/`int16` = 2 (`char`
is UTF-16), `int`/`float32` = 4, `int64`/`float` = 8.

- **Nested structs are inline** — a struct field of struct type contributes its
  own bytes, never a pointer (`Nested {V3f; int}` = 16, no refs).
- **A reference-typed field is one pointer word** stored inline (`RefRec
  {int; string}` = 8, `RefMask` word 1).
- **Arrays of structs are contiguous** — `Point[]` = header + `[x0,y0][x1,y1]…`,
  stride = the struct's `Size` with .NET padding, no per-element box/header.
- **Value copy semantics** on assignment / parameter passing / return.

Reference types (`string`, `list`, `array`, closures, reference tuples, heap
unions, non-`[<Struct>]` records) are one pointer word `{4,4, ref}`.

## One source of truth

`layoutOf` is authoritative for inline layout. The existing `RecPod` scheme is
**not** .NET-parity — it reorders fields *scalars-first / refs-last* and does
not size `int` (it predates `int` becoming a raw scalar). It is left untouched
here; the inline-value rewrite must rebuild `RecPod` (and array stride, and the
GC `start`/ref-map registration) **from `layoutOf`**, not maintain a second
scheme. Struct-vs-reference is decided by one fact: `RecFieldTys` lists a record
iff it is `[<Struct>]`.

## API

```fsharp
// pure core — takes a resolver, so it needs no St and unit-tests standalone.
// resolve name -> a struct record's ordered (field, type-name) list, or None
// for a reference type.
val layoutOfWith : (string -> (string * string) list option) -> Type -> Layout

// the St-bound wrapper used in codegen: resolve = dictTryFind st.RecFieldTys
val layoutOf : St -> Type -> Layout            // private (St is private)
```

`St.RecFieldTys : Dict<string, (string*string) list>` — every `[<Struct>]`
record's declared fields in order. Written in `emit`'s setup pass; read only by
`layoutOf` today.

## Next stages (not in this commit)

1. **Value-witness for generics.** A witness is `{ size; align; refMask }` (this
   `Layout`, minus `Generic`) built on the `Sized<'c>` idea (DESIGN.md:144).
   Each quantified type parameter is passed as a hidden leading argument to a
   generic function; a generic container reads element `size`/`refMask` from the
   witness to place, copy, and scan elements. **Open decision for the user:** the
   witness ABI — a hidden `witness` pointer per type param (simple, one extra
   arg) vs. inlining `(size, align, refMask)` as scalar args (no indirection,
   more args). Recommend the pointer form first.
2. **Containers store inline.** cons cells, tuples, arrays, union payloads and
   record fields hold elements by `layoutOf`/witness — width and ref-scan from
   the layout, no per-value tag or box.
3. **GC scans by `RefMask`.** FK_TAGGED (low-bit word tag) is replaced by
   per-shape ref-maps derived from `layoutOf`; the shadow stack pushes only ref
   words. This is what lets raw scalars live in heap slots without crashing the
   collector.
4. **Reconcile `RecPod` + array stride to `layoutOf`** and delete the
   scalars-first scheme.

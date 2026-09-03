/* Exports for a hand-emitted wasm mutator that imports fpprt's memory.
 * The mutator cannot touch fpprt's thread-local top-frame or the static
 * inline typeid read, so expose them as real functions. Frame structs are
 * built by the mutator in shared linear memory; we just splice the list. */
#include "fpprt.h"
#include <stdint.h>
#include <stdlib.h>   /* getenv */
#include <string.h>   /* strlen */

/* push a frame the mutator has already laid out in memory at `f`
 * (prev/nslots/slots/npods/pods filled in), making it the new top. */
void fpprt_frame_push(struct fpprt_frame *f) {
  f->prev = fpprt_top_frame;
  fpprt_top_frame = f;
}
void fpprt_frame_pop(struct fpprt_frame *f) { fpprt_top_frame = f->prev; }

uint32_t fpprt_tid_of(fpprt_ref o) { return (uint32_t)((*(uintptr_t *)o) >> 1); }
/* sizes so the mutator can lay out frame structs without guessing ABI */
uint32_t fpprt_sizeof_frame(void) { return (uint32_t)sizeof(struct fpprt_frame); }
uint32_t fpprt_sizeof_pod(void)   { return (uint32_t)sizeof(struct fpprt_frame_pod); }

/* scalar-arg wrapper: struct-by-value across the wasm boundary is ABI-
 * fragile, so the mutator passes fields and we assemble the struct here. */
void fpprt_register_type_s(uint32_t tid, uint32_t size, uint32_t kind,
                           uint32_t nrefs, const uint32_t *refoffs,
                           const char *name) {
  struct fpprt_type t = { size, kind, nrefs, refoffs, name };
  fpprt_register_type(tid, t);
}

/* Root table for a hand-emitted wasm mutator: its module globals holding heap
 * pointers (constant strings, the print scratch buffer) live in THIS array,
 * which sits in fpprt's stable static memory — so a moving collection scans and
 * UPDATES the slots, and the mutator reads current addresses back. Slot 0 is
 * the scratch buffer; 1.. are string constants. */
#define FPPRT_WASM_NROOTS 2097152
static fpprt_ref g_wasm_roots[FPPRT_WASM_NROOTS];
uint32_t fpprt_wasm_roots_base(void) { return (uint32_t)(uintptr_t)g_wasm_roots; }
void fpprt_wasm_roots_register(uint32_t n) { fpprt_add_static_roots(g_wasm_roots, n); }

/* The STRUCT-RETURN stack. A by-value struct result is written through a
 * destination on a raw region the collector never scans, and that region has
 * to be memory NOBODY else owns. It used to be carved out of the mutator's
 * own address space at a compile-time constant — which, once the reactor is
 * merged in, lands in the MIDDLE of g_wasm_roots above: every struct return
 * wrote its fields over root slots, and the collector then traced a double's
 * bit pattern as a pointer. So it lives here, beside the other regions the
 * mutator asks the runtime for. Grows DOWN from the top. */
#define FPPRT_WASM_SSTACK_BYTES (1u << 20)
static uint8_t g_wasm_sstack[FPPRT_WASM_SSTACK_BYTES];
uint32_t fpprt_wasm_sstack_top(void) {
  return (uint32_t)(uintptr_t)(g_wasm_sstack + FPPRT_WASM_SSTACK_BYTES);
}
uint32_t fpprt_wasm_sstack_base(void) { return (uint32_t)(uintptr_t)g_wasm_sstack; }

/* ENVIRONMENT VARIABLES. The wasm-hosted compiler could not read one:
 * `System.Environment.GetEnvironmentVariable` has no implementation there, so
 * it answered null and every env-gated pass silently did nothing in stage-1.
 * That is why the fixpoint could not validate one — stage-0 read the variable
 * and stage-1 did not, and the byte mismatch meant nothing.
 *
 * WASI gives the reactor a real environment, so libc's getenv is all it takes.
 * The name arrives as UTF-16 in linear memory (ptr = first char, n = chars);
 * env names are ASCII, so the low byte of each is the name. The value is
 * handed back a byte at a time rather than copied, which keeps the mutator
 * from having to own a buffer. */
#define FPPRT_ENV_NAME_MAX 1024
static char g_env_name[FPPRT_ENV_NAME_MAX];
static const char *g_env_val;

int32_t fpprt_env_get(uint32_t ptr, uint32_t n) {
  if (n >= FPPRT_ENV_NAME_MAX) return -1;
  const uint16_t *src = (const uint16_t *)(uintptr_t)ptr;
  for (uint32_t i = 0; i < n; i++) g_env_name[i] = (char)(src[i] & 0xFF);
  g_env_name[n] = 0;
  g_env_val = getenv(g_env_name);
  if (!g_env_val) return -1;
  return (int32_t)strlen(g_env_val);
}

uint32_t fpprt_env_byte(uint32_t i) {
  return g_env_val ? (uint32_t)(uint8_t)g_env_val[i] : 0u;
}

/* tid -> class-id table for the wasm-linear backend: the object header holds
 * (tid<<1)|1 for the collector, but type tests and vtable dispatch want the
 * language class-id. This fixed static table (raw ints, never scanned as
 * pointers) maps one to the other; the mutator fills it at startup. */
/* one entry per interned SHAPE. A large program interns thousands (the
 * adaptive port passes 4100), and writing past the end silently corrupted
 * whatever followed while the shapes that fell off the end read class-id 0 —
 * a vtable dispatch through the wrong row. The mutator refuses to emit a
 * program with more shapes than this. */
#define FPPRT_WASM_NTIDS 65536
static uint32_t g_tid2cid[FPPRT_WASM_NTIDS];
uint32_t fpprt_tid2cid_base(void) { return (uint32_t)(uintptr_t)g_tid2cid; }

/* ref-offset maps for FK_STRUCT shapes: a flat pool of uint32 byte-offsets. A
 * shape registered as FK_STRUCT points its `refoffs` at a slice here; the
 * collector reads these to trace ONLY the pointer words, so raw scalar words
 * (an unboxed int/bool in a tuple or union payload) are correctly skipped.
 * Static, never moves — the type table stores a raw pointer into it. */
#define FPPRT_WASM_NREFOFFS 65536
static uint32_t g_refoffs[FPPRT_WASM_NREFOFFS];
uint32_t fpprt_wasm_refoffs_base(void) { return (uint32_t)(uintptr_t)g_refoffs; }

/* value-witness tables for the generic ABI: a flat pool of {size,align,refMask}
 * triples. A generic function receives a POINTER into here per type parameter
 * (a concrete type's witness is a compile-time constant interned once); a
 * generic aggregate reads the element witness's refMask to pick its FK_STRUCT
 * scan map. Static, never moves — witness pointers thread through the call
 * graph as plain args and must stay valid across a moving collection. */
#define FPPRT_WASM_NWITNESS 12288
static uint32_t g_witnesses[FPPRT_WASM_NWITNESS];
uint32_t fpprt_wasm_witness_base(void) { return (uint32_t)(uintptr_t)g_witnesses; }

/* Does the collector SCAN byte-offset `off` of an object of type `tid`?
 * The mutator asks this for a pattern binder whose static type it cannot
 * resolve (a desugar lost it): the binder's value was loaded from a slot the
 * collector already classifies, so the OBJECT's own scan map is the ground
 * truth for whether that value is a pointer (root it) or a raw scalar
 * (never root it). Mirrors gc_trace_object's dispatch. */
struct fpprt_type_intern {
  uint32_t size; uint32_t kind; uint32_t nrefs;
  const uint32_t *refoffs; const char *name;
};
extern struct fpprt_type_intern *fpprt_types_;
extern uint32_t fpprt_ntypes_;
uint32_t fpprt_tid_scans(uint32_t tid, uint32_t off) {
  if (tid >= fpprt_ntypes_) return 1; /* unknown: conservatively a pointer */
  struct fpprt_type_intern *t = &fpprt_types_[tid];
  switch (t->kind) {
  case FPPRT_KIND_STRUCT:
    for (uint32_t i = 0; i < t->nrefs; i++)
      if (t->refoffs[i] == off) return 1;
    return 0;
  case FPPRT_KIND_TAGGED:
    /* scans all words from the first-payload index (t->nrefs); the value
     * itself must still be even+nonzero, which the caller's push preserves */
    return (off / 4) >= t->nrefs;
  case FPPRT_KIND_REF_ARRAY:
    return off >= 8;
  default: /* scalar arrays, pod arrays' scalar prefix, ephemerons */
    return 0;
  }
}

/* Exports for a hand-emitted wasm mutator that imports fpprt's memory.
 * The mutator cannot touch fpprt's thread-local top-frame or the static
 * inline typeid read, so expose them as real functions. Frame structs are
 * built by the mutator in shared linear memory; we just splice the list. */
#include "fpprt.h"
#include <stdint.h>

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

/* tid -> class-id table for the wasm-linear backend: the object header holds
 * (tid<<1)|1 for the collector, but type tests and vtable dispatch want the
 * language class-id. This fixed static table (raw ints, never scanned as
 * pointers) maps one to the other; the mutator fills it at startup. */
#define FPPRT_WASM_NTIDS 4096
static uint32_t g_tid2cid[FPPRT_WASM_NTIDS];
uint32_t fpprt_tid2cid_base(void) { return (uint32_t)(uintptr_t)g_tid2cid; }

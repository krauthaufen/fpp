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

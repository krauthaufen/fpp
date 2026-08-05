/* fpprt implementation over the Whippet gc-api. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "gc-api.h"
#include "gc-allocate.h"
#include "gc-barrier.h"
#include "gc-safepoint.h"
#include "gc-basic-stats.h"
#include "gc-ephemeron.h"

#include "fpprt.h"
#include "fpprt-embedder.h"

/* ---- globals ----------------------------------------------------------- */

struct fpprt_type_intern *fpprt_types_ = NULL;
uint32_t fpprt_ntypes_ = 0;
static uint32_t types_cap_ = 0;

struct fpprt_frame *fpprt_top_frame = NULL;

static struct gc_heap *heap_;
static struct gc_mutator *mut_;
static struct gc_mutator_roots roots_;
static struct gc_basic_stats stats_;

/* ---- types ------------------------------------------------------------- */

void fpprt_register_type(uint32_t tid, struct fpprt_type t) {
  if (tid >= types_cap_) {
    uint32_t cap = types_cap_ ? types_cap_ : 64;
    while (tid >= cap) cap *= 2;
    fpprt_types_ = realloc(fpprt_types_, cap * sizeof(*fpprt_types_));
    memset(fpprt_types_ + types_cap_, 0,
           (cap - types_cap_) * sizeof(*fpprt_types_));
    types_cap_ = cap;
  }
  fpprt_types_[tid] = (struct fpprt_type_intern){
    t.size, t.kind, t.nrefs, t.refoffs, t.name
  };
  if (tid >= fpprt_ntypes_) fpprt_ntypes_ = tid + 1;
}

/* ---- lifecycle --------------------------------------------------------- */

void fpprt_init(const struct fpprt_opts *opts) {
  size_t heap_bytes = (opts && opts->heap_bytes) ? opts->heap_bytes
                                                 : 64 * 1024 * 1024;
  struct gc_options *o = gc_allocate_options();
  gc_options_set_int(o, GC_OPTION_HEAP_SIZE_POLICY, GC_HEAP_SIZE_FIXED);
  gc_options_set_size(o, GC_OPTION_HEAP_SIZE, heap_bytes);
  if (opts && opts->parallelism)
    gc_options_set_int(o, GC_OPTION_PARALLELISM, opts->parallelism);
  if (!gc_init(o, gc_empty_stack_addr(), &heap_, &mut_,
               GC_BASIC_STATS, &stats_)) {
    fprintf(stderr, "fpprt: gc_init failed\n");
    abort();
  }
  roots_.top = (struct fpprt_frame_intern **)&fpprt_top_frame;
  gc_mutator_set_roots(mut_, &roots_);

  /* the runtime's own types */
  fpprt_register_type(FPPRT_TID_EPHEMERON, (struct fpprt_type){
    0, FPPRT_KIND_EPHEMERON, 0, NULL, "$ephemeron" });
  fpprt_register_type(FPPRT_TID_REF_ARRAY, (struct fpprt_type){
    0, FPPRT_KIND_REF_ARRAY, 0, NULL, "$refarray" });
}

/* ---- allocation -------------------------------------------------------- */

fpprt_ref fpprt_alloc(uint32_t tid) {
  struct fpprt_type_intern *t = &fpprt_types_[tid];
  /* gc_allocate zeroes; the tag makes the object scannable, so it must be
   * written before any later allocation can trigger a collection */
  void *obj = gc_allocate(mut_, t->size, GC_ALLOCATION_TAGGED);
  ((uintptr_t *)obj)[0] = ((uintptr_t)tid << 1) | 1;
  return (fpprt_ref)obj;
}

fpprt_ref fpprt_alloc_array(uint32_t tid, size_t len) {
  struct fpprt_type_intern *t = &fpprt_types_[tid];
  size_t bytes = t->kind == FPPRT_KIND_REF_ARRAY
    ? 2 * sizeof(uintptr_t) + len * sizeof(uintptr_t)
    : fpprt_align_(2 * sizeof(uintptr_t) + len * (size_t)t->size);
  void *obj = gc_allocate(mut_, bytes, GC_ALLOCATION_TAGGED);
  ((uintptr_t *)obj)[0] = ((uintptr_t)tid << 1) | 1;
  ((uintptr_t *)obj)[1] = len;
  return (fpprt_ref)obj;
}

/* ---- writes ------------------------------------------------------------ */

void fpprt_write_ref(fpprt_ref o, uint32_t byteoff, fpprt_ref v) {
  fpprt_ref *loc = (fpprt_ref *)((char *)o + byteoff);
  uintptr_t tag = *(uintptr_t *)o;
  size_t sz = fpprt_object_size_(tag, (void *)o);
  gc_write_barrier(mut_, gc_ref((uintptr_t)o), sz,
                   gc_edge(loc), gc_ref((uintptr_t)v));
  *loc = v;
}

/* ---- weak references --------------------------------------------------- */

fpprt_ref fpprt_weak_new(fpprt_ref target) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = target;
  struct gc_ephemeron *e = gc_allocate_ephemeron(mut_);
  ((struct fpprt_header *)e)->tag = ((uintptr_t)FPPRT_TID_EPHEMERON << 1) | 1;
  gc_ephemeron_init(mut_, e, gc_ref((uintptr_t)f_slots[0]),
                    gc_ref((uintptr_t)f_slots[0]));
  FPPRT_LEAVE(f);
  return (fpprt_ref)e;
}

fpprt_ref fpprt_weak_get(fpprt_ref weak) {
  return (fpprt_ref)gc_ref_value(
      gc_ephemeron_value((struct gc_ephemeron *)weak));
}

/* ---- pinning ----------------------------------------------------------- */

int fpprt_can_pin(void) {
  return gc_can_pin_objects();
}

void fpprt_pin(fpprt_ref o) {
  if (!gc_can_pin_objects()) {
    fprintf(stderr, "fpprt: this collector cannot pin (build with mmc)\n");
    abort();
  }
  gc_pin_object(mut_, gc_ref((uintptr_t)o));
}

/* ---- control ----------------------------------------------------------- */

void fpprt_collect(void) { gc_collect(mut_, GC_COLLECTION_COMPACTING); }
void fpprt_safepoint(void) { gc_safepoint(mut_); }
size_t fpprt_allocated_bytes(void) { return gc_allocation_counter(heap_); }

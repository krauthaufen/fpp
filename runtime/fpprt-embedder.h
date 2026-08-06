/* The Whippet embedder API, implemented over fpprt's object model.
 * Included by the collector's translation units (see Makefile): everything
 * here must be `static inline` and cheap — gc_trace_object is the inner
 * loop of every collection.
 *
 * Tag word protocol (shared with fpprt.h):
 *   live:      (typeid << 1) | 1
 *   busy:      0                      (mid-forwarding, parallel copy)
 *   forwarded: new address            (aligned, bit 0 = 0)
 */
#ifndef FPPRT_EMBEDDER_H
#define FPPRT_EMBEDDER_H

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>

#include "gc-atomics.h"
#include "gc-config.h"
#include "gc-embedder-api.h"
#include "gc-ephemeron.h"

struct fpprt_type_intern {
  uint32_t size;
  uint32_t kind;
  uint32_t nrefs;
  const uint32_t *refoffs;
  const char *name;
};
/* the type table lives in fpprt.c */
extern struct fpprt_type_intern *fpprt_types_;
extern uint32_t fpprt_ntypes_;

#define FPPRT_EMB_KIND_STRUCT 0u
#define FPPRT_EMB_KIND_REF_ARRAY 1u
#define FPPRT_EMB_KIND_SCALAR_ARRAY 2u
#define FPPRT_EMB_KIND_EPHEMERON 3u

struct fpprt_header { uintptr_t tag; };

#define GC_EMBEDDER_EPHEMERON_HEADER struct fpprt_header header;
#define GC_EMBEDDER_FINALIZER_HEADER struct fpprt_header header;

static inline uintptr_t *fpprt_tag_word_(struct gc_ref ref) {
  return &((struct fpprt_header *)gc_ref_heap_object(ref))->tag;
}

static inline size_t fpprt_align_(size_t n) {
  return (n + sizeof(uintptr_t) - 1) & ~(sizeof(uintptr_t) - 1);
}

static inline size_t fpprt_object_size_(uintptr_t tag, void *obj) {
  struct fpprt_type_intern *t = &fpprt_types_[tag >> 1];
  switch (t->kind) {
  case FPPRT_EMB_KIND_STRUCT:
    return t->size;
  case FPPRT_EMB_KIND_REF_ARRAY:
    return 2 * sizeof(uintptr_t)
      + ((uintptr_t *)obj)[1] * sizeof(uintptr_t);
  case FPPRT_EMB_KIND_SCALAR_ARRAY:
    return fpprt_align_(2 * sizeof(uintptr_t)
                        + ((uintptr_t *)obj)[1] * (size_t)t->size);
  case FPPRT_EMB_KIND_EPHEMERON:
  default:
    return gc_ephemeron_size();
  }
}

static inline int gc_is_valid_conservative_ref_displacement(uintptr_t d) {
  return d == 0;
}
static inline size_t gc_finalizer_priority_count(void) { return 2; }

/* no second (extern) space in v0 */
static inline int gc_extern_space_visit(struct gc_extern_space *space,
                                        struct gc_ref ref) {
  GC_CRASH();
}
static inline void gc_extern_space_start_gc(struct gc_extern_space *space,
                                            int is_minor_gc) {}
static inline void gc_extern_space_finish_gc(struct gc_extern_space *space,
                                             int is_minor_gc) {}

/* FPP_GC_CENSUS builds: bytes traced per typeid, dumped by fpprt.c */
#ifdef FPP_GC_CENSUS
extern size_t fpprt_census_[4096];
#endif

static inline size_t gc_trace_object(struct gc_ref ref,
                                     void (*visit)(struct gc_edge edge,
                                                   struct gc_heap *heap,
                                                   void *visit_data),
                                     struct gc_heap *heap,
                                     void *trace_data) {
  void *obj = gc_ref_heap_object(ref);
  uintptr_t tag = *fpprt_tag_word_(ref);
  struct fpprt_type_intern *t = &fpprt_types_[tag >> 1];
#ifdef FPP_GC_CENSUS
  if ((tag >> 1) < 4096)
    fpprt_census_[tag >> 1] += fpprt_object_size_(tag, obj);
#endif
  switch (t->kind) {
  case FPPRT_EMB_KIND_STRUCT:
    if (visit)
      for (uint32_t i = 0; i < t->nrefs; i++) {
        uintptr_t *slot = (uintptr_t *)((char *)obj + t->refoffs[i]);
        /* a slot on the map can hold a TAGGED SCALAR (bit 0 set) where its
         * static type is generic — those are values, not edges */
        if (*slot && !(*slot & 1))
          visit(gc_edge(slot), heap, trace_data);
      }
    return t->size;
  case FPPRT_EMB_KIND_REF_ARRAY: {
    uintptr_t len = ((uintptr_t *)obj)[1];
    if (visit) {
      uintptr_t *elems = (uintptr_t *)obj + 2;
      for (uintptr_t i = 0; i < len; i++)
        if (elems[i] && !(elems[i] & 1))
          visit(gc_edge(&elems[i]), heap, trace_data);
    }
    return 2 * sizeof(uintptr_t) + len * sizeof(uintptr_t);
  }
  case FPPRT_EMB_KIND_SCALAR_ARRAY:
    return fpprt_align_(2 * sizeof(uintptr_t)
                        + ((uintptr_t *)obj)[1] * (size_t)t->size);
  case FPPRT_EMB_KIND_EPHEMERON:
    if (visit)
      gc_trace_ephemeron((struct gc_ephemeron *)obj, visit, heap, trace_data);
    return gc_ephemeron_size();
  default:
    GC_CRASH();
  }
}

/* ---- roots: the shadow stack ------------------------------------------- */

struct fpprt_frame_intern {
  struct fpprt_frame_intern *prev;
  uint32_t nslots;
  uintptr_t *slots;
};
struct gc_mutator_roots {
  struct fpprt_frame_intern **top; /* &fpprt_top_frame */
};
struct fpprt_static_range {
  uintptr_t *base;
  size_t n;
};
struct gc_heap_roots {
  uintptr_t *statics;              /* the idhash buckets */
  size_t nstatics;
  struct fpprt_static_range *ranges; /* compiler-registered global roots */
  size_t nranges;
};

static inline void gc_trace_mutator_roots(struct gc_mutator_roots *roots,
                                          void (*trace_edge)(struct gc_edge edge,
                                                             struct gc_heap *heap,
                                                             void *trace_data),
                                          struct gc_heap *heap,
                                          void *trace_data) {
  if (!roots) return;
  for (struct fpprt_frame_intern *f = *roots->top; f; f = f->prev)
    for (uint32_t i = 0; i < f->nslots; i++)
      if (f->slots[i] && !(f->slots[i] & 1))
        trace_edge(gc_edge(&f->slots[i]), heap, trace_data);
}

static inline void gc_trace_heap_roots(struct gc_heap_roots *roots,
                                       void (*trace_edge)(struct gc_edge edge,
                                                          struct gc_heap *heap,
                                                          void *trace_data),
                                       struct gc_heap *heap,
                                       void *trace_data) {
  if (!roots) return;
  for (size_t i = 0; i < roots->nstatics; i++)
    if (roots->statics[i] && !(roots->statics[i] & 1))
      trace_edge(gc_edge(&roots->statics[i]), heap, trace_data);
  for (size_t r = 0; r < roots->nranges; r++) {
    uintptr_t *base = roots->ranges[r].base;
    for (size_t i = 0; i < roots->ranges[r].n; i++)
      if (base[i] && !(base[i] & 1))
        trace_edge(gc_edge(&base[i]), heap, trace_data);
  }
}

static inline void
gc_trace_mutator_pinned_roots(struct gc_mutator_roots *roots,
                              void (*trace_pinned)(struct gc_ref ref,
                                                   struct gc_heap *heap,
                                                   void *data),
                              void (*trace_ambiguous)(uintptr_t start,
                                                      uintptr_t end,
                                                      int possibly_interior,
                                                      struct gc_heap *heap,
                                                      void *data),
                              struct gc_heap *heap,
                              void *data) {}
static inline void
gc_trace_heap_pinned_roots(struct gc_heap_roots *roots,
                           void (*trace_pinned)(struct gc_ref ref,
                                                struct gc_heap *heap,
                                                void *data),
                           void (*trace_ambiguous)(uintptr_t start,
                                                   uintptr_t end,
                                                   int possibly_interior,
                                                   struct gc_heap *heap,
                                                   void *data),
                           struct gc_heap *heap,
                           void *data) {}

/* ---- forwarding: the tag word, atomically when parallel ---------------- */

static inline uintptr_t gc_object_forwarded_nonatomic(struct gc_ref ref) {
  uintptr_t tag = *fpprt_tag_word_(ref);
  return (tag & 1) ? 0 : tag;
}
static inline void gc_object_forward_nonatomic(struct gc_ref ref,
                                               struct gc_ref new_ref) {
  *fpprt_tag_word_(ref) = gc_ref_value(new_ref);
}

static inline struct gc_atomic_forward
gc_atomic_forward_begin(struct gc_ref ref) {
  uintptr_t tag = gc_atomic_load(fpprt_tag_word_(ref));
  enum gc_forwarding_state state;
  if (tag == 0)
    state = GC_FORWARDING_STATE_BUSY;
  else if (tag & 1)
    state = GC_FORWARDING_STATE_NOT_FORWARDED;
  else
    state = GC_FORWARDING_STATE_FORWARDED;
  return (struct gc_atomic_forward){ ref, tag, state };
}

static inline int
gc_atomic_forward_retry_busy(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_BUSY);
  uintptr_t tag = gc_atomic_load(fpprt_tag_word_(fwd->ref));
  if (tag == 0)
    return 0;
  fwd->state = (tag & 1) ? GC_FORWARDING_STATE_NOT_FORWARDED
                         : GC_FORWARDING_STATE_FORWARDED;
  fwd->data = tag;
  return 1;
}

static inline void
gc_atomic_forward_acquire(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_NOT_FORWARDED);
  if (gc_atomic_cmpxchg_strong(fpprt_tag_word_(fwd->ref), &fwd->data, 0))
    fwd->state = GC_FORWARDING_STATE_ACQUIRED;
  else if (fwd->data == 0)
    fwd->state = GC_FORWARDING_STATE_BUSY;
  else {
    GC_ASSERT((fwd->data & 1) == 0);
    fwd->state = GC_FORWARDING_STATE_FORWARDED;
  }
}

static inline void
gc_atomic_forward_abort(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_ACQUIRED);
  gc_atomic_store(fpprt_tag_word_(fwd->ref), fwd->data);
  fwd->state = GC_FORWARDING_STATE_NOT_FORWARDED;
}

static inline size_t
gc_atomic_forward_object_size(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_ACQUIRED);
  return fpprt_object_size_(fwd->data, gc_ref_heap_object(fwd->ref));
}

static inline void
gc_atomic_forward_commit(struct gc_atomic_forward *fwd, struct gc_ref new_ref) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_ACQUIRED);
  *fpprt_tag_word_(new_ref) = fwd->data;
  gc_atomic_store(fpprt_tag_word_(fwd->ref), gc_ref_value(new_ref));
  fwd->state = GC_FORWARDING_STATE_FORWARDED;
}

static inline uintptr_t
gc_atomic_forward_address(struct gc_atomic_forward *fwd) {
  GC_ASSERT(fwd->state == GC_FORWARDING_STATE_FORWARDED);
  return fwd->data;
}

#endif /* FPPRT_EMBEDDER_H */

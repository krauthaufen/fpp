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
#include <stdio.h>
#include <stdlib.h>
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

/* DEBUG: see the range-root probe in gc_trace_heap_roots. Read once — a
 * collection walks two million slots and getenv per slot is not viable. */
static inline int fpprt_rootcheck_(void) {
#ifdef __wasm__
  static int v = -1;
  if (v < 0) { const char *s = getenv("FPPRT_ROOTCHECK"); v = (s && *s == '1'); }
  return v;
#else
  /* wasm only: a RANGE root is the wasm backend's shadow stack, and the probe
   * bounds its read against linear memory, which has no native counterpart */
  return 0;
#endif
}

#define FPPRT_EMB_KIND_STRUCT 0u
#define FPPRT_EMB_KIND_REF_ARRAY 1u
#define FPPRT_EMB_KIND_SCALAR_ARRAY 2u
#define FPPRT_EMB_KIND_EPHEMERON 3u
#define FPPRT_EMB_KIND_POD_ARRAY 4u
#define FPPRT_EMB_KIND_TAGGED 5u

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
  case FPPRT_EMB_KIND_POD_ARRAY:
    return fpprt_align_(2 * sizeof(uintptr_t)
                        + ((uintptr_t *)obj)[1] * (size_t)t->size);
  case FPPRT_EMB_KIND_TAGGED:
    return t->size;
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

/* the collector (mmc) reads this at init: uniform-word bodies are traced
 * conservatively, so evacuation must be off (see below) */
#define FPPRT_UNIFORM_CONSERVATIVE 1

/* set by mmc's gc_init: RANGE roots (the wasm shadow stack + root table) are
 * scanned CONSERVATIVELY through the pinned-roots channel — a raw scalar that
 * leaks onto the stack through a generic seam is then validated and skipped
 * instead of chased. semi leaves it 0 and keeps the precise range scan. */
extern int fpprt_ranges_ambiguous_;

/* The wasm-linear UNIFORM-WORD forms (FK_TAGGED objects and ref arrays) may
 * hold RAW scalars in slots whose static type is generic — a stamped int in a
 * canonical cell, a builtin-seq head. Tracing those bodies PRECISELY chased
 * the raw even word as a pointer (mmc's trace_edge crashed on it). They are
 * traced CONSERVATIVELY instead: each word is validated against the heap and
 * the target marked IN PLACE (never moved), so a raw int is skipped — or at
 * worst over-retains one object — and never rewritten. Returns the byte size
 * of the body to sweep conservatively, 0 for precisely-traced kinds. */
static inline size_t gc_object_conservative_body(struct gc_ref ref) {
  uintptr_t tag = *fpprt_tag_word_(ref);
  struct fpprt_type_intern *t = &fpprt_types_[tag >> 1];
  switch (t->kind) {
  case FPPRT_EMB_KIND_TAGGED:
    return t->size;
  case FPPRT_EMB_KIND_REF_ARRAY: {
    uintptr_t len = ((uintptr_t *)gc_ref_heap_object(ref))[1];
    return 2 * sizeof(uintptr_t) + len * sizeof(uintptr_t);
  }
  case FPPRT_EMB_KIND_STRUCT:
    // In the conservative (non-moving) configuration, trace FK_STRUCT bodies
    // CONSERVATIVELY too: a witness the compiler resolved WRONG (a raw scalar
    // slot marked as a pointer in refoffs) would otherwise be chased precisely
    // and crash. Validated conservative tracing skips it. This is only reached
    // when fpprt_ranges_ambiguous_ is set (see trace_one); under moving the
    // precise refoffs path runs and the witnesses must be exact.
    return t->size;
  default:
    return 0;
  }
}

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
  case FPPRT_EMB_KIND_TAGGED:
    /* the wasm-linear backend's uniform value model: every body word is
     * either a tagged scalar (bit 0 set) or a heap pointer (even). No
     * refoffs map — scan all words from `nrefs` (the first-payload index,
     * skipping the header and any raw metadata) and follow the even ones. */
    if (visit) {
      uintptr_t *w = (uintptr_t *)obj;
      uint32_t n = t->size / (uint32_t)sizeof(uintptr_t);
      for (uint32_t i = t->nrefs; i < n; i++)
        if (w[i] && !(w[i] & 1))
          visit(gc_edge(&w[i]), heap, trace_data);
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
  case FPPRT_EMB_KIND_POD_ARRAY: {
    uintptr_t len = ((uintptr_t *)obj)[1];
    if (visit) {
      char *elems = (char *)obj + 2 * sizeof(uintptr_t);
      for (uintptr_t i = 0; i < len; i++) {
        char *e = elems + i * (size_t)t->size;
        for (uint32_t r = 0; r < t->nrefs; r++) {
          uintptr_t *slot = (uintptr_t *)(e + t->refoffs[r]);
          if (*slot && !(*slot & 1))
            visit(gc_edge(slot), heap, trace_data);
        }
      }
    }
    return fpprt_align_(2 * sizeof(uintptr_t) + len * (size_t)t->size);
  }
  case FPPRT_EMB_KIND_EPHEMERON:
    if (visit)
      gc_trace_ephemeron((struct gc_ephemeron *)obj, visit, heap, trace_data);
    return gc_ephemeron_size();
  default:
    GC_CRASH();
  }
}

/* ---- roots: the shadow stack ------------------------------------------- */

struct fpprt_frame_pod_intern {
  char *base;
  uint32_t tid;
};
struct fpprt_frame_intern {
  struct fpprt_frame_intern *prev;
  uint32_t nslots;
  uintptr_t *slots;
  uint32_t npods;
  struct fpprt_frame_pod_intern *pods;
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
  for (struct fpprt_frame_intern *f = *roots->top; f; f = f->prev) {
    for (uint32_t i = 0; i < f->nslots; i++)
      if (f->slots[i] && !(f->slots[i] & 1))
        trace_edge(gc_edge(&f->slots[i]), heap, trace_data);
    /* stack structs: the type table's blob offsets apply to base */
    for (uint32_t i = 0; i < f->npods; i++) {
      if (!f->pods[i].base) continue;
      struct fpprt_type_intern *t = &fpprt_types_[f->pods[i].tid];
      for (uint32_t r = 0; r < t->nrefs; r++) {
        uintptr_t *slot =
            (uintptr_t *)(f->pods[i].base + t->refoffs[r]);
        if (*slot && !(*slot & 1))
          trace_edge(gc_edge(slot), heap, trace_data);
      }
    }
  }
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
    /* DEBUG (FPPRT_ROOTCHECK=1): a range root that is not a plausible object
     * start — its header word must be an odd (tid<<1)|1 for a registered tid.
     * The wasm shadow stack is a RANGE, so a slot holding a raw scalar or a
     * non-heap address is traced as an edge and faults deep inside the
     * collector, where the backtrace names nothing. This prints the slot
     * INDEX (= shadow-stack depth) and the value before that happens. */
#ifdef __wasm__
    if (fpprt_rootcheck_())
      for (size_t i = 0; i < roots->ranges[r].n; i++) {
        uintptr_t v = base[i];
        if (!v || (v & 1)) continue;
        uintptr_t lim = (uintptr_t)__builtin_wasm_memory_size(0) * 65536u;
        uintptr_t hdr = 0;
        if (v + sizeof(uintptr_t) <= lim) {
          hdr = *(uintptr_t *)v;
          if ((hdr & 1) && (hdr >> 1) < fpprt_ntypes_) continue;
        }
        fprintf(stderr,
                "BADROOT range=%zu slot=%zu at=0x%08x base=0x%08x n=%zu "
                "val=0x%08x hdr=0x%08x\n",
                r, i, (unsigned)(uintptr_t)&base[i], (unsigned)(uintptr_t)base,
                roots->ranges[r].n, (unsigned)v, (unsigned)hdr);
        abort();
      }
#endif
    if (!fpprt_ranges_ambiguous_)
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
                           void *data) {
  /* mmc: the RANGE roots, conservatively — validated + pinned, raw skipped */
  if (fpprt_ranges_ambiguous_ && roots)
    for (size_t r = 0; r < roots->nranges; r++) {
      uintptr_t lo = (uintptr_t)roots->ranges[r].base;
      trace_ambiguous(lo, lo + roots->ranges[r].n * sizeof(uintptr_t), 0,
                      heap, data);
    }
}

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

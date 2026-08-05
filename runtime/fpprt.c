/* fpprt implementation over the Whippet gc-api. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "gc-api.h"
#include "gc-allocate.h"
#include "gc-barrier.h"
#include "gc-safepoint.h"
#include "gc-ephemeron.h"
#include "gc-event-listener.h"
#include "gc-null-event-listener.h"

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
static struct gc_heap_roots heap_roots_;

/* ---- identity-hash table ----------------------------------------------
 * Buckets of ephemeron chains, keyed by object ADDRESS. Addresses go stale
 * whenever the collector moves objects, so the whole table rehashes in the
 * restarting-mutators window — the world is still stopped, every surviving
 * object sits at its final address, and nothing here allocates. Dead-key
 * ephemerons are dropped during that same walk: the table never pins its
 * keys and never leaks its entries. */
static struct gc_ephemeron **idh_buckets_;
static size_t idh_nbuckets_;
static size_t idh_count_;
static uintptr_t idh_next_ = 0x9e3779b97f4a7c15ull; /* never 0 */

static size_t idh_bucket_of_(uintptr_t addr, size_t nbuckets) {
  uintptr_t h = addr >> 4;
  h ^= h >> 17; h *= 0xed5ad4bb; h ^= h >> 11;
  return (size_t)h & (nbuckets - 1);
}

static void idh_publish_roots_(void) {
  heap_roots_.statics = (uintptr_t *)idh_buckets_;
  heap_roots_.nstatics = idh_nbuckets_;
}

/* rebuild into `nbuckets` buckets from the chains in `old`; entries whose
 * key died are dropped. malloc only — callable with the world stopped. */
static void idh_rebuild_(struct gc_ephemeron **old, size_t nold,
                         size_t nbuckets) {
  struct gc_ephemeron **fresh = calloc(nbuckets, sizeof(*fresh));
  if (!fresh) abort();
  size_t live = 0;
  for (size_t i = 0; i < nold; i++) {
    struct gc_ephemeron *e = old[i] ? gc_ephemeron_chain_head(&old[i]) : NULL;
    while (e) {
      struct gc_ephemeron *next = gc_ephemeron_chain_next(e);
      uintptr_t key = gc_ref_value(gc_ephemeron_key(e));
      if (key) {
        size_t b = idh_bucket_of_(key, nbuckets);
        gc_ephemeron_chain_push(&fresh[b], e);
        live++;
      }
      e = next;
    }
  }
  free(old);
  idh_buckets_ = fresh;
  idh_nbuckets_ = nbuckets;
  idh_count_ = live;
  idh_publish_roots_();
}

static void idh_on_restarting_mutators_(void *data) {
  if (idh_count_)
    idh_rebuild_(idh_buckets_, idh_nbuckets_, idh_nbuckets_);
}

#define FPPRT_EVENT_LISTENER                                   \
  ((struct gc_event_listener) {                                \
    gc_null_event_listener_init,                               \
    gc_null_event_listener_requesting_stop,                    \
    gc_null_event_listener_waiting_for_stop,                   \
    gc_null_event_listener_mutators_stopped,                   \
    gc_null_event_listener_prepare_gc,                         \
    gc_null_event_listener_roots_traced,                       \
    gc_null_event_listener_heap_traced,                        \
    gc_null_event_listener_ephemerons_traced,                  \
    gc_null_event_listener_finalizers_traced,                  \
    idh_on_restarting_mutators_,                               \
    gc_null_event_listener_mutator_added,                      \
    gc_null_event_listener_mutator_cause_gc,                   \
    gc_null_event_listener_mutator_stopping,                   \
    gc_null_event_listener_mutator_stopped,                    \
    gc_null_event_listener_mutator_restarted,                  \
    gc_null_event_listener_mutator_removed,                    \
    gc_null_event_listener_heap_resized,                       \
    gc_null_event_listener_live_data_size,                     \
  })

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
                                                 : 16 * 1024 * 1024;
  struct gc_options *o = gc_allocate_options();
  gc_options_set_int(o, GC_OPTION_HEAP_SIZE_POLICY, GC_HEAP_SIZE_GROWABLE);
  gc_options_set_size(o, GC_OPTION_HEAP_SIZE, heap_bytes);
  if (opts && opts->max_heap_bytes)
    gc_options_set_size(o, GC_OPTION_MAXIMUM_HEAP_SIZE, opts->max_heap_bytes);
  if (opts && opts->parallelism)
    gc_options_set_int(o, GC_OPTION_PARALLELISM, opts->parallelism);
  if (!gc_init(o, gc_empty_stack_addr(), &heap_, &mut_,
               FPPRT_EVENT_LISTENER, NULL)) {
    fprintf(stderr, "fpprt: gc_init failed\n");
    abort();
  }
  roots_.top = (struct fpprt_frame_intern **)&fpprt_top_frame;
  gc_mutator_set_roots(mut_, &roots_);
  idh_buckets_ = calloc(64, sizeof(*idh_buckets_));
  if (!idh_buckets_) abort();
  idh_nbuckets_ = 64;
  idh_publish_roots_();
  gc_heap_set_roots(heap_, &heap_roots_);

  /* the runtime's own types */
  fpprt_register_type(FPPRT_TID_EPHEMERON, (struct fpprt_type){
    0, FPPRT_KIND_EPHEMERON, 0, NULL, "$ephemeron" });
  fpprt_register_type(FPPRT_TID_REF_ARRAY, (struct fpprt_type){
    0, FPPRT_KIND_REF_ARRAY, 0, NULL, "$refarray" });
  fpprt_register_type(FPPRT_TID_HASHBOX, (struct fpprt_type){
    sizeof(uintptr_t), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "$hashbox" });
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

/* ---- identity hash ----------------------------------------------------- */

uintptr_t fpprt_idhash(fpprt_ref o) {
  size_t b = idh_bucket_of_((uintptr_t)o, idh_nbuckets_);
  for (struct gc_ephemeron *e = idh_buckets_[b]
         ? gc_ephemeron_chain_head(&idh_buckets_[b]) : NULL;
       e; e = gc_ephemeron_chain_next(e)) {
    if (gc_ref_value(gc_ephemeron_key(e)) == (uintptr_t)o) {
      fpprt_ref box = (fpprt_ref)gc_ref_value(gc_ephemeron_value(e));
      return *(uintptr_t *)fpprt_elems(box);
    }
  }
  /* first ask: assign. Allocations below can collect, which MOVES o and
   * rehashes the table — hold o in a frame and look the bucket up again
   * before inserting. */
  FPPRT_FRAME(f, 2);
  f_slots[0] = o;
  idh_next_ = idh_next_ * 0xd1342543de82ef95ull + 0x2545f4914f6cdd1dull;
  uintptr_t h = idh_next_ >> 3;
  if (!h) h = 1;
  fpprt_ref box = fpprt_alloc_array(FPPRT_TID_HASHBOX, 1);
  *(uintptr_t *)fpprt_elems(box) = h;
  f_slots[1] = box;
  struct gc_ephemeron *e = gc_allocate_ephemeron(mut_);
  ((struct fpprt_header *)e)->tag = ((uintptr_t)FPPRT_TID_EPHEMERON << 1) | 1;
  gc_ephemeron_init(mut_, e, gc_ref((uintptr_t)f_slots[0]),
                    gc_ref((uintptr_t)f_slots[1]));
  b = idh_bucket_of_((uintptr_t)f_slots[0], idh_nbuckets_);
  gc_ephemeron_chain_push(&idh_buckets_[b], e);
  idh_count_++;
  FPPRT_LEAVE(f);
  if (idh_count_ > idh_nbuckets_ * 4)
    idh_rebuild_(idh_buckets_, idh_nbuckets_, idh_nbuckets_ * 2);
  return h;
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

/* fpprt implementation over the Whippet gc-api. */
#include <pthread.h>
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

_Thread_local struct fpprt_frame *fpprt_top_frame = NULL;
static int fpprt_sp_zero_ = 0;
_Thread_local int *fpprt_sp_flag_ = &fpprt_sp_zero_;

static struct gc_heap *heap_;
static _Thread_local struct gc_mutator *mut_;
static _Thread_local struct gc_mutator_roots roots_;
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

static int gc_log_ = -1;
static unsigned gc_count_ = 0;
static void log_prepare_gc_(void *data, enum gc_collection_kind kind,
                            uint64_t counter) {
  if (gc_log_ < 0) {
    const char *e = getenv("FPP_GC_LOG");
    gc_log_ = e && e[0] == '1';
  }
  gc_count_++;
  if (gc_log_ && (gc_count_ & 0xf) == 0)
    fprintf(stderr, "[gc %u allocated=%llu MB]\n", gc_count_,
            (unsigned long long)(counter >> 20));
}
#ifdef FPP_GC_CENSUS
size_t fpprt_census_[4096];
#endif

static void log_live_(void *data, size_t size) {
#ifdef FPP_GC_CENSUS
  if (gc_log_ > 0 && (gc_count_ & 0xf) == 0) {
    for (int r = 0; r < 5; r++) {
      size_t best = 0; uint32_t bi = 0;
      for (uint32_t i = 0; i < 4096; i++)
        if (fpprt_census_[i] > best) { best = fpprt_census_[i]; bi = i; }
      if (!best) break;
      fprintf(stderr, "  [census %s tid=%u %zu MB]\n",
              fpprt_type_name(bi), bi, best >> 20);
      fpprt_census_[bi] = 0;
    }
    memset(fpprt_census_, 0, sizeof fpprt_census_);
  } else
    memset(fpprt_census_, 0, sizeof fpprt_census_);
#endif
  if (gc_log_ > 0 && (gc_count_ & 0xf) == 0) {
    size_t nframes = 0, nslots = 0;
    for (struct fpprt_frame *fr = fpprt_top_frame; fr; fr = fr->prev) {
      nframes++;
      nslots += fr->nslots;
    }
    fprintf(stderr, "[gc %u live=%zu MB idh=%zu frames=%zu slots=%zu]\n",
            gc_count_, size >> 20, idh_count_, nframes, nslots);
  }
}

#define FPPRT_EVENT_LISTENER                                   \
  ((struct gc_event_listener) {                                \
    gc_null_event_listener_init,                               \
    gc_null_event_listener_requesting_stop,                    \
    gc_null_event_listener_waiting_for_stop,                   \
    gc_null_event_listener_mutators_stopped,                   \
    log_prepare_gc_,                                           \
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
    log_live_,                                                 \
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

const char *fpprt_type_name(uint32_t tid) {
  if (tid < fpprt_ntypes_ && fpprt_types_[tid].name) return fpprt_types_[tid].name;
  return "?";
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
  if (gc_cooperative_safepoint_kind() != GC_COOPERATIVE_SAFEPOINT_NONE)
    fpprt_sp_flag_ = gc_safepoint_flag_loc(mut_);
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

fpprt_ref fpprt_eph_new(fpprt_ref key, fpprt_ref value) {
  FPPRT_FRAME(f, 2);
  f_slots[0] = key;
  f_slots[1] = value;
  struct gc_ephemeron *e = gc_allocate_ephemeron(mut_);
  ((struct fpprt_header *)e)->tag = ((uintptr_t)FPPRT_TID_EPHEMERON << 1) | 1;
  gc_ephemeron_init(mut_, e, gc_ref((uintptr_t)f_slots[0]),
                    gc_ref((uintptr_t)f_slots[1]));
  FPPRT_LEAVE(f);
  return (fpprt_ref)e;
}

fpprt_ref fpprt_eph_key(fpprt_ref e) {
  return (fpprt_ref)gc_ref_value(
      gc_ephemeron_key((struct gc_ephemeron *)e));
}

fpprt_ref fpprt_eph_value(fpprt_ref e) {
  return (fpprt_ref)gc_ref_value(
      gc_ephemeron_value((struct gc_ephemeron *)e));
}

/* ---- static roots ------------------------------------------------------ */

void fpprt_add_static_roots(fpprt_ref *base, size_t n) {
  size_t i = heap_roots_.nranges++;
  heap_roots_.ranges = realloc(heap_roots_.ranges,
                               heap_roots_.nranges
                               * sizeof(*heap_roots_.ranges));
  if (!heap_roots_.ranges) abort();
  heap_roots_.ranges[i] = (struct fpprt_static_range){ base, n };
}

/* ---- identity hash ----------------------------------------------------- */

/* idhash is SHARED state across mutators: one lock around bucket access.
 * The insert path allocates (which may collect and rehash), so the lock is
 * released before allocation and the bucket re-searched after. */
static pthread_mutex_t idh_lock_ = PTHREAD_MUTEX_INITIALIZER;

static uintptr_t idh_find_(fpprt_ref o) {
  size_t b = idh_bucket_of_((uintptr_t)o, idh_nbuckets_);
  for (struct gc_ephemeron *e = idh_buckets_[b]
         ? gc_ephemeron_chain_head(&idh_buckets_[b]) : NULL;
       e; e = gc_ephemeron_chain_next(e)) {
    if (gc_ref_value(gc_ephemeron_key(e)) == (uintptr_t)o) {
      fpprt_ref box = (fpprt_ref)gc_ref_value(gc_ephemeron_value(e));
      return *(uintptr_t *)fpprt_elems(box);
    }
  }
  return 0;
}

uintptr_t fpprt_idhash(fpprt_ref o) {
  pthread_mutex_lock(&idh_lock_);
  uintptr_t found = idh_find_(o);
  pthread_mutex_unlock(&idh_lock_);
  if (found) return found;
  /* first ask: assign. The allocations below can collect, which MOVES o
   * and rehashes the table — hold o in a frame, and NEVER hold the lock
   * across an allocation (the holder would block a collection another
   * thread started). Re-search under the lock before inserting: a racing
   * thread may have assigned meanwhile, and ITS hash must win. */
  FPPRT_FRAME(f, 2);
  f_slots[0] = o;
  fpprt_ref box = fpprt_alloc_array(FPPRT_TID_HASHBOX, 1);
  f_slots[1] = box;
  struct gc_ephemeron *e = gc_allocate_ephemeron(mut_);
  ((struct fpprt_header *)e)->tag = ((uintptr_t)FPPRT_TID_EPHEMERON << 1) | 1;
  gc_ephemeron_init(mut_, e, gc_ref((uintptr_t)f_slots[0]),
                    gc_ref((uintptr_t)f_slots[1]));
  pthread_mutex_lock(&idh_lock_);
  uintptr_t h = idh_find_(f_slots[0]);
  if (!h) {
    idh_next_ = idh_next_ * 0xd1342543de82ef95ull + 0x2545f4914f6cdd1dull;
    h = idh_next_ >> 3;
    if (!h) h = 1;
    *(uintptr_t *)fpprt_elems(f_slots[1]) = h;
    size_t b = idh_bucket_of_((uintptr_t)f_slots[0], idh_nbuckets_);
    gc_ephemeron_chain_push(&idh_buckets_[b], e);
    idh_count_++;
    if (idh_count_ > idh_nbuckets_ * 4)
      idh_rebuild_(idh_buckets_, idh_nbuckets_, idh_nbuckets_ * 2);
  }
  pthread_mutex_unlock(&idh_lock_);
  FPPRT_LEAVE(f);
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

/* ---- threads: one GC mutator per OS thread ----------------------------- */

void fpprt_thread_attach(void) {
  if (mut_) return;
  mut_ = gc_init_for_thread(gc_empty_stack_addr(), heap_);
  roots_.top = (struct fpprt_frame_intern **)&fpprt_top_frame;
  gc_mutator_set_roots(mut_, &roots_);
  if (gc_cooperative_safepoint_kind() != GC_COOPERATIVE_SAFEPOINT_NONE)
    fpprt_sp_flag_ = gc_safepoint_flag_loc(mut_);
}

void fpprt_thread_detach(void) {
  if (!mut_) return;
  gc_finish_for_thread(mut_);
  mut_ = NULL;
}

/* park while BLOCKED outside GC'd code (a barrier or lock wait): the
 * collector may run without this thread reaching a safepoint */
void fpprt_thread_park(void) { gc_deactivate(mut_); }
void fpprt_thread_unpark(void) { gc_reactivate(mut_); }
size_t fpprt_allocated_bytes(void) { return gc_allocation_counter(heap_); }

/* ---- the worker pool ---------------------------------------------------
 * Fixed, sized to the hardware, created at first dispatch. The unit of
 * work is a CHUNK [lo,hi) of a dense index range; workers grab chunks off
 * one atomic cursor (deques arrive with the phase engine — one cursor is
 * enough while every dispatch is a single phase). The caller participates
 * and PARKS while waiting, so collection never stalls on a joining
 * thread; workers park between dispatches for the same reason. */

#include <unistd.h>
#include <sched.h>

#define FPP_POOL_MAX 16

typedef struct {
  fpp_pool_kernel kernel;
  void *env;
  int n;
  int chunk;
} fpp_dispatch;

static pthread_t pool_threads_[FPP_POOL_MAX];
static int pool_size_ = 0;               /* workers, excluding the caller */
static int pool_started_ = 0;
static pthread_mutex_t pool_mu_ = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t pool_go_ = PTHREAD_COND_INITIALIZER;
static pthread_cond_t pool_done_ = PTHREAD_COND_INITIALIZER;
static fpp_dispatch pool_job_;
static unsigned long pool_gen_ = 0;      /* bumps per dispatch            */
static int pool_cursor_ = 0;             /* next chunk start              */
static int pool_active_ = 0;             /* threads still in the dispatch */

static void pool_work_(void) {
  for (;;) {
    int lo;
    pthread_mutex_lock(&pool_mu_);
    lo = pool_cursor_;
    pool_cursor_ += pool_job_.chunk;
    pthread_mutex_unlock(&pool_mu_);
    if (lo >= pool_job_.n) return;
    int hi = lo + pool_job_.chunk;
    if (hi > pool_job_.n) hi = pool_job_.n;
    pool_job_.kernel(pool_job_.env, lo, hi);
    fpprt_safepoint();
  }
}

static void *pool_main_(void *arg) {
  (void)arg;
  fpprt_thread_attach();
  unsigned long seen = 0;
  for (;;) {
    fpprt_thread_park();
    pthread_mutex_lock(&pool_mu_);
    while (pool_gen_ == seen) pthread_cond_wait(&pool_go_, &pool_mu_);
    seen = pool_gen_;
    pthread_mutex_unlock(&pool_mu_);
    fpprt_thread_unpark();
    pool_work_();
    pthread_mutex_lock(&pool_mu_);
    pool_active_--;
    if (pool_active_ == 0) pthread_cond_signal(&pool_done_);
    pthread_mutex_unlock(&pool_mu_);
  }
  return NULL;
}

int fpp_pool_size(void) {
  long c = sysconf(_SC_NPROCESSORS_ONLN);
  int p = (int)c - 1;
  if (p < 1) p = 1;
  if (p > FPP_POOL_MAX) p = FPP_POOL_MAX;
  return p;
}

void fpp_pool_dispatch(int n, int chunk, fpp_pool_kernel kernel, void *env) {
  if (n <= 0) return;
  if (chunk <= 0) chunk = 1;
  if (!pool_started_) {
    pool_started_ = 1;
    pool_size_ = fpp_pool_size();
    for (int i = 0; i < pool_size_; i++)
      pthread_create(&pool_threads_[i], NULL, pool_main_, NULL);
  }
  pthread_mutex_lock(&pool_mu_);
  pool_job_.kernel = kernel;
  pool_job_.env = env;
  pool_job_.n = n;
  pool_job_.chunk = chunk;
  pool_cursor_ = 0;
  pool_active_ = pool_size_ + 1;
  pool_gen_++;
  pthread_cond_broadcast(&pool_go_);
  pthread_mutex_unlock(&pool_mu_);
  pool_work_();
  pthread_mutex_lock(&pool_mu_);
  pool_active_--;
  if (pool_active_ == 0) pthread_cond_signal(&pool_done_);
  fpprt_thread_park();
  while (pool_active_ != 0) pthread_cond_wait(&pool_done_, &pool_mu_);
  pthread_mutex_unlock(&pool_mu_);
  fpprt_thread_unpark();
}

/* ---- phased dispatch: groups × phases, barrier-as-retirement -----------
 * The index range splits into GROUPS (dense, equal slices); each group
 * runs PHASES in order, and a group's phase p+1 becomes runnable the
 * moment the last chunk of ITS phase p retires — group barriers never
 * join the world, so independent groups pipeline like GPU workgroups.
 * Workers never block at a barrier: they scan for any runnable chunk
 * (starting at a home group for locality — crude stealing) and park only
 * when nothing anywhere is runnable. */

typedef struct {
  int lo, hi;          /* the group's slice of [0, n)      */
  int phase;           /* current phase                    */
  int cursor;          /* next chunk start within the slice */
  int live;            /* chunks not yet retired this phase */
} fpp_group;

#define FPP_GROUP_MAX 256

static fpp_group phased_groups_[FPP_GROUP_MAX];
static int phased_ngroups_ = 0;
static int phased_phases_ = 0;
static int phased_chunk_ = 0;
static int phased_done_ = 0;         /* groups fully finished */
static fpp_phase_kernel phased_kernel_;
static void *phased_env_;

static int phased_chunks_of_(fpp_group *g) {
  int len = g->hi - g->lo;
  return (len + phased_chunk_ - 1) / phased_chunk_;
}

/* grab one runnable chunk; returns phase/lo/hi through the pointers.
 * 0 = nothing runnable ANYWHERE right now, -1 = the whole dispatch is
 * finished. Caller holds pool_mu_. */
static int phased_grab_(int home, int *phase, int *lo, int *hi) {
  if (phased_done_ == phased_ngroups_) return -1;
  for (int k = 0; k < phased_ngroups_; k++) {
    fpp_group *g = &phased_groups_[(home + k) % phased_ngroups_];
    if (g->phase >= phased_phases_) continue;
    if (g->cursor < g->hi) {
      *phase = g->phase;
      *lo = g->cursor;
      *hi = g->cursor + phased_chunk_;
      if (*hi > g->hi) *hi = g->hi;
      g->cursor = *hi;
      return 1;
    }
  }
  return 0;
}

static void phased_retire_(int home) {
  fpp_group *g = &phased_groups_[home];
  g->live--;
  if (g->live == 0) {
    g->phase++;
    if (g->phase >= phased_phases_) phased_done_++;
    else {
      g->cursor = g->lo;
      g->live = phased_chunks_of_(g);
    }
  }
}

static void phased_work_(int home) {
  for (;;) {
    int phase, lo, hi, r;
    pthread_mutex_lock(&pool_mu_);
    r = phased_grab_(home, &phase, &lo, &hi);
    pthread_mutex_unlock(&pool_mu_);
    if (r == -1) return;
    if (r == 0) {
      /* nothing runnable: another group's phase must retire first.
       * Yield rather than spin hot; the retirement that unblocks us is
       * chunks away, not milliseconds. */
      fpprt_safepoint();
      sched_yield();
      continue;
    }
    phased_kernel_(phased_env_, phase, lo, hi);
    fpprt_safepoint();
    pthread_mutex_lock(&pool_mu_);
    /* which group did [lo,hi) belong to — recompute from lo */
    for (int gi = 0; gi < phased_ngroups_; gi++)
      if (lo >= phased_groups_[gi].lo && lo < phased_groups_[gi].hi) {
        phased_retire_(gi);
        break;
      }
    pthread_mutex_unlock(&pool_mu_);
  }
}

/* the pool's generic job hook: a phased dispatch rides the same workers */
static void phased_pool_kernel_(void *env, int lo, int hi) {
  (void)env; (void)hi;
  phased_work_(lo);   /* lo doubles as the worker's home group */
}

void fpp_pool_dispatch_phased(int n, int chunk, int groups, int phases,
                              fpp_phase_kernel kernel, void *env) {
  if (n <= 0 || phases <= 0) return;
  if (groups <= 0) groups = 1;
  if (groups > FPP_GROUP_MAX) groups = FPP_GROUP_MAX;
  if (groups > n) groups = n;
  if (chunk <= 0) {
    chunk = n / (groups * 8) + 1;
    if (chunk < 1) chunk = 1;
  }
  phased_kernel_ = kernel;
  phased_env_ = env;
  phased_chunk_ = chunk;
  phased_ngroups_ = groups;
  phased_phases_ = phases;
  phased_done_ = 0;
  int base = n / groups, rem = n % groups, at = 0;
  for (int g = 0; g < groups; g++) {
    int len = base + (g < rem ? 1 : 0);
    phased_groups_[g].lo = at;
    phased_groups_[g].hi = at + len;
    phased_groups_[g].phase = 0;
    phased_groups_[g].cursor = at;
    phased_groups_[g].live = phased_chunks_of_(&phased_groups_[g]);
    at += len;
  }
  /* every pool thread (plus the caller) becomes a phased worker with a
   * distinct home group; the plain dispatch machinery provides the fan
   * out and the join */
  int workers = pool_started_ ? pool_size_ + 1 : fpp_pool_size() + 1;
  fpp_pool_dispatch(workers, 1, phased_pool_kernel_, NULL);
}

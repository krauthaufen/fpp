/* Multi-mutator smoke: N threads attach, allocate under pressure while the
 * collector moves things, park around a barrier wait, verify every list
 * survived intact. This is the runtime-side gate for the threading arc —
 * it must pass before any F++-level parallelism exists. Run on pcc and mmc
 * (semi is the single-mutator shakeout collector). */
#include <inttypes.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>

#include "../fpprt.h"

#define CHECK(x) do { if (!(x)) { printf("CHECK FAILED: %s\n", #x); ok = 0; } } while (0)

#define TID_CONS FPPRT_TID_FIRST
static const uint32_t cons_refs[] = { 2 * sizeof(uintptr_t) };
#define CONS_CDR (2 * sizeof(uintptr_t))
#define CONS_VAL (1 * sizeof(uintptr_t))

#define NTHREADS 6
#define PER_LIST 20000
#define ROUNDS 8

static int ok = 1;
static pthread_barrier_t bar;

static uintptr_t cons_val(fpprt_ref c) {
  return *(uintptr_t *)((char *)c + CONS_VAL);
}

static fpprt_ref build(size_t seed) {
  FPPRT_FRAME(f, 1);
  for (size_t i = 0; i < PER_LIST; i++) {
    fpprt_ref c = fpprt_alloc(TID_CONS);
    *(uintptr_t *)((char *)c + CONS_VAL) = seed + i;
    fpprt_write_ref(c, CONS_CDR, f_slots[0]);
    f_slots[0] = c;
  }
  fpprt_ref head = f_slots[0];
  FPPRT_LEAVE(f);
  return head;
}

static uintptr_t total(fpprt_ref head) {
  uintptr_t s = 0;
  for (fpprt_ref c = head; c; c = fpprt_read_ref(c, CONS_CDR))
    s += cons_val(c);
  return s;
}

static void *worker(void *arg) {
  uintptr_t tid = (uintptr_t)arg;
  fpprt_thread_attach();
  FPPRT_FRAME(f, 1);
  for (int round = 0; round < ROUNDS; round++) {
    uintptr_t seed = tid * 1000000 + round;
    f_slots[0] = build(seed);
    uintptr_t want =
        (uintptr_t)PER_LIST * seed
        + (uintptr_t)PER_LIST * (PER_LIST - 1) / 2;
    CHECK(total(f_slots[0]) == want);
    /* churn: garbage between rounds, some safepoint polling */
    for (int i = 0; i < 50; i++) {
      build(i);
      fpprt_safepoint();
    }
    CHECK(total(f_slots[0]) == want);
    /* a BLOCKING wait must park, or another thread's GC stalls forever */
    fpprt_thread_park();
    pthread_barrier_wait(&bar);
    fpprt_thread_unpark();
  }
  FPPRT_LEAVE(f);
  fpprt_thread_detach();
  return NULL;
}

int main(void) {
  fpprt_init(NULL);
  fpprt_register_type(TID_CONS, (struct fpprt_type){
    4 * sizeof(uintptr_t), FPPRT_KIND_STRUCT, 1, cons_refs, "cons" });
  pthread_barrier_init(&bar, NULL, NTHREADS);
  pthread_t ts[NTHREADS];
  for (uintptr_t i = 0; i < NTHREADS; i++)
    pthread_create(&ts[i], NULL, worker, (void *)i);
  /* the MAIN mutator keeps allocating and forcing collections meanwhile */
  for (int i = 0; i < 30; i++) {
    build(7);
    fpprt_collect();
  }
  /* joining BLOCKS: park, or a worker-triggered collection waits forever
   * for the main mutator to reach a safepoint */
  fpprt_thread_park();
  for (int i = 0; i < NTHREADS; i++)
    pthread_join(ts[i], NULL);
  fpprt_thread_unpark();
  if (ok) printf("threads OK (%d mutators, %d rounds)\n", NTHREADS, ROUNDS);
  return ok ? 0 : 1;
}

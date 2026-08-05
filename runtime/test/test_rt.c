/* fpprt v0 smoke: allocation under pressure, precise moving collection,
 * ref arrays, weak refs dying on time, pinning where the collector has it.
 * Run under `semi` first: it moves every object every collection, so a
 * missed root or a bad pointer map dies HERE, not in a stamped clone three
 * layers up. */
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#include "../fpprt.h"

#define CHECK(x) do { if (!(x)) { printf("CHECK FAILED: %s\n", #x); return 1; } } while (0)

/* type: cons { tag; car(ref); cdr(ref); val(scalar) } */
#define TID_CONS FPPRT_TID_FIRST
#define TID_F64S (FPPRT_TID_FIRST + 1)
static const uint32_t cons_refs[] = { 1 * sizeof(uintptr_t),
                                      2 * sizeof(uintptr_t) };
#define CONS_CAR (1 * sizeof(uintptr_t))
#define CONS_CDR (2 * sizeof(uintptr_t))
#define CONS_VAL (3 * sizeof(uintptr_t))

static uintptr_t cons_val(fpprt_ref c) {
  return *(uintptr_t *)((char *)c + CONS_VAL);
}
static void set_cons_val(fpprt_ref c, uintptr_t v) {
  *(uintptr_t *)((char *)c + CONS_VAL) = v;
}

static fpprt_ref make_list(size_t n) {
  FPPRT_FRAME(f, 1);
  for (size_t i = 0; i < n; i++) {
    fpprt_ref c = fpprt_alloc(TID_CONS);
    set_cons_val(c, i);
    fpprt_write_ref(c, CONS_CDR, f_slots[0]);
    f_slots[0] = c;
  }
  fpprt_ref head = f_slots[0];
  FPPRT_LEAVE(f);
  return head;
}

static size_t list_sum(fpprt_ref l) {
  size_t s = 0;
  for (; l; l = fpprt_read_ref(l, CONS_CDR)) s += cons_val(l);
  return s;
}

int main(void) {
  fpprt_init(&(struct fpprt_opts){ .heap_bytes = 16 * 1024 * 1024 });
  fpprt_register_type(TID_CONS, (struct fpprt_type){
    4 * sizeof(uintptr_t), FPPRT_KIND_STRUCT, 2, cons_refs, "cons" });
  fpprt_register_type(TID_F64S, (struct fpprt_type){
    sizeof(double), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "f64[]" });

  /* 1: live list survives explicit compacting collections, with garbage
   * churn big enough to force many cycles in a 16M heap */
  FPPRT_FRAME(f, 4);
  f_slots[0] = make_list(1000);          /* sum 0..999 = 499500 */
  for (int r = 0; r < 50; r++) {
    fpprt_ref junk = make_list(10000);
    (void)junk;
    if (r % 10 == 0) fpprt_collect();
    CHECK(list_sum(f_slots[0]) == 499500);
  }
  printf("list %zu\n", list_sum(f_slots[0]));

  /* 2: ref array holds across collection; scalar array data survives */
  f_slots[1] = fpprt_alloc_array(FPPRT_TID_REF_ARRAY, 64);
  for (int i = 0; i < 64; i++) {
    fpprt_ref c = fpprt_alloc(TID_CONS);
    set_cons_val(c, (uintptr_t)i * 3);
    fpprt_write_ref(f_slots[1], (uint32_t)(2 + i) * sizeof(uintptr_t), c);
  }
  f_slots[2] = fpprt_alloc_array(TID_F64S, 1000);
  { double *xs = fpprt_elems(f_slots[2]);
    for (int i = 0; i < 1000; i++) xs[i] = i * 0.5; }
  fpprt_collect();
  { size_t s = 0;
    for (int i = 0; i < 64; i++)
      s += cons_val(fpprt_read_ref(f_slots[1],
                                   (uint32_t)(2 + i) * sizeof(uintptr_t)));
    printf("refarray %zu\n", s); }              /* 3*(0+..+63) = 6048 */
  { double *xs = fpprt_elems(f_slots[2]); double s = 0;
    for (int i = 0; i < 1000; i++) s += xs[i];
    printf("f64array %.1f\n", s); }             /* 249750.0 */

  /* 3: a weak ref keeps nothing alive and reads 0 once the target dies */
  { fpprt_ref t = fpprt_alloc(TID_CONS);
    set_cons_val(t, 77);
    f_slots[3] = fpprt_weak_new(t);
    t = 0; }
  fpprt_collect();
  fpprt_collect();
  printf("weak %s\n", fpprt_weak_get(f_slots[3]) ? "ALIVE" : "dead");

  /* 4: a weak ref to a LIVE target stays readable across collections */
  f_slots[3] = fpprt_weak_new(f_slots[0]);
  fpprt_collect();
  printf("weaklive %s\n",
         fpprt_weak_get(f_slots[3]) == f_slots[0] ? "ok" : "WRONG");

  /* 5: pinning, where the collector supports it */
  if (fpprt_can_pin()) {
    FPPRT_FRAME(pf, 1);
    pf_slots[0] = fpprt_alloc(TID_CONS);
    set_cons_val(pf_slots[0], 5);
    fpprt_ref before = pf_slots[0];
    fpprt_pin(pf_slots[0]);
    fpprt_collect();
    printf("pin %s\n", pf_slots[0] == before ? "stable" : "MOVED");
    FPPRT_LEAVE(pf);
  } else {
    printf("pin unsupported\n");
  }

  printf("allocatedMB %" PRIuPTR "\n",
         (uintptr_t)(fpprt_allocated_bytes() / (1024 * 1024)));
  printf("OK\n");
  FPPRT_LEAVE(f);
  return 0;
}

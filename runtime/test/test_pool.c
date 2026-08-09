/* The pool and the monitors, together under GC churn: a dispatch sums a
 * range across every worker (chunk-order independent), a monitor guards a
 * shared counter, and the main mutator forces collections while both run.
 * The printed numbers are the assertion. */
#include <stdio.h>
#include <stdlib.h>
#include "../fpprt.h"
#include "../fpprt-lang.h"

static long partial_[64];

static void sum_kernel(void *env, int lo, int hi) {
  (void)env;
  long s = 0;
  for (int i = lo; i < hi; i++) s += (long)i;
  /* one slot per chunk start / chunk — race-free by construction */
  partial_[(lo / 1000) % 64] += s;
}

static V lock_obj_;
static long guarded_ = 0;

static void mon_kernel(void *env, int lo, int hi) {
  (void)env;
  for (int i = lo; i < hi; i++) {
    fpp_monitor_enter(lock_obj_);
    guarded_++;
    fpp_monitor_exit(lock_obj_);
  }
}


/* ---- phased-dispatch tests ---------------------------------------------- */
enum { PH_N = 50000 };
static long ph_a[PH_N], ph_b[PH_N], ph_c[PH_N];

static void ph_stencil(void *env, int phase, int lo, int hi) {
  (void)env;
  if (phase == 0)
    for (int i = lo; i < hi; i++) ph_a[i] = ph_a[i] * 2;
  else
    for (int i = lo; i < hi; i++)
      ph_b[i] = ph_a[i] + (i > 0 ? ph_a[i - 1] : 0);
}

static void ph_acc(void *env, int phase, int lo, int hi) {
  (void)env;
  for (int i = lo; i < hi; i++) ph_c[i] += phase + 1;
}

static void phased_tests(void) {
  for (int i = 0; i < PH_N; i++) ph_a[i] = i % 17;
  fpp_pool_dispatch_phased(PH_N, 700, 1, 2, ph_stencil, NULL);
  long got = 0, expect = 0;
  for (int i = 0; i < PH_N; i++) got += ph_b[i];
  for (int i = 0; i < PH_N; i++) {
    long ai = (i % 17) * 2, al = i > 0 ? ((i - 1) % 17) * 2 : 0;
    expect += ai + al;
  }
  printf("phased %s\n", got == expect ? "ok" : "WRONG");
  fpp_pool_dispatch_phased(PH_N, 300, 16, 3, ph_acc, NULL);
  long g2 = 0;
  for (int i = 0; i < PH_N; i++) g2 += ph_c[i];
  printf("groups %s\n", g2 == (long)PH_N * 6 ? "ok" : "WRONG");
}

int main(void) {
  fpprt_init(NULL);
  fpprt_thread_attach();
  /* any heap ref serves as a lock identity */
  fpprt_register_type(FPPRT_TID_FIRST, (struct fpprt_type){
    sizeof(double), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "f64s" });
  lock_obj_ = (V)fpprt_alloc_array(FPPRT_TID_FIRST, 4);
  long expect = 0;
  for (long i = 0; i < 64000; i++) expect += i;
  fpp_pool_dispatch(64000, 1000, sum_kernel, NULL);
  long got = 0;
  for (int i = 0; i < 64; i++) got += partial_[i];
  printf("sum %s\n", got == expect ? "ok" : "WRONG");
  fpp_pool_dispatch(40000, 512, mon_kernel, NULL);
  printf("mon %s (%ld)\n", guarded_ == 40000 ? "ok" : "WRONG", guarded_);
  /* dispatch again after a forced collection: workers must have parked */
  fpprt_collect();
  fpp_pool_dispatch(64000, 1000, sum_kernel, NULL);
  printf("again ok\n");
  /* phased tests use TOP-LEVEL kernels: emcc is clang, and clang has no
   * GCC nested functions (the first version died silently in the
   * wasm-linear leg) */
  phased_tests();
  return 0;
}

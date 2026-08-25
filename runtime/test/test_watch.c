/* The watch table: deterministic cleanup. A dead object's tag queues at the
 * collection that proves it, drains pop in REGISTRATION order, kinds stay
 * apart, a live object never fires, and a watch holds nothing alive. Run
 * under `semi` first: every collection moves every object, so the chunk
 * root slots and the ephemeron keys are both exercised hard. */
#include <stdio.h>
#include <string.h>

#include "../fpprt.h"

#define CHECK(x) do { if (!(x)) { printf("CHECK FAILED: %s\n", #x); return 1; } } while (0)

#define TID_CONS FPPRT_TID_FIRST
static const uint32_t cons_refs[] = { 1 * sizeof(uintptr_t),
                                      2 * sizeof(uintptr_t) };

static fpprt_ref mk(void) { return fpprt_alloc(TID_CONS); }

int main(void) {
  fpprt_init(&(struct fpprt_opts){ .heap_bytes = 16 * 1024 * 1024 });
  fpprt_register_type(TID_CONS, (struct fpprt_type){
    4 * sizeof(uintptr_t), FPPRT_KIND_STRUCT, 2, cons_refs, "cons" });

  FPPRT_FRAME(f, 2);

  /* 1: a dead watch fires exactly once, a live one not at all */
  { fpprt_ref a = mk(); fpprt_watch(a, 101, 1); (void)a; }
  f_slots[0] = mk();
  fpprt_watch(f_slots[0], 202, 1);
  fpprt_collect();
  CHECK(fpprt_drain1(1) == 101);
  CHECK(fpprt_drain1(1) == 0);

  /* 2: still live after more collections; fires when unrooted */
  fpprt_collect();
  CHECK(fpprt_drain1(1) == 0);
  f_slots[0] = 0;
  fpprt_collect();
  CHECK(fpprt_drain1(1) == 202);
  CHECK(fpprt_drain1(1) == 0);

  /* 3: kinds are separate queues */
  { fpprt_ref b = mk(); fpprt_watch(b, 7, 0); (void)b; }
  fpprt_collect();
  CHECK(fpprt_drain1(1) == 0);
  CHECK(fpprt_drain1(0) == 7);
  CHECK(fpprt_drain1(0) == 0);

  /* 4: registration order survives into the queue */
  for (int i = 0; i < 10; i++) { fpprt_ref c = mk(); fpprt_watch(c, 300 + i, 1); (void)c; }
  fpprt_collect();
  for (int i = 0; i < 10; i++) CHECK(fpprt_drain1(1) == (uint32_t)(300 + i));
  CHECK(fpprt_drain1(1) == 0);

  /* 5: chunk growth (spans several 512-entry chunks), NATURAL collections
   * from allocation pressure only — no explicit collect until the end */
  int fired[4000];
  memset(fired, 0, sizeof fired);
  for (int i = 0; i < 4000; i++) { fpprt_ref d = mk(); fpprt_watch(d, 4096 + i, 0); (void)d; }
  fpprt_collect();
  int n = 0, last = -1, ordered = 1;
  for (uint32_t t; (t = fpprt_drain1(0)) != 0; n++) {
    CHECK(t >= 4096 && t < 4096 + 4000);
    if ((int)t <= last) ordered = 0;
    last = (int)t;
    CHECK(!fired[t - 4096]);
    fired[t - 4096] = 1;
  }
  CHECK(n == 4000);
  CHECK(ordered);

  /* 6: a watch re-registered on a LIVE object fires once per watch */
  f_slots[1] = mk();
  fpprt_watch(f_slots[1], 900, 1);
  fpprt_watch(f_slots[1], 901, 1);
  fpprt_collect();
  CHECK(fpprt_drain1(1) == 0);
  f_slots[1] = 0;
  fpprt_collect();
  CHECK(fpprt_drain1(1) == 900);
  CHECK(fpprt_drain1(1) == 901);
  CHECK(fpprt_drain1(1) == 0);

  FPPRT_LEAVE(f);
  printf("watch ok\n");
  return 0;
}

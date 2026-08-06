/* fpprt-lang: the non-inline bodies. See fpprt-lang.h. */
#include "fpprt-lang.h"
#if !defined(__wasm__)
#include <sys/mman.h>
#endif

unsigned char *fpp_tclass_ = NULL;
unsigned int *fpp_tfields_ = NULL;
size_t fpp_tmeta_cap_ = 0;

_Thread_local struct fpp_handler *fpp_handler_top_ = NULL;
_Thread_local V fpp_exn_ = 0;

void fpp_reg_meta_(uint32_t tid, int tclass, unsigned nfields) {
  if (tid >= fpp_tmeta_cap_) {
    size_t cap = fpp_tmeta_cap_ ? fpp_tmeta_cap_ : 64;
    while (tid >= cap) cap *= 2;
    fpp_tclass_ = realloc(fpp_tclass_, cap);
    fpp_tfields_ = realloc(fpp_tfields_, cap * sizeof(unsigned int));
    if (!fpp_tclass_ || !fpp_tfields_) abort();
    memset(fpp_tclass_ + fpp_tmeta_cap_, 0, cap - fpp_tmeta_cap_);
    memset(fpp_tfields_ + fpp_tmeta_cap_, 0,
           (cap - fpp_tmeta_cap_) * sizeof(unsigned int));
    fpp_tmeta_cap_ = cap;
  }
  fpp_tclass_[tid] = (unsigned char)tclass;
  fpp_tfields_[tid] = nfields;
}

void fpp_reg_struct(uint32_t tid, unsigned nfields, int tclass,
                    const char *name) {
  uint32_t *offs = malloc(sizeof(uint32_t) * (nfields ? nfields : 1));
  if (!offs) abort();
  for (unsigned i = 0; i < nfields; i++) offs[i] = (i + 1) * sizeof(V);
  fpprt_register_type(tid, (struct fpprt_type){
    (uint32_t)((nfields + 1) * sizeof(V)), FPPRT_KIND_STRUCT,
    nfields, offs, name });
  fpp_reg_meta_(tid, tclass, nfields);
}

void fpp_reg_clo(uint32_t tid, unsigned nenv) {
  uint32_t *offs = malloc(sizeof(uint32_t) * (nenv ? nenv : 1));
  if (!offs) abort();
  for (unsigned i = 0; i < nenv; i++) offs[i] = (i + 3) * sizeof(V);
  fpprt_register_type(tid, (struct fpprt_type){
    (uint32_t)((nenv + 3) * sizeof(V)), FPPRT_KIND_STRUCT,
    nenv, offs, "closure" });
  fpp_reg_meta_(tid, FPP_TC_CLO, nenv);
}

/* ---- allocation helpers that must root their inputs -------------------- */

V fpp_str_utf8(const char *bytes, size_t len) {
  /* count units first: BMP chars are one unit, astral pairs two */
  size_t units = 0;
  for (size_t i = 0; i < len;) {
    unsigned char c = (unsigned char)bytes[i];
    if (c < 0x80) { i += 1; units += 1; }
    else if (c < 0xe0) { i += 2; units += 1; }
    else if (c < 0xf0) { i += 3; units += 1; }
    else { i += 4; units += 2; }
  }
  V s = fpprt_alloc_array(FPP_TID_STR, units);
  uint16_t *u = fpp_str_units(s);
  size_t k = 0;
  for (size_t i = 0; i < len;) {
    unsigned char c = (unsigned char)bytes[i];
    uint32_t cp;
    if (c < 0x80) { cp = c; i += 1; }
    else if (c < 0xe0) {
      cp = ((uint32_t)(c & 0x1f) << 6) | (bytes[i + 1] & 0x3f);
      i += 2;
    } else if (c < 0xf0) {
      cp = ((uint32_t)(c & 0x0f) << 12) | ((uint32_t)(bytes[i + 1] & 0x3f) << 6)
         | (bytes[i + 2] & 0x3f);
      i += 3;
    } else {
      cp = ((uint32_t)(c & 0x07) << 18) | ((uint32_t)(bytes[i + 1] & 0x3f) << 12)
         | ((uint32_t)(bytes[i + 2] & 0x3f) << 6) | (bytes[i + 3] & 0x3f);
      i += 4;
    }
    if (cp >= 0x10000) {
      cp -= 0x10000;
      u[k++] = (uint16_t)(0xd800 | (cp >> 10));
      u[k++] = (uint16_t)(0xdc00 | (cp & 0x3ff));
    } else {
      u[k++] = (uint16_t)cp;
    }
  }
  return s;
}

V fpp_str_concat(V a, V b) {
  FPPRT_FRAME(f, 2);
  f_slots[0] = a; f_slots[1] = b;
  V s = fpprt_alloc_array(FPP_TID_STR,
                          fpp_str_len(f_slots[0]) + fpp_str_len(f_slots[1]));
  memcpy(fpp_str_units(s), fpp_str_units(f_slots[0]),
         fpp_str_len(f_slots[0]) * 2);
  memcpy(fpp_str_units(s) + fpp_str_len(f_slots[0]),
         fpp_str_units(f_slots[1]), fpp_str_len(f_slots[1]) * 2);
  FPPRT_LEAVE(f);
  return s;
}

int fpp_str_cmp(V a, V b) {
  /* ordinal, by code unit — .NET's String.CompareOrdinal */
  size_t la = fpp_str_len(a), lb = fpp_str_len(b);
  size_t n = la < lb ? la : lb;
  uint16_t *ua = fpp_str_units(a), *ub = fpp_str_units(b);
  for (size_t i = 0; i < n; i++)
    if (ua[i] != ub[i]) return ua[i] < ub[i] ? -1 : 1;
  return la < lb ? -1 : la > lb ? 1 : 0;
}

void fpp_prints(V s) {
  uint16_t *u = fpp_str_units(s);
  size_t n = fpp_str_len(s);
  for (size_t i = 0; i < n; i++) {
    uint32_t cp = u[i];
    if (cp >= 0xd800 && cp < 0xdc00 && i + 1 < n
        && u[i + 1] >= 0xdc00 && u[i + 1] < 0xe000) {
      cp = 0x10000 + ((cp - 0xd800) << 10) + (u[i + 1] - 0xdc00);
      i++;
    }
    if (cp < 0x80) fputc((int)cp, stdout);
    else if (cp < 0x800) {
      fputc(0xc0 | (cp >> 6), stdout);
      fputc(0x80 | (cp & 0x3f), stdout);
    } else if (cp < 0x10000) {
      fputc(0xe0 | (cp >> 12), stdout);
      fputc(0x80 | ((cp >> 6) & 0x3f), stdout);
      fputc(0x80 | (cp & 0x3f), stdout);
    } else {
      fputc(0xf0 | (cp >> 18), stdout);
      fputc(0x80 | ((cp >> 12) & 0x3f), stdout);
      fputc(0x80 | ((cp >> 6) & 0x3f), stdout);
      fputc(0x80 | (cp & 0x3f), stdout);
    }
  }
}

void fpp_print(V s) {
  fpp_prints(s);
  fputc('\n', stdout);
}

V fpp_cons(V h, V t) {
  FPPRT_FRAME(f, 2);
  f_slots[0] = h; f_slots[1] = t;
  V c = fpprt_alloc(FPP_TID_CONS);
  fpprt_write_ref(c, 1 * sizeof(V), f_slots[0]);
  fpprt_write_ref(c, 2 * sizeof(V), f_slots[1]);
  FPPRT_LEAVE(f);
  return c;
}

V fpp_cell_new(V v) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = v;
  V c = fpprt_alloc(FPP_TID_CELL);
  fpprt_write_ref(c, 1 * sizeof(V), f_slots[0]);
  FPPRT_LEAVE(f);
  return c;
}

/* ---- apply: full curried semantics -------------------------------------- */
/* PAP layout: [tag][code][remaining][inner][got:tuple] — inner+got traced */

static V fpp_pap_code_(V self, V *args) {
  /* self: the PAP; args: the NEW arguments (exactly `remaining` of them) */
  FPPRT_FRAME(f, 3);
  f_slots[0] = fpprt_read_ref(self, 3 * sizeof(V));    /* inner closure */
  f_slots[1] = fpprt_read_ref(self, 4 * sizeof(V));    /* got tuple */
  size_t ngot = fpprt_array_len(f_slots[1]);
  size_t nnew = fpp_clo_arity(self);
  size_t total = ngot + nnew;
  /* assemble the full argument span in a frame-rooted C array */
  V full[64];
  if (total > 64) fpp_not_emitted("apply arity > 64");
  struct fpprt_frame af = { fpprt_top_frame, (uint32_t)total, full };
  for (size_t i = 0; i < total; i++) full[i] = 0;
  fpprt_top_frame = &af;
  for (size_t i = 0; i < ngot; i++) full[i] = fpp_tuple_get(f_slots[1], i);
  for (size_t i = 0; i < nnew; i++) full[ngot + i] = args[i];
  V r = fpp_apply(f_slots[0], full, total);
  fpprt_top_frame = af.prev;
  FPPRT_LEAVE(f);
  return r;
}

V fpp_apply(V clo, V *args, size_t n) {
  if (!clo || (clo & 1)) {
    fprintf(stderr, "fpp: apply to %s\n", clo ? "tagged value" : "null");
    fpp_not_emitted("apply to non-closure");
  }
  if (fpp_tclass_[fpprt_typeid(clo)] != FPP_TC_CLO) {
    fprintf(stderr, "fpp: apply to non-closure %s\n",
            fpprt_type_name(fpprt_typeid(clo)));
    fpp_not_emitted("apply to non-closure object");
  }
  size_t arity = fpp_clo_arity(clo);
  if (n == arity)
    return fpp_clo_code(clo)(clo, args);
  if (n < arity) {
    /* under-application: a PAP holding what arrived */
    FPPRT_FRAME(f, 2);
    f_slots[0] = clo;
    V got = fpp_tuple(n);
    f_slots[1] = got;
    for (size_t i = 0; i < n; i++) fpp_tuple_set(f_slots[1], i, args[i]);
    V pap = fpp_clo_new(FPP_TID_PAP, fpp_pap_code_, arity - n, 2);
    fpprt_write_ref(pap, 3 * sizeof(V), f_slots[0]);
    fpprt_write_ref(pap, 4 * sizeof(V), f_slots[1]);
    FPPRT_LEAVE(f);
    return pap;
  }
  /* over-application: saturate, then apply the result to the rest */
  {
    FPPRT_FRAME(f, 1);
    /* args beyond arity stay rooted: they live in the CALLER's frame span */
    V r = fpp_clo_code(clo)(clo, args);
    f_slots[0] = r;
    V out = fpp_apply(f_slots[0], args + arity, n - arity);
    FPPRT_LEAVE(f);
    return out;
  }
}

/* ---- interface dispatch ------------------------------------------------- */

static fpp_code_t *fpp_vt_ = NULL;
static size_t fpp_vt_tids_ = 0;
static int fpp_vt_slots_ = 0;

void fpp_vt_set(uint32_t tid, int slot, fpp_code_t fn) {
  if (tid >= fpp_vt_tids_ || slot >= fpp_vt_slots_) {
    size_t ntids = fpp_vt_tids_ ? fpp_vt_tids_ : 64;
    while (tid >= ntids) ntids *= 2;
    int nslots = fpp_vt_slots_ ? fpp_vt_slots_ : 32;
    while (slot >= nslots) nslots *= 2;
    fpp_code_t *nt = calloc(ntids * (size_t)nslots, sizeof(fpp_code_t));
    if (!nt) abort();
    for (size_t t = 0; t < fpp_vt_tids_; t++)
      for (int s = 0; s < fpp_vt_slots_; s++)
        nt[t * (size_t)nslots + s] = fpp_vt_[t * (size_t)fpp_vt_slots_ + s];
    free(fpp_vt_);
    fpp_vt_ = nt;
    fpp_vt_tids_ = ntids;
    fpp_vt_slots_ = nslots;
  }
  fpp_vt_[tid * (size_t)fpp_vt_slots_ + slot] = fn;
}

/* per-tid CompareTo dispatch: a CLASS that defines its own ordering must
 * order that way everywhere `compare` is asked — pointer order made the
 * Index machinery spin forever */
static int *fpp_cmp_slot_ = NULL;
static size_t fpp_cmp_cap_ = 0;
void fpp_reg_cmp(uint32_t tid, int slot) {
  if (tid >= fpp_cmp_cap_) {
    size_t cap = fpp_cmp_cap_ ? fpp_cmp_cap_ : 64;
    while (tid >= cap) cap *= 2;
    int *n = malloc(cap * sizeof(int));
    if (!n) abort();
    for (size_t i = 0; i < cap; i++) n[i] = i < fpp_cmp_cap_ ? fpp_cmp_slot_[i] : -1;
    free(fpp_cmp_slot_);
    fpp_cmp_slot_ = n;
    fpp_cmp_cap_ = cap;
  }
  fpp_cmp_slot_[tid] = slot;
}
static int fpp_cmp_slot_of_(uint32_t tid) {
  return tid < fpp_cmp_cap_ ? fpp_cmp_slot_[tid] : -1;
}

/* same shape for Equals / GetHashCode: a class overriding them must be
 * VALUE-keyed in dictionaries the way the oracle keys it, not identity */
static int *fpp_eq_slot_ = NULL;
static size_t fpp_eq_cap_ = 0;
void fpp_reg_eq(uint32_t tid, int slot) {
  if (tid >= fpp_eq_cap_) {
    size_t cap = fpp_eq_cap_ ? fpp_eq_cap_ : 64;
    while (tid >= cap) cap *= 2;
    int *n = malloc(cap * sizeof(int));
    if (!n) abort();
    for (size_t i = 0; i < cap; i++) n[i] = i < fpp_eq_cap_ ? fpp_eq_slot_[i] : -1;
    free(fpp_eq_slot_);
    fpp_eq_slot_ = n;
    fpp_eq_cap_ = cap;
  }
  fpp_eq_slot_[tid] = slot;
}
static int fpp_eq_slot_of_(uint32_t tid) {
  return tid < fpp_eq_cap_ ? fpp_eq_slot_[tid] : -1;
}
static int *fpp_hash_slot_ = NULL;
static size_t fpp_hash_cap_ = 0;
void fpp_reg_hash(uint32_t tid, int slot) {
  if (tid >= fpp_hash_cap_) {
    size_t cap = fpp_hash_cap_ ? fpp_hash_cap_ : 64;
    while (tid >= cap) cap *= 2;
    int *n = malloc(cap * sizeof(int));
    if (!n) abort();
    for (size_t i = 0; i < cap; i++) n[i] = i < fpp_hash_cap_ ? fpp_hash_slot_[i] : -1;
    free(fpp_hash_slot_);
    fpp_hash_slot_ = n;
    fpp_hash_cap_ = cap;
  }
  fpp_hash_slot_[tid] = slot;
}
static int fpp_hash_slot_of_(uint32_t tid) {
  return tid < fpp_hash_cap_ ? fpp_hash_slot_[tid] : -1;
}

/* parent tid per tid: `:? Base` walks up from the object's exact tid */
static uint32_t *fpp_parent_ = NULL;
static size_t fpp_parent_cap_ = 0;
void fpp_reg_parent(uint32_t tid, uint32_t parent) {
  if (tid >= fpp_parent_cap_) {
    size_t cap = fpp_parent_cap_ ? fpp_parent_cap_ : 64;
    while (tid >= cap) cap *= 2;
    uint32_t *n = malloc(cap * sizeof(uint32_t));
    if (!n) abort();
    for (size_t i = 0; i < cap; i++) n[i] = i < fpp_parent_cap_ ? fpp_parent_[i] : 0;
    free(fpp_parent_);
    fpp_parent_ = n;
    fpp_parent_cap_ = cap;
  }
  fpp_parent_[tid] = parent;
}
int fpp_isa(V x, uint32_t tid) {
  if (!x || (x & 1)) return 0;
  uint32_t t = fpprt_typeid(x);
  for (int guard = 0; guard < 64; guard++) {
    if (t == tid) return 1;
    uint32_t p = t < fpp_parent_cap_ ? fpp_parent_[t] : 0;
    if (!p || p == t) return 0;
    t = p;
  }
  return 0;
}

V fpp_append(V a, V b) {
  FPPRT_FRAME(f, 3);
  f_slots[0] = a; f_slots[1] = b; f_slots[2] = 0;
  while (fpp_is_tid(f_slots[0], FPP_TID_CONS)) {
    f_slots[2] = fpp_cons(fpprt_read_ref(f_slots[0], sizeof(V)), f_slots[2]);
    f_slots[0] = fpprt_read_ref(f_slots[0], 2 * sizeof(V));
  }
  while (fpp_is_tid(f_slots[2], FPP_TID_CONS)) {
    f_slots[1] = fpp_cons(fpprt_read_ref(f_slots[2], sizeof(V)), f_slots[1]);
    f_slots[2] = fpprt_read_ref(f_slots[2], 2 * sizeof(V));
  }
  V r = f_slots[1];
  FPPRT_LEAVE(f);
  return r;
}

int fpp_vt_has(V obj, int slot) {
  if (!obj || (obj & 1)) return 0;
  uint32_t tid = fpprt_typeid(obj);
  return tid < fpp_vt_tids_ && slot < fpp_vt_slots_
      && fpp_vt_[tid * (size_t)fpp_vt_slots_ + slot] != NULL;
}

static int fpp_slot_ge_ = -1, fpp_slot_mn_ = -1, fpp_slot_disp_ = -1;
void fpp_seq_slots(int ge, int mn, int disp) {
  fpp_slot_ge_ = ge; fpp_slot_mn_ = mn; fpp_slot_disp_ = disp;
}

V fpp_vcall(V obj, int slot, V *args, size_t n) {
  (void)n;
  if (!obj) {
    /* null IS the empty list: enumerating it must work like the oracle */
    if (slot == fpp_slot_ge_) return fpp_seq_getenum(0, NULL);
    if (slot == fpp_slot_mn_) return TAGI(0);
    if (slot == fpp_slot_disp_) return VUNIT;
  }
  if (!obj || (obj & 1)) fpp_not_emitted("vcall on non-object");
  uint32_t tid = fpprt_typeid(obj);
  fpp_code_t fn = (tid < fpp_vt_tids_ && slot < fpp_vt_slots_)
    ? fpp_vt_[tid * (size_t)fpp_vt_slots_ + slot] : NULL;
  if (!fn) {
    fprintf(stderr, "fpp: no vtable entry (tid %u slot %d)\n", tid, slot);
    abort();
  }
  return fn(obj, args);
}

V fpp_arr_zeroed(int kind, size_t n) {
  /* primitive elements now live in SCALAR arrays — the allocator zeroes */
  if (kind == 1) return fpprt_alloc_array(FPP_TID_AI32, n);
  if (kind == 2) return fpprt_alloc_array(FPP_TID_AF64, n);
  if (kind == 3) return fpprt_alloc_array(FPP_TID_AI64, n);
  return fpprt_alloc_array(FPP_TID_ARR, n);
}

/* ---- builtin seq enumerators -------------------------------------------- */
/* [tag][src][idx] — idx tagged; for a LIST src walks the cons chain */

V fpp_seq_getenum(V self, V *args) {
  (void)args;
  FPPRT_FRAME(f, 1);
  f_slots[0] = self;
  V e = fpprt_alloc(FPP_TID_ENUM);
  fpprt_write_ref(e, 1 * sizeof(V), f_slots[0]);
  ((uintptr_t *)e)[2] = TAGI(-1);
  FPPRT_LEAVE(f);
  return e;
}

V fpp_enum_movenext(V self, V *args) {
  (void)args;
  V src = fpprt_read_ref(self, 1 * sizeof(V));
  if (src == 0) return TAGI(0);
  {
    uint32_t t = fpprt_typeid(src);
    if (t == FPP_TID_ARR || t == FPP_TID_STR || t == FPP_TID_TUPLE
        || (t >= FPP_TID_AF64 && t <= FPP_TID_AU8)) {
      intptr_t i = UNTAGI(((uintptr_t *)self)[2]) + 1;
      ((uintptr_t *)self)[2] = TAGI(i);
      return TAGI((size_t)i < fpprt_array_len(src));
    }
  }
  /* a list: idx == -1 means "before first" — first MoveNext stays on src,
   * later ones advance the chain */
  if (((intptr_t)UNTAGI(((uintptr_t *)self)[2])) < 0) {
    ((uintptr_t *)self)[2] = TAGI(0);
    return TAGI(fpp_is_tid(src, FPP_TID_CONS));
  }
  V next = fpp_is_tid(src, FPP_TID_CONS) ? fpprt_read_ref(src, 2 * sizeof(V)) : 0;
  fpprt_write_ref(self, 1 * sizeof(V), next);
  return TAGI(fpp_is_tid(next, FPP_TID_CONS));
}

V fpp_enum_current(V self, V *args) {
  (void)args;
  V src = fpprt_read_ref(self, 1 * sizeof(V));
  if (fpp_is_tid(src, FPP_TID_CONS))
    return fpprt_read_ref(src, 1 * sizeof(V));
  if (fpp_is_tid(src, FPP_TID_STR)) {
    intptr_t i = UNTAGI(((uintptr_t *)self)[2]);
    return TAGI(fpp_str_units(src)[i]);
  }
  intptr_t i = UNTAGI(((uintptr_t *)self)[2]);
  return fpp_arr_get(src, (size_t)i);
}

V fpp_enum_dispose(V self, V *args) {
  (void)self; (void)args;
  return VUNIT;
}

/* ---- exceptions --------------------------------------------------------- */

uint32_t fpp_failure_tid_ = 0;

V fpp_failure(const char *msg, size_t len) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = fpp_str_c(msg, len);
  V r = f_slots[0];
  if (fpp_failure_tid_) {
    r = fpprt_alloc(fpp_failure_tid_);
    fpprt_write_ref(r, sizeof(V), f_slots[0]);
  }
  FPPRT_LEAVE(f);
  return r;
}

const char *fpp_hlog_site_[64];
char fpp_hlog_kind_[64];
void *fpp_hlog_ptr_[64];
unsigned fpp_hlog_n_ = 0;
void fpp_hlog_dump(void) {
  fflush(stdout);
  unsigned start = fpp_hlog_n_ > 40 ? fpp_hlog_n_ - 40 : 0;
  for (unsigned i = start; i < fpp_hlog_n_; i++)
    fprintf(stderr, "  hlog %c %p %s\n", fpp_hlog_kind_[i & 63],
            fpp_hlog_ptr_[i & 63], fpp_hlog_site_[i & 63]);
}

void fpp_raise(V payload) {
  fpp_hlog_('R', fpp_handler_top_ ? fpp_handler_top_->site : "none",
            (void *)fpp_handler_top_);
#ifdef FPP_RAISE_DEBUG
  {
    int depth = 0;
    for (struct fpp_handler *h = fpp_handler_top_; h; h = h->prev) depth++;
    fprintf(stderr, "[raise depth=%d payload=%s]\n", depth,
            (payload && !(payload & 1))
              ? fpprt_type_name(fpprt_typeid(payload)) : "tagged");
  }
#endif
  if (!fpp_handler_top_) {
    fflush(stdout);
    fprintf(stderr, "fpp: unhandled exception\n");
    if (fpp_is_tid(payload, FPP_TID_STR)) {
      fprintf(stderr, "  ");
      for (size_t i = 0; i < fpp_str_len(payload); i++)
        fputc((int)fpp_str_units(payload)[i] & 0x7f, stderr);
      fputc('\n', stderr);
    }
    exit(101);
  }
  struct fpp_handler *h = fpp_handler_top_;
  fpp_handler_top_ = h->prev;
  fpp_exn_ = payload;
  fpprt_top_frame = h->frame_top;
  longjmp(h->jb, 1);
}

void fpp_reraise(void) { fpp_raise(fpp_exn_); }

void fpp_match_fail(void) {
  fpp_raise(fpp_failure("match failure", 13));
}

/* ---- structural equality / hash / compare ------------------------------ */

static int fpp_tclass_of_(V v) {
  uint32_t tid = fpprt_typeid(v);
  return tid < fpp_tmeta_cap_ ? fpp_tclass_[tid] : FPP_TC_OTHER;
}

int fpp_eqv(V a, V b) {
  /* the identity fast path must not answer for floats: the same NaN box
   * still compares UNEQUAL to itself */
  if (a == b && !((a && !(a & 1)) && fpprt_typeid(a) == FPP_TID_F64)) return 1;
  if (a == b) return fpp_unbox_f64(a) == fpp_unbox_f64(b);
  if (!a || !b) return 0;
  if ((a & 1) || (b & 1)) {
    /* representational drift: tagged vs boxed of the SAME number is equal */
    V r = (a & 1) ? b : a;
    if (r & 1) return 0;
    intptr_t tv = (intptr_t)UNTAGI((a & 1) ? a : b);
    uint32_t tr = fpprt_typeid(r);
    if (tr == FPP_TID_I64) return fpp_unbox_i64(r) == (int64_t)tv;
    if (tr == FPP_TID_F64) return fpp_unbox_f64(r) == (double)tv;
    return 0;
  }
  uint32_t ta = fpprt_typeid(a), tb = fpprt_typeid(b);
  if (ta != tb) return 0;
  switch (ta) {
  case FPP_TID_STR: return fpp_str_cmp(a, b) == 0;
  case FPP_TID_F64: return fpp_unbox_f64(a) == fpp_unbox_f64(b);
  case FPP_TID_I64: return fpp_unbox_i64(a) == fpp_unbox_i64(b);
  case FPP_TID_TUPLE: {
    size_t n = fpprt_array_len(a);
    if (n != fpprt_array_len(b)) return 0;
    for (size_t i = 0; i < n; i++)
      if (!fpp_eqv(fpp_tuple_get(a, i), fpp_tuple_get(b, i))) return 0;
    return 1;
  }
  case FPP_TID_CONS:
    return fpp_eqv(fpprt_read_ref(a, sizeof(V)), fpprt_read_ref(b, sizeof(V)))
        && fpp_eqv(fpprt_read_ref(a, 2 * sizeof(V)),
                   fpprt_read_ref(b, 2 * sizeof(V)));
  case FPP_TID_ARR: return 0;              /* reference equality only */
  case FPP_TID_CELL: return 0;
  default: {
    int tc = fpp_tclass_of_(a);
    if (tc == FPP_TC_RECORD || tc == FPP_TC_CASE) {
      unsigned n = fpp_tfields_[ta];
      for (unsigned i = 0; i < n; i++)
        if (!fpp_eqv(fpprt_read_ref(a, (i + 1) * sizeof(V)),
                     fpprt_read_ref(b, (i + 1) * sizeof(V)))) return 0;
      return 1;
    }
    if (tc == FPP_TC_CLASS) {
      int slot = fpp_eq_slot_of_(ta);
      if (slot >= 0) {
        V arg = b;
        return UNTAGI(fpp_vcall(a, slot, &arg, 1)) != 0;
      }
    }
    if (tc == FPP_TC_POD) return fpp_pod_eq(a, b);
    return 0;                              /* closures, classes: identity */
  }
  }
}

int fpp_cmpv(V a, V b) {
  if (a == b) return 0;
  if ((a & 1) && (b & 1))
    return UNTAGI(a) < UNTAGI(b) ? -1 : UNTAGI(a) > UNTAGI(b) ? 1 : 0;
  if (!a) return -1;
  if (!b) return 1;
  if ((a & 1) || (b & 1)) {
    /* representational drift: the same numeric value can arrive TAGGED on
     * one side and BOXED on the other — order NUMERICALLY or int64 map
     * keys get an inconsistent ordering (MapExt inserts then loop) */
    V r = (a & 1) ? b : a;
    intptr_t tv = (intptr_t)UNTAGI((a & 1) ? a : b);
    uint32_t tr = fpprt_typeid(r);
    if (tr == FPP_TID_I64) {
      int64_t x = (a & 1) ? (int64_t)tv : fpp_unbox_i64(a);
      int64_t y = (b & 1) ? (int64_t)tv : fpp_unbox_i64(b);
      return x < y ? -1 : x > y ? 1 : 0;
    }
    if (tr == FPP_TID_F64) {
      double x = (a & 1) ? (double)tv : fpp_unbox_f64(a);
      double y = (b & 1) ? (double)tv : fpp_unbox_f64(b);
      return x < y ? -1 : x > y ? 1 : 0;
    }
    return (a & 1) ? -1 : 1;
  }
  uint32_t ta = fpprt_typeid(a), tb = fpprt_typeid(b);
  if (ta != tb) return ta < tb ? -1 : 1;
  switch (ta) {
  case FPP_TID_STR: return fpp_str_cmp(a, b);
  case FPP_TID_F64: {
    double x = fpp_unbox_f64(a), y = fpp_unbox_f64(b);
    return x < y ? -1 : x > y ? 1 : 0;
  }
  case FPP_TID_I64: {
    int64_t x = fpp_unbox_i64(a), y = fpp_unbox_i64(b);
    return x < y ? -1 : x > y ? 1 : 0;
  }
  case FPP_TID_TUPLE: {
    size_t na = fpprt_array_len(a), nb = fpprt_array_len(b);
    size_t n = na < nb ? na : nb;
    for (size_t i = 0; i < n; i++) {
      int c = fpp_cmpv(fpp_tuple_get(a, i), fpp_tuple_get(b, i));
      if (c) return c;
    }
    return na < nb ? -1 : na > nb ? 1 : 0;
  }
  case FPP_TID_CONS: {
    int c = fpp_cmpv(fpprt_read_ref(a, sizeof(V)), fpprt_read_ref(b, sizeof(V)));
    if (c) return c;
    return fpp_cmpv(fpprt_read_ref(a, 2 * sizeof(V)),
                    fpprt_read_ref(b, 2 * sizeof(V)));
  }
  default: {
    int tc = fpp_tclass_of_(a);
    if (tc == FPP_TC_RECORD || tc == FPP_TC_CASE) {
      unsigned n = fpp_tfields_[ta];
      for (unsigned i = 0; i < n; i++) {
        int c = fpp_cmpv(fpprt_read_ref(a, (i + 1) * sizeof(V)),
                         fpprt_read_ref(b, (i + 1) * sizeof(V)));
        if (c) return c;
      }
      return 0;
    }
    if (tc == FPP_TC_POD) return fpp_pod_cmp(a, b);
    if (tc == FPP_TC_CLASS) {
      int slot = fpp_cmp_slot_of_(ta);
      if (slot >= 0) {
        V arg = b;
        return (int)UNTAGI(fpp_vcall(a, slot, &arg, 1));
      }
    }
    /* no defined ordering: order by IDENTITY HASH, which is stable for an
     * object's whole life — raw pointers move with the collector and vary
     * with ASLR, and a comparison that changes between calls corrupts
     * every ordered structure built on it */
    {
      intptr_t ha = fpprt_idhash(a), hb = fpprt_idhash(b);
      return ha < hb ? -1 : ha > hb ? 1 : (a < b ? -1 : a > b ? 1 : 0);
    }
  }
  }
}

intptr_t fpp_hashv(V v) {
  if (v & 1) return UNTAGI(v);
  if (!v) return 0;
  uint32_t t = fpprt_typeid(v);
  switch (t) {
  case FPP_TID_STR: {
    intptr_t h = 5381;
    uint16_t *p = fpp_str_units(v);
    for (size_t i = 0; i < fpp_str_len(v); i++) h = h * 33 + p[i];
    return h & 0x3fffffff;
  }
  case FPP_TID_F64: return (intptr_t)fpp_unbox_f64(v);
  case FPP_TID_I64: return (intptr_t)fpp_unbox_i64(v);
  case FPP_TID_TUPLE: {
    intptr_t h = 17;
    for (size_t i = 0; i < fpprt_array_len(v); i++)
      h = h * 31 + fpp_hashv(fpp_tuple_get(v, i));
    return h & 0x3fffffff;
  }
  case FPP_TID_CONS: {
    intptr_t h = 23;
    V cur = v;
    while (fpp_is_tid(cur, FPP_TID_CONS)) {
      h = h * 31 + fpp_hashv(fpprt_read_ref(cur, sizeof(V)));
      cur = fpprt_read_ref(cur, 2 * sizeof(V));
    }
    return h & 0x3fffffff;
  }
  default: {
    int tc = fpp_tclass_of_(v);
    if (tc == FPP_TC_RECORD || tc == FPP_TC_CASE) {
      intptr_t h = 29 + (intptr_t)t;
      unsigned n = fpp_tfields_[t];
      for (unsigned i = 0; i < n; i++)
        h = h * 31 + fpp_hashv(fpprt_read_ref(v, (i + 1) * sizeof(V)));
      return h & 0x3fffffff;
    }
    if (tc == FPP_TC_POD) return fpp_pod_hash(v);
    if (tc == FPP_TC_CLASS) {
      int slot = fpp_hash_slot_of_(t);
      if (slot >= 0) {
        V arg = VUNIT;                 /* nullary members may take unit */
        return (intptr_t)UNTAGI(fpp_vcall(v, slot, &arg, 1));
      }
    }
    return (intptr_t)fpprt_idhash(v);
  }
  }
}

/* ---- to-string ---------------------------------------------------------- */

/* the ORACLE's $ftoa, ported instruction-for-instruction: NaN, sign,
 * U+221E infinity, /10 normalization only at >= 1e18, integer part, up to
 * 15 fractional digits stopping on an EXACTLY-zero residual, E+exponent.
 * Byte-identical output is the parity contract. */
static size_t fpp_ftoa_(double v, char *buf) {
  size_t p = 0;
  if (v != v) { buf[0] = 'N'; buf[1] = 'a'; buf[2] = 'N'; return 3; }
  if (v < 0) { buf[p++] = '-'; v = -v; }
  if (v == __builtin_inf()) {
    buf[p++] = (char)0xe2; buf[p++] = (char)0x88; buf[p++] = (char)0x9e;
    return p;
  }
  int e = 0;
  if (v >= 1e18) {
    while (!(v < 10.0)) { v /= 10.0; e++; }
  }
  double ip = __builtin_floor(v);
  p += (size_t)snprintf(buf + p, 24, "%" PRId64, (int64_t)ip);
  double frac = v - ip;
  if (frac > 0.0) {
    buf[p++] = '.';
    for (int k = 0; k < 15; k++) {
      frac *= 10.0;
      int d = (int)__builtin_floor(frac);
      buf[p++] = (char)('0' + d);
      frac -= __builtin_floor(frac);
      if (frac == 0.0) break;
    }
  }
  if (e != 0)
    p += (size_t)snprintf(buf + p, 8, "E+%d", e);
  return p;
}

V fpp_to_string(V x) {
  if (x & 1) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRIdPTR, (intptr_t)UNTAGI(x));
    return fpp_str_c(buf, (size_t)n);
  }
  if (!x) return fpp_str_c("", 0);
  uint32_t t = fpprt_typeid(x);
  if (t == FPP_TID_STR) return x;
  if (t == FPP_TID_F64) {
    char buf[48];
    return fpp_str_c(buf, fpp_ftoa_(fpp_unbox_f64(x), buf));
  }
  if (t == FPP_TID_I64) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRId64, fpp_unbox_i64(x));
    return fpp_str_c(buf, (size_t)n);
  }
  return fpp_str_c("<obj>", 5);
}

V fpp_f64_to_string(V x) {
  char buf[48];
  return fpp_str_c(buf, fpp_ftoa_(fpp_unbox_f64(x), buf));
}

/* ---- generic arithmetic: the oracle's $addv family ---------------------- */

/* representational drift is REAL in the uniform pipeline: a generic zero
 * seeds as a tagged int and meets int64 boxes — same source-level type,
 * two runtime spellings. The dispatch coerces numeric mixes. */
static inline int fpp_numeric_(V v) {
  return (v & 1) || fpp_is_tid(v, FPP_TID_F64) || fpp_is_tid(v, FPP_TID_I64);
}
static inline double fpp_as_f64_(V v) {
  if (v & 1) return (double)UNTAGI(v);
  if (fpp_is_tid(v, FPP_TID_F64)) return fpp_unbox_f64(v);
  return (double)fpp_unbox_i64(v);
}
static inline int64_t fpp_as_i64_(V v) {
  if (v & 1) return (int64_t)UNTAGI(v);
  return fpp_unbox_i64(v);
}

#define FPP_ARITH2(name, op, strcase)                                   \
V name(V a, V b) {                                                      \
  if ((a & 1) && (b & 1))                                               \
    return TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(a) op (int32_t)UNTAGI(b))); \
  if (fpp_is_tid(a, FPP_TID_F64) && fpp_is_tid(b, FPP_TID_F64))         \
    return fpp_box_f64(fpp_unbox_f64(a) op fpp_unbox_f64(b));           \
  if (fpp_is_tid(a, FPP_TID_I64) && fpp_is_tid(b, FPP_TID_I64))         \
    return fpp_box_i64(fpp_unbox_i64(a) op fpp_unbox_i64(b));           \
  if (fpp_numeric_(a) && fpp_numeric_(b)) {                             \
    if (fpp_is_tid(a, FPP_TID_F64) || fpp_is_tid(b, FPP_TID_F64))       \
      return fpp_box_f64(fpp_as_f64_(a) op fpp_as_f64_(b));             \
    return fpp_box_i64(fpp_as_i64_(a) op fpp_as_i64_(b));               \
  }                                                                     \
  strcase                                                               \
  fprintf(stderr, "fpp: mixed arith a=%s b=%s\n",                       \
          (a & 1) ? "tagged" : a ? fpprt_type_name(fpprt_typeid(a)) : "null", \
          (b & 1) ? "tagged" : b ? fpprt_type_name(fpprt_typeid(b)) : "null"); \
  fpp_not_emitted("generic arith on mixed values");                     \
  return 0;                                                             \
}
FPP_ARITH2(fpp_addv, +,
  if (fpp_is_tid(a, FPP_TID_STR) && fpp_is_tid(b, FPP_TID_STR))
    return fpp_str_concat(a, b);)
FPP_ARITH2(fpp_subv, -, )
FPP_ARITH2(fpp_mulv, *, )

V fpp_divv(V a, V b) {
  if ((a & 1) && (b & 1)) {
    if (UNTAGI(b) == 0) fpp_raise(fpp_failure("division by zero", 16));
    return TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(a) / (int32_t)UNTAGI(b)));
  }
  if (fpp_is_tid(a, FPP_TID_F64) && fpp_is_tid(b, FPP_TID_F64))
    return fpp_box_f64(fpp_unbox_f64(a) / fpp_unbox_f64(b));
  if (fpp_is_tid(a, FPP_TID_I64) && fpp_is_tid(b, FPP_TID_I64))
    return fpp_box_i64(fpp_unbox_i64(a) / fpp_unbox_i64(b));
  fpp_not_emitted("generic div on mixed values");
  return 0;
}
V fpp_modv(V a, V b) {
  if ((a & 1) && (b & 1)) {
    if (UNTAGI(b) == 0) fpp_raise(fpp_failure("division by zero", 16));
    return TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(a) % (int32_t)UNTAGI(b)));
  }
  if (fpp_is_tid(a, FPP_TID_F64) && fpp_is_tid(b, FPP_TID_F64))
    return fpp_box_f64(__builtin_fmod(fpp_unbox_f64(a), fpp_unbox_f64(b)));
  if (fpp_is_tid(a, FPP_TID_I64) && fpp_is_tid(b, FPP_TID_I64))
    return fpp_box_i64(fpp_unbox_i64(a) % fpp_unbox_i64(b));
  fpp_not_emitted("generic mod on mixed values");
  return 0;
}

V fpp_negv(V a) {
  if (a & 1) return TAGI(-UNTAGI(a));
  if (fpp_is_tid(a, FPP_TID_F64)) return fpp_box_f64(-fpp_unbox_f64(a));
  if (fpp_is_tid(a, FPP_TID_I64)) return fpp_box_i64(-fpp_unbox_i64(a));
  fpp_not_emitted("generic negation");
  return 0;
}

V fpp_absv(V a) {
  if (a & 1) { intptr_t v = UNTAGI(a); return TAGI(v < 0 ? -v : v); }
  if (fpp_is_tid(a, FPP_TID_F64))
    return fpp_box_f64(__builtin_fabs(fpp_unbox_f64(a)));
  if (fpp_is_tid(a, FPP_TID_I64)) {
    int64_t v = fpp_unbox_i64(a);
    return fpp_box_i64(v < 0 ? -v : v);
  }
  fpp_not_emitted("abs");
  return 0;
}

V fpp_signv(V a) {
  if (a & 1) { intptr_t v = UNTAGI(a); return TAGI(v < 0 ? -1 : v > 0 ? 1 : 0); }
  if (fpp_is_tid(a, FPP_TID_F64)) {
    double v = fpp_unbox_f64(a);
    return TAGI(v < 0 ? -1 : v > 0 ? 1 : 0);
  }
  if (fpp_is_tid(a, FPP_TID_I64)) {
    int64_t v = fpp_unbox_i64(a);
    return TAGI(v < 0 ? -1 : v > 0 ? 1 : 0);
  }
  fpp_not_emitted("sign");
  return 0;
}

double fpp_round_even(double x) {
  /* .NET Math.Round: banker's rounding */
  double r = __builtin_nearbyint(x);
  return r == 0.0 ? 0.0 : r;   /* normalize -0 */
}

/* ---- show and the print family ------------------------------------------ */

V fpp_showv(V x) {
  /* the generic renderer; grows toward the oracle's $showv as parity
   * demands (records, unions, lists) */
  return fpp_to_string(x);
}

void fpp_print_any(V x) {
  fpp_print(fpp_showv(x));
}

void fpp_print_u32(V x) {
  char buf[16];
  int n = snprintf(buf, sizeof buf, "%u", (unsigned)UNTAGI(x));
  V s = fpp_str_c(buf, (size_t)n);
  fpp_print(s);
}

/* ---- init --------------------------------------------------------------- */

V fpp_cmpv_clo_ = 0;
static V fpp_cmpv_code_(V self, V *args) {
  (void)self;
  return TAGI(fpp_cmpv(args[0], args[1]));
}

void fpp_lang_init(void) {
  /* FPP_HEAP_MB: initial heap for compiled programs. The growable policy
   * still applies; a bigger floor keeps a copying collector out of
   * near-boundary thrash on allocation-heavy workloads. */
  struct fpprt_opts opts = { 0 };
  const char *mb = getenv("FPP_HEAP_MB");
  if (mb && mb[0]) opts.heap_bytes = (size_t)strtoull(mb, NULL, 10) << 20;
  fpprt_init(opts.heap_bytes ? &opts : NULL);
  fpprt_register_type(FPP_TID_STR, (struct fpprt_type){
    2, FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "string" });
  fpprt_register_type(FPP_TID_F64, (struct fpprt_type){
    sizeof(double), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "float" });
  fpprt_register_type(FPP_TID_I64, (struct fpprt_type){
    sizeof(int64_t), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "int64" });
  fpprt_register_type(FPP_TID_TUPLE, (struct fpprt_type){
    0, FPPRT_KIND_REF_ARRAY, 0, NULL, "tuple" });
  fpprt_register_type(FPP_TID_ARR, (struct fpprt_type){
    0, FPPRT_KIND_REF_ARRAY, 0, NULL, "array" });
  fpprt_register_type(FPP_TID_AF64, (struct fpprt_type){
    sizeof(double), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "float[]" });
  fpprt_register_type(FPP_TID_AF32, (struct fpprt_type){
    sizeof(float), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "float32[]" });
  fpprt_register_type(FPP_TID_AI64, (struct fpprt_type){
    sizeof(int64_t), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "int64[]" });
  fpprt_register_type(FPP_TID_AI32, (struct fpprt_type){
    sizeof(int32_t), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "int[]" });
  fpprt_register_type(FPP_TID_AU16, (struct fpprt_type){
    sizeof(uint16_t), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "char[]" });
  fpprt_register_type(FPP_TID_AU8, (struct fpprt_type){
    1, FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "byte[]" });
  fpp_reg_struct(FPP_TID_CONS, 2, FPP_TC_OTHER, "cons");
  /* [tag][src][idx]: idx is a TAGGED int, so both fields sit on the map
   * and the tracer skips the tagged one */
  fpp_reg_struct(FPP_TID_ENUM, 2, FPP_TC_OTHER, "enum");
  fpp_reg_struct(FPP_TID_CELL, 1, FPP_TC_OTHER, "cell");
  fpp_reg_clo(FPP_TID_PAP, 2);
  fpp_reg_clo(FPP_TID_CMPCLO, 0);
  fpp_cmpv_clo_ = fpp_clo_new(FPP_TID_CMPCLO, fpp_cmpv_code_, 2, 0);
  fpprt_add_static_roots(&fpp_cmpv_clo_, 1);
}

/* ---- string methods: the $str.* family, .NET semantics ------------------ */

static int fpp_str_index_of_(V s, V what, intptr_t start, int last) {
  size_t n = fpp_str_len(s);
  uint16_t *u = fpp_str_units(s);
  if (what & 1) {
    uint16_t c = (uint16_t)UNTAGI(what);
    if (last) {
      for (intptr_t i = (intptr_t)n - 1; i >= start; i--)
        if (u[i] == c) return (int)i;
    } else {
      for (size_t i = (size_t)start; i < n; i++)
        if (u[i] == c) return (int)i;
    }
    return -1;
  }
  size_t m = fpp_str_len(what);
  uint16_t *w = fpp_str_units(what);
  if (m == 0) return last ? (int)n : (int)start;
  if (m > n) return -1;
  if (last) {
    for (intptr_t i = (intptr_t)(n - m); i >= start; i--)
      if (memcmp(u + i, w, m * 2) == 0) return (int)i;
  } else {
    for (size_t i = (size_t)start; i + m <= n; i++)
      if (memcmp(u + i, w, m * 2) == 0) return (int)i;
  }
  return -1;
}

static V fpp_str_sub_(V s, size_t start, size_t len) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = s;
  V r = fpprt_alloc_array(FPP_TID_STR, len);
  memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]) + start, len * 2);
  FPPRT_LEAVE(f);
  return r;
}

static int fpp_str_ws_(uint16_t c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r'
      || c == '\v' || c == '\f' || c == 0xa0;
}

V fpp_str_method(const char *m, V recv, V *args, size_t nargs) {
  size_t n = fpp_str_len(recv);
  uint16_t *u = fpp_str_units(recv);
  if (!strcmp(m, "Contains"))
    return TAGI(fpp_str_index_of_(recv, args[0], 0, 0) >= 0);
  if (!strcmp(m, "IndexOf")) {
    intptr_t start = nargs > 1 ? UNTAGI(args[1]) : 0;
    return TAGI(fpp_str_index_of_(recv, args[0], start, 0));
  }
  if (!strcmp(m, "LastIndexOf"))
    return TAGI(fpp_str_index_of_(recv, args[0], 0, 1));
  if (!strcmp(m, "StartsWith")) {
    size_t mlen = fpp_str_len(args[0]);
    return TAGI(mlen <= n && memcmp(u, fpp_str_units(args[0]), mlen * 2) == 0);
  }
  if (!strcmp(m, "EndsWith")) {
    size_t mlen = fpp_str_len(args[0]);
    return TAGI(mlen <= n
                && memcmp(u + n - mlen, fpp_str_units(args[0]), mlen * 2) == 0);
  }
  if (!strcmp(m, "Substring")) {
    size_t start = (size_t)UNTAGI(args[0]);
    size_t len = nargs > 1 ? (size_t)UNTAGI(args[1]) : n - start;
    if (start > n || start + len > n)
      fpp_raise(fpp_failure("Substring out of range", 22));
    return fpp_str_sub_(recv, start, len);
  }
  if (!strcmp(m, "Remove")) {
    size_t start = (size_t)UNTAGI(args[0]);
    size_t cut = nargs > 1 ? (size_t)UNTAGI(args[1]) : n - start;
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpprt_alloc_array(FPP_TID_STR, n - cut);
    memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]), start * 2);
    memcpy(fpp_str_units(r) + start, fpp_str_units(f_slots[0]) + start + cut,
           (n - start - cut) * 2);
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Insert")) {
    size_t at = (size_t)UNTAGI(args[0]);
    FPPRT_FRAME(f, 2);
    f_slots[0] = recv;
    f_slots[1] = args[1];
    size_t mlen = fpp_str_len(f_slots[1]);
    V r = fpprt_alloc_array(FPP_TID_STR, n + mlen);
    memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]), at * 2);
    memcpy(fpp_str_units(r) + at, fpp_str_units(f_slots[1]), mlen * 2);
    memcpy(fpp_str_units(r) + at + mlen, fpp_str_units(f_slots[0]) + at,
           (n - at) * 2);
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Replace")) {
    /* build by scanning; args may be chars or strings */
    FPPRT_FRAME(f, 3);
    f_slots[0] = recv;
    f_slots[1] = args[0];
    f_slots[2] = args[1];
    if ((f_slots[1] & 1) && (f_slots[2] & 1)) {
      V r = fpp_str_sub_(f_slots[0], 0, n);
      uint16_t from = (uint16_t)UNTAGI(f_slots[1]);
      uint16_t to = (uint16_t)UNTAGI(f_slots[2]);
      for (size_t i = 0; i < n; i++)
        if (fpp_str_units(r)[i] == from) fpp_str_units(r)[i] = to;
      FPPRT_LEAVE(f);
      return r;
    }
    size_t flen = fpp_str_len(f_slots[1]);
    size_t tlen = fpp_str_len(f_slots[2]);
    /* count matches */
    size_t count = 0;
    for (size_t i = 0; flen && i + flen <= n;) {
      if (memcmp(fpp_str_units(f_slots[0]) + i, fpp_str_units(f_slots[1]),
                 flen * 2) == 0) { count++; i += flen; }
      else i++;
    }
    V r = fpprt_alloc_array(FPP_TID_STR, n + count * tlen - count * flen);
    uint16_t *out = fpp_str_units(r);
    size_t k = 0;
    for (size_t i = 0; i < n;) {
      if (flen && i + flen <= n
          && memcmp(fpp_str_units(f_slots[0]) + i, fpp_str_units(f_slots[1]),
                    flen * 2) == 0) {
        memcpy(out + k, fpp_str_units(f_slots[2]), tlen * 2);
        k += tlen;
        i += flen;
      } else out[k++] = fpp_str_units(f_slots[0])[i++];
    }
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "ToUpper") || !strcmp(m, "ToLower")) {
    int up = m[2] == 'U';
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpp_str_sub_(f_slots[0], 0, n);
    for (size_t i = 0; i < n; i++) {
      uint16_t c = fpp_str_units(r)[i];
      if (up && c >= 'a' && c <= 'z') fpp_str_units(r)[i] = c - 32;
      if (!up && c >= 'A' && c <= 'Z') fpp_str_units(r)[i] = c + 32;
    }
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Trim") || !strcmp(m, "TrimStart") || !strcmp(m, "TrimEnd")) {
    size_t a = 0, b = n;
    int doStart = strcmp(m, "TrimEnd") != 0;
    int doEnd = strcmp(m, "TrimStart") != 0;
    if (doStart) while (a < b && fpp_str_ws_(u[a])) a++;
    if (doEnd) while (b > a && fpp_str_ws_(u[b - 1])) b--;
    return fpp_str_sub_(recv, a, b - a);
  }
  if (!strcmp(m, "PadLeft") || !strcmp(m, "PadRight")) {
    size_t want = (size_t)UNTAGI(args[0]);
    uint16_t fill = nargs > 1 ? (uint16_t)UNTAGI(args[1]) : ' ';
    if (want <= n) return recv;
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpprt_alloc_array(FPP_TID_STR, want);
    size_t pad = want - n;
    if (m[3] == 'L') {
      for (size_t i = 0; i < pad; i++) fpp_str_units(r)[i] = fill;
      memcpy(fpp_str_units(r) + pad, fpp_str_units(f_slots[0]), n * 2);
    } else {
      memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]), n * 2);
      for (size_t i = 0; i < pad; i++) fpp_str_units(r)[n + i] = fill;
    }
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "ToCharArray")) {
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpp_arr_new(n);
    for (size_t i = 0; i < n; i++)
      ((uintptr_t *)r)[i + 2] = TAGI(fpp_str_units(f_slots[0])[i]);
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Split")) {
    /* split on one char (tagged) — .NET drops nothing by default */
    FPPRT_FRAME(f, 2);
    f_slots[0] = recv;
    uint16_t sep = (uint16_t)UNTAGI(args[0]);
    size_t parts = 1;
    for (size_t i = 0; i < n; i++) if (u[i] == sep) parts++;
    f_slots[1] = fpp_arr_new(parts);
    size_t start = 0, k = 0;
    for (size_t i = 0; i <= n; i++) {
      if (i == n || fpp_str_units(f_slots[0])[i] == sep) {
        V piece = fpp_str_sub_(f_slots[0], start, i - start);
        fpp_arr_set(f_slots[1], k++, piece);
        start = i + 1;
      }
    }
    V r = f_slots[1];
    FPPRT_LEAVE(f);
    return r;
  }
  fprintf(stderr, "fpp: string method %s\n", m);
  fpp_not_emitted("string method");
  return 0;
}

/* ---- ConditionalWeakTable ----------------------------------------------- */

#define CWT_SLOT_(i) ((uint32_t)(((i) + 2) * sizeof(V)))

void fpp_cwt_init(V self) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = self;
  V a = fpp_arr_zeroed(0, 8);
  fpprt_write_ref(f_slots[0], sizeof(V), a);
  FPPRT_LEAVE(f);
}

V fpp_cwt_tryget(V self, V k) {
  V a = fpprt_read_ref(self, sizeof(V));
  size_t n = fpprt_array_len(a);
  for (size_t i = 0; i < n; i++) {
    V e = fpprt_read_ref(a, CWT_SLOT_(i));
    if (e && fpprt_eph_key(e) == k)
      return fpprt_eph_value(e);
  }
  return 0;
}

void fpp_cwt_add(V self, V k, V v) {
  FPPRT_FRAME(f, 4);
  f_slots[0] = self; f_slots[1] = k; f_slots[2] = v;
  f_slots[3] = fpprt_eph_new(f_slots[1], f_slots[2]);
  V a = fpprt_read_ref(f_slots[0], sizeof(V));
  size_t n = fpprt_array_len(a);
  for (size_t i = 0; i < n; i++) {
    V e = fpprt_read_ref(a, CWT_SLOT_(i));
    if (!e || !fpprt_eph_key(e)) {
      fpprt_write_ref(a, CWT_SLOT_(i), f_slots[3]);
      FPPRT_LEAVE(f);
      return;
    }
  }
  /* full: grow, keeping only live entries */
  V b = fpp_arr_zeroed(0, n * 2);
  a = fpprt_read_ref(f_slots[0], sizeof(V));
  size_t j = 0;
  for (size_t i = 0; i < n; i++) {
    V e = fpprt_read_ref(a, CWT_SLOT_(i));
    if (e && fpprt_eph_key(e))
      fpprt_write_ref(b, CWT_SLOT_(j++), e);
  }
  fpprt_write_ref(b, CWT_SLOT_(j), f_slots[3]);
  fpprt_write_ref(f_slots[0], sizeof(V), b);
  FPPRT_LEAVE(f);
}

V fpp_cwt_remove(V self, V k) {
  V a = fpprt_read_ref(self, sizeof(V));
  size_t n = fpprt_array_len(a);
  for (size_t i = 0; i < n; i++) {
    V e = fpprt_read_ref(a, CWT_SLOT_(i));
    if (e && fpprt_eph_key(e) == k) {
      fpprt_write_ref(a, CWT_SLOT_(i), 0);
      return TAGI(1);
    }
  }
  return TAGI(0);
}

V fpp_cwt_count(V self) {
  V a = fpprt_read_ref(self, sizeof(V));
  size_t n = fpprt_array_len(a), c = 0;
  for (size_t i = 0; i < n; i++) {
    V e = fpprt_read_ref(a, CWT_SLOT_(i));
    if (e && fpprt_eph_key(e)) c++;
  }
  return TAGI((intptr_t)c);
}

V fpp_cwt_indexof(V self, V k) {
  V a = fpprt_read_ref(self, sizeof(V));
  size_t n = fpprt_array_len(a);
  for (size_t i = 0; i < n; i++) {
    V e = fpprt_read_ref(a, CWT_SLOT_(i));
    if (e && fpprt_eph_key(e) == k)
      return TAGI((intptr_t)i);
  }
  return TAGI(-1);
}

/* out-of-line i64 box hooks for the 32-bit TAGI/UNTAGI spill path (the
 * inline helpers in the header run before fpp_box_i64 is declared) */
V fpp_box_i64_(int64_t x) { return fpp_box_i64(x); }
int64_t fpp_unbox_i64_(V b) { return fpp_unbox_i64(b); }

/* ---- POD (blittable) structs -------------------------------------------- */

struct fpp_pod_field_ { uint32_t off; char kind; };
struct fpp_pod_info_ {
  uint32_t size;
  uint32_t nfields, cap;
  struct fpp_pod_field_ *fields;
  uint32_t elemtid;                 /* for ARRAY tids: the element's tid */
};
static struct fpp_pod_info_ **fpp_pods_ = NULL;
static size_t fpp_pods_cap_ = 0;

static struct fpp_pod_info_ *fpp_pod_info_(uint32_t tid) {
  return tid < fpp_pods_cap_ ? fpp_pods_[tid] : NULL;
}
static struct fpp_pod_info_ *fpp_pod_ensure_(uint32_t tid) {
  if (tid >= fpp_pods_cap_) {
    size_t cap = fpp_pods_cap_ ? fpp_pods_cap_ : 64;
    while (tid >= cap) cap *= 2;
    struct fpp_pod_info_ **n = calloc(cap, sizeof(*n));
    if (!n) abort();
    for (size_t i = 0; i < fpp_pods_cap_; i++) n[i] = fpp_pods_[i];
    free(fpp_pods_);
    fpp_pods_ = n;
    fpp_pods_cap_ = cap;
  }
  if (!fpp_pods_[tid]) {
    fpp_pods_[tid] = calloc(1, sizeof(struct fpp_pod_info_));
    if (!fpp_pods_[tid]) abort();
  }
  return fpp_pods_[tid];
}

void fpp_reg_pod(uint32_t tid, uint32_t size, const char *name) {
  struct fpp_pod_info_ *p = fpp_pod_ensure_(tid);
  p->size = size;
  /* the heap blob: header pad to FPP_POD_OFF + payload, no ref fields */
  uint32_t total = FPP_POD_OFF + ((size + 7u) & ~7u);
  fpprt_register_type(tid, (struct fpprt_type){
    total, FPPRT_KIND_STRUCT, 0, NULL, name });
  fpp_reg_meta_(tid, FPP_TC_POD, 0);
}

void fpp_reg_pod_field(uint32_t tid, uint32_t off, char kind) {
  struct fpp_pod_info_ *p = fpp_pod_ensure_(tid);
  if (p->nfields == p->cap) {
    p->cap = p->cap ? p->cap * 2 : 8;
    p->fields = realloc(p->fields, p->cap * sizeof(*p->fields));
    if (!p->fields) abort();
  }
  p->fields[p->nfields].off = off;
  p->fields[p->nfields].kind = kind;
  p->nfields++;
}

void fpp_reg_pod_arr(uint32_t arrtid, uint32_t elemtid, uint32_t elemsz,
                     const char *name) {
  struct fpp_pod_info_ *p = fpp_pod_ensure_(arrtid);
  p->size = elemsz;
  p->elemtid = elemtid;
  fpprt_register_type(arrtid, (struct fpprt_type){
    elemsz, FPPRT_KIND_SCALAR_ARRAY, 0, NULL, name });
}

V fpp_pod_box(uint32_t tid, uint32_t size) {
  (void)size;
  return fpprt_alloc(tid);            /* zeroed by the allocator */
}

V fpp_pod_get(V a, size_t i, uint32_t elemtid) {
  fpp_arr_check_(a, i);
  uint32_t sz = fpp_pod_info_(elemtid)->size;
  FPPRT_FRAME(f, 1);
  f_slots[0] = a;
  V b = fpprt_alloc(elemtid);
  memcpy((char *)b + FPP_POD_OFF,
         (char *)fpprt_elems(f_slots[0]) + i * sz, sz);
  FPPRT_LEAVE(f);
  return b;
}

void fpp_pod_set(V a, size_t i, V blob) {
  fpp_arr_check_(a, i);
  uint32_t sz = fpp_pod_info_(fpprt_typeid(blob))->size;
  memcpy((char *)fpprt_elems(a) + i * sz, (char *)blob + FPP_POD_OFF, sz);
}

static int fpp_pod_field_cmp_(char k, const char *pa, const char *pb) {
  switch (k) {
  case 'f': { double x = *(double *)pa, y = *(double *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 's': { float x = *(float *)pa, y = *(float *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 'l': { int64_t x = *(int64_t *)pa, y = *(int64_t *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 'v': { uint64_t x = *(uint64_t *)pa, y = *(uint64_t *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 'i': { int32_t x = *(int32_t *)pa, y = *(int32_t *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 'w': { uint32_t x = *(uint32_t *)pa, y = *(uint32_t *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 'm': { int16_t x = *(int16_t *)pa, y = *(int16_t *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 'h': { uint16_t x = *(uint16_t *)pa, y = *(uint16_t *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  case 'n': { int8_t x = *(int8_t *)pa, y = *(int8_t *)pb;
              return x < y ? -1 : x > y ? 1 : 0; }
  default: { uint8_t x = *(uint8_t *)pa, y = *(uint8_t *)pb;
             return x < y ? -1 : x > y ? 1 : 0; }
  }
}

int fpp_pod_eq(V a, V b) {
  struct fpp_pod_info_ *p = fpp_pod_info_(fpprt_typeid(a));
  const char *pa = (const char *)a + FPP_POD_OFF;
  const char *pb = (const char *)b + FPP_POD_OFF;
  for (uint32_t i = 0; i < p->nfields; i++)
    if (fpp_pod_field_cmp_(p->fields[i].kind, pa + p->fields[i].off,
                           pb + p->fields[i].off) != 0) return 0;
  return 1;
}

int fpp_pod_cmp(V a, V b) {
  struct fpp_pod_info_ *p = fpp_pod_info_(fpprt_typeid(a));
  const char *pa = (const char *)a + FPP_POD_OFF;
  const char *pb = (const char *)b + FPP_POD_OFF;
  for (uint32_t i = 0; i < p->nfields; i++) {
    int c = fpp_pod_field_cmp_(p->fields[i].kind, pa + p->fields[i].off,
                               pb + p->fields[i].off);
    if (c) return c;
  }
  return 0;
}

intptr_t fpp_pod_hash(V v) {
  struct fpp_pod_info_ *p = fpp_pod_info_(fpprt_typeid(v));
  const char *pv = (const char *)v + FPP_POD_OFF;
  intptr_t h = 29 + (intptr_t)fpprt_typeid(v);
  for (uint32_t i = 0; i < p->nfields; i++) {
    const char *pf = pv + p->fields[i].off;
    intptr_t x;
    switch (p->fields[i].kind) {
    case 'f': x = (intptr_t)*(double *)pf; break;
    case 's': x = (intptr_t)*(float *)pf; break;
    case 'l': case 'v': x = (intptr_t)*(int64_t *)pf; break;
    case 'i': case 'w': x = (intptr_t)*(int32_t *)pf; break;
    case 'm': case 'h': x = (intptr_t)*(uint16_t *)pf; break;
    default: x = (intptr_t)*(uint8_t *)pf; break;
    }
    h = h * 31 + x;
  }
  return h & 0x3fffffff;
}

/* ---- linear memory arena ------------------------------------------------ */

/* Addresses in the Memory/pin world are ABSOLUTE 32-bit-representable
 * pointers: on wasm32 every pointer already is one; natively the heap and
 * this arena live in the low 2GB (MAP_32BIT reservations). fpp_mem_base()
 * returns NULL so foreign code's base+offset arithmetic stays valid. */
static char *fpp_mem_ = NULL;
static size_t fpp_mem_top_ = 0;
static size_t fpp_mem_cap_ = 0;

static void fpp_mem_init_(void) {
  if (fpp_mem_) return;
  fpp_mem_cap_ = (size_t)1 << 26;     /* 64 MB, fixed: addresses are stable */
#if defined(__wasm__)
  fpp_mem_ = calloc(1, fpp_mem_cap_);
  if (!fpp_mem_) abort();
#else
  void *m = MAP_FAILED;
#ifdef MAP_32BIT
  m = mmap(NULL, fpp_mem_cap_, PROT_READ | PROT_WRITE,
           MAP_PRIVATE | MAP_ANONYMOUS | MAP_32BIT, -1, 0);
#endif
  if (m == MAP_FAILED)
    m = mmap(NULL, fpp_mem_cap_, PROT_READ | PROT_WRITE,
             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (m == MAP_FAILED) abort();
  fpp_mem_ = (char *)m;
#endif
  if ((uintptr_t)fpp_mem_ + fpp_mem_cap_ > 0x7fffffffu) {
    fprintf(stderr, "fpp: Memory arena outside the 32-bit address range\n");
    abort();
  }
}

char *fpp_mem_base(void) { return NULL; }

int32_t fpp_mem_alloc(int32_t n) {
  fpp_mem_init_();
  size_t off = (fpp_mem_top_ + 7) & ~(size_t)7;
  if (off + (size_t)n > fpp_mem_cap_) {
    fprintf(stderr, "fpp: Memory arena exhausted\n");
    abort();
  }
  fpp_mem_top_ = off + (size_t)n;
  return (int32_t)(uintptr_t)(fpp_mem_ + off);
}

int32_t fpp_mem_size(void) { fpp_mem_init_(); return (int32_t)fpp_mem_cap_; }

void fpp_mem_copy(int32_t dst, int32_t src, int32_t n) {
  memmove((char *)(uintptr_t)(uint32_t)dst, (char *)(uintptr_t)(uint32_t)src,
          (size_t)n);
}

int32_t fpp_arr_bytesize(V a) {
  uint32_t tid = fpprt_typeid(a);
  struct fpp_pod_info_ *p = fpp_pod_info_(tid);
  uint32_t elem;
  if (p && p->size) elem = p->size;
  else if (tid == FPP_TID_AF64 || tid == FPP_TID_AI64) elem = 8;
  else if (tid == FPP_TID_AF32 || tid == FPP_TID_AI32) elem = 4;
  else if (tid == FPP_TID_AU16 || tid == FPP_TID_STR) elem = 2;
  else if (tid == FPP_TID_AU8) elem = 1;
  else elem = (uint32_t)sizeof(V);
  return (int32_t)(fpprt_array_len(a) * elem);
}

/* pinning is IN-PLACE: the flat element storage IS the C image, the
 * collector guarantees the object never moves (mmc; the always-moving
 * collectors abort — pinning workloads run the pinning collector). The
 * pinned array stays reachable through the program's own references;
 * foreign writes are visible through the array IMMEDIATELY, .NET `fixed`
 * semantics. Unpin is a no-op: mmc pins are for the object's lifetime. */
int32_t fpp_arr_pin(V a) {
  if (!fpprt_can_pin()) {
    fprintf(stderr, "fpp: Array.pin needs the pinning collector (mmc)\n");
    abort();
  }
  fpprt_pin(a);
  uintptr_t addr = (uintptr_t)fpprt_elems(a);
  if (addr > 0x7fffffffu) {
    fprintf(stderr, "fpp: pinned address outside the 32-bit range\n");
    abort();
  }
  return (int32_t)addr;
}

void fpp_arr_unpin(V a) { (void)a; }

/* ---- dispatching array accessors ---------------------------------------- */

V fpp_arr_get(V a, size_t i) {
  fpp_arr_check_(a, i);
  switch (fpprt_typeid(a)) {
  case FPP_TID_AF64: return fpp_box_f64(((double *)fpprt_elems(a))[i]);
  case FPP_TID_AF32: return fpp_box_f64((double)((float *)fpprt_elems(a))[i]);
  case FPP_TID_AI64: return fpp_box_i64(((int64_t *)fpprt_elems(a))[i]);
  case FPP_TID_AI32: return TAGI((intptr_t)((int32_t *)fpprt_elems(a))[i]);
  case FPP_TID_AU16: return TAGI((intptr_t)((uint16_t *)fpprt_elems(a))[i]);
  case FPP_TID_AU8:  return TAGI((intptr_t)((uint8_t *)fpprt_elems(a))[i]);
  default: {
    struct fpp_pod_info_ *p = fpp_pod_info_(fpprt_typeid(a));
    if (p && p->elemtid) return fpp_pod_get(a, i, p->elemtid);
    return fpprt_read_ref(a, (uint32_t)((i + 2) * sizeof(V)));
  }
  }
}

void fpp_arr_set(V a, size_t i, V v) {
  fpp_arr_check_(a, i);
  switch (fpprt_typeid(a)) {
  /* stores coerce representational drift the way the arith family does */
  case FPP_TID_AF64: ((double *)fpprt_elems(a))[i] = fpp_as_f64_(v); return;
  case FPP_TID_AF32: ((float *)fpprt_elems(a))[i] = (float)fpp_as_f64_(v); return;
  case FPP_TID_AI64: ((int64_t *)fpprt_elems(a))[i] = fpp_as_i64_(v); return;
  case FPP_TID_AI32: ((int32_t *)fpprt_elems(a))[i] = (int32_t)fpp_as_i64_(v); return;
  case FPP_TID_AU16: ((uint16_t *)fpprt_elems(a))[i] = (uint16_t)fpp_as_i64_(v); return;
  case FPP_TID_AU8:  ((uint8_t *)fpprt_elems(a))[i] = (uint8_t)fpp_as_i64_(v); return;
  default: {
    struct fpp_pod_info_ *p = fpp_pod_info_(fpprt_typeid(a));
    if (p && p->elemtid) { fpp_pod_set(a, i, v); return; }
    fpprt_write_ref(a, (uint32_t)((i + 2) * sizeof(V)), v);
  }
  }
}


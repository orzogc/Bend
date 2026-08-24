
// Imports
// =======

#pragma clang fp contract(off)

#ifdef __METAL_VERSION__
#include <metal_stdlib>
using namespace metal;
#else
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/resource.h>
#if BEND_METAL
#import <Metal/Metal.h>
#import <Foundation/Foundation.h>
#endif
#endif

// Dialect
// =======

#ifdef __METAL_VERSION__
#define DEV     device
#define GRP     threadgroup
#define THR     thread
#define INLINE  inline
#define HOT     inline
#define OUTLINE static
#define CONSTV  constant
#define DEVICE  1
#define A32(p)  ((DEV atomic_uint*)(p))
#define RLX     memory_order_relaxed
#define FENCE() atomic_thread_fence(mem_flags::mem_device, memory_order_seq_cst)
#else
#define DEV
#define THR
#define INLINE  static inline
#define HOT     static inline __attribute__((always_inline))
#define OUTLINE static __attribute__((noinline))
#define CONSTV  static const
#define DEVICE  0
#define FENCE() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#endif

#ifdef __METAL_VERSION__
#define WL_CASE(F) case F:
#define WL_JMP(F)  { fid = (F); break; }
#define WL_DYN     WL_JMP
#define WL_SPIN \
  for (;;) { \
    if (err_spun(e.mem, &wpoll, 4095)) { \
      return 0; \
    }
#define WL_SPUN    } break;
#else
#define WL_CASE(F) L_##F: ;
#define WL_JMP(F)  goto L_##F
#define WL_DYN(F)  { fid = (F); goto *wl_lbl[fid]; }
#define WL_SPIN    for (;;) {
#define WL_SPUN    }
#endif
#define WL_AGAIN   continue
#define WL_POP() { sp -= LANE_STEP; WL_DYN((Fid)STK(0)); }

#ifdef __METAL_VERSION__
#define LANE_STEP CUBE
#else
#define LANE_STEP 1
#endif
#define STK(I) sp[(int64_t)(I) * LANE_STEP]

#define WL_RET(V) { res = (V); WL_POP(); }
#define WL_CONT   STK(-3)
#define WL_IDX    STK(-2)
#define WL_POPN(N)  sp -= N * LANE_STEP
#define WL_PUSHN(N) sp += N * LANE_STEP
#define WL_KONT(F, T, I) WL_CONT = term_task(F, T); WL_IDX = I
#define WL_KID(J, A, F, C) e.mem[J + A] = term_task(F, C)
#define TAB_AT(T, S, I) T[S < I ? S : I]

// Types
// =====

#ifdef __METAL_VERSION__
typedef ulong u64;
typedef uint  u32;
typedef uchar u8;
typedef float f32;
#else
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
typedef float    f32;
#endif

typedef u64 Loc;
#define LOC_MASK ((1ull << 40) - 1)

#define f32_unbox(x)  __builtin_bit_cast(f32, (u32)(x))
#define u32_unbox(x)  ((u32)(x))
#define f32_rewrap(x) ((u64)__builtin_bit_cast(u32, (f32)(x)))
#define u32_rewrap(x) ((u64)(x))

#define u32_inc(a)      U32_BIN(a, +, 1)
#define u32_not(a)      u32_rewrap(~u32_unbox(a))
#define u32_shl(a)      U32_BIN(a, <<, 1)
#define u32_shr(a)      U32_BIN(a, >>, 1)
#define u32_is_zero(a)  U32_BIN(a, ==, 0)
#define u32_to_f32(a)   f32_rewrap((f32)u32_unbox(a))
#define u32_to_nat(a)   u32_rewrap(u32_unbox(a))
#define u32_from_nat    u32_to_nat
#define U32_BIN(a, o, b) u32_rewrap(u32_unbox(a) o u32_unbox(b))
#define F32_BIN(a, o, b) f32_rewrap(f32_unbox(a) o f32_unbox(b))
#define F32_CMP(a, o, b) u32_rewrap(f32_unbox(a) o f32_unbox(b))

#define u32_and(a, b)   U32_BIN(a, &, b)
#define u32_or(a, b)    U32_BIN(a, |, b)
#define u32_xor(a, b)   U32_BIN(a, ^, b)
#define u32_is_eq(a, b) U32_BIN(a, ==, b)
#define u32_is_ne(a, b) U32_BIN(a, !=, b)
#define u32_is_lt(a, b) U32_BIN(a, <, b)
#define u32_is_le(a, b) U32_BIN(a, <=, b)
#define u32_is_gt(a, b) U32_BIN(a, >, b)
#define u32_is_ge(a, b) U32_BIN(a, >=, b)
#define u32_cmp(a, b) (u32_is_gt(a, b) + u32_is_ge(a, b))
#define u32_add(a, b)   U32_BIN(a, +, b)
#define u32_sub(a, b)   U32_BIN(a, -, b)
#define u32_mul(a, b)   U32_BIN(a, *, b)
#define bool_or(a, b)   ((a) | (b))
#define bool_xor(a, b)  ((a) ^ (b))
#define f32_add(a, b)   F32_BIN(a, +, b)
#define f32_sub(a, b)   F32_BIN(a, -, b)
#define f32_mul(a, b)   F32_BIN(a, *, b)
#define f32_div(a, b)   F32_BIN(a, /, b)
#define f32_sqrt(a)     f32_rewrap(sqrtf(f32_unbox(a)))

typedef u32 Cls;

typedef u32 Fid;

typedef u32 Cid;

typedef u64 Term;
#define TAG_PACK  1ull
#define TAG_CTOR  2ull
#define TAG_CLOS  3ull
#define TAG_FLAT  4ull
#define TAG_TASK  5ull
#define TAG_ARRS  6ull
#define TERM_HOLE (~0ull)

#define RFC_BIT  (1ull << 63)
#define RFC_CNT  ((1u << 24) - 1)

typedef Term Reply;

typedef u32 Err;
#define ERR_FAIL 1
#define ERR_RING 2
#define ERR_TAGS 3
#define ERR_HEAP 5
#define ERR_FIDS 6
#define ERR_LEAK 7
#define ERR_NATS 8
#define ERR_RFCS 9
#define ERR_DEEP 10
#define ERR_TICK ((1u << 20) - 1)

typedef u32 Page;
#define PAGE_NIL 0xFFFFFFFEu

typedef u32 Monk;
#define M_RING_PUT  0
#define M_RING_GET  1
#define M_HEAD      2
#define M_HUGE      (2 + 2 * NCLS)
#define M_SNAP      (3 + 2 * NCLS)
#define monk_word(H, m, w) ((H) + MONK_OFF + (u64)(w) * CUBE + (m))

typedef u32 Ring;

#define MONK_OFF 96ull
#define RING_OFF (MONK_OFF + CUBE * MONK_WORDS)
#define STAK_OFF (RING_OFF + CUBE * RING_LEN)

#define H_PAGE_BUMP   0ull
#define H_PAGE_CAP    8ull
#define H_HUGE_FREE  32ull
#define H_ROOT_WORD  56ull
#define H_ROOT_DONE  57ull
#define H_CURSOR     58ull
#define H_ERROR_CODE 64ull
#define H_TOME_WIRED 65ull

#define HEAP_OFF  (STAK_OFF + CUBE * STAK_LEN)

typedef DEV u64* Corpus;

typedef struct {
  Corpus   mem;
  Monk     mnk;
#ifdef __METAL_VERSION__
  GRP u64* alc;
#endif
} Env;

typedef DEV Term* Stk;

typedef Term Nat;
#define NAT_IMM ((1ull << 48) - 1)

typedef Term U32;

typedef Term Str;
#define SHOW_STRING 0
#define SHOW_NAT    1
#define SHOW_U32    2
#define SHOW_CHAR   3
#define SHOW_DASH   4
#define SHOW_SIGMA  5

// Constants
// =========

#define PAGE_BITS  7
#define QUANTUM_BITS (DEVICE ? PAGE_BITS : 12)
#define DOOM_WORDS (1ull << NCLS)
#define CUBE_SIDE  128
#define CUBE       (1ull << 14)
#define RING_LEN   (1ull << 10)
#define STAK_LEN   (1ull << 11)
#define MONK_WORDS 32ull
#define NCLS       9
#define HUGE_CLS   (32 - NCLS)
#define TOME_PAGES (1u << 18)

// Globals
// =======

#ifndef __METAL_VERSION__

static Corpus CORPUS;

static u32   pool_size;
static _Atomic u32 pool_row;
static bool  pool_grow;
static _Atomic u64 pool_tick;
static _Atomic u32 pool_done;
static pthread_mutex_t pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  pool_wake = PTHREAD_COND_INITIALIZER;

#if BEND_METAL
static id<MTLDevice>               gpu_dev;
static id<MTLCommandQueue>         gpu_que;
static id<MTLLibrary>              gpu_lib;
static id<MTLComputePipelineState> gpu_grow_pso;
static id<MTLComputePipelineState> gpu_work_pso;
static id<MTLBuffer>               gpu_buf;
static u64                         gpu_wired;
static u64                         gpu_cap;
#endif

#endif

// Book
// ====

INLINE u32 fid_arity(Fid fid) {
  return (u32)FID_ARITY_T[fid];
}

INLINE bool fid_bangs(Fid fid) {
  return (bool)FID_BANGS_T[fid];
}

INLINE bool fid_nofk(Fid fid) {
  return (bool)FID_NOFK_T[fid];
}

INLINE bool fid_seqk(Fid fid) {
  return (bool)FID_SEQK_T[fid];
}

INLINE u32 cid_arity(Cid cid) {
  return (u32)CID_ARITY_T[cid];
}

// A32
// ===

#ifdef __METAL_VERSION__

#define a32_load(p)         atomic_load_explicit(A32(p), RLX)
#define a32_store(p, v)     atomic_store_explicit(A32(p), v, RLX)
#define a32_add(p, v)       atomic_fetch_add_explicit(A32(p), v, RLX)

INLINE u32 a32_sub_rel(DEV u32* p, u32 v) {
  FENCE();
  return atomic_fetch_sub_explicit(A32(p), v, RLX);
}

INLINE void a32_store_rel(DEV u32* p, u32 v) {
  FENCE();
  atomic_store_explicit(A32(p), v, RLX);
}

INLINE u32 a32_load_acq(DEV u32* p) {
  u32 v = a32_load(p);
  FENCE();
  return v;
}

#define a32_acq(p) FENCE()

INLINE bool a32_cas(DEV u32* p, thread u32* e, u32 v) {
  FENCE();
  bool ok = atomic_compare_exchange_weak_explicit(A32(p), e, v, RLX, RLX);
  if (ok) {
    FENCE();
  }
  return ok;
}

#else

#define a32_load(p)         __atomic_load_n(p, __ATOMIC_RELAXED)
#define a32_store(p, v)     __atomic_store_n(p, v, __ATOMIC_RELAXED)
#define a32_add(p, v)       __atomic_fetch_add(p, v, __ATOMIC_RELAXED)
#define a32_sub_rel(p, v)   __atomic_fetch_sub(p, v, __ATOMIC_RELEASE)
#define a32_store_rel(p, v) __atomic_store_n(p, v, __ATOMIC_RELEASE)
#define a32_load_acq(p)     __atomic_load_n(p, __ATOMIC_ACQUIRE)
#define a32_acq(p)          ((void)a32_load_acq(p))

INLINE bool a32_cas(u32* p, u32* e, u32 v) {
  return __atomic_compare_exchange_n(
    p, e, v, 1, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
}

#endif

#define a32_at(H, word) ((DEV u32*)&(H)[word])

// Err
// ===

#ifdef __METAL_VERSION__

INLINE void err_post(Corpus H, Err code) {
  u32 seen = 0;
  while (!a32_cas(a32_at(H, H_ERROR_CODE), &seen, code)) {
    if (seen != 0) {
      return;
    }
  }
}

#else

static void err_fail(Err code, const char* msg) {
  fprintf(stderr, "bend: error %u: %s\n", code, msg);
  abort();
}

static void err_post(Corpus H, Err code) {
  (void)H;
  err_fail(code, "runtime fail-stop");
}

static void err_trap(int sig) {
  (void)sig;
  err_fail(ERR_DEEP, "memory fault (machine stack overflow?)");
}

#endif

INLINE bool err_seen(Corpus H) {
  return a32_load(a32_at(H, H_ERROR_CODE)) != 0;
}

INLINE bool err_spun(Corpus H, THR u32* n, u32 mask) {
  bool tick = (++*n & mask) == 0;
  return tick && err_seen(H);
}

// Cls
// ===

INLINE Cls cls_fit(u32 words) {
  Cls c = 0;
  while ((1u << c) < words) {
    c += 1;
  }
  return c;
}

// Page
// ====

#define page_loc(p) (HEAP_OFF + ((u64)(p) << PAGE_BITS))

INLINE Page page_claim(Corpus H, u32 span) {
  Page p = DEVICE && err_seen(H) ? 0
    : a32_add(a32_at(H, H_PAGE_BUMP), span);
  if ((u64)p + span > a32_load(a32_at(H, DEVICE ? H_TOME_WIRED : H_PAGE_CAP))) {
    err_post(H, ERR_HEAP);
    p = 0;
  }
  return p;
}

#define loc_doomed(loc) (DEVICE && (loc) == page_loc(0))

#if DEVICE

INLINE bool tight(Corpus H, u32 tomes) {
  u32 wired = a32_load(a32_at(H, H_TOME_WIRED));
  u32 bump  = a32_load(a32_at(H, H_PAGE_BUMP));
  return bump + tomes * TOME_PAGES >= wired
    && bump >= (tomes - 1) * TOME_PAGES
    && wired < a32_load(a32_at(H, H_PAGE_CAP));
}

INLINE bool park(Env e) {
  if (tight(e.mem, 1)) {
    a32_add(a32_at(e.mem, H_CURSOR), 1);
    return true;
  }
  return false;
}

#else

#define tight(H, tomes) false
#define park(e)         false

#endif

INLINE Page page_stack_pop(Corpus H, DEV u32* head) {
  for (;;) {
    u32 e = a32_load_acq(head);
    if (e == PAGE_NIL || (DEVICE && err_seen(H))) {
      return PAGE_NIL;
    }
    if (e != (u32)-1 && a32_cas(head, &e, (u32)-1)) {
      u32 next = a32_load(a32_at(H, page_loc(e)));
      a32_store_rel(head, next);
      return e;
    }
  }
}

INLINE void page_stack_push(Corpus H, Cls cls, Loc loc) {
  Page p = (u32)((loc - HEAP_OFF) >> PAGE_BITS);
  DEV u32* head = a32_at(H, H_HUGE_FREE + (cls - NCLS));
  DEV u32* link = a32_at(H, page_loc(p));
  u32 e = a32_load(head);
  for (;;) {
    if (DEVICE && err_seen(H)) {
      return;
    }
    if (e == (u32)-1) {
      e = a32_load(head);
      continue;
    }
    a32_store(link, e);
    if (a32_cas(head, &e, p)) {
      return;
    }
  }
}

// Heap
// ====

#define ALC_WORDS (2 * NCLS)
#ifdef __METAL_VERSION__
INLINE void alc_open(Env e) {
  for (u32 i = 0; i < ALC_WORDS; i += 1) {
    e.alc[i * CUBE_SIDE] = *monk_word(e.mem, e.mnk, M_HEAD + i);
  }
}
INLINE void alc_close(Env e) {
  for (u32 i = 0; i < ALC_WORDS; i += 1) {
    *monk_word(e.mem, e.mnk, M_HEAD + i) = e.alc[i * CUBE_SIDE];
  }
}

INLINE u64 alc_load(Env e, u32 ride, Cls c) {
  return e.alc[(ride * NCLS + c) * CUBE_SIDE];
}
INLINE void alc_store(Env e, u32 ride, Cls c, u64 v) {
  e.alc[(ride * NCLS + c) * CUBE_SIDE] = v;
}
#else
static u64 ALC[CUBE_SIDE][ALC_WORDS];
INLINE u64 alc_load(Env e, u32 ride, Cls c) {
  return ALC[e.mnk][ride * NCLS + c];
}
INLINE void alc_store(Env e, u32 ride, Cls c, u64 v) {
  ALC[e.mnk][ride * NCLS + c] = v;
}
#endif

#define cls_quantum(cls) (1u << ((cls) > QUANTUM_BITS ? (cls) : QUANTUM_BITS))

HOT void heap_free_huge(Env e, Cls cls, Loc loc) {
  if (!DEVICE) {
    page_stack_push(e.mem, cls, loc);
    return;
  }
  DEV u64* held = monk_word(e.mem, e.mnk, M_HUGE);
  u64 prev = *held;
  *held = ((u64)cls << 40) | loc;
  if (prev != 0) {
    page_stack_push(e.mem, (u32)(prev >> 40), prev & LOC_MASK);
  }
}

OUTLINE Loc heap_alloc_miss(Env e, Cls cls) {
  Corpus H = e.mem;
  if (cls >= NCLS) {
    if (DEVICE) {
      DEV u64* held = monk_word(H, e.mnk, M_HUGE);
      u64 prev = *held;
      if ((prev >> 40) == cls) {
        *held = 0;
        return prev & LOC_MASK;
      }
    }
    DEV u32* head = a32_at(H, H_HUGE_FREE + (cls - NCLS));
    Page got = page_stack_pop(H, head);
    if (got != PAGE_NIL) {
      return page_loc(got);
    }
    return page_loc(page_claim(H, 1u << (cls - PAGE_BITS)));
  }
  Page p = page_claim(H, cls_quantum(cls) >> PAGE_BITS);
  if (p == 0) {
    return page_loc(0);
  }
  alc_store(e, 1, cls, ((u64)(1u << cls) << 32) | (p + 1));
  return page_loc(p);
}

HOT Loc heap_alloc(Env e, Cls cls) {
  Corpus H = e.mem;
  if (cls < NCLS) {
    u64 h = alc_load(e, 0, cls);
    if (h != 0) {
      alc_store(e, 0, cls, H[h]);
      return h;
    }
    u64 own  = alc_load(e, 1, cls);
    u32 used = (u32)(own >> 32);
    if ((u32)own != 0 && used < cls_quantum(cls)) {
      alc_store(e, 1, cls, own + ((u64)(1u << cls) << 32));
      return page_loc((u32)own - 1) + used;
    }
  }
  return heap_alloc_miss(e, cls);
}

HOT void heap_free(Env e, Cls cls, Loc loc) {
  Corpus H = e.mem;
  if (cls < NCLS) {
    H[loc] = alc_load(e, 0, cls);
    alc_store(e, 0, cls, loc);
  } else {
    heap_free_huge(e, cls, loc);
  }
}

HOT void spare_free(Env e, Cls cls, Loc loc) {
  if (loc != 0) {
    heap_free(e, cls, loc);
  }
}

// Term
// ====

INLINE Term term_make(u64 tag, u64 aux, Loc loc) {
  return (tag << 56) | (aux << 40) | loc;
}

#define term_ctor(cid, loc) term_make(TAG_CTOR, cid, loc)
#define term_pack(cid, loc) term_make(TAG_PACK, cid, loc)
#define term_clos(fid, loc) term_make(TAG_CLOS, fid, loc)
#define term_flat(cls, loc) term_make(TAG_FLAT, cls, loc)
#define term_task(fid, loc) term_make(TAG_TASK, fid, loc)

INLINE Term term_arrs(bool arr, Cls cls, Loc loc) {
  return term_flat(cls, loc) | ((u64)arr << 57);
}

INLINE u64 term_tag(Term t) {
  return (t >> 56) & 0x7f;
}

INLINE bool term_rfc(Term t) {
  return (t & RFC_BIT) != 0;
}

INLINE u64 term_aux(Term t) {
  return (t >> 40) & 0xFFFF;
}

INLINE Loc term_loc(Term t) {
  return t & LOC_MASK;
}

INLINE bool term_triv(Term t) {
  return term_tag(t) <= TAG_PACK || t == TERM_HOLE;
}

static void term_drop(Env e, Term t);

INLINE Term rfc_wrap(Env e, Term t, u32 cnt) {
  #ifdef CLO_SHR
  if (term_tag(t) == TAG_TASK) {
  #else
  if (term_tag(t) == TAG_CLOS || term_tag(t) == TAG_TASK) {
  #endif
    err_post(e.mem, ERR_RFCS);
    return t;
  }
  Loc r = heap_alloc(e, 0);
  e.mem[r] = ((u64)term_loc(t) << 24) | cnt;
  return (t & ~LOC_MASK) | RFC_BIT | r;
}

INLINE Term rfc_seal(Env e, Term t) {
  if (term_triv(t) || term_rfc(t)) {
    return t;
  }
  return rfc_wrap(e, t, 1);
}

INLINE Term rfc_sole(Env e, Term t) {
  Loc  r = term_loc(t);
  Term s = (t & ~(RFC_BIT | LOC_MASK)) | (e.mem[r] >> 24);
  heap_free(e, 0, r);
  return s;
}

INLINE u64 rfc_view(Env e, Loc r) {
  DEV u32* w = a32_at(e.mem, r);
  u64 cell = ((u64)a32_load(w + 1) << 32) | a32_load(w);
  if ((cell & RFC_CNT) == 1) {
    a32_acq(w);
  }
  return cell;
}

INLINE bool rfc_out(Env e, Loc r) {
  DEV u32* p = a32_at(e.mem, r);
  if ((a32_sub_rel(p, 1) & RFC_CNT) != 1) {
    return false;
  }
  a32_acq(p);
  return true;
}

INLINE void rfc_bump(Env e, Loc r) {
  u32 c = a32_add(a32_at(e.mem, r), 1);
  if ((c & RFC_CNT) >= RFC_CNT - 1) {
    err_post(e.mem, ERR_RFCS);
  }
}

HOT Term term_keep(Env e, Term t) {
  if (term_rfc(t)) {
    rfc_bump(e, term_loc(t));
    return t;
  }
  if (term_triv(t)) {
    return t;
  }
  return rfc_wrap(e, t, 2);
}

HOT Loc term_peek(Env e, Term t) {
  if (term_rfc(t)) {
    return rfc_view(e, term_loc(t)) >> 24;
  }
  return term_loc(t);
}

OUTLINE void span_fade(Env e, Term t, Loc src, u32 n) {
  for (u32 j = 0; j < n; j += 1) {
    Term f = e.mem[src + j];
    if (term_rfc(f)) {
      rfc_bump(e, term_loc(f));
    } else if (!term_triv(f)) {
      err_post(e.mem, ERR_RFCS);
    }
  }
  term_drop(e, t);
}

HOT Loc ctr_take(Env e, Term t, u32 n, THR Term* out) {
  Corpus H = e.mem;
  if (!term_rfc(t)) {
    for (u32 j = 0; j < n; j += 1) {
      out[j] = H[term_loc(t) + j];
    }
    return term_loc(t);
  }
  Loc r    = term_loc(t);
  u64 cell = rfc_view(e, r);
  Loc src  = cell >> 24;
  for (u32 j = 0; j < n; j += 1) {
    out[j] = H[src + j];
  }
  if ((cell & RFC_CNT) == 1) {
    heap_free(e, 0, r);
    return src;
  }
  span_fade(e, t, src, n);
  return 0;
}

INLINE Cls flat_cls(Env e, Term t) {
  Cls c = (u32)term_aux(t);
  if (c > 31) {
    err_post(e.mem, ERR_TAGS);
    return 0;
  }
  return c;
}

#define flat_wcls(c) ((c) == 0 ? 0 : (c) - 1)

INLINE Cls blk_cls(Env e, Term t) {
  Cls c = flat_cls(e, t);
  return term_tag(t) == TAG_ARRS ? c : flat_wcls(c);
}

INLINE void flat_free(Env e, Term t) {
  heap_free(e, blk_cls(e, t), term_loc(t));
}

OUTLINE Term rfc_open(Env e, Term t) {
  Corpus H = e.mem;
  u32 cls  = blk_cls(e, t);
  u64 span = 1ull << cls;
  Loc r    = term_loc(t);
  u64 cell = rfc_view(e, r);
  if ((cell & RFC_CNT) == 1) {
    return rfc_sole(e, t);
  }
  Loc src = cell >> 24;
  Loc dst = heap_alloc(e, cls);
  if (loc_doomed(dst)) {
    return term_flat(0, dst);
  }
  for (u64 j = 0; j < span; j += 1) {
    H[dst + j] = H[src + j];
  }
  span_fade(e, t, src, term_tag(t) == TAG_ARRS ? (u32)span : 0);
  return (t & ~(RFC_BIT | LOC_MASK)) | dst;
}

static void term_drop(Env e, Term t) {
  Corpus H = e.mem;
  u64  cur = 0;
  Term c0  = 0;
  u32  step = 0;
  for (;;) {
    if (!term_triv(t) && term_rfc(t)) {
      t = rfc_out(e, term_loc(t)) ? rfc_sole(e, t) : 0;
    }
    if (!term_triv(t) && term_tag(t) == TAG_CLOS
      && fid_arity((u32)term_aux(t)) == 1) {
      t = 0;
    }
    if (!term_triv(t)) {
      u64 tag = term_tag(t);
      if (tag == TAG_FLAT) {
        flat_free(e, t);
      } else {
        u32 aux = (u32)term_aux(t);
        Loc loc = term_loc(t);
        u32 n   = 0;
        Cls cls;
        if (tag == TAG_ARRS) {
          cls = 64 | flat_cls(e, t);
        } else {
          if (tag == TAG_CTOR) {
            n = cid_arity(aux);
          } else if (tag == TAG_CLOS) {
            n = fid_arity(aux) - 1;
          } else {
            n = fid_arity(aux);
          }
          cls = cls_fit(tag == TAG_TASK ? n + 2 : n);
        }
        c0 = H[loc];
        H[loc] = cur;
        cur = loc | ((u64)n << 48) | ((u64)cls << 56);
      }
    }
    for (;;) {
      if (err_spun(H, &step, ERR_TICK)) {
        return;
      }
      if (cur == 0) {
        return;
      }
      Loc  loc = cur & LOC_MASK;
      u32  i   = (u8)(cur >> 40);
      u32  n   = (u8)(cur >> 48);
      Cls  cls = (u32)(cur >> 56);
      bool arr = cls > 63;
      u32  j   = i;
      if (arr) {
        cls &= 63;
        n   = 1u << cls;
        if (i == 2) {
          j = (u32)H[loc + 1];
        }
      }
      if (j < n) {
        Term c = j == 0 ? c0 : H[loc + j];
        if (arr && j > 0) {
          H[loc + 1] = j + 1;
        }
        if (!arr || i < 2) {
          cur += 1ull << 40;
        }
        if (!term_triv(c)) {
          t = c;
          break;
        }
      } else {
        u64 up = H[loc];
        heap_free(e, cls, loc);
        cur = up;
      }
    }
  }
}

HOT void term_sink(Env e, Term t) {
  if (!term_triv(t)) {
    term_drop(e, t);
  }
}

// Natives
// =======

INLINE Str str_scon(Env e, U32 head, Str tail) {
  Loc loc = heap_alloc(e, 1);
  e.mem[loc]     = head;
  e.mem[loc + 1] = tail;
  return term_ctor(CID_SCON, loc);
}

INLINE Str str_digits(Env e, Str out, u64 v) {
  do {
    out = str_scon(e, '0' + (v % 10), out);
    v /= 10;
  } while (v != 0);
  return out;
}

#ifndef __METAL_VERSION__

static Str str_text(Env e, Str out, const char* text) {
  for (u64 n = strlen(text); n > 0; n -= 1) {
    out = str_scon(e, text[n - 1], out);
  }
  return out;
}

OUTLINE Str show_walk(Env e, u32* at, Term v, Str out) {
  u32 op = MAIN_PLAN[*at];
  *at += 1;
  if (op == SHOW_NAT) {
    return str_digits(e, str_scon(e, 'n', out), v);
  }
  if (op == SHOW_U32) {
    return str_digits(e, out, v);
  }
  if (op == SHOW_CHAR) {
    return str_scon(e, v, out);
  }
  if (op == SHOW_DASH) {
    return str_scon(e, '-', out);
  }
  Term fb[2];
  spare_free(e, cls_fit(2), ctr_take(e, v, 2, fb));
  out = show_walk(e, at, fb[1], str_scon(e, '}', out));
  out = show_walk(e, at, fb[0], str_text(e, out, ", "));
  return str_text(e, out, "Tuple{");
}

static Str main_show(Env e, Term v) {
  if (MAIN_PLAN[0] == SHOW_STRING) {
    return v;
  }
  u32 at = 0;
  return show_walk(e, &at, v, term_pack(CID_SNIL, 0));
}

OUTLINE u64 str_fnv(Env e, Str s) {
  u64 fnv = 0xcbf29ce484222325ull;
  while (term_aux(s) == CID_SCON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    char c = (char)fb[0];
    putchar(c);
    fnv ^= (u8)c;
    fnv *= 0x100000001b3ull;
    s = fb[1];
  }
  putchar('\n');
  if (term_aux(s) != CID_SNIL) {
    err_fail(ERR_TAGS, "result is not a String");
  }
  return fnv;
}

#endif

INLINE U32 u32_div(U32 a, U32 b) {
  if ((u32)b == 0) {
    return 0;
  }
  return (u32)a / (u32)b;
}

INLINE U32 u32_mod(U32 a, U32 b) {
  if ((u32)b == 0) {
    return 0;
  }
  return (u32)a % (u32)b;
}

INLINE U32 u32_shln(U32 n, U32 a) {
  if (n >= 32) {
    return 0;
  }
  return (u32)a << n;
}

INLINE U32 u32_shrn(U32 n, U32 a) {
  if (n >= 32) {
    return 0;
  }
  return (u32)a >> n;
}

#ifdef __METAL_VERSION__
#define sqrtf precise::sqrt
#endif

INLINE u32 f32_to_u32(u32 b) {
  if ((b >> 31) != 0) {
    return 0;
  }
  u32 e = (b >> 23) & 0xff;
  if (e < 127 || e >= 159) {
    return 0;
  }
  u32 m = (b & 0x7fffff) | 0x800000;
  if (e >= 150) {
    return m << (e - 150);
  }
  return m >> (150 - e);
}

INLINE Nat nat_succ(Env e, Nat n) {
  if (n + 1 > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
    return NAT_IMM;
  }
  return n + 1;
}

#ifdef __METAL_VERSION__
typedef u32 u32a;
#else
typedef u32 __attribute__((may_alias)) u32a;
#endif

INLINE DEV u32a* flat_ptr(Corpus H, Loc loc, u32 i) {
  return (DEV u32a*)(H + loc) + i;
}

INLINE Term blk_read(Corpus H, bool arr, Loc loc, u32 i) {
  if (arr) {
    return H[loc + i];
  }
  return (u64)*flat_ptr(H, loc, i);
}

INLINE void blk_write(Corpus H, bool arr, Loc loc, u32 i, Term v) {
  if (arr) {
    H[loc + i] = v;
  } else {
    *flat_ptr(H, loc, i) = (u32)v;
  }
}

INLINE Term flat_new(Env e, Nat d, Term v) {
  if (d > 31) {
    err_post(e.mem, ERR_NATS);
    d = 0;
  }
  Cls c = (u32)d;
  Loc n = heap_alloc(e, flat_wcls(c));
  if (loc_doomed(n)) {
    return term_flat(0, n);
  }
  for (u64 i = 0; i < (1ull << flat_wcls(c)); i += 1) {
    e.mem[n + i] = (u64)(u32)v * 0x100000001ull;
  }
  return term_flat(c, n);
}

INLINE u32 flat_at(Env e, Term a, U32 i) {
  return (u32)i & (u32)((1ull << flat_cls(e, a)) - 1);
}

INLINE Term flat_read(Env e, Term a, U32 i) {
  return blk_read(e.mem, 0, term_loc(a), flat_at(e, a, i));
}

INLINE Term flat_cow(Env e, Term a) {
  return term_rfc(a) ? rfc_open(e, a) : a;
}

INLINE Term blk_leaf(Env e, Term v) {
  Loc loc = heap_alloc(e, 0);
  e.mem[loc] = rfc_seal(e, v);
  return term_arrs(1, 0, loc);
}

INLINE Term flat_node(Env e, Term l, Term r) {
  Corpus H = e.mem;
  l = flat_cow(e, l);
  r = flat_cow(e, r);
  bool arr = term_tag(l) == TAG_ARRS;
  Cls c = flat_cls(e, l);
  if (c != flat_cls(e, r) || c > 30) {
    err_post(H, ERR_TAGS);
    return l;
  }
  Loc n = heap_alloc(e, c + arr);
  if (loc_doomed(n)) {
    return term_flat(0, n);
  }
  for (u32 w = 0; w < (1u << c); w += 1) {
    blk_write(H, arr, n, 2 * w, blk_read(H, arr, term_loc(l), w));
    blk_write(H, arr, n, 2 * w + 1, blk_read(H, arr, term_loc(r), w));
  }
  flat_free(e, l);
  flat_free(e, r);
  return term_arrs(arr, c + 1, n);
}

INLINE Term flat_half(Env e, Term a, u32 hi) {
  Corpus H = e.mem;
  bool arr = term_tag(a) == TAG_ARRS;
  Cls c = flat_cls(e, a);
  if (c == 0) {
    err_post(H, ERR_TAGS);
    return a;
  }
  c -= 1;
  Loc pa = term_loc(a);
  Loc n  = heap_alloc(e, arr ? c : flat_wcls(c));
  if (loc_doomed(n)) {
    return term_flat(0, n);
  }
  for (u32 i = 0; i < (1u << c); i += 1) {
    blk_write(H, arr, n, i, blk_read(H, arr, pa, 2 * i + hi));
  }
  return term_arrs(arr, c, n);
}

INLINE Term flat_rest(Env e, Term a) {
  Term r = flat_half(e, a, 1);
  flat_free(e, a);
  return r;
}

INLINE Term flat_take(Env e, Term a) {
  Term v = blk_read(e.mem, term_tag(a) == TAG_ARRS, term_loc(a), 0);
  heap_free(e, 0, term_loc(a));
  return v;
}

INLINE Term blk_give(Env e, bool arr, Term a, U32 i, Term v) {
  u32 at = flat_at(e, a, i);
  if (arr) {
    v = rfc_seal(e, v);
  }
  Term old = blk_read(e.mem, arr, term_loc(a), at);
  blk_write(e.mem, arr, term_loc(a), at, v);
  return old;
}

// Ring
// ====

INLINE DEV u64* ring_slot(Corpus H, Ring r, u64 pos) {
  return H + RING_OFF + (pos & (RING_LEN - 1)) * CUBE + r;
}

#ifdef __METAL_VERSION__
typedef threadgroup atomic_uint* Cursor;
#define CUR_STEP(c) atomic_fetch_add_explicit(c, 1, RLX)
#else
typedef u32* Cursor;
#define CUR_STEP(c) ((*(c))++)
#endif

INLINE DEV u32* ring_put(Corpus H, Ring r) {
  return (DEV u32*)monk_word(H, r, M_RING_PUT);
}

INLINE DEV u32* ring_get(Corpus H, Ring r) {
  return (DEV u32*)monk_word(H, r, M_RING_GET);
}

INLINE u32 ring_lap(u32 pos) {
  return ~(u32)(pos / RING_LEN) & 1;
}

INLINE void ring_push(Corpus H, Ring r, Term tsk) {
  u32 pos = a32_add(ring_put(H, r), 1);
  if (pos - a32_load(ring_get(H, r)) >= RING_LEN) {
    err_post(H, ERR_RING);
    return;
  }
  DEV u32* lo = (DEV u32*)ring_slot(H, r, pos);
  a32_store(lo, (u32)tsk);
  a32_store_rel(lo + 1, (u32)(tsk >> 32) | (ring_lap(pos) << 31));
}

INLINE Term ring_head(Corpus H, Ring r) {
  u32 get = *ring_get(H, r);
  DEV u32* lo = (DEV u32*)ring_slot(H, r, get);
  u32 hi = a32_load_acq(lo + 1);
  if ((hi >> 31) != ring_lap(get)) {
    return 0;
  }
  return (((u64)hi << 32) | a32_load(lo)) & ~RFC_BIT;
}

INLINE void ring_skip(Corpus H, Ring r) {
  DEV u32* get = ring_get(H, r);
  a32_store(get, *get + 1);
}

INLINE Ring ring_flip(u32 i) {
  return i / CUBE_SIDE + CUBE_SIDE * (i % CUBE_SIDE);
}

#define ring_pick(b, s, c) \
  ((s) == 0 ? (b) : (b) + (s) * (CUR_STEP(c) & (CUBE_SIDE - 1)))

// Task
// ====

INLINE Loc task_node(Env e, Fid fid, Term cont, u32 idx, u32 rem) {
  u32 ar  = fid_arity(fid);
  Loc loc = heap_alloc(e, cls_fit(ar + 2));
  e.mem[loc + ar]     = cont;
  e.mem[loc + ar + 1] = ((u64)idx << 32) | rem;
  return loc;
}

INLINE Loc task_tail(Term t) {
  return term_loc(t) + fid_arity((u32)term_aux(t));
}

INLINE bool reply_runs(Corpus H, Reply r) {
  return (u32)H[task_tail(r) + 1] == 0;
}

INLINE Term task_deliver(Corpus H, Term cont, u32 idx, Term v) {
  if (cont == TERM_HOLE) {
    H[H_ROOT_WORD] = v;
    a32_store_rel(a32_at(H, H_ROOT_DONE), 1);
    return 0;
  }
  Loc tl = task_tail(cont);
  H[term_loc(cont) + idx] = v;
  if (a32_sub_rel(a32_at(H, tl + 1), 1) == 1) {
    a32_acq(a32_at(H, tl + 1));
    return cont;
  }
  return 0;
}

INLINE bool root_done(Corpus H) {
  return a32_load_acq(a32_at(H, H_ROOT_DONE)) != 0;
}

INLINE void task_deal(Corpus H, Term join, u32 base, u32 stride, Cursor cur) {
  Loc loc = term_loc(join);
  u32 ar  = fid_arity((u32)term_aux(join));
  u32 g   = 0;
  if (stride == 0) {
    u32 rem = (u32)H[loc + ar + 1];
    g = a32_add(a32_at(H, H_CURSOR), rem);
  }
  for (u32 i = 0; i < ar; i += 1) {
    Term k = H[loc + i];
    if (term_tag(k) == TAG_TASK) {
      H[loc + i] = TERM_HOLE;
      Ring to;
      if (stride != 0) {
        to = ring_pick(base, stride, cur);
      } else {
        to = ring_flip(g & (u32)(CUBE - 1));
        g += 1;
      }
      ring_push(H, to, k);
    }
  }
}

// Stack
// =====

#ifdef __METAL_VERSION__
#define WL_ROOM(N) \
  if (sp + (N) * CUBE > e.mem + STAK_OFF + e.mnk + CUBE * STAK_LEN) { \
    err_post(e.mem, ERR_DEEP); \
    return 0; \
  }
#else
#define WL_ROOM(N)
#endif

// Code
// ====

static Reply work_loop(Env e, Stk sp, Term t, bool seq) {
  Fid  fid;
  Term res = 0;
  WL_BANK
  {
  fid = (u32)term_aux(t);
  Loc  a    = term_loc(t);
  u32  war  = fid_arity(fid);
  Loc  atl  = task_tail(t);
  STK(0) = e.mem[atl];
  STK(1) = e.mem[atl + 1] >> 32;
  STK(2) = FID_EXIT;
  sp += 3 * LANE_STEP;
  if (fid_seqk(fid)) {
    res = e.mem[a + war - 1];
    for (u32 wi = 0; wi + 1 < war; wi += 1) {
      STK(wi) = e.mem[a + wi];
    }
    sp += (war - 1) * LANE_STEP;
  } else {
    WL_LOAD
  }
  heap_free(e, cls_fit(war + 2), a);
  }
#ifdef __METAL_VERSION__
  u32 wpoll = 0;
  for (;;) {
  if (err_spun(e.mem, &wpoll, 255)) {
    return 0;
  }
  switch (fid) {
#else
  static const void* wl_lbl[] = {
    WL_LABELS
  };
  goto *wl_lbl[fid];
#endif

// Segments
// ========

#ifdef FID_CLO_APPLY
  WL_CASE(FID_CLO_APPLY)
  {
    Term fun = r0;
    res      = r1;
    fid      = (Fid)term_aux(fun);
    u32 war  = fid_arity(fid) - 1;
    Loc a    = term_loc(fun);
    u64 cnt  = 0;
    if (term_rfc(fun)) {
      u64 cell = rfc_view(e, a);
      cnt = cell & RFC_CNT;
      a   = cell >> 24;
    }
    WL_LOAD
    if (cnt > 1) {
      span_fade(e, fun, a, war);
    } else {
      if (cnt == 1) {
        heap_free(e, 0, term_loc(fun));
      }
      if (war > 0) {
        heap_free(e, cls_fit(war), a);
      }
    }
    WL_LAST
    WL_DYN(fid);
  }
#endif

  WL_CASE(FID_EXIT)
  {
    if (DEVICE && err_seen(e.mem)) {
      return 0;
    }
    sp -= 2 * LANE_STEP;
    Term cont = STK(0);
    u32  idx  = (u32)STK(1);
    if (cont != TERM_HOLE && fid_seqk((u32)term_aux(cont)) && !park(e)) {
      Fid wf = (u32)term_aux(cont);
      Loc wa = term_loc(cont);
      u32 wn = fid_arity(wf);
      Loc wtl = task_tail(cont);
      STK(0) = e.mem[wtl];
      STK(1) = e.mem[wtl + 1] >> 32;
      STK(2) = FID_EXIT;
      sp += 3 * LANE_STEP;
      for (u32 wi = 0; wi + 1 < wn; wi += 1) {
        STK(wi) = e.mem[wa + wi];
      }
      sp += (wn - 1) * LANE_STEP;
      heap_free(e, cls_fit(wn + 2), wa);
      WL_DYN(wf);
    }
    return task_deliver(e.mem, cont, idx, res);
  }

#ifdef __METAL_VERSION__
  default: {
    err_post(e.mem, ERR_FIDS);
    return 0;
  }
  }
  }
#else
  err_post(e.mem, ERR_FIDS);
  return 0;
#endif
}

// Monk
// ====

INLINE bool run_root(Env e, Stk stk, Term t, bool seq, u32 base, u32 stride,
  Cursor cur) {
  u32 spin = 0;
  for (;;) {
    Reply r = work_loop(e, stk, t, seq);
    if (r == 0) {
      return false;
    }
    if (reply_runs(e.mem, r)) {
      if (err_spun(e.mem, &spin, ERR_TICK)) {
        return false;
      }
      if ((DEVICE && stride != 0) || park(e)) {
        ring_push(e.mem, ring_pick(base, stride, cur), r);
        return false;
      }
      t   = r;
      seq = false;
      continue;
    }
    task_deal(e.mem, r, base, stride, cur);
    return true;
  }
}

INLINE bool grow_step(Env e, Stk stk, Ring rg, u32 put0, u32 base, u32 stride,
  Cursor cur) {
  Corpus H = e.mem;
  if (*ring_get(H, rg) == put0) {
    return false;
  }
  Term t = ring_head(H, rg);
  if (t == 0 || fid_nofk((u32)term_aux(t)) || park(e)) {
    return false;
  }
  ring_skip(H, rg);
  return run_root(e, stk, t, false, base, stride, cur);
}

static void monk_work(Env e, Stk stk, Monk m) {
  Corpus H = e.mem;
#ifdef __METAL_VERSION__
  u32 put0 = a32_load(ring_put(H, m));
#else
  u32 put0 = (u32)*monk_word(H, m, M_SNAP);
#endif
  while (*ring_get(H, m) != put0) {
    if (err_seen(H) || park(e)) {
      return;
    }
    Term t = ring_head(H, m);
    if (t == 0) {
      continue;
    }
    ring_skip(H, m);
    run_root(e, stk, t, !tight(H, 2), m, 0, (Cursor)0);
  }
}

#ifdef __METAL_VERSION__

kernel void grow_dev(Corpus H [[buffer(0)]],
  u32 grids [[threadgroups_per_grid]],
  u32 row [[threadgroup_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
  u32  stride = grids == 1 ? CUBE_SIDE : 1;
  Ring rg  = (row << 7) + stride * lane;
  threadgroup u64 tg_alc[CUBE_SIDE * ALC_WORDS];
  Env  e   = { H, rg, tg_alc + lane };
  alc_open(e);
  threadgroup atomic_uint tg_cur;
  threadgroup atomic_uint tg_grew;
  threadgroup atomic_uint tg_has;
  atomic_store_explicit(&tg_cur, 0, RLX);
  atomic_store_explicit(&tg_grew, 0, RLX);
  atomic_store_explicit(&tg_has, 0, RLX);
  threadgroup_barrier(mem_flags::mem_threadgroup);
  u32 seen_has  = 0;
  u32 seen_grew = 0;
  for (;;) {
    u32 put0 = a32_load(ring_put(H, rg));
    u32 vote = put0 != a32_load(ring_get(H, rg));
    if (lane == 0 && (err_seen(H) || root_done(H))) {
      vote = CUBE_SIDE;
    }
    atomic_fetch_add_explicit(&tg_has, vote, RLX);
    threadgroup_barrier(mem_flags::mem_threadgroup);
    u32 has = atomic_load_explicit(&tg_has, RLX);
    if (has - seen_has >= CUBE_SIDE) {
      break;
    }
    seen_has = has;
    if (grow_step(e, H + STAK_OFF + rg, rg, put0, row << 7, stride, &tg_cur)) {
      atomic_fetch_add_explicit(&tg_grew, 1, RLX);
    }
    threadgroup_barrier(mem_flags::mem_device | mem_flags::mem_threadgroup);
    u32 grew = atomic_load_explicit(&tg_grew, RLX);
    if (grew == seen_grew) {
      break;
    }
    seen_grew = grew;
  }
  alc_close(e);
}

kernel void work_dev(Corpus H [[buffer(0)]],
  u32 tid [[thread_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
  threadgroup u64 tg_alc[CUBE_SIDE * ALC_WORDS];
  Env e = { H, tid, tg_alc + lane };
  alc_open(e);
  monk_work(e, H + STAK_OFF + tid, ring_flip(tid));
  alc_close(e);
}

#endif

#ifndef __METAL_VERSION__

// Cube
// ====

static void row_grow(Env e, Stk stk, u32 base, u32 stride) {
  Corpus H = e.mem;
  u32 cur = 0;
  for (;;) {
    u32 put0[CUBE_SIDE];
    u32 has = 0;
    for (u32 i = 0; i < CUBE_SIDE; i += 1) {
      Ring rg = base + stride * i;
      put0[i] = *ring_put(H, rg);
      has += put0[i] != *ring_get(H, rg);
    }
    bool done = root_done(H);
    if (done || has == CUBE_SIDE) {
      return;
    }
    u32 grew = 0;
    for (u32 i = 0; i < CUBE_SIDE; i += 1) {
      Ring rg = base + stride * i;
      grew += grow_step(e, stk, rg, put0[i], base, stride, &cur);
    }
    if (grew == 0) {
      return;
    }
  }
}

// Pool
// ====

static Term* stack_new(void) {
  u64   len = 1ull << 31;
  void* p   = mmap(NULL, len + 16384 + SIGSTKSZ, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (p == MAP_FAILED || mprotect((char*)p + len, 16384, PROT_NONE) != 0) {
    err_fail(ERR_HEAP, "machine stack reservation failed");
  }
  stack_t ss = { .ss_sp = (char*)p + len + 16384, .ss_size = SIGSTKSZ };
  sigaltstack(&ss, NULL);
  struct sigaction sa = { .sa_handler = err_trap, .sa_flags = SA_ONSTACK };
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
  return (Term*)p;
}

static void* pool_work(void* arg) {
  u32   w    = (u32)(uintptr_t)arg;
  Term* stk  = stack_new();
  u64   seen = 0;
  for (;;) {
    pthread_mutex_lock(&pool_lock);
    while (atomic_load_explicit(&pool_tick, memory_order_acquire) == seen) {
      pthread_cond_wait(&pool_wake, &pool_lock);
    }
    pthread_mutex_unlock(&pool_lock);
    seen = atomic_load_explicit(&pool_tick, memory_order_acquire);
    Env e = { CORPUS, w };
    for (;;) {
      u32 r = atomic_fetch_add_explicit(&pool_row, 1, memory_order_relaxed);
      if (r >= CUBE_SIDE) {
        break;
      }
      if (pool_grow) {
        row_grow(e, stk, r << 7, 1);
      } else {
        for (u32 c = 0; c < CUBE_SIDE; c += 1) {
          monk_work(e, stk, ring_flip((r << 7) + c));
        }
      }
    }
    u32 done = atomic_fetch_add_explicit(&pool_done, 1, memory_order_release);
    if (done + 1 == pool_size) {
      pthread_mutex_lock(&pool_lock);
      pthread_cond_broadcast(&pool_wake);
      pthread_mutex_unlock(&pool_lock);
    }
  }
}

OUTLINE void pool_open(void) {
  struct rlimit rlim;
  pthread_attr_t attr;
  u64 most = 1ull << 30;
  bool sized = getrlimit(RLIMIT_STACK, &rlim) == 0
    && pthread_attr_init(&attr) == 0
    && pthread_attr_setstacksize(&attr,
      rlim.rlim_cur < most ? rlim.rlim_cur : most) == 0;
  if (!sized) {
    err_fail(ERR_FAIL, "worker stack sizing");
  }
  for (u32 w = 0; w < pool_size; w += 1) {
    pthread_t tid;
    if (pthread_create(&tid, &attr, pool_work, (void*)(uintptr_t)w)) {
      err_fail(ERR_FAIL, "pthread_create");
    }
  }
}

OUTLINE void pool_turn(bool grow) {
  pool_grow = grow;
  atomic_store_explicit(&pool_row, 0, memory_order_relaxed);
  atomic_store_explicit(&pool_done, 0, memory_order_relaxed);
  pthread_mutex_lock(&pool_lock);
  atomic_fetch_add_explicit(&pool_tick, 1, memory_order_release);
  pthread_cond_broadcast(&pool_wake);
  while (atomic_load_explicit(&pool_done, memory_order_acquire) < pool_size) {
    pthread_cond_wait(&pool_wake, &pool_lock);
  }
  pthread_mutex_unlock(&pool_lock);
}

// Gpu
// ===

#if BEND_METAL

static bool gpu_probe(void) {
  return (gpu_dev = MTLCreateSystemDefaultDevice()) != nil;
}

static id<MTLComputePipelineState> gpu_pipe(const char* name) {
  NSError* err = nil;
  id<MTLFunction> fn =
    [gpu_lib newFunctionWithName:[NSString stringWithUTF8String:name]];
  if (!fn) {
    err_fail(ERR_FAIL, name);
  }
  id<MTLComputePipelineState> pso =
    [gpu_dev newComputePipelineStateWithFunction:fn error:&err];
  if (!pso) {
    err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
  }
  if ([pso maxTotalThreadsPerThreadgroup] < CUBE_SIDE) {
    err_fail(ERR_FAIL, "threadgroup too small");
  }
  return pso;
}

static bool feed(Corpus H) {
  u64 need = gpu_wired == 0 ? 2 * TOME_PAGES
    : ((u64)a32_load(a32_at(H, H_PAGE_BUMP)) / TOME_PAGES + 3) * TOME_PAGES;
  if (!err_seen(H) && need <= gpu_wired) {
    return false;
  }
  u64 want = 2 * gpu_wired > need ? 2 * gpu_wired : need;
  want = want > gpu_cap ? gpu_cap : want;
  if (want <= gpu_wired) {
    return false;
  }
  gpu_buf = [gpu_dev
    newBufferWithBytesNoCopy:CORPUS
    length:(page_loc(want) * 8 + 16383) & ~16383ull
    options:MTLResourceStorageModeShared
      | MTLResourceHazardTrackingModeUntracked deallocator:nil];
  if (!gpu_buf) {
    err_fail(ERR_HEAP, "wiring failed");
  }
  gpu_wired = want;
  a32_store(a32_at(H, H_PAGE_CAP), (u32)gpu_cap);
  a32_store(a32_at(H, H_TOME_WIRED), (u32)want);
  return true;
}

static u64 gpu_reserve(void) {
  u64 span = [gpu_dev recommendedMaxWorkingSetSize];
  u64 most = [gpu_dev maxBufferLength];
  span = span < most ? span : most;
  if (span < page_loc(2 * TOME_PAGES) * 8) {
    err_fail(ERR_HEAP, "device too small");
  }
  @autoreleasepool {
    gpu_que = [gpu_dev newCommandQueue];
    NSError* err = nil;
    NSString* text = [NSString stringWithContentsOfFile:@__FILE__
      encoding:NSUTF8StringEncoding error:nil];
    if (!text) {
      err_fail(ERR_FAIL, "cannot read own source");
    }
    MTLCompileOptions* opts = [MTLCompileOptions new];
    opts.mathMode = MTLMathModeSafe;
    gpu_lib = [gpu_dev newLibraryWithSource:text options:opts error:&err];
    if (!gpu_lib) {
      err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
    }
    gpu_grow_pso = gpu_pipe("grow_dev");
    gpu_work_pso = gpu_pipe("work_dev");
  }
  return span / 8;
}

static void gpu_kernel(id<MTLComputeCommandEncoder> enc,
  id<MTLComputePipelineState> pso, u32 groups) {
  [enc setComputePipelineState:pso];
  [enc setBuffer:gpu_buf offset:0 atIndex:0];
  [enc dispatchThreadgroups:MTLSizeMake(groups, 1, 1)
    threadsPerThreadgroup:MTLSizeMake(CUBE_SIDE, 1, 1)];
  [enc memoryBarrierWithScope:MTLBarrierScopeBuffers];
}

static bool gpu_round(Corpus H, u32 f) {
  feed(H);
  @autoreleasepool {
    id<MTLCommandBuffer> cb = [gpu_que commandBuffer];
    id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
    if (f < CUBE_SIDE) {
      gpu_kernel(enc, gpu_grow_pso, 1);
    }
    if (f < CUBE) {
      gpu_kernel(enc, gpu_grow_pso, CUBE_SIDE);
    }
    gpu_kernel(enc, gpu_work_pso, CUBE_SIDE);
    [enc endEncoding];
    [cb commit];
    [cb waitUntilCompleted];
    if ([cb error]) {
      err_fail(ERR_FAIL, [[[cb error] localizedDescription] UTF8String]);
    }
  }
  u32 ec = a32_load(a32_at(H, H_ERROR_CODE));
  if (ec && ec != ERR_HEAP) {
    err_fail(ec, ec == ERR_DEEP ? "device stack exceeded" : "device error");
  }
  return ec;
}

#else

#define gpu_probe()   false
#define gpu_reserve() 0

#endif

// Driver
// ======

static void cube_run(Corpus H, bool metal) {
  for (;;) {
    u32 f = a32_load(a32_at(H, H_CURSOR));
    a32_store(a32_at(H, H_CURSOR), 0);
    if (root_done(H)) {
      return;
    }
    if (f == 0) {
      err_fail(ERR_LEAK, "frontier drained without a result");
    }
    if (metal) {
      #if BEND_METAL
      if (gpu_round(H, f)) {
        return;
      }
      #endif
    } else {
      if (f < CUBE) {
        pool_turn(true);
      }
      for (Ring r = 0; r < CUBE; r += 1) {
        *monk_word(H, r, M_SNAP) = *ring_put(H, r);
      }
      pool_turn(false);
    }
  }
}

// Corpus
// ======

static void corpus_seed(Corpus H) {
  u64 doom = term_ctor(0, HEAP_OFF);
  u64 lone = PAGE_NIL;
  memset_pattern8(H + HEAP_OFF, &doom, DOOM_WORDS * 8);
  memset_pattern8(H + H_HUGE_FREE, &lone, HUGE_CLS * 8);
  H[H_PAGE_BUMP] = DOOM_WORDS >> PAGE_BITS;
}

static Corpus corpus_setup(bool metal, long threads) {
  u64 span = metal ? gpu_reserve() : 1ull << 40;
  CORPUS = mmap(NULL, span * 8, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (CORPUS == MAP_FAILED) {
    err_fail(ERR_HEAP, "corpus reservation failed");
  }
  Corpus H = CORPUS;
  corpus_seed(H);
  u64 cap = (span - HEAP_OFF) >> PAGE_BITS;
  if (cap > PAGE_NIL) {
    cap = PAGE_NIL;
  }
  a32_store(a32_at(H, H_PAGE_CAP), (u32)cap);
#if BEND_METAL
  gpu_cap = cap;
#endif
  pool_size = (u32)(threads < CUBE_SIDE ? threads : CUBE_SIDE);
  return H;
}

#if BEND_METAL

static Term corpus_wake(Env e) {
  Corpus H = e.mem;
  if (!feed(H)) {
    err_fail(ERR_HEAP, "device out of memory");
  }
  memset(ALC, 0, sizeof(ALC));
  memset(H + MONK_OFF, 0, (STAK_OFF - MONK_OFF) * 8);
  memset(H + H_ROOT_WORD, 0, 72);
  corpus_seed(H);
  return term_task(FID_MAIN, task_node(e, FID_MAIN, TERM_HOLE, 0, 0));
}

#endif

OUTLINE Term corpus_eval(Corpus H, bool metal) {
  Env  e   = { H, 0 };
  Stk  stk = stack_new();
  Loc  ml  = task_node(e, FID_MAIN, TERM_HOLE, 0, 0);
  Term t   = term_task(FID_MAIN, ml);
  for (;;) {
    Reply r = work_loop(e, stk, t, false);
    if (r == 0) {
      if (root_done(H)) {
        return H[H_ROOT_WORD];
      }
      err_fail(ERR_LEAK, "solo delivery lost");
    }
    if (reply_runs(H, r)) {
      t = r;
      if (metal && fid_bangs((u32)term_aux(t))) {
        Loc  tl   = task_tail(t);
        Term cont = H[tl];
        u32  idx  = (u32)(H[tl + 1] >> 32);
        H[tl]     = TERM_HOLE;
        H[tl + 1] = 0;
        a32_store(a32_at(H, H_CURSOR), 1);
        ring_push(H, 0, t);
        cube_run(H, true);
        #if BEND_METAL
        if (err_seen(H)) {
          t = corpus_wake(e);
          continue;
        }
        #endif
        Term v = H[H_ROOT_WORD];
        a32_store(a32_at(H, H_ROOT_DONE), 0);
        Term p = task_deliver(H, cont, idx, v);
        if (root_done(H)) {
          return H[H_ROOT_WORD];
        }
        if (p == 0) {
          err_fail(ERR_LEAK, "seam delivery lost");
        }
        t = p;
      }
      continue;
    }
    task_deal(H, r, 0, 0, (Cursor)0);
    break;
  }
  pool_open();
  cube_run(H, false);
  return H[H_ROOT_WORD];
}

// Main
// ====

static const char* CLI_HELP =
  "usage: %s [options]\n"
  "  --threads N        worker threads, up to 128 (default: the CPU count)\n"
  "  --parallel on|off  off means one thread and no GPU (default: on)\n"
  "  --gpu on|off       send ! calls to the GPU (default: on if present)\n"
  "  --help             show this text\n";

static void cli_fail(const char* msg, const char* arg) {
  fprintf(stderr, "bend: %s%s\n", msg, arg != NULL ? arg : "");
  exit(1);
}

static bool cli_flag(const char* name, const char* val) {
  if (val != NULL && strcmp(val, "on") == 0) {
    return true;
  }
  if (val != NULL && strcmp(val, "off") == 0) {
    return false;
  }
  cli_fail("expected 'on' or 'off' after ", name);
  return false;
}

int main(int argc, char** argv) {
  long thr = 0;
  int  par = -1;
  int  gpu = -1;
  for (int i = 1; i < argc; i += 1) {
    const char* a = argv[i];
    const char* v = i + 1 < argc ? argv[i + 1] : NULL;
    if (strcmp(a, "--help") == 0) {
      printf(CLI_HELP, argv[0]);
      return 0;
    } else if (strcmp(a, "--threads") == 0) {
      char* end = NULL;
      thr = v != NULL ? strtol(v, &end, 10) : 0;
      if (thr < 1 || end == NULL || *end != '\0') {
        cli_fail("expected a thread count of 1 or more after --threads", NULL);
      }
      i += 1;
    } else if (strcmp(a, "--parallel") == 0) {
      par = cli_flag("--parallel", v);
      i += 1;
    } else if (strcmp(a, "--gpu") == 0) {
      gpu = cli_flag("--gpu", v);
      i += 1;
    } else {
      cli_fail("unknown option ", a);
    }
  }
  if (par == 0 && (gpu == 1 || thr > 1)) {
    cli_fail("--parallel off means --threads 1 with --gpu off", NULL);
  }
  if (par == 0) {
    thr = 1;
    gpu = 0;
  }
  bool metal = gpu != 0 && gpu_probe();
  if (gpu == 1 && !metal) {
    cli_fail("--gpu on, but this binary found no Metal device", NULL);
  }
  long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
  long dflt = ncpu > 0 ? ncpu : 1;
  Corpus H  = corpus_setup(metal, thr > 0 ? thr : dflt);
  Env e = { H, 0 };
  Term out = corpus_eval(H, metal);
  u64  fnv = str_fnv(e, main_show(e, out));
  printf("fnv: 0x%016llx\n", (unsigned long long)fnv);
  return 0;
}

#endif

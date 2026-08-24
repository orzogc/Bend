// Bend4 Runtime
// =============

// Imports
// =======

#ifdef __METAL_VERSION__
#include <metal_stdlib>
using namespace metal;
#else
// HOST BEGIN imports
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <unistd.h>
#include <sys/mman.h>
#if BEND_METAL
#import <Metal/Metal.h>
#import <Foundation/Foundation.h>
#include <mach/mach.h>
#include <mach/mach_vm.h>
#endif
// HOST END imports
#endif

// Dialect
// =======

#ifdef __METAL_VERSION__
#define DEV     device
#define THR     thread
#define INLINE  inline
#define A32(p)  ((DEV atomic_uint*)(p))
#define RLX     memory_order_relaxed
#define FENCE() atomic_thread_fence(mem_flags::mem_device, memory_order_seq_cst)
#else
#define DEV
#define THR
#define INLINE  static inline
#define FENCE() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#endif

// Types
// =====

#ifdef __METAL_VERSION__
typedef ulong u64;
typedef uint  u32;
typedef uchar u8;
#else
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
#endif

// Loc ::= u40
typedef u64 Loc;
#define LOC_MASK ((1ull << 40) - 1)

// Cls ::= u5
typedef u32 Cls;

// Fid ::= FID_*
typedef u32 Fid;

// Cid ::= CID_*
typedef u32 Cid;

// Term ::=
//   | Word ::= { val: u48 }
//   | Ctor ::= { cid: Cid, loc: Loc }
//   | Clos ::= { fid: Fid, loc: Loc }
//   | Flat ::= { cls: Cls, loc: Loc }
//   | Task ::= { fid: Fid, loc: Loc }
//   | Hole
//   | Need
//   | Work
typedef u64 Term;
#define AUX_MASK  ((1ull << 20) - 1)
#define TAG_WORD  0ull
#define TAG_CTOR  1ull
#define TAG_CLOS  2ull
#define TAG_FLAT  3ull
#define TAG_TASK  4ull
#define TERM_HOLE (~0ull)
#define TERM_NEED (~0ull - 1)
#define TERM_WORK (~0ull - 2)

// Drop ::=
//   | None
//   | Node ::= { loc: Loc, idx: u8, len: u8, cls: u8 }
typedef u64 Drop;
#define DROP_NONE 0

// Reply ::=
//   | Done ::= Term
//   | Call ::= Term
//   | Fork ::= Term
//   | Work
//   | Need
typedef Term Reply;
#define REPLY_DONE 0
#define REPLY_CALL 1
#define REPLY_FORK 2
#define REPLY_WORK 3
#define REPLY_NEED 4

// Fill ::= { idx: u32, rem: u32 }
typedef u64 Fill;

// Err ::=
//   | Fail
//   | Ring
//   | Tags
//   | Turn
//   | Heap
//   | Fids
//   | Leak
//   | Nats
typedef u32 Err;
#define ERR_FAIL 1
#define ERR_RING 2
#define ERR_TAGS 3
#define ERR_TURN 4
#define ERR_HEAP 5
#define ERR_FIDS 6
#define ERR_LEAK 7
#define ERR_NATS 8

// Mode ::=
//   | Grow
//   | Work
//   | Seed
typedef u32 Mode;
#define MODE_GROW 0
#define MODE_WORK 1
#define MODE_SEED 2

// Page ::= {
//   list: u32,
//   live: u32,
//   size: Cls,
//   bump: u32,
// }
typedef u32 Page;
#define PAGE_HDR   2
#define SLOT_NIL   0x7FFu
#define PAGE_NIL   0xFFFFFu
#define PAGE_OWNED 0x80000000u

// Tome ::= u64[TOME_WORDS]
typedef u32 Tome;

// Monk ::= {
//   ring_put: u64,
//   ring_get: u64,
//   own_page: u64[NCLS],
// }
typedef u32 Monk;
#define M_RING_PUT 0
#define M_RING_GET 1
#define M_OWN_PAGE 2

// Ring ::= Term[RING_LEN]
typedef u32 Ring;

// Cube ::= {
//   monk: Monk[CUBE],
//   ring: Ring[CUBE],
// }
#define MONK_OFF 96ull
#define RING_OFF (MONK_OFF + CUBE * MONK_WORDS)

// Head ::= {
//   tome_bump: Tome,
//   page_bump: Page,
//   gpu_turns: u64,
//   page_free: u32,
//   huge_free: u32[HUGE_CLS],
//   root_word: Term,
//   root_done: u32,
// }
#define HEAD_OFF    0ull
#define H_TOME_BUMP (HEAD_OFF + 0)
#define H_PAGE_BUMP (HEAD_OFF + 8)
#define H_GPU_TURNS (HEAD_OFF + 16)
#define H_PAGE_FREE (HEAD_OFF + 24)
#define H_HUGE_FREE (HEAD_OFF + 32)
#define H_ROOT_WORD (HEAD_OFF + 56)
#define H_ROOT_DONE (HEAD_OFF + 57)

// Chan ::= {
//   is_focused: u32,
//   need_tomes: u32,
//   error_code: Err,
// }
#define CHAN_OFF     64ull
#define C_IS_FOCUSED (CHAN_OFF + 0)
#define C_NEED_TOMES (CHAN_OFF + 8)
#define C_ERROR_CODE (CHAN_OFF + 16)

// Heap ::= Page[]
#define HEAP_OFF  (3ull * TOME_WORDS)
#define WRECK_LOC (HEAP_OFF + PAGE_HDR)

// Corpus ::= {
//   head: Head,
//   chan: Chan,
//   task: Cube,
//   heap: Heap,
// }
typedef DEV u64* Corpus;

// Env ::= {
//   mem: Corpus,
//   mnk: Monk,
// }
typedef struct {
  Corpus mem;
  Monk   mnk;
} Env;

// Nat ::=
//   | Zero
//   | Succ ::= Nat
typedef Term Nat;
#define NAT_IMM ((1ull << NAT_BITS) - 1)

// U32 ::= { val: u32 }
typedef Term U32;

// Bool ::=
//   | False
//   | True
typedef Term Bool;

// Chr ::= { val: u32 }
typedef Term Chr;

// Tuple ::= { fst: Term, snd: Term }
typedef Term Tuple;

// Cmp ::=
//   | LT
//   | EQ
//   | GT
typedef Term Cmp;

// Str ::=
//   | SNil
//   | SCon ::= { head: Chr, tail: Str }
typedef Term Str;

#ifndef __METAL_VERSION__
// HOST BEGIN types
typedef _Atomic u32     a32;
typedef _Atomic u64     a64;
typedef pthread_mutex_t Mutex;
typedef pthread_cond_t  Cond;
typedef pthread_t       Tid;
#if BEND_METAL
typedef id<MTLDevice>               GpuDev;
typedef id<MTLCommandQueue>         GpuQueue;
typedef id<MTL4CommandQueue>        GpuQueue4;
typedef id<MTLSharedEvent>          GpuEvent;
typedef id<MTLLibrary>              GpuLib;
typedef id<MTLComputePipelineState> GpuPipe;
typedef id<MTLBuffer>               GpuBuf;
typedef id<MTLHeap>                 GpuHeap;
#endif
// HOST END types
#endif

// Constants
// =========

#define TOME_BITS  25
#define TOME_WORDS (1ull << TOME_BITS)
#define PAGE_BITS  11
#define PAGE_WORDS (1ull << PAGE_BITS)
#define TOME_PAGES (TOME_WORDS / PAGE_WORDS)
#define CUBE_SIDE  128
#define CUBE       (CUBE_SIDE * CUBE_SIDE)
#define RING_BITS  12
#define RING_LEN   (1u << RING_BITS)
#define MONK_WORDS 16ull
#define MAX_FORK   32
#define NCLS       11
#define HUGE_CLS   (32 - NCLS)
#define NAT_BITS   48

#define TAKE_RESERVE CUBE

#ifndef __METAL_VERSION__
// HOST BEGIN constants
#ifndef MAP_NORESERVE
#define MAP_NORESERVE 0
#endif
#define SPIN_COUNT   40000
#define POOL_MAX     256
#define SPAN_DEV     (1ull << 29)
#define SPAN_HOST    (1ull << 40)
#define CPU_TURN_MAX 1000000
#define GPU_TURN_MAX 200000
#if BEND_METAL
#define TOME_MAX     64
#define GPU_GROUP    256
#define GPU_TILE     (16 * 1024)
#define GPU_FENCE_MS 10000
#endif
// HOST END constants
#endif

// Globals
// =======

#ifndef __METAL_VERSION__
// HOST BEGIN globals

// Corpus
static Corpus CORPUS;
static u64    corpus_span;
static Mutex  corpus_wire = PTHREAD_MUTEX_INITIALIZER;

// Pool
static Mode  pool_mode;
static u32   pool_size;
static bool  pool_boot;
static a32   pool_kill;
static a64   pool_tick;
static a32   pool_done;
static Mutex pool_lock = PTHREAD_MUTEX_INITIALIZER;
static Cond  pool_wake = PTHREAD_COND_INITIALIZER;
static Tid   pool_tids[POOL_MAX];

// Gpu
#if BEND_METAL
static GpuDev    gpu_dev;
static GpuQueue  gpu_que;
static GpuQueue4 gpu_map;
static GpuEvent  gpu_evt;
static u64       gpu_seq;
static GpuLib    gpu_lib;
static GpuPipe   gpu_pso[2];
static GpuBuf    gpu_buf;
static GpuHeap   gpu_ram[TOME_MAX];
static GpuBuf    gpu_win[TOME_MAX];
#endif

// HOST END globals
#endif

// Book
// ====

//GEN:DEFS//

INLINE Reply fid_call(Env e, Fid fid, Loc a, Term cont, u32 idx);

// Checks
// ======

#ifndef __METAL_VERSION__
// HOST BEGIN checks
#if !defined(__STDC_VERSION__) || __STDC_VERSION__ < 201112L
#error "Bend4 needs C11 with atomics and pthreads"
#endif
#define TAG_TOP ((TAG_TASK << 60) | (AUX_MASK << 40) | LOC_MASK)
_Static_assert(sizeof(u64) == 8, "sizeof(u64) == 8");
_Static_assert(MAX_FORK * MAX_FORK <= RING_LEN, "MAX_FORK^2 <= RING_LEN");
_Static_assert((PAGE_WORDS & (PAGE_WORDS - 1)) == 0, "PAGE_WORDS == 2^PAGE_BITS");
_Static_assert(TAG_TOP < TERM_WORK, "TAG_TOP < TERM_WORK");
_Static_assert(MAX_ARITY < 256, "MAX_ARITY < 256");
_Static_assert(RING_OFF + (u64)CUBE * RING_LEN <= HEAP_OFF, "Cube ends below Heap");
#if BEND_METAL
_Static_assert(CUBE % GPU_GROUP == 0, "GPU_GROUP divides CUBE");
#endif
// HOST END checks
#endif

// A32
// ===

#ifdef __METAL_VERSION__

INLINE u32 a32_load(DEV u32* p) {
  return atomic_load_explicit(A32(p), RLX);
}

INLINE void a32_store(DEV u32* p, u32 v) {
  atomic_store_explicit(A32(p), v, RLX);
}

INLINE u32 a32_add(DEV u32* p, u32 v) {
  return atomic_fetch_add_explicit(A32(p), v, RLX);
}

INLINE u32 a32_sub(DEV u32* p, u32 v) {
  return atomic_fetch_sub_explicit(A32(p), v, RLX);
}

INLINE u32 a32_max(DEV u32* p, u32 v) {
  return atomic_fetch_max_explicit(A32(p), v, RLX);
}

INLINE bool a32_cas(DEV u32* p, thread u32* e, u32 v) {
  FENCE();
  bool ok = atomic_compare_exchange_weak_explicit(A32(p), e, v, RLX, RLX);
  if (ok) {
    FENCE();
  }
  return ok;
}

INLINE void a32_store_rel(DEV u32* p, u32 v) {
  FENCE();
  a32_store(p, v);
}

INLINE u32 a32_load_acq(DEV u32* p) {
  u32 v = a32_load(p);
  FENCE();
  return v;
}

#else

INLINE u32 a32_load(u32* p) {
  return __atomic_load_n(p, __ATOMIC_RELAXED);
}

INLINE void a32_store(u32* p, u32 v) {
  __atomic_store_n(p, v, __ATOMIC_RELAXED);
}

INLINE u32 a32_add(u32* p, u32 v) {
  return __atomic_fetch_add(p, v, __ATOMIC_RELAXED);
}

INLINE u32 a32_sub(u32* p, u32 v) {
  return __atomic_fetch_sub(p, v, __ATOMIC_RELAXED);
}

INLINE u32 a32_max(u32* p, u32 v) {
  u32 o = __atomic_load_n(p, __ATOMIC_RELAXED);
  while (o < v) {
    if (__atomic_compare_exchange_n(p, &o, v, 1, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {
      return o;
    }
  }
  return o;
}

INLINE bool a32_cas(u32* p, u32* e, u32 v) {
  return __atomic_compare_exchange_n(p, e, v, 1, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
}

INLINE void a32_store_rel(u32* p, u32 v) {
  __atomic_store_n(p, v, __ATOMIC_RELEASE);
}

INLINE u32 a32_load_acq(u32* p) {
  return __atomic_load_n(p, __ATOMIC_ACQUIRE);
}

#endif

// Err
// ===

#ifdef __METAL_VERSION__

INLINE void err_post(Corpus H, Err code) {
  u32 none = 0;
  a32_cas((DEV u32*)&H[C_ERROR_CODE], &none, code);
}

#else
// HOST BEGIN err

static void err_fail(Err code, const char* msg) {
  fprintf(stderr, "bend: error %u: %s\n", code, msg);
  abort();
}

static void err_post(Corpus H, Err code) {
  (void)H;
  err_fail(code, "runtime fail-stop");
}

// HOST END err
#endif

// Chan
// ====

INLINE void chan_unfocus(Corpus H) {
  a32_store((DEV u32*)&H[C_IS_FOCUSED], 0);
}

#ifndef __METAL_VERSION__
// HOST BEGIN chan

static void chan_arm(Corpus H) {
  a32_store((u32*)&H[C_IS_FOCUSED], 1);
  a32_store((u32*)&H[C_NEED_TOMES], 0);
  a32_store((u32*)&H[C_ERROR_CODE], 0);
}

// HOST END chan
#endif

// Loc
// ===

INLINE Loc loc_clip(u64 i) {
  return i & LOC_MASK;
}

INLINE u64 loc_at(Loc loc) {
#ifdef __METAL_VERSION__
  if (loc < HEAP_OFF) {
    return loc;
  } else {
    u64 hl = loc - HEAP_OFF;
    u64 p  = hl >> PAGE_BITS;
    u64 i  = hl & (PAGE_WORDS - 1);
    u64 t  = p / TOME_PAGES;
    u64 s  = p % TOME_PAGES;
    return HEAP_OFF + (t << TOME_BITS) + i * TOME_PAGES + s;
  }
#else
  return loc;
#endif
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

INLINE u32 cls_cap(Cls cls) {
  return (u32)((PAGE_WORDS - PAGE_HDR) >> cls);
}

// Fill
// ====

INLINE Fill fill_new(u32 idx, u32 rem) {
  return ((u64)idx << 32) | rem;
}

INLINE u32 fill_idx(Fill f) {
  return (u32)(f >> 32);
}

INLINE u32 fill_rem(Fill f) {
  return (u32)f;
}

#ifdef __METAL_VERSION__

INLINE u32 fill_drop(DEV u32* p) {
  FENCE();
  u32 prior = a32_sub(p, 1);
  if (prior == 1) {
    FENCE();
  }
  return prior;
}

#else

INLINE u32 fill_drop(u32* p) {
  return __atomic_fetch_sub(p, 1, __ATOMIC_ACQ_REL);
}

#endif

// Tome
// ====

INLINE u64 tome_pages(Tome t) {
  return (u64)t * TOME_PAGES - HEAP_OFF / PAGE_WORDS;
}

#ifndef __METAL_VERSION__
// HOST BEGIN tome

static void tome_wire_host(Tome t) {
  u64   size = TOME_WORDS * 8;
  char* base = (char*)CORPUS + (u64)t * size;
  if (mprotect(base, size, PROT_READ | PROT_WRITE) != 0) {
    err_fail(ERR_HEAP, "tome_wire: mprotect failed");
  }
}

#if BEND_METAL
static void tome_wire_leaf(Tome t) {
  if (!gpu_buf) {
    tome_wire_host(t);
  } else {
    if (t >= TOME_MAX) {
      err_fail(ERR_HEAP, "tome backing table exhausted");
    }
    @autoreleasepool {
      u64 size = TOME_WORDS * 8;
      MTLHeapDescriptor* hd = [MTLHeapDescriptor new];
      hd.type        = MTLHeapTypePlacement;
      hd.storageMode = MTLStorageModeShared;
      hd.size        = size;
      hd.maxCompatiblePlacementSparsePageSize = MTLSparsePageSize16;
      GpuHeap ram = [gpu_dev newHeapWithDescriptor:hd];
      if (!ram) {
        err_fail(ERR_HEAP, "tome_wire: backing heap allocation failed");
      }
      MTLResourceOptions shr = MTLResourceStorageModeShared;
      GpuBuf win = [ram newBufferWithLength:size options:shr offset:0];
      if (!win) {
        err_fail(ERR_HEAP, "tome_wire: heap view buffer failed");
      }
      u64     tiles = size / GPU_TILE;
      NSRange range = NSMakeRange((u64)t * tiles, tiles);
      MTL4UpdateSparseBufferMappingOperation op = { MTLSparseTextureMappingModeMap, range, 0 };
      [gpu_map updateBufferMappings:gpu_buf heap:ram operations:&op count:1];
      [gpu_map signalEvent:gpu_evt value:++gpu_seq];
      if (![gpu_evt waitUntilSignaledValue:gpu_seq timeoutMS:GPU_FENCE_MS]) {
        err_fail(ERR_HEAP, "tome_wire: mapping fence timeout");
      }
      mach_port_t       self = mach_task_self();
      mach_vm_address_t dst  = (mach_vm_address_t)((char*)CORPUS + (u64)t * size);
      mach_vm_address_t src  = (mach_vm_address_t)[win contents];
      int               flag = VM_FLAGS_FIXED | VM_FLAGS_OVERWRITE;
      boolean_t         keep = FALSE;
      vm_inherit_t      inh  = VM_INHERIT_NONE;
      vm_prot_t         cur;
      vm_prot_t         max;
      kern_return_t kr = mach_vm_remap(self, &dst, size, 0, flag, self, src, keep, &cur, &max, inh);
      if (kr != KERN_SUCCESS) {
        err_fail(ERR_HEAP, "tome_wire: mach_vm_remap failed");
      }
      gpu_ram[t] = ram;
      gpu_win[t] = win;
    }
  }
}
#else
static void tome_wire_leaf(Tome t) {
  tome_wire_host(t);
}
#endif

static void tome_wire(Corpus H) {
  pthread_mutex_lock(&corpus_wire);
  Tome t   = a32_load((u32*)&H[H_TOME_BUMP]);
  u64  top = ((u64)t + 1) * TOME_WORDS;
  if (top > corpus_span) {
    err_fail(ERR_HEAP, "corpus span exhausted (grow BEND_SPAN)");
  }
  tome_wire_leaf(t);
  a32_store((u32*)&H[H_TOME_BUMP], t + 1);
  pthread_mutex_unlock(&corpus_wire);
}

// HOST END tome
#endif

// Page
// ====

INLINE Loc page_loc(Page p) {
  return HEAP_OFF + ((u64)p << PAGE_BITS);
}

INLINE Page page_take(Corpus H) {
  Page p = a32_add((DEV u32*)&H[H_PAGE_BUMP], 1);
#ifdef __METAL_VERSION__
  u64 wired = tome_pages(a32_load((DEV u32*)&H[H_TOME_BUMP]));
  if ((u64)p + 1 > wired) {
    err_post(H, ERR_HEAP);
    return PAGE_NIL;
  }
#else
  while ((u64)p + 1 > tome_pages(a32_load((u32*)&H[H_TOME_BUMP]))) {
    tome_wire(H);
  }
#endif
  return p;
}

INLINE void page_stack_push(Corpus H, DEV u32* head, Page p) {
  DEV u32* link = (DEV u32*)&H[loc_at(page_loc(p))];
  u32 e = a32_load(head);
  for (;;) {
    a32_store(link, e & PAGE_NIL);
    if (a32_cas(head, &e, ((e + (PAGE_NIL + 1)) & ~PAGE_NIL) | p)) {
      return;
    }
  }
}

INLINE Page page_stack_pop(Corpus H, DEV u32* head) {
  u32 e = a32_load(head);
  while ((e & PAGE_NIL) != PAGE_NIL) {
    u32 next = a32_load((DEV u32*)&H[loc_at(page_loc(e & PAGE_NIL))]);
    if (a32_cas(head, &e, ((e + (PAGE_NIL + 1)) & ~PAGE_NIL) | (next & PAGE_NIL))) {
      return e & PAGE_NIL;
    }
  }
  return PAGE_NIL;
}

INLINE void page_free_push(Corpus H, Page p) {
  page_stack_push(H, (DEV u32*)&H[H_PAGE_FREE], p);
}

INLINE Page page_free_pop(Corpus H) {
  return page_stack_pop(H, (DEV u32*)&H[H_PAGE_FREE]);
}

// Heap
// ====

INLINE bool heap_guard(Corpus H, u32 need) {
#ifdef __METAL_VERSION__
  u64 pb = a32_load((DEV u32*)&H[H_PAGE_BUMP]);
  u64 wp = tome_pages(a32_load((DEV u32*)&H[H_TOME_BUMP]));
  if (pb + need + TAKE_RESERVE <= wp) {
    return true;
  } else {
    a32_max((DEV u32*)&H[C_NEED_TOMES], (u32)((pb + need + TAKE_RESERVE - wp) / TOME_PAGES) + 1);
    return false;
  }
#else
  for (;;) {
    u64 want = a32_load((u32*)&H[H_PAGE_BUMP]) + need + TAKE_RESERVE;
    u64 have = tome_pages(a32_load((u32*)&H[H_TOME_BUMP]));
    if (want <= have) {
      return true;
    }
    tome_wire(H);
  }
#endif
}

INLINE Loc heap_alloc(Env e, Cls cls) {
  Corpus H = e.mem;
  if (cls < NCLS) {
    DEV u64* owns = &H[MONK_OFF + (u64)e.mnk * MONK_WORDS + M_OWN_PAGE + cls];
    for (;;) {
      u32 p = (u32)*owns;
      if (p == 0) {
        Page np = page_free_pop(H);
        if (np == PAGE_NIL) {
          np = page_take(H);
        }
        if (np == PAGE_NIL) {
          return WRECK_LOC;
        }
        DEV u32* stk  = (DEV u32*)&H[loc_at(page_loc(np))];
        DEV u32* meta = (DEV u32*)&H[loc_at(page_loc(np) + 1)];
        a32_store(stk, SLOT_NIL);
        a32_store(stk + 1, PAGE_OWNED);
        meta[0] = cls;
        meta[1] = 0;
        *owns = (u64)np + 1;
        continue;
      }
      p -= 1;
      DEV u32* stk  = (DEV u32*)&H[loc_at(page_loc(p))];
      DEV u32* live = stk + 1;
      u32 e0 = a32_load(stk);
      while ((e0 & SLOT_NIL) != SLOT_NIL) {
        u32 b    = e0 & SLOT_NIL;
        Loc bloc = page_loc(p) + PAGE_HDR + ((u64)b << cls);
        u32 next = a32_load((DEV u32*)&H[loc_at(bloc)]);
        if (a32_cas(stk, &e0, ((e0 + (SLOT_NIL + 1)) & ~SLOT_NIL) | (next & SLOT_NIL))) {
          a32_add(live, 1);
          return bloc;
        }
      }
      DEV u32* meta = (DEV u32*)&H[loc_at(page_loc(p) + 1)];
      u32 bump = meta[1];
      if (bump < cls_cap(cls)) {
        meta[1] = bump + 1;
        a32_add(live, 1);
        return page_loc(p) + PAGE_HDR + ((u64)bump << cls);
      }
      *owns = 0;
      if (a32_sub(live, PAGE_OWNED) == PAGE_OWNED) {
        page_free_push(H, p);
      }
    }
  } else {
    DEV u32* head = (DEV u32*)&H[H_HUGE_FREE + (cls - NCLS)];
    Page got = page_stack_pop(H, head);
    if (got != PAGE_NIL) {
      return page_loc(got);
    }
    u32 span = 1u << (cls - PAGE_BITS);
    DEV u32* pb = (DEV u32*)&H[H_PAGE_BUMP];
    u32 o = a32_load(pb);
    for (;;) {
      u32 base = (o + span - 1) & ~(span - 1);
      if (a32_cas(pb, &o, base + span)) {
        for (u32 p = o; p < base; p += 1) {
          page_free_push(H, p);
        }
#ifdef __METAL_VERSION__
        u64 wired = tome_pages(a32_load((DEV u32*)&H[H_TOME_BUMP]));
        if ((u64)base + span > wired) {
          err_post(H, ERR_HEAP);
          return WRECK_LOC;
        }
#else
        while ((u64)base + span > tome_pages(a32_load((u32*)&H[H_TOME_BUMP]))) {
          tome_wire(H);
        }
#endif
        return page_loc(base);
      }
    }
  }
}

INLINE void heap_free(Corpus H, Cls cls, Loc loc) {
  if (cls < NCLS) {
    Page p = (u32)((loc - HEAP_OFF) >> PAGE_BITS);
    u32  b = (u32)(((loc - HEAP_OFF) & (PAGE_WORDS - 1)) - PAGE_HDR) >> cls;
    DEV u32* stk  = (DEV u32*)&H[loc_at(page_loc(p))];
    DEV u32* live = stk + 1;
    u32 e = a32_load(stk);
    for (;;) {
      a32_store((DEV u32*)&H[loc_at(loc)], e & SLOT_NIL);
      if (a32_cas(stk, &e, ((e + (SLOT_NIL + 1)) & ~SLOT_NIL) | b)) {
        break;
      }
    }
    if (a32_sub(live, 1) == 1) {
      page_free_push(H, p);
    }
  } else {
    Page p = (u32)((loc - HEAP_OFF) >> PAGE_BITS);
    DEV u32* head = (DEV u32*)&H[H_HUGE_FREE + (cls - NCLS)];
    page_stack_push(H, head, p);
  }
}

INLINE Loc heap_swap(Env e, Loc own, Cls ocls, Cls ncls) {
  if (ocls == ncls) {
    return own;
  } else {
    heap_free(e.mem, ocls, own);
    return heap_alloc(e, ncls);
  }
}

// Drop
// ====

INLINE Drop drop_new(Loc loc, u32 len, Cls cls) {
  return loc | ((u64)len << 48) | ((u64)cls << 56);
}

INLINE Loc drop_loc(Drop d) {
  return d & LOC_MASK;
}

INLINE u32 drop_idx(Drop d) {
  return (u8)(d >> 40);
}

INLINE u32 drop_len(Drop d) {
  return (u8)(d >> 48);
}

INLINE Cls drop_cls(Drop d) {
  return (u32)(d >> 56);
}

INLINE Drop drop_step(Drop d) {
  return d + (1ull << 40);
}

// Term
// ====

INLINE Term term_ctor(Cid cid, Loc loc) {
  return (TAG_CTOR << 60) | ((u64)cid << 40) | loc;
}

INLINE Term term_clos(Fid fid, Loc loc) {
  return (TAG_CLOS << 60) | ((u64)fid << 40) | loc;
}

INLINE Term term_flat(Cls cls, Loc loc) {
  return (TAG_FLAT << 60) | ((u64)cls << 40) | loc;
}

INLINE Term term_task(Fid fid, Loc loc) {
  return (TAG_TASK << 60) | ((u64)fid << 40) | loc;
}

INLINE u64 term_tag(Term t) {
  return t >> 60;
}

INLINE u64 term_aux(Term t) {
  return (t >> 40) & AUX_MASK;
}

INLINE Loc term_loc(Term t) {
  return t & LOC_MASK;
}

INLINE bool term_triv(Term t) {
  u64 tag = term_tag(t);
  return t >= TERM_WORK || tag == TAG_WORD || (tag == TAG_CTOR && term_loc(t) == 0) || (tag == TAG_CLOS && fid_arity((u32)term_aux(t)) <= 1);
}

static void term_drop(Corpus H, Term t) {
  Drop cur = DROP_NONE;
  Term c0  = 0;
  for (;;) {
    if (!term_triv(t)) {
      u64 tag = term_tag(t);
      if (tag == TAG_FLAT) {
        heap_free(H, (u32)term_aux(t), term_loc(t));
      } else {
        u32 aux = (u32)term_aux(t);
        Loc loc = term_loc(t);
        u32 n;
        if (tag == TAG_CTOR) {
          n = cid_arity(aux);
        } else if (tag == TAG_CLOS) {
          n = fid_arity(aux) - 1;
        } else {
          n = fid_arity(aux);
        }
        u32 slots;
        if (tag == TAG_TASK) {
          slots = n + 2;
        } else if (n == 0) {
          slots = 1;
        } else {
          slots = n;
        }
        Cls cls = cls_fit(slots);
        if (n == 0) {
          c0 = 0;
        } else {
          c0 = H[loc_at(loc)];
        }
        H[loc_at(loc)] = cur;
        cur = drop_new(loc, n, cls);
      }
    }
    for (;;) {
      if (cur == DROP_NONE) {
        return;
      }
      Loc loc = drop_loc(cur);
      u32 i   = drop_idx(cur);
      u32 n   = drop_len(cur);
      Cls cls = drop_cls(cur);
      if (i < n) {
        Term c;
        if (i == 0) {
          c = c0;
        } else {
          c = H[loc_at(loc + i)];
        }
        cur = drop_step(cur);
        if (!term_triv(c)) {
          t = c;
          break;
        }
      } else {
        Drop up = H[loc_at(loc)];
        heap_free(H, cls, loc);
        cur = up;
      }
    }
  }
}

// Tuple
// =====

INLINE Tuple tuple_new(Env e, Term fst, Term snd) {
  Loc loc = heap_alloc(e, 1);
  e.mem[loc_at(loc)]     = fst;
  e.mem[loc_at(loc + 1)] = snd;
  return term_ctor(CID_TUPLE, loc);
}

// Str
// ===

INLINE Str str_snil(void) {
  return term_ctor(CID_SNIL, 0);
}

INLINE Str str_scon(Env e, Chr head, Str tail) {
  Loc loc = heap_alloc(e, 1);
  e.mem[loc_at(loc)]     = head;
  e.mem[loc_at(loc + 1)] = tail;
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
// HOST BEGIN str

static u64 str_fnv(Corpus H, Str s) {
  u64 fnv = 0xcbf29ce484222325ull;
  while (term_aux(s) == CID_SCON) {
    Loc  loc = term_loc(s);
    char c   = (char)(u32)H[loc_at(loc)];
    Str  cs  = H[loc_at(loc + 1)];
    heap_free(H, cls_fit(2), loc);
    putchar(c);
    fnv ^= (u8)c;
    fnv *= 0x100000001b3ull;
    s = cs;
  }
  putchar('\n');
  if (term_aux(s) != CID_SNIL) {
    err_fail(ERR_TAGS, "result is not a String");
  }
  return fnv;
}

// HOST END str
#endif

// Chr
// ===

INLINE Chr chr_new(u32 val) {
  return (u64)val;
}

INLINE Str chr_show(Env e, Chr v) {
  return str_scon(e, v, str_snil());
}

// U32
// ===

INLINE Tuple u32_copy(Env e, U32 x) {
  return tuple_new(e, tuple_new(e, x, 0), tuple_new(e, x, 0));
}

INLINE U32 u32_div(U32 a, U32 b) {
  if ((u32)b == 0) {
    return 0;
  } else {
    return (u32)a / (u32)b;
  }
}

INLINE U32 u32_mod(U32 a, U32 b) {
  if ((u32)b == 0) {
    return 0;
  } else {
    return (u32)a % (u32)b;
  }
}

INLINE U32 u32_shln(U32 a, U32 n) {
  if (n >= 32) {
    return 0;
  } else {
    return (u64)(u32)((u32)a << n);
  }
}

INLINE U32 u32_shrn(U32 a, U32 n) {
  if (n >= 32) {
    return 0;
  } else {
    return (u64)((u32)a >> n);
  }
}

INLINE Str u32_show(Env e, U32 v) {
  return str_digits(e, str_snil(), v);
}

// Nat
// ===

INLINE Nat nat_succ(Env e, Nat n) {
  if (n + 1 > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
  }
  return n + 1;
}

INLINE Nat nat_pred(Nat n) {
  if (n == 0) {
    return 0;
  } else {
    return n - 1;
  }
}

INLINE Tuple nat_copy(Env e, Nat x) {
  return tuple_new(e, tuple_new(e, x, 0), tuple_new(e, x, 0));
}

INLINE Nat nat_add(Env e, Nat a, Nat b) {
  if (a + b > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
  }
  return a + b;
}

INLINE Nat nat_sub(Nat a, Nat b) {
  if (a < b) {
    return 0;
  } else {
    return a - b;
  }
}

INLINE Nat nat_mul(Env e, Nat a, Nat b) {
  if (b != 0 && a > NAT_IMM / b) {
    err_post(e.mem, ERR_NATS);
  }
  return a * b;
}

INLINE Nat nat_div(Nat a, Nat b) {
  if (b == 0) {
    return 0;
  } else {
    return a / b;
  }
}

INLINE Nat nat_mod(Nat a, Nat b) {
  if (b == 0) {
    return a;
  } else {
    return a % b;
  }
}

INLINE Nat nat_min(Nat a, Nat b) {
  if (a < b) {
    return a;
  } else {
    return b;
  }
}

INLINE Nat nat_max(Nat a, Nat b) {
  if (a < b) {
    return b;
  } else {
    return a;
  }
}

INLINE Nat nat_double(Env e, Nat n) {
  if (n << 1 > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
  }
  return n << 1;
}

INLINE Nat nat_pow2(Env e, Nat n) {
  if (n >= NAT_BITS) {
    err_post(e.mem, ERR_NATS);
  }
  return 1ull << n;
}

INLINE Tuple nat_divmod(Env e, Nat a, Nat b) {
  if (b == 0) {
    return tuple_new(e, 0, a);
  } else {
    return tuple_new(e, a / b, a % b);
  }
}

INLINE Tuple nat_bits(Env e, Nat n) {
  return tuple_new(e, n & 1, n >> 1);
}

INLINE Str nat_show(Env e, Nat v) {
  return str_digits(e, str_scon(e, chr_new('n'), str_snil()), v);
}

// Bool
// ====

INLINE Tuple bool_copy(Env e, Bool x) {
  return tuple_new(e, tuple_new(e, x, 0), tuple_new(e, x, 0));
}

INLINE Term bool_if(Corpus H, Bool b, Term t, Term f) {
  if (b) {
    term_drop(H, f);
    return t;
  } else {
    term_drop(H, t);
    return f;
  }
}

INLINE Str bool_show(Env e, Bool v) {
  Str out = str_scon(e, chr_new('{'), str_scon(e, chr_new('}'), str_snil()));
  if (v) {
    out = str_scon(e, chr_new('e'), out);
    out = str_scon(e, chr_new('u'), out);
    out = str_scon(e, chr_new('r'), out);
    out = str_scon(e, chr_new('T'), out);
  } else {
    out = str_scon(e, chr_new('e'), out);
    out = str_scon(e, chr_new('s'), out);
    out = str_scon(e, chr_new('l'), out);
    out = str_scon(e, chr_new('a'), out);
    out = str_scon(e, chr_new('F'), out);
  }
  return out;
}

// Cmp
// ===

INLINE Cmp cmp_lt(void) {
  return term_ctor(CID_LT, 0);
}

INLINE Cmp cmp_eq(void) {
  return term_ctor(CID_EQ, 0);
}

INLINE Cmp cmp_gt(void) {
  return term_ctor(CID_GT, 0);
}

INLINE Cmp cmp_new(u64 a, u64 b) {
  if (a < b) {
    return cmp_lt();
  } else if (a == b) {
    return cmp_eq();
  } else {
    return cmp_gt();
  }
}

// Flat
// ====

INLINE Term flat_leaf(Env e, Term v) {
  Loc loc = heap_alloc(e, 0);
  e.mem[loc_at(loc)] = v;
  return term_flat(0, loc);
}

INLINE Term flat_node(Env e, Term l, Term r) {
  Corpus H = e.mem;
  Cls c = (u32)term_aux(l);
  Loc n = heap_alloc(e, c + 1);
  for (u64 i = 0; i < (1ull << c); i += 1) {
    H[loc_at(n + i)]               = H[loc_at(term_loc(l) + i)];
    H[loc_at(n + (1ull << c) + i)] = H[loc_at(term_loc(r) + i)];
  }
  heap_free(H, c, term_loc(l));
  heap_free(H, c, term_loc(r));
  return term_flat(c + 1, n);
}

INLINE Term flat_half(Env e, Term a, u32 hi) {
  Corpus H = e.mem;
  Cls c = (u32)term_aux(a) - 1;
  Loc n = heap_alloc(e, c);
  for (u64 i = 0; i < (1ull << c); i += 1) {
    H[loc_at(n + i)] = H[loc_at(term_loc(a) + ((u64)hi << c) + i)];
  }
  return term_flat(c, n);
}

INLINE u32 flat_swap(Corpus H, Term a, u32 i, u32 v) {
  DEV u64* cell = &H[loc_at(term_loc(a) + loc_clip(i))];
  u32 old = (u32)*cell;
  *cell = v;
  return old;
}

INLINE u32 flat_clamp(Term a, Term i) {
  u64 len = 1ull << term_aux(a);
  if (i < len) {
    return (u32)i;
  } else {
    return (u32)(len - 1);
  }
}

INLINE Term flat_take(Corpus H, Term a) {
  Term v = H[loc_at(term_loc(a))];
  heap_free(H, 0, term_loc(a));
  return v;
}

INLINE Tuple flat_trade(Env e, Term a, U32 i, U32 v) {
  return tuple_new(e, a, (u64)flat_swap(e.mem, a, flat_clamp(a, i), (u32)v));
}

// Reply
// =====

INLINE u32 reply_kind(Corpus H, Reply r) {
  if (r >= TERM_WORK) {
    if (r == TERM_NEED) {
      return REPLY_NEED;
    } else {
      return REPLY_WORK;
    }
  } else if (term_tag(r) == TAG_TASK) {
    Fill fill = H[loc_at(term_loc(r) + fid_arity((u32)term_aux(r)) + 1)];
    if (fill_rem(fill) == 0) {
      return REPLY_CALL;
    } else {
      return REPLY_FORK;
    }
  } else {
    return REPLY_DONE;
  }
}

// Ring
// ====

INLINE DEV u64* ring_cursors(Corpus H, Ring r) {
  return H + MONK_OFF + (u64)r * MONK_WORDS;
}

INLINE u64 ring_len(Corpus H, Ring r) {
  DEV u64* mk = ring_cursors(H, r);
  return mk[M_RING_PUT] - mk[M_RING_GET];
}

INLINE void ring_push(Corpus H, Ring r, Term tsk) {
  DEV u64* mk = ring_cursors(H, r);
  if (mk[M_RING_PUT] - mk[M_RING_GET] >= RING_LEN) {
    err_post(H, ERR_RING);
  } else {
    H[RING_OFF + ((u64)r << RING_BITS) + (mk[M_RING_PUT] & (RING_LEN - 1))] = tsk;
    mk[M_RING_PUT] += 1;
  }
}

INLINE Term ring_pop_fifo(Corpus H, Ring r) {
  DEV u64* mk = ring_cursors(H, r);
  if (mk[M_RING_GET] == mk[M_RING_PUT]) {
    return 0;
  } else {
    Term t = H[RING_OFF + ((u64)r << RING_BITS) + (mk[M_RING_GET] & (RING_LEN - 1))];
    mk[M_RING_GET] += 1;
    return t;
  }
}

INLINE Term ring_pop_lifo(Corpus H, Ring r) {
  DEV u64* mk = ring_cursors(H, r);
  if (mk[M_RING_GET] == mk[M_RING_PUT]) {
    return 0;
  } else {
    mk[M_RING_PUT] -= 1;
    return H[RING_OFF + ((u64)r << RING_BITS) + (mk[M_RING_PUT] & (RING_LEN - 1))];
  }
}

// Task
// ====

INLINE Loc task_node(Env e, Fid fid, Term cont, u32 idx, u32 rem) {
  u32 ar  = fid_arity(fid);
  Loc loc = heap_alloc(e, cls_fit(ar + 2));
  e.mem[loc_at(loc + ar)]     = cont;
  e.mem[loc_at(loc + ar + 1)] = fill_new(idx, rem);
  return loc;
}

INLINE Term task_deliver(Corpus H, Term cont, u32 idx, Term v) {
  chan_unfocus(H);
  if (cont == TERM_HOLE) {
    H[H_ROOT_WORD] = v;
    a32_store_rel((DEV u32*)&H[H_ROOT_DONE], 1);
    return 0;
  } else {
    Loc loc = term_loc(cont);
    u32 ar  = fid_arity((u32)term_aux(cont));
    H[loc_at(loc + idx)] = v;
    u32 prior = fill_drop((DEV u32*)&H[loc_at(loc + ar + 1)]);
    if (prior == 1) {
      return cont;
    } else {
      return 0;
    }
  }
}

INLINE void task_deal(Corpus H, Term join, Ring even, Ring odd) {
  chan_unfocus(H);
  Loc loc = term_loc(join);
  u32 ar  = fid_arity((u32)term_aux(join));
  u32 j   = 0;
  for (u32 i = 0; i < ar; i += 1) {
    Term k = H[loc_at(loc + i)];
    if (k != TERM_HOLE && term_tag(k) == TAG_TASK) {
      H[loc_at(loc + i)] = TERM_HOLE;
      if (j & 1) {
        ring_push(H, odd, k);
      } else {
        ring_push(H, even, k);
      }
      j += 1;
    }
  }
}

INLINE Reply task_run(Env e, Term tsk, THR Term* cont_o, THR u32* idx_o) {
  Fid  fid  = (u32)term_aux(tsk);
  Loc  loc  = term_loc(tsk);
  u32  ar   = fid_arity(fid);
  Term cont = e.mem[loc_at(loc + ar)];
  u32  idx  = fill_idx(e.mem[loc_at(loc + ar + 1)]);
  *cont_o = cont;
  *idx_o  = idx;
  return fid_call(e, fid, loc, cont, idx);
}

// Clos
// ====

INLINE Reply clos_call(Env e, Term f, Term x, Term cont, u32 idx) {
  Fid fid = (u32)term_aux(f);
  u32 ar  = fid_arity(fid);
  Loc tk  = task_node(e, fid, cont, idx, 0);
  if (ar > 1) {
    Loc cl = term_loc(f);
    for (u32 i = 0; i < ar - 1; i += 1) {
      e.mem[loc_at(tk + i)] = e.mem[loc_at(cl + i)];
    }
    heap_free(e.mem, cls_fit(ar - 1), cl);
  }
  e.mem[loc_at(tk + ar - 1)] = x;
  return term_task(fid, tk);
}

// Code
// ====

//GEN:CODE//

// Monk
// ====

static void monk_grow(Corpus H, Monk m) {
  Env e = { H, m };
  u64 budget = ring_len(H, m) + RING_LEN;
  for (u64 n = 0; n < budget; n += 1) {
    Term t = ring_pop_fifo(H, m);
    if (t == 0) {
      return;
    }
    if (!fid_forks((u32)term_aux(t))) {
      ring_push(H, m, t);
      continue;
    }
    Term cont;
    u32  idx;
    Reply r = task_run(e, t, &cont, &idx);
    switch (reply_kind(H, r)) {
      case REPLY_NEED: {
        ring_push(H, m, t);
        return;
      }
      case REPLY_DONE: {
        Term p = task_deliver(H, cont, idx, r);
        if (p) {
          ring_push(H, m, p);
        }
        break;
      }
      case REPLY_CALL: {
        chan_unfocus(H);
        ring_push(H, m, r);
        break;
      }
      case REPLY_FORK: {
        task_deal(H, r, m, m);
        break;
      }
      case REPLY_WORK: {
        err_post(H, ERR_FIDS);
        return;
      }
    }
  }
}

static void monk_work(Corpus H, Monk m) {
  Env e = { H, m };
  u64 budget = ring_len(H, m) + RING_LEN;
  u64 n = 0;
  while (n < budget) {
    Term t = ring_pop_lifo(H, m);
    if (t == 0) {
      return;
    }
    bool live = true;
    while (live) {
      n += 1;
      Term cont;
      u32  idx;
      Reply r = task_run(e, t, &cont, &idx);
      switch (reply_kind(H, r)) {
        case REPLY_NEED: {
          ring_push(H, m, t);
          return;
        }
        case REPLY_DONE: {
          Term p = task_deliver(H, cont, idx, r);
          if (p == 0) {
            live = false;
          } else {
            t = p;
          }
          break;
        }
        case REPLY_CALL: {
          chan_unfocus(H);
          t = r;
          break;
        }
        case REPLY_FORK: {
          task_deal(H, r, m, m);
          live = false;
          break;
        }
        case REPLY_WORK: {
          err_post(H, ERR_FIDS);
          return;
        }
      }
    }
  }
}

#ifdef __METAL_VERSION__
kernel void monk_grow_dev(Corpus H [[buffer(0)]], u32 tid [[thread_position_in_grid]]) {
  monk_grow(H, tid);
}

kernel void monk_work_dev(Corpus H [[buffer(0)]], u32 tid [[thread_position_in_grid]]) {
  monk_work(H, tid);
}
#endif

#ifndef __METAL_VERSION__
// HOST BEGIN driver

// Cube
// ====

static u64 cube_frontier(Corpus H) {
  u64 n = 0;
  for (Ring r = 0; r < CUBE; r += 1) {
    n += ring_len(H, r);
  }
  return n;
}

static Mode cube_mode(Corpus H) {
  if (a32_load((u32*)&H[C_IS_FOCUSED]) == 1) {
    return MODE_WORK;
  } else if (cube_frontier(H) < CUBE) {
    return MODE_SEED;
  } else {
    return MODE_GROW;
  }
}

static void cube_seed_step(Corpus H, Ring src, Ring dst) {
  Env  e = { H, src };
  Term t = ring_pop_fifo(H, src);
  if (t == 0) {
    return;
  }
  for (;;) {
    Term cont;
    u32  idx;
    Reply r = task_run(e, t, &cont, &idx);
    switch (reply_kind(H, r)) {
      case REPLY_DONE: {
        Term p = task_deliver(H, cont, idx, r);
        if (p == 0) {
          return;
        }
        t = p;
        break;
      }
      case REPLY_CALL: {
        t = r;
        break;
      }
      default: {
        task_deal(H, r, src, dst);
        return;
      }
    }
  }
}

static void cube_seed(Corpus H, u32 w0) {
  for (u32 w = w0; w < CUBE_SIDE; w <<= 1) {
    for (u32 r = 0; r < w; r += 1) {
      cube_seed_step(H, r, r + w);
    }
  }
  for (u32 w = 1; w < CUBE_SIDE; w <<= 1) {
    for (u32 r = 0; r < CUBE_SIDE; r += 1) {
      for (u32 c = 0; c < w; c += 1) {
        cube_seed_step(H, c * CUBE_SIDE + r, (c + w) * CUBE_SIDE + r);
      }
    }
  }
}

// Pool
// ====

static void* pool_work(void* arg) {
  u32  w    = (u32)(uintptr_t)arg;
  u32  span = CUBE / pool_size;
  Monk m0   = w * span;
  Monk m1   = m0 + span;
  u64  seen = 0;
  for (;;) {
    u32 spins = 0;
    for (;;) {
      u64 tick = atomic_load_explicit(&pool_tick, memory_order_acquire);
      u32 stop = atomic_load_explicit(&pool_kill, memory_order_acquire);
      if (tick != seen || stop) {
        break;
      }
      spins += 1;
      if (spins > SPIN_COUNT) {
        pthread_mutex_lock(&pool_lock);
        for (;;) {
          u64 wtick = atomic_load_explicit(&pool_tick, memory_order_acquire);
          u32 wstop = atomic_load_explicit(&pool_kill, memory_order_acquire);
          if (wtick != seen || wstop) {
            break;
          }
          pthread_cond_wait(&pool_wake, &pool_lock);
        }
        pthread_mutex_unlock(&pool_lock);
      }
    }
    if (atomic_load_explicit(&pool_kill, memory_order_acquire)) {
      return NULL;
    }
    seen = atomic_load_explicit(&pool_tick, memory_order_acquire);
    if (pool_mode == MODE_GROW) {
      for (Monk m = m0; m < m1; m += 1) {
        monk_grow(CORPUS, m);
      }
    } else {
      for (Monk m = m0; m < m1; m += 1) {
        monk_work(CORPUS, m);
      }
    }
    atomic_fetch_add_explicit(&pool_done, 1, memory_order_release);
  }
}

static void pool_init(void) {
  u32 nt = 0;
  const char* te = getenv("BEND_THREADS");
  if (te) {
    nt = (u32)strtoul(te, NULL, 0);
  }
  if (nt == 0) {
    long cores = sysconf(_SC_NPROCESSORS_ONLN);
    nt = 1;
    while ((u32)(nt << 1) <= (u32)cores) {
      nt <<= 1;
    }
  }
  while (nt > POOL_MAX || CUBE % nt) {
    nt >>= 1;
  }
  pool_size = nt;
}

static void pool_start(void) {
  if (!pool_boot) {
    for (u32 w = 0; w < pool_size; w += 1) {
      if (pthread_create(&pool_tids[w], NULL, pool_work, (void*)(uintptr_t)w)) {
        err_fail(ERR_FAIL, "pthread_create");
      }
    }
    pool_boot = true;
  }
}

static void pool_stop(void) {
  if (pool_boot) {
    pthread_mutex_lock(&pool_lock);
    atomic_store_explicit(&pool_kill, 1, memory_order_release);
    atomic_fetch_add_explicit(&pool_tick, 1, memory_order_release);
    pthread_cond_broadcast(&pool_wake);
    pthread_mutex_unlock(&pool_lock);
    for (u32 w = 0; w < pool_size; w += 1) {
      pthread_join(pool_tids[w], NULL);
    }
    pool_boot = false;
  }
}

static void pool_turn(Mode mode) {
  pool_mode = mode;
  atomic_store_explicit(&pool_done, 0, memory_order_relaxed);
  pthread_mutex_lock(&pool_lock);
  atomic_fetch_add_explicit(&pool_tick, 1, memory_order_release);
  pthread_cond_broadcast(&pool_wake);
  pthread_mutex_unlock(&pool_lock);
  while (atomic_load_explicit(&pool_done, memory_order_acquire) < pool_size) {
    sched_yield();
  }
}

// Gpu
// ===

#if BEND_METAL

static bool gpu_probe(void) {
  if (!gpu_dev) {
    gpu_dev = MTLCreateSystemDefaultDevice();
  }
  return gpu_dev != nil;
}

static char* gpu_source(void) {
  const char* path = getenv("BEND_SRC");
  if (!path) {
    path = __FILE__;
  }
  FILE* f = fopen(path, "rb");
  if (!f) {
    err_fail(ERR_FAIL, "gpu_source: cannot read own source (set BEND_SRC)");
  }
  fseek(f, 0, SEEK_END);
  long len = ftell(f);
  fseek(f, 0, SEEK_SET);
  char* in = malloc((size_t)len + 1);
  if (fread(in, 1, (size_t)len, f) != (size_t)len) {
    err_fail(ERR_FAIL, "gpu_source: short read");
  }
  fclose(f);
  in[len] = 0;
  char*  out = malloc((size_t)len + 1);
  size_t o   = 0;
  int    cut = 0;
  char*  p   = in;
  while (*p) {
    char*  nl = strchr(p, '\n');
    size_t l;
    if (nl != NULL) {
      l = (size_t)(nl - p) + 1;
    } else {
      l = strlen(p);
    }
    if (strnstr(p, "// HOST " "BEGIN", l)) {
      cut = 1;
    }
    if (!cut) {
      memcpy(out + o, p, l);
      o += l;
    }
    if (strnstr(p, "// HOST " "END", l)) {
      cut = 0;
    }
    p += l;
  }
  out[o] = 0;
  free(in);
  return out;
}

static void gpu_compile(void) {
  if (!gpu_lib) {
    @autoreleasepool {
      char* src = gpu_source();
      NSError* err = nil;
      MTLCompileOptions* opt = [MTLCompileOptions new];
      opt.mathMode = MTLMathModeSafe;
      NSString* text = [NSString stringWithUTF8String:src];
      gpu_lib = [gpu_dev newLibraryWithSource:text options:opt error:&err];
      free(src);
      if (!gpu_lib) {
        err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
      }
    }
  }
}

static void gpu_pipeline(void) {
  @autoreleasepool {
    NSError* err = nil;
    const char* names[2] = {"monk_grow_dev", "monk_work_dev"};
    for (u32 i = 0; i < 2; i += 1) {
      id<MTLFunction> fn = [gpu_lib newFunctionWithName:[NSString stringWithUTF8String:names[i]]];
      gpu_pso[i] = [gpu_dev newComputePipelineStateWithFunction:fn error:&err];
      if (!gpu_pso[i]) {
        err_fail(ERR_FAIL, [[err localizedDescription] UTF8String]);
      }
    }
    gpu_que = [gpu_dev newCommandQueue];
    gpu_map = [gpu_dev newMTL4CommandQueue];
    gpu_evt = [gpu_dev newSharedEvent];
    if (!gpu_map || !gpu_evt) {
      err_fail(ERR_FAIL, "MTL4 mapping queue unavailable");
    }
    u64                span = corpus_span * 8;
    MTLResourceOptions priv = MTLResourceStorageModePrivate;
    MTLSparsePageSize  tile = MTLSparsePageSize16;
    gpu_buf = [gpu_dev newBufferWithLength:span options:priv placementSparsePageSize:tile];
    if (!gpu_buf) {
      err_fail(ERR_FAIL, "placement sparse corpus buffer failed");
    }
  }
}

static void gpu_dispatch(Corpus H, Mode mode) {
  (void)H;
  @autoreleasepool {
    id<MTLCommandBuffer> cb = [gpu_que commandBuffer];
    id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
    MTLSize grid  = MTLSizeMake(CUBE / GPU_GROUP, 1, 1);
    MTLSize group = MTLSizeMake(GPU_GROUP, 1, 1);
    [enc setComputePipelineState:gpu_pso[mode]];
    [enc setBuffer:gpu_buf offset:0 atIndex:0];
    [enc dispatchThreadgroups:grid threadsPerThreadgroup:group];
    [enc endEncoding];
    [cb commit];
    [cb waitUntilCompleted];
  }
}

#else

static bool gpu_probe(void) {
  return false;
}

static void gpu_compile(void) {
}

static void gpu_pipeline(void) {
}

static void gpu_dispatch(Corpus H, Mode mode) {
  (void)H;
  (void)mode;
  err_fail(ERR_FIDS, "no device");
}

#endif

static Term gpu_run(Corpus H, Term tsk) {
  Loc  loc  = term_loc(tsk);
  u32  ar   = fid_arity((u32)term_aux(tsk));
  Term cont = H[loc_at(loc + ar)];
  u32  idx  = fill_idx(H[loc_at(loc + ar + 1)]);
  H[loc_at(loc + ar)]     = TERM_HOLE;
  H[loc_at(loc + ar + 1)] = fill_new(0, 0);
  a32_store((u32*)&H[H_ROOT_DONE], 0);
  ring_push(H, 0, tsk);
  cube_seed(H, 1);
  Mode mode = MODE_GROW;
  while (!a32_load_acq((u32*)&H[H_ROOT_DONE])) {
    chan_arm(H);
    if (mode == MODE_SEED) {
      cube_seed(H, 1);
    } else {
      gpu_dispatch(H, mode);
    }
    H[H_GPU_TURNS] += 1;
    if (H[H_GPU_TURNS] > GPU_TURN_MAX) {
      err_fail(ERR_TURN, "gpu turn budget exceeded");
    }
    u32 ec = a32_load((u32*)&H[C_ERROR_CODE]);
    if (ec) {
      err_fail(ec, "device error");
    }
    u32 need = a32_load((u32*)&H[C_NEED_TOMES]);
    if (need) {
      while (need > 0) {
        tome_wire(H);
        need -= 1;
      }
      continue;
    }
    if (a32_load_acq((u32*)&H[H_ROOT_DONE])) {
      break;
    }
    if (cube_frontier(H) == 0) {
      err_fail(ERR_LEAK, "device frontier drained without a result");
    }
    mode = cube_mode(H);
  }
  Term v = H[H_ROOT_WORD];
  a32_store((u32*)&H[H_ROOT_DONE], 0);
  return task_deliver(H, cont, idx, v);
}

// Corpus
// ======

static Corpus corpus_setup(bool metal) {
  if (metal) {
    corpus_span = SPAN_DEV;
  } else {
    corpus_span = SPAN_HOST;
  }
  const char* sp = getenv("BEND_SPAN");
  if (sp) {
    corpus_span = strtoull(sp, NULL, 0);
  }
  CORPUS = mmap(NULL, corpus_span * 8, PROT_NONE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
  if (CORPUS == MAP_FAILED) {
    err_fail(ERR_HEAP, "corpus VA reservation failed (shrink BEND_SPAN)");
  }
  if (metal) {
    gpu_compile();
    gpu_pipeline();
  }
  for (Tome t = 0; t < HEAP_OFF / TOME_WORDS; t += 1) {
    tome_wire_leaf(t);
  }
  Corpus H = CORPUS;
  a32_store((u32*)&H[H_TOME_BUMP], HEAP_OFF / TOME_WORDS);
  a32_store((u32*)&H[H_PAGE_BUMP], 1);
  a32_store((u32*)&H[H_PAGE_FREE], PAGE_NIL);
  for (u32 c = 0; c < HUGE_CLS; c += 1) {
    a32_store((u32*)&H[H_HUGE_FREE + c], PAGE_NIL);
  }
  tome_wire(H);
  pool_init();
  return H;
}

static Term corpus_eval(Corpus H, bool metal) {
  Env  e  = { H, 0 };
  Loc  ml = task_node(e, FID_MAIN, TERM_HOLE, 0, 0);
  Term t  = term_task(FID_MAIN, ml);
  a32_store((u32*)&H[H_ROOT_DONE], 0);
  bool solo = true;
  while (solo) {
    Term cont;
    u32  idx;
    Reply r = task_run(e, t, &cont, &idx);
    switch (reply_kind(H, r)) {
      case REPLY_DONE: {
        Term p = task_deliver(H, cont, idx, r);
        if (a32_load_acq((u32*)&H[H_ROOT_DONE])) {
          return H[H_ROOT_WORD];
        }
        if (p == 0) {
          err_fail(ERR_LEAK, "solo delivery lost");
        }
        t = p;
        break;
      }
      case REPLY_CALL: {
        t = r;
        if (metal && fid_bangs((u32)term_aux(t))) {
          Term p = gpu_run(H, t);
          if (a32_load_acq((u32*)&H[H_ROOT_DONE])) {
            return H[H_ROOT_WORD];
          }
          if (p == 0) {
            err_fail(ERR_LEAK, "seam delivery lost");
          }
          t = p;
        }
        break;
      }
      case REPLY_FORK: {
        task_deal(H, r, 0, 1);
        solo = false;
        break;
      }
      default: {
        err_fail(ERR_LEAK, "host NEED is never observed");
      }
    }
  }
  pool_start();
  cube_seed(H, 2);
  Mode mode  = MODE_GROW;
  u64  turns = 0;
  while (!a32_load_acq((u32*)&H[H_ROOT_DONE])) {
    chan_arm(H);
    if (mode == MODE_SEED) {
      cube_seed(H, 1);
    } else {
      pool_turn(mode);
    }
    turns += 1;
    if (turns > CPU_TURN_MAX) {
      err_fail(ERR_TURN, "cpu turn budget exceeded");
    }
    if (a32_load_acq((u32*)&H[H_ROOT_DONE])) {
      break;
    }
    if (cube_frontier(H) == 0) {
      err_fail(ERR_LEAK, "frontier drained without a result");
    }
    mode = cube_mode(H);
  }
  return H[H_ROOT_WORD];
}

static void corpus_verify(Corpus H, Str s) {
  u64 fnv = str_fnv(H, s);
  pool_stop();
  u32 pb    = a32_load((u32*)&H[H_PAGE_BUMP]);
  u32 leaks = 0;
  for (Page p = 1; p < pb; p += 1) {
    u32 live = a32_load((u32*)&H[loc_at(page_loc(p))] + 1) & ~PAGE_OWNED;
    if (live) {
      Cls cls = (u32)H[loc_at(page_loc(p) + 1)];
      leaks += live;
      fprintf(stderr, "leak: page %u class %u live %u\n", p, cls, live);
    }
  }
  if (leaks) {
    err_fail(ERR_LEAK, "page live count nonzero at exit (leak)");
  }
  for (Ring r = 0; r < CUBE; r += 1) {
    if (ring_len(H, r) != 0) {
      err_fail(ERR_LEAK, "ring not drained at exit");
    }
  }
  u32                tomes = a32_load((u32*)&H[H_TOME_BUMP]);
  unsigned long long turns = H[H_GPU_TURNS];
  printf("fnv: 0x%016llx\n", (unsigned long long)fnv);
  printf("stats: pages %u, tomes %u, turns %llu, threads %u\n", pb, tomes, turns, pool_size);
}

// Main
// ====

int main(void) {
  const char* md = getenv("BEND_MODE");
  bool metal;
  if (md != NULL) {
    metal = strcmp(md, "metal") == 0;
  } else {
    metal = gpu_probe();
  }
  if (metal && !gpu_probe()) {
    err_fail(ERR_FIDS, "BEND_MODE=metal but no device");
  }
  Corpus H = corpus_setup(metal);
  if (getenv("BEND_WARM") == NULL) {
    Str s = corpus_eval(H, metal);
    corpus_verify(H, s);
  }
  munmap(CORPUS, corpus_span * 8);
  return 0;
}

// HOST END driver
#endif

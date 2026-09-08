// IO
// ==

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <signal.h>
#include <sys/socket.h>

#define IO_ROWS 4096
#define IO_EFFS 64

#define IO_NONE 0
#define IO_FILE 1
#define IO_TCPS 2
#define IO_UDPS 3
#define IO_LSNR 4

// IoHand ::=
//   | IoHand(slot, mint)
typedef struct {
  uint32_t slot;
  uint32_t mint;
} IoHand;

// IoFall ::=
//   | IoFall(code, text)
typedef struct {
  uint32_t    code;
  const char* text;
} IoFall;

// IoRow ::=
//   | IoRow(mint, file, kind)
typedef struct {
  uint32_t mint;
  intptr_t file;
  int      kind;
} IoRow;

static IoRow    io_sys_rows[IO_ROWS];
static uint32_t io_sys_next = 0;
static uint32_t io_sys_free[IO_ROWS];
static uint32_t io_sys_idle = 0;

static pthread_mutex_t io_sys_lock = PTHREAD_MUTEX_INITIALIZER;

static void __attribute__((constructor)) io_sys_boot(void) {
  signal(SIGPIPE, SIG_IGN);
}

static uint64_t io_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

#define io_sys_done() io_sys_fall(0)

static IoFall io_sys_fall(uint32_t code) {
  IoFall out = { code, NULL };
  return out;
}

static int io_sys_mint(int kind, intptr_t fd, IoHand* out) {
  pthread_mutex_lock(&io_sys_lock);
  uint32_t slot = io_sys_idle > 0 ? io_sys_free[io_sys_idle - 1] : io_sys_next;
  io_sys_idle -= io_sys_idle > 0;
  io_sys_next += slot == io_sys_next && slot < IO_ROWS;
  if (slot < IO_ROWS) {
    IoRow* row = &io_sys_rows[slot];
    row->mint += 1;
    row->file = fd;
    row->kind = kind;
    out->slot = slot;
    out->mint = row->mint;
  }
  pthread_mutex_unlock(&io_sys_lock);
  return slot < IO_ROWS ? 0 : -1;
}

static IoRow* io_sys_row(IoHand hand) {
  IoRow* row = hand.slot < io_sys_next ? &io_sys_rows[hand.slot] : NULL;
  return row != NULL && row->mint == hand.mint ? row : NULL;
}

static intptr_t io_sys_read(IoHand hand, int kind) {
  pthread_mutex_lock(&io_sys_lock);
  IoRow*   row = io_sys_row(hand);
  intptr_t fd  = row != NULL && (kind == 0 || row->kind == kind)
    ? row->file : -1;
  pthread_mutex_unlock(&io_sys_lock);
  return fd;
}

static intptr_t io_sys_kill(IoHand hand) {
  pthread_mutex_lock(&io_sys_lock);
  IoRow*   row = io_sys_row(hand);
  intptr_t fd  = row != NULL ? row->file : -1;
  if (fd >= 0) {
    row->file = -1;
    row->kind = IO_NONE;
    io_sys_free[io_sys_idle] = hand.slot;
    io_sys_idle += 1;
  }
  pthread_mutex_unlock(&io_sys_lock);
  return fd;
}

static int io_sys_quad(const char* s, uint8_t* quad) {
  for (int i = 0; i < 4; i += 1, s += *s == '.') {
    const char* d = s;
    uint32_t    v = 0;
    while (*s >= '0' && *s <= '9' && s - d < 3) {
      v = v * 10 + (uint32_t)(*s - '0');
      s += 1;
    }
    if (s == d || v > 255 || (s - d > 1 && *d == '0')) {
      return -1;
    }
    if (*s != (i < 3 ? '.' : 0)) {
      return -1;
    }
    quad[i] = (uint8_t)v;
  }
  return 0;
}

static int io_sys_addr(const char* host, uint32_t port, void* out) {
  struct sockaddr_in* at = (struct sockaddr_in*)out;
  uint8_t quad[4];
  if (port > 65535 || io_sys_quad(host, quad) < 0) {
    return -1;
  }
  memset(at, 0, sizeof(*at));
  at->sin_family = AF_INET;
  at->sin_port = htons((uint16_t)port);
  memcpy(&at->sin_addr, quad, 4);
  return 0;
}

static int io_sys_sock(int type) {
  return socket(AF_INET, type, 0);
}

// Effects
// -------

#define IO_READ 1
#define IO_TIME 2
#define IO_PARK TERM_HOLE
#define IO_WORK (TERM_HOLE - 1)
#define IO_WAIT (TERM_HOLE - 2)

struct IoWork;
typedef void (*IoCall)(struct IoWork* w);
typedef Term (*IoPack)(Env e, struct IoWork* w);

// IoWork ::=
//   | IoWork(hand, made, word, size, data, text, fall, call, pack)
typedef struct IoWork {
  IoHand   hand;
  IoHand   made;
  uint32_t word;
  uint64_t size;
  char*    data;
  char*    text;
  IoFall   fall;
  IoCall   call;
  IoPack   pack;
} IoWork;

typedef Term (*Effect)(Env e, Term* f, IoWork* w);

// IoEff ::=
//   | IoEff(fid, cid, run, ask)
typedef struct {
  uint32_t fid;
  uint32_t cid;
  Effect   run;
  uint32_t ask;
} IoEff;

OUTLINE void* io_mem(void* mem) {
  if (mem == NULL) {
    err_fail(ERR_HEAP, "host allocation failed");
  }
  return mem;
}

static IoEff    io_eff_rows[IO_EFFS];
static uint32_t io_eff_len;

static Term*    io_run_at;
static uint32_t io_run_cap;
static uint32_t io_run_beg;
static uint32_t io_run_len;
static uint32_t io_live;

static void io_eff(u32 fid, u32 cid, Effect run, u32 need) {
  if (io_eff_len >= IO_EFFS) {
    err_fail(ERR_FIDS, "the effect registry is full");
  }
  IoEff* row = &io_eff_rows[io_eff_len];
  row->fid  = fid;
  row->cid  = cid;
  row->run  = run;
  row->ask  = need;
  io_eff_len += 1;
}

static IoEff* io_eff_at(bool clo, u32 key) {
  for (u32 i = 0; i < io_eff_len; i += 1) {
    IoEff* row = &io_eff_rows[i];
    if ((clo ? row->fid : row->cid) == key) {
      return row;
    }
  }
  return NULL;
}

static Term io_work(IoWork* w, IoCall call, IoPack pack) {
  w->call = call;
  w->pack = pack;
  return IO_WORK;
}

static uint64_t io_sys_end(IoWork* w, ssize_t n) {
  w->fall = n < 0 ? io_sys_fall((uint32_t)errno) : io_sys_done();
  return n < 0 ? 0 : (uint64_t)n;
}

static void io_sys_keep(IoWork* w, int kind, int fd) {
  io_sys_end(w, fd);
  if (fd >= 0 && io_sys_mint(kind, fd, &w->made) < 0) {
    close(fd);
    w->fall = io_sys_fall(EMFILE);
  }
}

static void io_push(Term op, Term x, bool fresh) {
  if (io_run_len == io_run_cap) {
    uint32_t cap = io_run_cap == 0 ? 64 : io_run_cap * 2;
    Term*    at  = io_mem(malloc((uint64_t)cap * 2 * sizeof(Term)));
    for (uint32_t i = 0; i < 2 * io_run_len; i += 1) {
      at[i] = io_run_at[(2 * io_run_beg + i) & (2 * io_run_cap - 1)];
    }
    free(io_run_at);
    io_run_at  = at;
    io_run_cap = cap;
    io_run_beg = 0;
  }
  Term* s = &io_run_at[2 * ((io_run_beg + io_run_len) & (io_run_cap - 1))];
  s[0] = op;
  s[1] = x;
  io_run_len += 1;
  io_live    += fresh ? 1 : 0;
}

static Term* io_pop(void) {
  Term* s = &io_run_at[2 * io_run_beg];
  io_run_beg = (io_run_beg + 1) & (io_run_cap - 1);
  io_run_len -= 1;
  return s;
}

// Codecs
// ------

OUTLINE __attribute__((cold)) void io_out(FILE* h, const char* data,
  uint64_t len) {
  if (fwrite(data, 1, len, h) != len) {
    err_fail(ERR_FAIL, "a short write on a standard stream");
  }
}

OUTLINE __attribute__((cold)) void io_sync(void) {
  if (fflush(stdout) != 0) {
    err_fail(ERR_FAIL, "a short write on a standard stream");
  }
}

OUTLINE char* io_cstr(Env e, Term s, uint64_t* len) {
  uint64_t cap = 64;
  uint64_t n   = 0;
  char*    buf = io_mem(malloc(cap));
  while (term_aux(s) == CID_SCON) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (n + 2 > cap) {
      cap *= 2;
      buf = io_mem(realloc(buf, cap));
    }
    buf[n] = (char)fb[0];
    n += 1;
    s = fb[1];
  }
  buf[n] = 0;
  *len = n;
  return buf;
}

OUTLINE __attribute__((cold)) void io_errs(Env e, Term s) {
  uint64_t n    = 0;
  char*    text = io_cstr(e, s, &n);
  io_sync();
  io_out(stderr, text, n);
  io_out(stderr, "\n", 1);
  free(text);
}

static int io_nul(const char* s, uint64_t n) {
  return strlen(s) != n;
}

#define io_seal(e, t, hot) ((hot) != 0 ? rfc_seal(e, t) : (t))

static Term io_str(Env e, const char* p, uint64_t n) {
  Term s = term_pak(CID_SNIL, 0);
  while (n > 0) {
    n -= 1;
    Loc loc = heap_alloc(e, 1);
    e.mem[loc]     = (uint8_t)p[n];
    e.mem[loc + 1] = io_seal(e, s, IO_HOTS & 1);
    s = term_ctr(CID_SCON, loc);
  }
  return s;
}

static Term io_tup(Env e, Term a, Term b) {
  Loc l = heap_alloc(e, 1);
  e.mem[l]     = io_seal(e, a, IO_HOTS & 2);
  e.mem[l + 1] = io_seal(e, b, IO_HOTS & 2);
  return term_ctr(CID_TUPLE, l);
}

static Term io_box(Env e, uint64_t cid, Term v, int hot) {
  Loc l = heap_alloc(e, 0);
  e.mem[l] = io_seal(e, v, hot);
  return term_ctr(cid, l);
}

#define io_done(e, v) io_box(e, CID_DONE, v, IO_HOTS & 4)

static Term io_fail(Env e, IoFall q) {
  const char* s = q.text != NULL ? q.text : strerror((int)q.code);
  Term t = io_tup(e, (uint64_t)q.code, io_str(e, s, strlen(s)));
  return io_box(e, CID_FAIL, t, IO_HOTS & 8);
}

static Term io_hand(Env e, uint64_t cid, IoHand h) {
  Loc l = heap_alloc(e, 1);
  e.mem[l]     = (uint64_t)h.slot;
  e.mem[l + 1] = (uint64_t)h.mint;
  return term_ctr(cid, l);
}

static IoHand io_hand_p(Env e, Term t) {
  Loc at = term_rfc(t) ? (Loc)(e.mem[term_loc(t)] >> 24) : term_loc(t);
  IoHand h = { (uint32_t)e.mem[at], (uint32_t)e.mem[at + 1] };
  return h;
}

static IoHand io_hand_c(Env e, Term t) {
  IoHand h = io_hand_p(e, t);
  term_drop(e, t);
  return h;
}

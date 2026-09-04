// IO
// ==

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

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
  int      file;
  int      kind;
} IoRow;

static IoRow    io_sys_rows[IO_ROWS];
static uint32_t io_sys_next = 0;
static uint32_t io_sys_free[IO_ROWS];
static uint32_t io_sys_idle = 0;

static void __attribute__((constructor)) io_sys_boot(void) {
  signal(SIGPIPE, SIG_IGN);
}

static IoFall io_sys_done(void) {
  IoFall out;
  out.code = 0;
  out.text = NULL;
  return out;
}

static IoFall io_sys_fall(uint32_t code) {
  IoFall out;
  out.code = code;
  out.text = strerror((int)code);
  return out;
}

static int io_sys_mint(int kind, int fd, IoHand* out) {
  uint32_t slot;
  if (io_sys_idle > 0) {
    io_sys_idle -= 1;
    slot = io_sys_free[io_sys_idle];
  } else {
    if (io_sys_next >= IO_ROWS) {
      return -1;
    }
    slot = io_sys_next;
    io_sys_next += 1;
  }
  IoRow* row = &io_sys_rows[slot];
  row->mint += 1;
  row->file = fd;
  row->kind = kind;
  out->slot = slot;
  out->mint = row->mint;
  return 0;
}

static int io_sys_read(IoHand hand, int kind) {
  if (hand.slot >= io_sys_next) {
    return -1;
  }
  IoRow* row = &io_sys_rows[hand.slot];
  if (row->mint != hand.mint || row->file < 0 || row->kind != kind) {
    return -1;
  }
  return row->file;
}

static int io_sys_kill(IoHand hand) {
  if (hand.slot >= io_sys_next) {
    return -1;
  }
  IoRow* row = &io_sys_rows[hand.slot];
  if (row->mint != hand.mint || row->file < 0) {
    return -1;
  }
  int fd = row->file;
  row->file = -1;
  row->kind = IO_NONE;
  io_sys_free[io_sys_idle] = hand.slot;
  io_sys_idle += 1;
  return fd;
}

static int io_sys_quad(const char* host, uint8_t* quad) {
  const char* s = host;
  for (int i = 0; i < 4; i += 1) {
    if (i > 0) {
      if (*s != '.') {
        return -1;
      }
      s += 1;
    }
    const char* digits = s;
    uint32_t value = 0;
    while (*s >= '0' && *s <= '9') {
      value = value * 10 + (uint32_t)(*s - '0');
      s += 1;
    }
    long count = s - digits;
    if (count < 1 || count > 3 || value > 255) {
      return -1;
    }
    if (count > 1 && digits[0] == '0') {
      return -1;
    }
    quad[i] = (uint8_t)value;
  }
  if (*s != 0) {
    return -1;
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
  int fd = socket(AF_INET, type, 0);
#ifdef SO_NOSIGPIPE
  if (fd >= 0) {
    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof(one));
  }
#endif
  return fd;
}

static int io_sys_flag(void) {
#ifdef MSG_NOSIGNAL
  return MSG_NOSIGNAL;
#else
  return 0;
#endif
}

// Effects
// -------

typedef Term (*Effect)(Env e, Term* f);

static u32    io_eff_fids[IO_EFFS];
static u32    io_eff_cids[IO_EFFS];
static Effect io_eff_runs[IO_EFFS];
static u32    io_eff_len;

static void io_eff(u32 fid, u32 cid, Effect run) {
  if (io_eff_len >= IO_EFFS) {
    err_fail(ERR_FIDS, "the effect registry is full");
  }
  io_eff_fids[io_eff_len] = fid;
  io_eff_cids[io_eff_len] = cid;
  io_eff_runs[io_eff_len] = run;
  io_eff_len += 1;
}

static Effect io_eff_at(u32* keys, u32 key) {
  for (u32 i = 0; i < io_eff_len; i += 1) {
    if (keys[i] == key) {
      return io_eff_runs[i];
    }
  }
  return NULL;
}

// Codecs
// ------

OUTLINE void* io_mem(void* mem) {
  if (mem == NULL) {
    err_fail(ERR_HEAP, "host allocation failed");
  }
  return mem;
}

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

static Term io_str(Env e, const char* p, uint64_t n) {
  Term s = term_pak(CID_SNIL, 0);
  while (n > 0) {
    n -= 1;
    Loc loc = heap_alloc(e, 1);
    e.mem[loc]     = (uint8_t)p[n];
    e.mem[loc + 1] = s;
    s = term_ctr(CID_SCON, loc);
  }
  return s;
}

static Term io_tup(Env e, Term a, Term b) {
  Loc l = heap_alloc(e, 1);
  e.mem[l]     = a;
  e.mem[l + 1] = b;
  return term_ctr(CID_TUPLE, l);
}

static Term io_done(Env e, Term v) {
  Loc l = heap_alloc(e, 0);
  e.mem[l] = v;
  return term_ctr(CID_DONE, l);
}

static Term io_fail(Env e, IoFall q) {
  const char* s = q.text != NULL ? q.text : strerror((int)q.code);
  Term t = io_tup(e, (uint64_t)q.code, io_str(e, s, strlen(s)));
  Loc l = heap_alloc(e, 0);
  e.mem[l] = t;
  return term_ctr(CID_FAIL, l);
}

static Term io_hand(Env e, uint64_t cid, IoHand h) {
  Loc l = heap_alloc(e, 1);
  e.mem[l]     = (uint64_t)h.slot;
  e.mem[l + 1] = (uint64_t)h.mint;
  return term_ctr(cid, l);
}

static IoHand io_hand_c(Env e, Term t) {
  Term fb[2];
  spare_free(e, cls_fit(2), ctr_take(e, t, 2, fb));
  IoHand h = { (uint32_t)fb[0], (uint32_t)fb[1] };
  return h;
}

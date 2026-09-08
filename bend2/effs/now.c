// IO
// ==
//! use ./sys.c

#include <time.h>

static uint64_t io_clock(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000ull + (uint64_t)ts.tv_nsec / 1000000ull;
}

Term io_now_run(Env e, Term* f, IoWork* w) {
  return (Term)io_clock();
}

static void __attribute__((constructor)) io_now_use(void) {
  io_eff(FID_IO_NOW, CID_IO_NOW, io_now_run, 0);
}

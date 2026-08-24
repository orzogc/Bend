// IO
// ==

#include <stdio.h>

static int64_t short_left = -1;

static int short_take(void) {
  if (short_left < 0) {
    return 0;
  }
  if (short_left == 0) {
    short_left = -1;
    return 1;
  }
  short_left -= 1;
  return 0;
}

size_t fwrite(const void* data, size_t wide, size_t n, FILE* h) {
  if (short_take()) {
    return 0;
  }
  const char* p = (const char*)data;
  for (size_t i = 0; i < wide * n; i += 1) {
    fputc(p[i], h);
  }
  return n;
}

Term short_arm_run(Env e, Term* f) {
  short_left = (int64_t)(uint32_t)f[0];
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) short_arm_use(void) {
  io_eff(FID_SHORT_ARM, CID_SHORT_ARM, short_arm_run);
}

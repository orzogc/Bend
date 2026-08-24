// IO
// ==

#include <malloc/malloc.h>

static int64_t oom_left = -1;

static int oom_take(void) {
  if (oom_left < 0) {
    return 0;
  }
  if (oom_left == 0) {
    oom_left = -1;
    return 1;
  }
  oom_left -= 1;
  return 0;
}

void* malloc(size_t n) {
  if (oom_take()) {
    return NULL;
  }
  return malloc_zone_malloc(malloc_default_zone(), n);
}

void* realloc(void* p, size_t n) {
  if (oom_take()) {
    return NULL;
  }
  return malloc_zone_realloc(malloc_default_zone(), p, n);
}

Term oom_arm_run(Env e, Term* f) {
  oom_left = (int64_t)(uint32_t)f[0];
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) oom_arm_use(void) {
  io_eff(FID_OOM_ARM, CID_OOM_ARM, oom_arm_run);
}

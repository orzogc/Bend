// IO
// ==

#include <unistd.h>

Term exit_now_run(Env e, Term* f) {
  _exit((int)(uint32_t)f[0]);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) exit_now_use(void) {
  io_eff(FID_EXIT_NOW, CID_EXIT_NOW, exit_now_run);
}

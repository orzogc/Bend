// Window
// ======

#if BEND_METAL

#import <AppKit/AppKit.h>

static void window_close(intptr_t at) {
  NSWindow* win = CFBridgingRelease((void*)at);
  [win close];
}

#else

static void window_close(intptr_t at) {
}

#endif

Term window_close_run(Env e, Term* f, IoWork* w) {
  window_close((intptr_t)io_hand_v(f[0]));
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) window_close_use(void) {
  io_eff(CID_WINDOW_CLOSE, window_close_run, 0);
}

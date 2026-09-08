// Window
// ======

#define IO_WIND 5

#if BEND_METAL

#import <AppKit/AppKit.h>

static void window_close(IoHand hand) {
  if (io_sys_read(hand, IO_WIND) < 0) {
    return;
  }
  NSWindow* win = CFBridgingRelease((void*)io_sys_kill(hand));
  [win close];
}

#else

static void window_close(IoHand hand) {
}

#endif

Term window_close_run(Env e, Term* f, IoWork* w) {
  window_close(io_hand_c(e, f[0]));
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) window_close_use(void) {
  io_eff(FID_WINDOW_CLOSE, CID_WINDOW_CLOSE, window_close_run, 0);
}

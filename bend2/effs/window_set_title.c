// Window
// ======

#define IO_WIND 5

#if BEND_METAL

#import <AppKit/AppKit.h>

static void window_set_title(IoHand hand, const char* text, u64 n) {
  intptr_t at = io_sys_read(hand, IO_WIND);
  if (at < 0) {
    return;
  }
  NSWindow* win = (__bridge NSWindow*)(void*)at;
  win.title = [[NSString alloc] initWithBytes:text length:n
    encoding:NSUTF8StringEncoding];
}

#else

static void window_set_title(IoHand hand, const char* text, u64 n) {
}

#endif

Term window_set_title_run(Env e, Term* f, IoWork* w) {
  IoHand hand = io_hand_c(e, f[0]);
  u64    n    = 0;
  char*  text = io_cstr(e, f[1], &n);
  window_set_title(hand, text, n);
  free(text);
  return io_hand(e, CID_WINDOW, hand);
}

static void __attribute__((constructor)) window_set_title_use(void) {
  io_eff(FID_WINDOW_SET_TITLE, CID_WINDOW_SET_TITLE, window_set_title_run, 0);
}

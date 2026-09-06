// Window
// ======
//! use ./window.c

IoFall window_open(const char* title, uint32_t w, uint32_t h, IoHand* out) {
  if (w < 1 || h < 1 || w > 4096 || h > 4096) {
    return io_sys_fall(EINVAL);
  }
  int i = 0;
  while (i < WIN_ROWS && window_rows[i].used) {
    i += 1;
  }
  if (i == WIN_ROWS) {
    return io_sys_fall(EMFILE);
  }
  WinRow* row = &window_rows[i];
  WinId app = ((WinMsg)objc_msgSend)((WinId)objc_getClass("NSApplication"),
    sel_registerName("sharedApplication"));
  ((WinMsgLong)objc_msgSend)(app, sel_registerName("setActivationPolicy:"), 0);
  if (window_delegate == NULL) {
    Class root = objc_getClass("NSObject");
    Class cls  = objc_allocateClassPair(root, "BendWindow", 0);
    class_addMethod(cls, sel_registerName("windowShouldClose:"),
      (IMP)window_should_close, "c@:@");
    objc_registerClassPair(cls);
    window_delegate = ((WinMsg)objc_msgSend)((WinId)cls,
      sel_registerName("new"));
  }
  WinId win = ((WinMsg)objc_msgSend)((WinId)objc_getClass("NSWindow"),
    sel_registerName("alloc"));
  win = ((WinMsgInit)objc_msgSend)(win,
    sel_registerName("initWithContentRect:styleMask:backing:defer:"),
    CGRectMake(0, 0, w, h), 1 | 2, 2, NO);
  ((WinMsgBool)objc_msgSend)(win, sel_registerName("setReleasedWhenClosed:"),
    NO);
  ((WinMsgBool)objc_msgSend)(win,
    sel_registerName("setAcceptsMouseMovedEvents:"), YES);
  ((WinMsgId)objc_msgSend)(win, sel_registerName("setTitle:"),
    window_str(title));
  ((WinMsgId)objc_msgSend)(win, sel_registerName("setDelegate:"),
    window_delegate);
  WinId view = ((WinMsg)objc_msgSend)(win, sel_registerName("contentView"));
  ((WinMsgBool)objc_msgSend)(view, sel_registerName("setWantsLayer:"), YES);
  row->layer = ((WinMsg)objc_msgSend)(view, sel_registerName("layer"));
  ((WinMsgVoid)objc_msgSend)(win, sel_registerName("center"));
  ((WinMsgId)objc_msgSend)(win, sel_registerName("makeKeyAndOrderFront:"),
    NULL);
  ((WinMsgBool)objc_msgSend)(app,
    sel_registerName("activateIgnoringOtherApps:"), YES);
  row->win   = win;
  row->w     = (int)w;
  row->h     = (int)h;
  row->fb[0] = io_mem(calloc((size_t)w * h, 4));
  row->fb[1] = io_mem(calloc((size_t)w * h, 4));
  row->back  = 0;
  row->used  = 1;
  row->due   = window_now();
  row->evq_h = 0;
  row->evq_t = 0;
  if (io_sys_mint(IO_WIND, i, out) < 0) {
    return io_sys_fall(EMFILE);
  }
  window_pump();
  return io_sys_done();
}

Term window_open_run(Env e, Term* f) {
  uint64_t n = 0;
  char* title = io_cstr(e, f[0], &n);
  IoHand out;
  IoFall q = io_nul(title, n) ? io_sys_fall(EILSEQ)
    : window_open(title, (uint32_t)f[1], (uint32_t)f[2], &out);
  free(title);
  if (q.code != 0) {
    return io_fail(e, q);
  }
  return io_done(e, io_hand(e, CID_WINDOW, out));
}

static void __attribute__((constructor)) window_open_use(void) {
  io_eff(FID_WINDOW_OPEN, CID_WINDOW_OPEN, window_open_run);
}

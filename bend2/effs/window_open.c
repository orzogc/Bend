// Window
// ======
//! use ./window.c

IoFall window_open(const char* title, uint32_t w, uint32_t h, IoHand* out) {
  int row = 0;
  IoFall q = window_make(title, w, h, &row);
  if (q.code != 0) {
    return q;
  }
  if (io_sys_mint(IO_WIND, row, out) < 0) {
    window_drop(row);
    return io_sys_fall(EMFILE);
  }
  return io_sys_done();
}

Term window_open_run(Env e, Term* f, IoWork* w) {
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
  io_eff(FID_WINDOW_OPEN, CID_WINDOW_OPEN, window_open_run, 0);
}

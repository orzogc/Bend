// Window
// ======
//! use ./window.c

void window_close(IoHand hand) {
  int i = io_sys_read(hand, IO_WIND);
  if (i < 0) {
    return;
  }
  io_sys_kill(hand);
  window_drop(&window_rows[i]);
}

Term window_close_run(Env e, Term* f) {
  window_close(io_hand_c(e, f[0]));
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) window_close_use(void) {
  io_eff(FID_WINDOW_CLOSE, CID_WINDOW_CLOSE, window_close_run);
}

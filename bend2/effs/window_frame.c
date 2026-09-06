// Window
// ======
//! use ./window.c

Term window_frame(Env e, IoHand hand, Term image) {
  int row = io_sys_read(hand, IO_WIND);
  if (row < 0) {
    return term_pak(CID_NIL, 0);
  }
  io_sync();
  window_show(e, row, image);
  return window_events(e, row);
}

Term window_frame_run(Env e, Term* f) {
  IoHand hand = io_hand_c(e, f[0]);
  Term events = window_frame(e, hand, f[1]);
  return io_tup(e, io_hand(e, CID_WINDOW, hand), io_tup(e, f[1], events));
}

static void __attribute__((constructor)) window_frame_use(void) {
  io_eff(FID_WINDOW_FRAME, CID_WINDOW_FRAME, window_frame_run);
}

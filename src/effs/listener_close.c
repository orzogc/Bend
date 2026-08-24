// Listener
// ========
//! use ./sys.c

void listener_close(IoHand listener) {
  if (io_sys_read(listener, IO_LSNR) >= 0) {
    close(io_sys_kill(listener));
  }
}

Term listener_close_run(Env e, Term* f) {
  listener_close(io_hand_c(e, f[0]));
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) listener_close_use(void) {
  io_eff(FID_LISTENER_CLOSE, CID_LISTENER_CLOSE, listener_close_run);
}

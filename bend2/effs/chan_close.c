// Chan
// ====
//! use ./chan.c

Term chan_close_run(Env e, Term* f, IoWork* w) {
  IoHand   h   = io_hand_c(e, f[0]);
  ChanRow* row = chan_at(h);
  if (row != NULL && !row->shut) {
    chan_shut(e, h, row);
  }
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) chan_close_use(void) {
  io_eff(FID_CHAN_CLOSE, CID_CHAN_CLOSE, chan_close_run, 0);
}

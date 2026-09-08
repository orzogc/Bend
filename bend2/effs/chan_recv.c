// Chan
// ====
//! use ./chan.c

Term chan_recv_run(Env e, Term* f, IoWork* w) {
  IoHand   h   = io_hand_c(e, f[0]);
  ChanRow* row = chan_at(h);
  if (row == NULL) {
    return term_pak(CID_NONE, 0);
  }
  if (row->size > 0) {
    Term v = chan_take(row);
    if (row->shut && row->size == 0) {
      chan_free(h, row);
    }
    return chan_some(e, v);
  }
  if (row->wait != NULL && row->wait->item != TERM_HOLE) {
    return chan_some(e, chan_wake(row, chan_bool(true)));
  }
  if (row->shut) {
    chan_free(h, row);
    return term_pak(CID_NONE, 0);
  }
  chan_park(row, f[1], TERM_HOLE);
  return IO_PARK;
}

static void __attribute__((constructor)) chan_recv_use(void) {
  io_eff(FID_CHAN_RECV, CID_CHAN_RECV, chan_recv_run, 0);
}

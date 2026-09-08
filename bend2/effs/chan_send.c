// Chan
// ====

Term chan_send_run(Env e, Term* f, IoWork* w) {
  ChanRow* row = chan_at(io_hand_c(e, f[0]));
  if (row == NULL || row->shut) {
    term_drop(e, f[1]);
    return chan_bool(false);
  }
  if (row->wait != NULL && row->wait->item == TERM_HOLE) {
    chan_wake(row, chan_some(e, f[1]));
    return chan_bool(true);
  }
  if (row->size < row->room) {
    row->ring[(row->head + row->size) % row->room] = f[1];
    row->size += 1;
    return chan_bool(true);
  }
  chan_park(row, f[2], f[1]);
  return IO_PARK;
}

static void __attribute__((constructor)) chan_send_use(void) {
  io_eff(FID_CHAN_SEND, CID_CHAN_SEND, chan_send_run, 0);
}

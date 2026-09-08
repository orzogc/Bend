// Chan
// ====

Term chan_new_run(Env e, Term* f, IoWork* w) {
  ChanRow* row = io_mem(calloc(1, sizeof(ChanRow)));
  IoHand   h;
  row->room = (uint32_t)f[0];
  row->ring = row->room == 0 ? NULL : io_mem(malloc(row->room * sizeof(Term)));
  if (io_sys_mint(IO_CHAN, (intptr_t)row, &h) < 0) {
    err_fail(ERR_FAIL, "the handle table is full");
  }
  return io_hand(e, CID_CHAN, h);
}

static void __attribute__((constructor)) chan_new_use(void) {
  io_eff(FID_CHAN_NEW, CID_CHAN_NEW, chan_new_run, 0);
}

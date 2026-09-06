// Window
// ======
//! use ./window.c

static Term window_frame_events(Env e, WinRow* row) {
  Term list = term_pak(CID_NIL, 0);
  while (row->evq_t != row->evq_h) {
    row->evq_t -= 1;
    Loc loc = heap_alloc(e, 1);
    e.mem[loc]     = (uint64_t)row->evq[row->evq_t & (WIN_EVQ - 1)];
    e.mem[loc + 1] = io_seal(e, list, IO_HOTS & 16);
    list = term_ctr(CID_CON, loc);
  }
  row->evq_h = 0;
  row->evq_t = 0;
  return list;
}

Term window_frame(Env e, IoHand hand, Term image) {
  int i = io_sys_read(hand, IO_WIND);
  if (i < 0) {
    term_drop(e, image);
    return term_pak(CID_NIL, 0);
  }
  WinRow* row = &window_rows[i];
  int sz = 1;
  while (sz < row->w || sz < row->h) {
    sz <<= 1;
  }
  io_sync();
  window_walk(e, row, image, 0, 0, sz);
  window_present(row);
  window_pace(row);
  window_pump();
  return window_frame_events(e, row);
}

Term window_frame_run(Env e, Term* f) {
  IoHand hand = io_hand_c(e, f[0]);
  Term events = window_frame(e, hand, f[1]);
  return io_tup(e, io_hand(e, CID_WINDOW, hand), events);
}

static void __attribute__((constructor)) window_frame_use(void) {
  io_eff(FID_WINDOW_FRAME, CID_WINDOW_FRAME, window_frame_run);
}

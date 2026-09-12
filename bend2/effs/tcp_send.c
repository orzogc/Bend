// TCP
// ===

static void tcp_send_call(IoWork* w) {
  int fd = (int)w->hand;
  ssize_t n = 0;
  for (uint64_t at = 0; n >= 0 && at < w->size; at += (uint64_t)n) {
    n = send(fd, w->data + at, w->size - at, 0);
  }
  io_sys_end(w, n);
}

static Term tcp_send_pack(Env e, IoWork* w) {
  Term r = w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, term_pak(CID_UNIT, 0));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

Term tcp_send_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->data = io_cstr(e, f[1], &w->size);
  return io_work(w, tcp_send_call, tcp_send_pack);
}

static void __attribute__((constructor)) tcp_send_use(void) {
  io_eff(CID_TCP_SEND, tcp_send_run, 0);
}

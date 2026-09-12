// TCP
// ===

static void tcp_accept_call(IoWork* w) {
  int fd = (int)w->hand;
  w->made = (intptr_t)io_sys_end(w, accept(fd, NULL, NULL));
}

static Term tcp_accept_pack(Env e, IoWork* w) {
  Term r = w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, io_hand(w->made));
  return io_tup(e, io_hand(w->hand), r);
}

Term tcp_accept_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  return io_work(w, tcp_accept_call, tcp_accept_pack);
}

static void __attribute__((constructor)) tcp_accept_use(void) {
  io_eff(CID_TCP_ACCEPT, tcp_accept_run, IO_READ);
}

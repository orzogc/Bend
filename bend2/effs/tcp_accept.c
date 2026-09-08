// TCP
// ===
//! use ./sys.c

static void tcp_accept_call(IoWork* w) {
  int fd = (int)io_sys_read(w->hand, IO_LSNR);
  io_sys_keep(w, IO_TCPS, accept(fd, NULL, NULL));
}

static Term tcp_accept_pack(Env e, IoWork* w) {
  Term r = w->fall.code != 0 ? io_fail(e, w->fall)
    : io_done(e, io_hand(e, CID_SOCKET, w->made));
  return io_tup(e, io_hand(e, CID_LISTENER, w->hand), r);
}

Term tcp_accept_run(Env e, Term* f, IoWork* w) {
  w->hand = io_hand_c(e, f[0]);
  return io_work(w, tcp_accept_call, tcp_accept_pack);
}

static void __attribute__((constructor)) tcp_accept_use(void) {
  io_eff(FID_TCP_ACCEPT, CID_TCP_ACCEPT, tcp_accept_run, IO_READ);
}

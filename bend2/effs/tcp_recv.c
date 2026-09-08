// TCP
// ===
//! use ./sys.c

static void tcp_recv_call(IoWork* w) {
  int fd = (int)io_sys_read(w->hand, IO_TCPS);
  w->size = io_sys_end(w, recv(fd, w->data, w->word, 0));
}

static Term tcp_recv_pack(Env e, IoWork* w) {
  Term r = w->fall.code != 0 ? io_fail(e, w->fall)
    : io_done(e, io_str(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(e, CID_SOCKET, w->hand), r);
}

Term tcp_recv_run(Env e, Term* f, IoWork* w) {
  w->hand = io_hand_c(e, f[0]);
  w->word = (uint32_t)f[1];
  w->data = io_mem(malloc((uint64_t)w->word + 1));
  tcp_recv_call(w);
  return tcp_recv_pack(e, w);
}

static void __attribute__((constructor)) tcp_recv_use(void) {
  io_eff(FID_TCP_RECV, CID_TCP_RECV, tcp_recv_run, IO_READ);
}

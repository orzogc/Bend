// TCP
// ===
//! use ./sys.c

static void tcp_send_call(IoWork* w) {
  int fd = (int)io_sys_read(w->hand, IO_TCPS);
  ssize_t n = 0;
  for (uint64_t at = 0; n >= 0 && at < w->size; at += (uint64_t)n) {
    n = send(fd, w->data + at, w->size - at, MSG_NOSIGNAL);
  }
  io_sys_end(w, n);
}

static Term tcp_send_pack(Env e, IoWork* w) {
  Term r = w->fall.code != 0 ? io_fail(e, w->fall)
    : io_done(e, term_pak(CID_UNIT, 0));
  free(w->data);
  return io_tup(e, io_hand(e, CID_SOCKET, w->hand), r);
}

Term tcp_send_run(Env e, Term* f, IoWork* w) {
  w->hand = io_hand_c(e, f[0]);
  w->data = io_cstr(e, f[1], &w->size);
  return io_work(w, tcp_send_call, tcp_send_pack);
}

static void __attribute__((constructor)) tcp_send_use(void) {
  io_eff(FID_TCP_SEND, CID_TCP_SEND, tcp_send_run, IO_WRITE);
}

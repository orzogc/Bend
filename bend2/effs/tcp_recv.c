// TCP
// ===
//! use ./sys.c

Term tcp_recv_run(Env e, Term* f, IoWork* w) {
  int   fd  = io_sys_read(io_hand_p(e, f[0]), IO_TCPS);
  w->word   = f[1] < INT32_MAX ? f[1] : INT32_MAX;
  char* buf = io_mem(malloc(w->word + 1));
  u64   n   = io_sys_end(w, recv(fd, buf, w->word, MSG_DONTWAIT));
  Term  r   = w->fall.code == EAGAIN ? IO_WAIT : w->fall.code
    ? io_fail(e, w->fall) : io_done(e, io_str(e, buf, n));
  free(buf);
  return r == IO_WAIT ? r : io_tup(e, f[0], r);
}

static void __attribute__((constructor)) tcp_recv_use(void) {
  io_eff(FID_TCP_RECV, CID_TCP_RECV, tcp_recv_run, IO_READ);
}

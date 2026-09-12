// TCP
// ===

static void tcp_recv_call(IoWork* w) {
  int fd  = (int)w->hand;
  w->size = io_sys_end(w, recv(fd, w->data, w->word, 0));
}

static Term tcp_recv_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, io_str(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

Term tcp_recv_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->word = f[1] < INT32_MAX ? f[1] : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  int fd  = (int)w->hand;
  w->size = io_sys_end(w, recv(fd, w->data, w->word, MSG_DONTWAIT));
  return w->code == EAGAIN ? io_work(w, tcp_recv_call, tcp_recv_pack)
    : tcp_recv_pack(e, w);
}

static void __attribute__((constructor)) tcp_recv_use(void) {
  io_eff(CID_TCP_RECV, tcp_recv_run, IO_READ);
}

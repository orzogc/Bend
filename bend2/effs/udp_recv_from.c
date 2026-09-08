// UDP
// ===

static void udp_recv_from_call(IoWork* w) {
  struct sockaddr_in at = { 0 };
  socklen_t alen = sizeof(at);
  int fd = io_sys_read(w->hand, IO_UDPS);
  ssize_t n = recvfrom(fd, w->data, w->word, 0, (struct sockaddr*)&at, &alen);
  w->size = io_sys_end(w, n);
  inet_ntop(AF_INET, &at.sin_addr, w->text, 16);
  w->word = ntohs(at.sin_port);
}

static Term udp_recv_from_pack(Env e, IoWork* w) {
  Term r = w->fall.code ? io_fail(e, w->fall)
    : io_done(e, io_tup(e, io_str(e, w->text, strlen(w->text)),
      io_tup(e, w->word, io_str(e, w->data, w->size))));
  free(w->text);
  free(w->data);
  return io_tup(e, io_hand(e, CID_SOCKET, w->hand), r);
}

Term udp_recv_from_run(Env e, Term* f, IoWork* w) {
  w->hand = io_hand_c(e, f[0]);
  w->word = f[1] < INT32_MAX ? f[1] : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  w->text = io_mem(calloc(16, 1));
  return io_work(w, udp_recv_from_call, udp_recv_from_pack);
}

static void __attribute__((constructor)) udp_recv_from_use(void) {
  io_eff(FID_UDP_RECV_FROM, CID_UDP_RECV_FROM, udp_recv_from_run, IO_READ);
}

// UDP
// ===

static void udp_send_to_call(IoWork* w) {
  struct sockaddr_in at;
  int fd = (int)w->hand;
  ssize_t n = -1;
  errno = EINVAL;
  if (io_sys_addr(w->text, w->word, &at) == 0) {
    n = sendto(fd, w->data, w->size, 0, (struct sockaddr*)&at, sizeof(at));
  }
  io_sys_end(w, n);
}

static Term udp_send_to_pack(Env e, IoWork* w) {
  Term r = w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, term_pak(CID_UNIT, 0));
  free(w->text);
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

Term udp_send_to_run(Env e, Term* f, IoWork* w) {
  uint64_t hn = 0;
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->text = io_cstr(e, f[1], &hn);
  w->word = (uint32_t)f[2];
  w->data = io_cstr(e, f[3], &w->size);
  if (io_nul(w->text, hn)) {
    w->code = EINVAL;
    return udp_send_to_pack(e, w);
  }
  return io_work(w, udp_send_to_call, udp_send_to_pack);
}

static void __attribute__((constructor)) udp_send_to_use(void) {
  io_eff(CID_UDP_SEND_TO, udp_send_to_run, 0);
}

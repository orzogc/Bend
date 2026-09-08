// UDP
// ===
//! use ./sys.c

static void udp_send_to_call(IoWork* w) {
  struct sockaddr_in at;
  int fd = (int)io_sys_read(w->hand, IO_UDPS);
  ssize_t n = -1;
  errno = fd < 0 ? EBADF : EINVAL;
  if (fd >= 0 && io_sys_addr(w->text, w->word, &at) == 0) {
    n = sendto(fd, w->data, w->size, 0, (struct sockaddr*)&at, sizeof(at));
  }
  io_sys_end(w, n);
}

static Term udp_send_to_pack(Env e, IoWork* w) {
  Term r = w->fall.code != 0 ? io_fail(e, w->fall)
    : io_done(e, term_pak(CID_UNIT, 0));
  free(w->text);
  free(w->data);
  return io_tup(e, io_hand(e, CID_SOCKET, w->hand), r);
}

Term udp_send_to_run(Env e, Term* f, IoWork* w) {
  uint64_t hn = 0;
  w->hand = io_hand_c(e, f[0]);
  w->text = io_cstr(e, f[1], &hn);
  w->word = (uint32_t)f[2];
  w->data = io_cstr(e, f[3], &w->size);
  if (io_sys_read(w->hand, IO_UDPS) >= 0 && io_nul(w->text, hn)) {
    w->fall = io_sys_fall(EINVAL);
    return udp_send_to_pack(e, w);
  }
  return io_work(w, udp_send_to_call, udp_send_to_pack);
}

static void __attribute__((constructor)) udp_send_to_use(void) {
  io_eff(FID_UDP_SEND_TO, CID_UDP_SEND_TO, udp_send_to_run, 0);
}

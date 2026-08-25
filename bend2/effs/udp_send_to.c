// UDP
// ===
//! use ./sys.c

IoFall udp_send_to(IoHand socket, const char* host, uint64_t hn,
  uint32_t port, const char* data, uint32_t len) {
  int fd = io_sys_read(socket, IO_UDPS);
  if (fd < 0) {
    return io_sys_fall(EBADF);
  }
  if (io_nul(host, hn)) {
    return io_sys_fall(EINVAL);
  }
  struct sockaddr_in at;
  if (io_sys_addr(host, port, &at) < 0) {
    return io_sys_fall(EINVAL);
  }
  ssize_t n = sendto(fd, data, len, 0, (struct sockaddr*)&at, sizeof(at));
  if (n < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  return io_sys_done();
}

Term udp_send_to_run(Env e, Term* f) {
  IoHand socket = io_hand_c(e, f[0]);
  uint64_t hn = 0;
  uint64_t dn = 0;
  char* host = io_cstr(e, f[1], &hn);
  char* data = io_cstr(e, f[3], &dn);
  IoFall q = udp_send_to(socket, host, hn, (uint32_t)f[2], data,
    (uint32_t)dn);
  free(host);
  free(data);
  Term r = q.code != 0 ? io_fail(e, q) : io_done(e, term_pak(CID_UNIT, 0));
  return io_tup(e, io_hand(e, CID_SOCKET, socket), r);
}

static void __attribute__((constructor)) udp_send_to_use(void) {
  io_eff(FID_UDP_SEND_TO, CID_UDP_SEND_TO, udp_send_to_run);
}

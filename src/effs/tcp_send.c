// TCP
// ===
//! use ./sys.c

IoFall tcp_send(IoHand socket, const char* data, uint32_t len) {
  int fd = io_sys_read(socket, IO_TCPS);
  if (fd < 0) {
    return io_sys_fall(EBADF);
  }
  uint32_t at = 0;
  while (at < len) {
    ssize_t n = send(fd, data + at, len - at, io_sys_flag());
    if (n < 0) {
      return io_sys_fall((uint32_t)errno);
    }
    at += (uint32_t)n;
  }
  return io_sys_done();
}

Term tcp_send_run(Env e, Term* f) {
  IoHand socket = io_hand_c(e, f[0]);
  uint64_t n = 0;
  char* data = io_cstr(e, f[1], &n);
  IoFall q = tcp_send(socket, data, (uint32_t)n);
  free(data);
  Term r = q.code != 0 ? io_fail(e, q) : io_done(e, term_pak(CID_UNIT, 0));
  return io_tup(e, io_hand(e, CID_SOCKET, socket), r);
}

static void __attribute__((constructor)) tcp_send_use(void) {
  io_eff(FID_TCP_SEND, CID_TCP_SEND, tcp_send_run);
}

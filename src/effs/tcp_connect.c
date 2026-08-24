// TCP
// ===
//! use ./sys.c

IoFall tcp_connect(const char* host, uint32_t port, IoHand* out) {
  struct sockaddr_in at;
  if (io_sys_addr(host, port, &at) < 0) {
    return io_sys_fall(EINVAL);
  }
  int fd = io_sys_sock(SOCK_STREAM);
  if (fd < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  io_sync();
  if (connect(fd, (struct sockaddr*)&at, sizeof(at)) < 0) {
    uint32_t code = (uint32_t)errno;
    close(fd);
    return io_sys_fall(code);
  }
  if (io_sys_mint(IO_TCPS, fd, out) < 0) {
    close(fd);
    return io_sys_fall(EMFILE);
  }
  return io_sys_done();
}

Term tcp_connect_run(Env e, Term* f) {
  uint64_t n = 0;
  char* host = io_cstr(e, f[0], &n);
  IoHand out;
  IoFall q;
  if (io_nul(host, n)) {
    q = io_sys_fall(EINVAL);
  } else {
    q = tcp_connect(host, (uint32_t)f[1], &out);
  }
  free(host);
  if (q.code != 0) {
    return io_fail(e, q);
  }
  return io_done(e, io_hand(e, CID_SOCKET, out));
}

static void __attribute__((constructor)) tcp_connect_use(void) {
  io_eff(FID_TCP_CONNECT, CID_TCP_CONNECT, tcp_connect_run);
}

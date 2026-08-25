// TCP
// ===
//! use ./sys.c

IoFall tcp_recv(IoHand socket, uint32_t max, char* buf, uint32_t* len) {
  int fd = io_sys_read(socket, IO_TCPS);
  if (fd < 0) {
    return io_sys_fall(EBADF);
  }
  io_sync();
  ssize_t n = recv(fd, buf, max, 0);
  if (n < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  *len = (uint32_t)n;
  return io_sys_done();
}

Term tcp_recv_run(Env e, Term* f) {
  IoHand socket = io_hand_c(e, f[0]);
  uint32_t max = (uint32_t)f[1];
  char* buf = io_mem(malloc((uint64_t)max + 1));
  uint32_t len = 0;
  IoFall q = tcp_recv(socket, max, buf, &len);
  Term r = q.code != 0 ? io_fail(e, q) : io_done(e, io_str(e, buf, len));
  free(buf);
  return io_tup(e, io_hand(e, CID_SOCKET, socket), r);
}

static void __attribute__((constructor)) tcp_recv_use(void) {
  io_eff(FID_TCP_RECV, CID_TCP_RECV, tcp_recv_run);
}

// TCP
// ===
//! use ./sys.c

IoFall tcp_listen(uint32_t port, IoHand* out) {
  int fd = io_sys_sock(SOCK_STREAM);
  if (fd < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  int one = 1;
  setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  struct sockaddr_in at;
  if (io_sys_addr("0.0.0.0", port, &at) < 0) {
    close(fd);
    return io_sys_fall(EINVAL);
  }
  int bound = bind(fd, (struct sockaddr*)&at, sizeof(at));
  if (bound < 0 || listen(fd, 16) < 0) {
    uint32_t code = (uint32_t)errno;
    close(fd);
    return io_sys_fall(code);
  }
  if (io_sys_mint(IO_LSNR, fd, out) < 0) {
    close(fd);
    return io_sys_fall(EMFILE);
  }
  return io_sys_done();
}

Term tcp_listen_run(Env e, Term* f) {
  IoHand out;
  IoFall q = tcp_listen((uint32_t)f[0], &out);
  if (q.code != 0) {
    return io_fail(e, q);
  }
  return io_done(e, io_hand(e, CID_LISTENER, out));
}

static void __attribute__((constructor)) tcp_listen_use(void) {
  io_eff(FID_TCP_LISTEN, CID_TCP_LISTEN, tcp_listen_run);
}

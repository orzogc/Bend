// TCP
// ===
//! use ./sys.c

IoFall tcp_accept(IoHand listener, IoHand* out) {
  int lfd = io_sys_read(listener, IO_LSNR);
  if (lfd < 0) {
    return io_sys_fall(EBADF);
  }
  io_sync();
  int fd = accept(lfd, NULL, NULL);
  if (fd < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  if (io_sys_mint(IO_TCPS, fd, out) < 0) {
    close(fd);
    return io_sys_fall(EMFILE);
  }
  return io_sys_done();
}

Term tcp_accept_run(Env e, Term* f) {
  IoHand listener = io_hand_c(e, f[0]);
  IoHand out;
  IoFall q = tcp_accept(listener, &out);
  Term r = q.code != 0 ? io_fail(e, q)
    : io_done(e, io_hand(e, CID_SOCKET, out));
  return io_tup(e, io_hand(e, CID_LISTENER, listener), r);
}

static void __attribute__((constructor)) tcp_accept_use(void) {
  io_eff(FID_TCP_ACCEPT, CID_TCP_ACCEPT, tcp_accept_run);
}

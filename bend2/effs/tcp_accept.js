// TCP
// ===

function tcp_accept(listener) {
  const sys = io_sys();
  const lfd = io_read(listener, "lsn");
  if (lfd === null) {
    return io_tup(listener, io_fail(9));
  }
  const fd = sys.accept(lfd, null, null);
  if (fd < 0) {
    return io_tup(listener, io_fail(sys.errno()));
  }
  const h = io_mint("Socket", "tcp", fd);
  if (h === null) {
    sys.close(fd);
    return io_tup(listener, io_fail(24));
  }
  return io_tup(listener, io_done(h));
}

function tcp_accept_need() {
  return { read: "lsn" };
}

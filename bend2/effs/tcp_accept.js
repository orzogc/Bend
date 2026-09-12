// TCP
// ===

function tcp_accept(listener) {
  const sys = io_sys();
  const lfd = listener;
  const fd = sys.accept(lfd, null, null);
  if (fd < 0) {
    return io_tup(listener, io_fail(sys.errno()));
  }
  return io_tup(listener, io_done(fd));
}

function tcp_accept_need() {
  return { read: true };
}

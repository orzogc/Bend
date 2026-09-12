// TCP
// ===

function tcp_connect(host, port) {
  const sys = io_sys();
  const at = io_addr(host, Number(port));
  if (at === null) {
    return io_fail(22);
  }
  const fd = sys.socket(2, 1, 0);
  if (fd < 0) {
    return io_fail(sys.errno());
  }
  if (sys.connect(fd, sys.ptr(at), 16) < 0) {
    const code = sys.errno();
    sys.close(fd);
    return io_fail(code);
  }
  return io_done(fd);
}

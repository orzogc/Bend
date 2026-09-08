// UDP
// ===

function udp_bind(port) {
  const sys = io_sys();
  const fd = sys.socket(2, 2, 0);
  if (fd < 0) {
    return io_fail(sys.errno());
  }
  const at = io_addr("0.0.0.0", Number(port));
  if (at === null) {
    sys.close(fd);
    return io_fail(22);
  }
  if (sys.bind(fd, sys.ptr(at), 16) < 0) {
    const code = sys.errno();
    sys.close(fd);
    return io_fail(code);
  }
  const h = io_mint("Socket", "udp", fd);
  if (h === null) {
    sys.close(fd);
    return io_fail(24);
  }
  return io_done(h);
}

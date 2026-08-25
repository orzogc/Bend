// TCP
// ===
//! use ./sys.js

function tcp_listen(port) {
  const sys = sys_get();
  const fd = sys.sock(sys.SOCK_STREAM);
  if (fd < 0) {
    return sys.fail(sys.errno());
  }
  sys.reuse(fd);
  const at = sys.addr("0.0.0.0", Number(port));
  if (at === null) {
    sys.s.close(fd);
    return sys.fail(22);
  }
  if (sys.s.bind(fd, sys.ptr(at), 16) < 0 || sys.s.listen(fd, 16) < 0) {
    const code = sys.errno();
    sys.s.close(fd);
    return sys.fail(code);
  }
  return sys.done(sys.mint("Listener", "lsn", fd));
}

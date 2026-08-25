// UDP
// ===
//! use ./sys.js

function udp_bind(port) {
  const sys = sys_get();
  const fd = sys.sock(sys.SOCK_DGRAM);
  if (fd < 0) {
    return sys.fail(sys.errno());
  }
  const at = sys.addr("0.0.0.0", Number(port));
  if (at === null) {
    sys.s.close(fd);
    return sys.fail(22);
  }
  if (sys.s.bind(fd, sys.ptr(at), 16) < 0) {
    const code = sys.errno();
    sys.s.close(fd);
    return sys.fail(code);
  }
  return sys.done(sys.mint("Socket", "udp", fd));
}

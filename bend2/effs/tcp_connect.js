// TCP
// ===
//! use ./sys.js

function tcp_connect(host, port) {
  const sys = sys_get();
  const at = sys.addr(host, Number(port));
  if (at === null) {
    return sys.fail(22);
  }
  const fd = sys.sock(sys.SOCK_STREAM);
  if (fd < 0) {
    return sys.fail(sys.errno());
  }
  if (sys.s.connect(fd, sys.ptr(at), 16) < 0) {
    const code = sys.errno();
    sys.s.close(fd);
    return sys.fail(code);
  }
  return sys.done(sys.mint("Socket", "tcp", fd));
}

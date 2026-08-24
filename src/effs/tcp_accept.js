// TCP
// ===
//! use ./sys.js

function tcp_accept(listener) {
  const sys = sys_get();
  const lfd = sys.read(listener, "lsn");
  if (lfd === null) {
    return sys.tup(listener, sys.fail(9));
  }
  const fd = sys.s.accept(lfd, null, null);
  if (fd < 0) {
    return sys.tup(listener, sys.fail(sys.errno()));
  }
  return sys.tup(listener, sys.done(sys.mint("Socket", "tcp", fd)));
}

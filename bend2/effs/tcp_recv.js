// TCP
// ===
//! use ./sys.js

function tcp_recv(socket, max) {
  const sys = sys_get();
  const fd = sys.read(socket, "tcp");
  if (fd === null) {
    return sys.tup(socket, sys.fail(9));
  }
  const b = new Uint8Array(Math.max(Number(max), 1));
  const n = Number(sys.s.recv(fd, sys.ptr(b), Number(max), 0));
  if (n < 0) {
    return sys.tup(socket, sys.fail(sys.errno()));
  }
  return sys.tup(socket, sys.done(sys.text(b, n)));
}

function tcp_recv_need() {
  return { read: "tcp" };
}

// UDP
// ===
//! use ./sys.js

function udp_recv_from(socket, max) {
  const sys = sys_get();
  const fd = sys.read(socket, "udp");
  if (fd === null) {
    return sys.tup(socket, sys.fail(9));
  }
  const b = new Uint8Array(Math.max(Number(max), 1));
  const peer = new Uint8Array(16);
  const len = new Uint32Array([16]);
  const peer_at = sys.ptr(peer);
  const peer_ln = sys.ptr(len);
  const got = sys.s.recvfrom(fd, sys.ptr(b), Number(max), 0, peer_at, peer_ln);
  const n = Number(got);
  if (n < 0) {
    return sys.tup(socket, sys.fail(sys.errno()));
  }
  const from = sys.addr_show(peer);
  const data = sys.text(b, n);
  return sys.tup(socket, sys.done(sys.tup(from.host, from.port, data)));
}

function udp_recv_from_need() {
  return { read: "udp" };
}

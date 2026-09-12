// UDP
// ===

function udp_recv_from(socket, max) {
  const sys = io_sys();
  const fd = socket;
  const b = new Uint8Array(Math.max(Number(max), 1));
  const peer = new Uint8Array(16);
  const len = new Uint32Array([16]);
  const peer_at = sys.ptr(peer);
  const peer_ln = sys.ptr(len);
  const got = sys.recvfrom(fd, sys.ptr(b), Number(max), 0, peer_at, peer_ln);
  const n = Number(got);
  if (n < 0) {
    return io_tup(socket, io_fail(sys.errno()));
  }
  const host = peer[4] + "." + peer[5] + "." + peer[6] + "." + peer[7];
  const port = (peer[2] << 8) | peer[3];
  return io_tup(socket, io_done(io_tup(host, port, io_text(b, n))));
}

function udp_recv_from_need() {
  return { read: true };
}

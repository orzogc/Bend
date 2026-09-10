// UDP
// ===

function udp_poll(socket, max) {
  const sys = io_sys();
  const fd = io_read(socket, "udp");
  if (fd === null) {
    return io_tup(socket, io_fail(9));
  }
  const b = new Uint8Array(Math.max(Number(max), 1));
  const peer = new Uint8Array(16);
  const len = new Uint32Array([16]);
  const wait = sys.mac ? 0x80 : 0x40;
  const got = sys.recvfrom(fd, sys.ptr(b), Number(max), wait, sys.ptr(peer),
    sys.ptr(len));
  const n = Number(got);
  if (n < 0 && sys.errno() === (sys.mac ? 35 : 11)) {
    return io_tup(socket, io_done({ $: "None" }));
  }
  if (n < 0) {
    return io_tup(socket, io_fail(sys.errno()));
  }
  const host = peer[4] + "." + peer[5] + "." + peer[6] + "." + peer[7];
  const port = (peer[2] << 8) | peer[3];
  return io_tup(socket, io_done({ $: "Some",
    value: io_tup(host, port, io_text(b, n)) }));
}

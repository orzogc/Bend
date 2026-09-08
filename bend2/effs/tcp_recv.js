// TCP
// ===

function tcp_recv(socket, max) {
  const sys = io_sys();
  const fd = io_read(socket, "tcp");
  if (fd === null) {
    return io_tup(socket, io_fail(9));
  }
  const b = new Uint8Array(Math.max(Number(max), 1));
  const wait = sys.mac ? 0x80 : 0x40;
  let n = Number(sys.recv(fd, sys.ptr(b), Number(max), wait));
  if (n < 0 && sys.errno() === (sys.mac ? 35 : 11)) {
    n = Number(sys.recv(fd, sys.ptr(b), Number(max), 0));
  }
  if (n < 0) {
    return io_tup(socket, io_fail(sys.errno()));
  }
  return io_tup(socket, io_done(io_text(b, n)));
}

function tcp_recv_need() {
  return { read: "tcp" };
}

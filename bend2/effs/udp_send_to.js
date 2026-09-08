// UDP
// ===

function udp_send_to(socket, host, port, data) {
  const sys = io_sys();
  const fd = io_read(socket, "udp");
  if (fd === null) {
    return io_tup(socket, io_fail(9));
  }
  const at = io_addr(host, Number(port));
  if (at === null) {
    return io_tup(socket, io_fail(22));
  }
  const b = io_bytes(data);
  const sent = sys.sendto(fd, sys.ptr(b), b.length, 0, sys.ptr(at), 16);
  if (Number(sent) < 0) {
    return io_tup(socket, io_fail(sys.errno()));
  }
  return io_tup(socket, io_done({ $: "Unit" }));
}

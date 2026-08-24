// UDP
// ===
//! use ./sys.js

function udp_send_to(socket, host, port, data) {
  const sys = sys_get();
  const fd = sys.read(socket, "udp");
  if (fd === null) {
    return sys.tup(socket, sys.fail(9));
  }
  const at = sys.addr(host, Number(port));
  if (at === null) {
    return sys.tup(socket, sys.fail(22));
  }
  const b = sys.bytes(data);
  const sent = sys.s.sendto(fd, sys.ptr(b), b.length, 0, sys.ptr(at), 16);
  if (Number(sent) < 0) {
    return sys.tup(socket, sys.fail(sys.errno()));
  }
  return sys.tup(socket, sys.done({ $: "Unit" }));
}

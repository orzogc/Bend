// TCP
// ===
//! use ./sys.js

function tcp_send(socket, data) {
  const sys = sys_get();
  const fd = sys.read(socket, "tcp");
  if (fd === null) {
    return sys.tup(socket, sys.fail(9));
  }
  const b = sys.bytes(data);
  let at = 0;
  while (at < b.length) {
    const part = b.subarray(at);
    const n = Number(sys.s.send(fd, sys.ptr(part), part.length, sys.flags()));
    if (n < 0) {
      return sys.tup(socket, sys.fail(sys.errno()));
    }
    at += n;
  }
  return sys.tup(socket, sys.done({ $: "Unit" }));
}

function tcp_send_need() {
  return { write: "tcp" };
}

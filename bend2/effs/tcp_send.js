// TCP
// ===

function tcp_send(socket, data) {
  const sys = io_sys();
  const fd = socket;
  const b = io_bytes(data);
  let at = 0;
  while (at < b.length) {
    const part = b.subarray(at);
    const n = Number(sys.send(fd, sys.ptr(part), part.length, 0));
    if (n < 0) {
      return io_tup(socket, io_fail(sys.errno()));
    }
    at += n;
  }
  return io_tup(socket, io_done({ $: "Unit" }));
}

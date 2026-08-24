// Socket
// ======
//! use ./sys.js

function socket_close(socket) {
  const sys = sys_get();
  const tcp = sys.read(socket, "tcp");
  const udp = sys.read(socket, "udp");
  if (tcp !== null || udp !== null) {
    sys.s.close(sys.kill(socket));
  }
  return { $: "Unit" };
}

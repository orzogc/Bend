// Socket
// ======

function socket_close(socket) {
  const sys = io_sys();
  const tcp = io_read(socket, "tcp");
  const udp = io_read(socket, "udp");
  if (tcp !== null || udp !== null) {
    sys.close(io_kill(socket));
  }
  return { $: "Unit" };
}

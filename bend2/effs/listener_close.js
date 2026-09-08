// Listener
// ========

function listener_close(listener) {
  const sys = io_sys();
  if (io_read(listener, "lsn") !== null) {
    sys.close(io_kill(listener));
  }
  return { $: "Unit" };
}

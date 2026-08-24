// Listener
// ========
//! use ./sys.js

function listener_close(listener) {
  const sys = sys_get();
  if (sys.read(listener, "lsn") !== null) {
    sys.s.close(sys.kill(listener));
  }
  return { $: "Unit" };
}

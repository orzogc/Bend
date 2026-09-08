// IO
// ==

function io_get_env(name) {
  const ffi = require("bun:ffi");
  const sys = io_sys();
  const key = io_bytes(name + "\0");
  if (key.indexOf(0) < key.length - 1) {
    return io_fail(2);
  }
  const at = sys.getenv(sys.ptr(key));
  if (at === null || at === 0) {
    return io_fail(2);
  }
  let out = "";
  for (let i = 0; ffi.read.u8(at, i) !== 0; i++) {
    out += String.fromCharCode(ffi.read.u8(at, i));
  }
  return io_done(out);
}

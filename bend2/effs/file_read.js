// File
// ====
//! use ./sys.js

function file_read(file, max) {
  const sys = sys_get();
  const fd = sys.read(file, "file");
  if (fd === null) {
    return sys.tup(file, sys.fail(9));
  }
  const len = Math.min(max, 2147483647);
  const b = new Uint8Array(Math.max(len, 1));
  const n = Number(sys.s.read(fd, sys.ptr(b), len));
  if (n < 0) {
    return sys.tup(file, sys.fail(sys.errno()));
  }
  return sys.tup(file, sys.done(sys.text(b, n)));
}

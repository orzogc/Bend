// File
// ====
//! use ./sys.js

function file_read(file, max) {
  const sys = sys_get();
  const fs = require("fs");
  const fd = sys.read(file, "file");
  if (fd === null) {
    return sys.tup(file, sys.fail(9));
  }
  const b = new Uint8Array(Math.max(Number(max), 1));
  try {
    const n = fs.readSync(fd, b, 0, Number(max), null);
    return sys.tup(file, sys.done(sys.text(b, n)));
  } catch (e) {
    return sys.tup(file, sys.fail(Math.abs(e.errno ?? 5)));
  }
}

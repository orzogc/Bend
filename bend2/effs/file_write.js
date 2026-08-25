// File
// ====
//! use ./sys.js

function file_write(file, data) {
  const sys = sys_get();
  const fs = require("fs");
  const fd = sys.read(file, "file");
  if (fd === null) {
    return sys.tup(file, sys.fail(9));
  }
  const b = sys.bytes(data);
  let at = 0;
  try {
    while (at < b.length) {
      at += fs.writeSync(fd, b, at, b.length - at, null);
    }
    return sys.tup(file, sys.done({ $: "Unit" }));
  } catch (e) {
    return sys.tup(file, sys.fail(Math.abs(e.errno ?? 5)));
  }
}

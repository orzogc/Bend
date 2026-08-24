// File
// ====
//! use ./sys.js

function file_open(path, mode) {
  const sys = sys_get();
  const fs = require("fs");
  const name = sys.bytes(path);
  if (name.includes(0)) {
    return sys.fail(92);
  }
  if (mode !== "r" && mode !== "w" && mode !== "a") {
    return sys.fail(22);
  }
  try {
    const fd = fs.openSync(Buffer.from(name), mode, 0o644);
    return sys.done(sys.mint("File", "file", fd));
  } catch (e) {
    return sys.fail(Math.abs(e.errno ?? 5));
  }
}

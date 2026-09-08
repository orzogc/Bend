// File
// ====
//! use ./sys.js

function file_open(path, mode) {
  const sys = sys_get();
  const name = sys.bytes(path);
  if (name.includes(0)) {
    return sys.fail(sys.EILSEQ);
  }
  if (!["r", "w", "a"].includes(mode)) {
    return sys.fail(22);
  }
  try {
    const fd = require("fs")
      .openSync(name.length > 0 ? Buffer.from(name) : "", mode, 0o644);
    return sys.done(sys.mint("File", "file", fd));
  } catch (e) {
    return sys.fail(-e.errno);
  }
}

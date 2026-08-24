// File
// ====
//! use ./sys.js

function file_close(file) {
  const sys = sys_get();
  const fs = require("fs");
  if (sys.read(file, "file") !== null) {
    try {
      fs.closeSync(sys.kill(file));
    } catch (e) {
    }
  }
  return { $: "Unit" };
}

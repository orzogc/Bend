// File
// ====

function file_close(file) {
  const fs = require("fs");
  if (io_read(file, "file") !== null) {
    try {
      fs.closeSync(io_kill(file));
    } catch (e) {
    }
  }
  return { $: "Unit" };
}

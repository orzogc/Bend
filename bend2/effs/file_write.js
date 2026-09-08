// File
// ====

function file_write(file, data) {
  const fs = require("fs");
  const fd = io_read(file, "file");
  if (fd === null) {
    return io_tup(file, io_fail(9));
  }
  const b = io_bytes(data);
  let at = 0;
  try {
    while (at < b.length) {
      at += fs.writeSync(fd, b, at, b.length - at, null);
    }
    return io_tup(file, io_done({ $: "Unit" }));
  } catch (e) {
    return io_tup(file, io_fail(Math.abs(e.errno ?? 5)));
  }
}

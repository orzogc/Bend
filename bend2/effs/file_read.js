// File
// ====

function file_read(file, max) {
  const sys = io_sys();
  const fd = io_read(file, "file");
  if (fd === null) {
    return io_tup(file, io_fail(9));
  }
  const len = Math.min(max, 2147483647);
  const b = new Uint8Array(Math.max(len, 1));
  const n = Number(sys.read(fd, sys.ptr(b), len));
  if (n < 0) {
    return io_tup(file, io_fail(sys.errno()));
  }
  return io_tup(file, io_done(io_text(b, n)));
}

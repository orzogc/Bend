// File
// ====
//! use ./sys.c

IoFall file_read(IoHand file, uint32_t max, char* buf, uint32_t* len) {
  int fd = io_sys_read(file, IO_FILE);
  if (fd < 0) {
    return io_sys_fall(EBADF);
  }
  io_sync();
  ssize_t n = read(fd, buf, max);
  if (n < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  *len = (uint32_t)n;
  return io_sys_done();
}

Term file_read_run(Env e, Term* f) {
  IoHand file = io_hand_c(e, f[0]);
  uint32_t max = (uint32_t)f[1];
  char* buf = io_mem(malloc((uint64_t)max + 1));
  uint32_t len = 0;
  IoFall q = file_read(file, max, buf, &len);
  Term r = q.code != 0 ? io_fail(e, q) : io_done(e, io_str(e, buf, len));
  free(buf);
  return io_tup(e, io_hand(e, CID_FILE, file), r);
}

static void __attribute__((constructor)) file_read_use(void) {
  io_eff(FID_FILE_READ, CID_FILE_READ, file_read_run);
}

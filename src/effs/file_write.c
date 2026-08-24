// File
// ====
//! use ./sys.c

IoFall file_write(IoHand file, const char* data, uint32_t len) {
  int fd = io_sys_read(file, IO_FILE);
  if (fd < 0) {
    return io_sys_fall(EBADF);
  }
  uint32_t at = 0;
  while (at < len) {
    ssize_t n = write(fd, data + at, len - at);
    if (n < 0) {
      return io_sys_fall((uint32_t)errno);
    }
    at += (uint32_t)n;
  }
  return io_sys_done();
}

Term file_write_run(Env e, Term* f) {
  IoHand file = io_hand_c(e, f[0]);
  uint64_t n = 0;
  char* data = io_cstr(e, f[1], &n);
  IoFall q = file_write(file, data, (uint32_t)n);
  free(data);
  Term r = q.code != 0 ? io_fail(e, q) : io_done(e, term_pak(CID_UNIT, 0));
  return io_tup(e, io_hand(e, CID_FILE, file), r);
}

static void __attribute__((constructor)) file_write_use(void) {
  io_eff(FID_FILE_WRITE, CID_FILE_WRITE, file_write_run);
}

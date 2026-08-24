// File
// ====
//! use ./sys.c

static int file_open_mode(const char* mode) {
  if (strcmp(mode, "r") == 0) {
    return O_RDONLY;
  }
  if (strcmp(mode, "w") == 0) {
    return O_WRONLY | O_CREAT | O_TRUNC;
  }
  if (strcmp(mode, "a") == 0) {
    return O_WRONLY | O_CREAT | O_APPEND;
  }
  return -1;
}

IoFall file_open(const char* path, const char* mode, IoHand* out) {
  int flags = file_open_mode(mode);
  if (flags < 0) {
    return io_sys_fall(EINVAL);
  }
  int fd = open(path, flags, 0644);
  if (fd < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  if (io_sys_mint(IO_FILE, fd, out) < 0) {
    close(fd);
    return io_sys_fall(EMFILE);
  }
  return io_sys_done();
}

Term file_open_run(Env e, Term* f) {
  uint64_t pn = 0;
  uint64_t mn = 0;
  char* path = io_cstr(e, f[0], &pn);
  char* mode = io_cstr(e, f[1], &mn);
  IoHand out;
  IoFall q;
  if (io_nul(path, pn)) {
    q = io_sys_fall(EILSEQ);
  } else if (io_nul(mode, mn)) {
    q = io_sys_fall(EINVAL);
  } else {
    q = file_open(path, mode, &out);
  }
  free(path);
  free(mode);
  if (q.code != 0) {
    return io_fail(e, q);
  }
  return io_done(e, io_hand(e, CID_FILE, out));
}

static void __attribute__((constructor)) file_open_use(void) {
  io_eff(FID_FILE_OPEN, CID_FILE_OPEN, file_open_run);
}

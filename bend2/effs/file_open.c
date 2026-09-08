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

static void file_open_call(IoWork* w) {
  io_sys_keep(w, IO_FILE, open(w->data, (int)w->word, 0644));
}

static Term file_open_pack(Env e, IoWork* w) {
  free(w->data);
  return w->fall.code != 0 ? io_fail(e, w->fall)
    : io_done(e, io_hand(e, CID_FILE, w->made));
}

Term file_open_run(Env e, Term* f, IoWork* w) {
  uint64_t mn = 0;
  w->data = io_cstr(e, f[0], &w->size);
  char* mode = io_cstr(e, f[1], &mn);
  int flags = io_nul(mode, mn) ? -1 : file_open_mode(mode);
  free(mode);
  w->word = (uint32_t)flags;
  if (io_nul(w->data, w->size) || flags < 0) {
    w->fall = io_sys_fall(io_nul(w->data, w->size) ? EILSEQ : EINVAL);
    return file_open_pack(e, w);
  }
  return io_work(w, file_open_call, file_open_pack);
}

static void __attribute__((constructor)) file_open_use(void) {
  io_eff(FID_FILE_OPEN, CID_FILE_OPEN, file_open_run, 0);
}

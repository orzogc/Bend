// File
// ====
//! use ./sys.c

static void file_read_call(IoWork* w) {
  int fd = io_sys_read(w->hand, IO_FILE);
  w->size = io_sys_end(w, read(fd, w->data, w->word));
}

static Term file_read_pack(Env e, IoWork* w) {
  Term r = w->fall.code ? io_fail(e, w->fall)
    : io_done(e, io_str(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(e, CID_FILE, w->hand), r);
}

Term file_read_run(Env e, Term* f, IoWork* w) {
  w->hand = io_hand_c(e, f[0]);
  w->word = f[1] < INT32_MAX ? f[1] : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  return io_work(w, file_read_call, file_read_pack);
}

static void __attribute__((constructor)) file_read_use(void) {
  io_eff(FID_FILE_READ, CID_FILE_READ, file_read_run, 0);
}

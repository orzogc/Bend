// File
// ====

// The bytes as they are (0..255), one List cell each; a text reader
// would decode them as UTF-8.
static void file_read_bytes_call(IoWork* w) {
  int fd = io_sys_read(w->hand, IO_FILE);
  w->size = io_sys_end(w, read(fd, w->data, w->word));
}

static Term file_read_bytes_pack(Env e, IoWork* w) {
  Term r;
  if (w->fall.code) {
    r = io_fail(e, w->fall);
  } else {
    Term xs = term_pak(CID_NIL, 0);
    for (u64 i = w->size; i > 0; i -= 1) {
      xs = io_node(e, CID_CON, ((uint8_t*)w->data)[i - 1], xs, IO_HOTS & 16);
    }
    r = io_done(e, xs);
  }
  free(w->data);
  return io_tup(e, io_hand(e, CID_FILE, w->hand), r);
}

Term file_read_bytes_run(Env e, Term* f, IoWork* w) {
  w->hand = io_hand_c(e, f[0]);
  w->word = f[1] < INT32_MAX ? f[1] : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  return io_work(w, file_read_bytes_call, file_read_bytes_pack);
}

static void __attribute__((constructor)) file_read_bytes_use(void) {
  io_eff(FID_FILE_READ_BYTES, CID_FILE_READ_BYTES, file_read_bytes_run, 0);
}

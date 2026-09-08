// File
// ====

void file_close(IoHand file) {
  if (io_sys_read(file, IO_FILE) >= 0) {
    close(io_sys_kill(file));
  }
}

Term file_close_run(Env e, Term* f, IoWork* w) {
  file_close(io_hand_c(e, f[0]));
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) file_close_use(void) {
  io_eff(FID_FILE_CLOSE, CID_FILE_CLOSE, file_close_run, 0);
}

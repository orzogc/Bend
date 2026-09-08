// IO
// ==

Term io_spawn_run(Env e, Term* f, IoWork* w) {
  io_push(f[0], term_clo(FID_IO_EMIT, 0), true);
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) io_spawn_use(void) {
  io_eff(FID_IO_SPAWN, CID_IO_SPAWN, io_spawn_run, 0);
}

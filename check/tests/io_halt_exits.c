// IO
// ==

Term halt_probe_run(Env e, Term* f) {
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) halt_probe_use(void) {
  io_eff(FID_HALT_PROBE, CID_HALT_PROBE, halt_probe_run);
}

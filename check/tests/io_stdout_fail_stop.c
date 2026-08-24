// IO
// ==

Term out_probe_run(Env e, Term* f) {
  close(1);
  return 0;
}

static void __attribute__((constructor)) out_probe_use(void) {
  io_eff(FID_OUT_PROBE, CID_OUT_PROBE, out_probe_run);
}

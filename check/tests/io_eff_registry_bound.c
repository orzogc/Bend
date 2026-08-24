// IO
// ==

Term reg_probe_run(Env e, Term* f) {
  return (Term)io_eff_len;
}

static void __attribute__((constructor)) reg_probe_use(void) {
  for (u32 i = 0; i < 62; i += 1) {
    io_eff(1000000 + i, 1000000 + i, NULL);
  }
  io_eff(FID_REG_PROBE, CID_REG_PROBE, reg_probe_run);
}

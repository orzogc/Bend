// IO
// ==

Term wide_sum_run(Env e, Term* f, IoWork* w) {
  uint64_t s = 0;
  for (int i = 0; i < 254; i += 1) {
    s += (uint32_t)f[i];
  }
  return (Term)(uint32_t)s;
}

static void __attribute__((constructor)) wide_sum_use(void) {
  io_eff(FID_WIDE_SUM, CID_WIDE_SUM, wide_sum_run, 0);
}

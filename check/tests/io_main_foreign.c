Term main_run(Env e, Term* f) {
  io_out(stdout, "EFF RAN\n", 8);
  return (Term)7;
}

static void __attribute__((constructor)) main_use(void) {
  io_eff(FID_MAIN, CID_MAIN, main_run);
}

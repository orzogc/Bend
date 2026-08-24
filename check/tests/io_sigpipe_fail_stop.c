// IO
// ==

Term pipe_probe_run(Env e, Term* f) {
  int p[2];
  pipe(p);
  dup2(p[1], 1);
  close(p[0]);
  close(p[1]);
  return 0;
}

static void __attribute__((constructor)) pipe_probe_use(void) {
  io_eff(FID_PIPE_PROBE, CID_PIPE_PROBE, pipe_probe_run);
}

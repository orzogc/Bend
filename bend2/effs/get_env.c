// IO
// ==

IoFall io_get_env(const char* name, const char** out) {
  const char* value = getenv(name);
  if (value == NULL) {
    return io_sys_fall(ENOENT);
  }
  *out = value;
  return io_sys_fall(0);
}

Term io_get_env_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* name = io_cstr(e, f[0], &n);
  const char* got = NULL;
  IoFall q;
  if (io_nul(name, n)) {
    q = io_sys_fall(ENOENT);
  } else {
    q = io_get_env(name, &got);
  }
  free(name);
  if (q.code != 0) {
    return io_fail(e, q);
  }
  return io_done(e, io_str(e, got, strlen(got)));
}

static void __attribute__((constructor)) io_get_env_use(void) {
  io_eff(FID_IO_GET_ENV, CID_IO_GET_ENV, io_get_env_run, 0);
}

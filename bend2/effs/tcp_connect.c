// TCP
// ===

static void tcp_connect_call(IoWork* w) {
  struct sockaddr_in at;
  int fd = -1;
  errno = EINVAL;
  if (io_sys_addr(w->data, w->word, &at) == 0) {
    fd = socket(AF_INET, SOCK_STREAM, 0);
  }
  if (fd >= 0 && connect(fd, (struct sockaddr*)&at, sizeof(at)) < 0) {
    int code = errno;
    close(fd);
    fd = -1;
    errno = code;
  }
  w->made = (intptr_t)io_sys_end(w, fd);
}

static Term tcp_connect_pack(Env e, IoWork* w) {
  free(w->data);
  return w->code != 0 ? io_fail(e, w->code, NULL)
    : io_done(e, io_hand(w->made));
}

Term tcp_connect_run(Env e, Term* f, IoWork* w) {
  w->data = io_cstr(e, f[0], &w->size);
  w->word = (uint32_t)f[1];
  if (io_nul(w->data, w->size)) {
    w->code = EINVAL;
    return tcp_connect_pack(e, w);
  }
  return io_work(w, tcp_connect_call, tcp_connect_pack);
}

static void __attribute__((constructor)) tcp_connect_use(void) {
  io_eff(CID_TCP_CONNECT, tcp_connect_run, 0);
}

// UDP
// ===

IoFall udp_bind(uint32_t port, IoHand* out) {
  int fd = socket(AF_INET, SOCK_DGRAM, 0);
  if (fd < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  struct sockaddr_in at;
  if (io_sys_addr("0.0.0.0", port, &at) < 0) {
    close(fd);
    return io_sys_fall(EINVAL);
  }
  if (bind(fd, (struct sockaddr*)&at, sizeof(at)) < 0) {
    uint32_t code = (uint32_t)errno;
    close(fd);
    return io_sys_fall(code);
  }
  if (io_sys_mint(IO_UDPS, fd, out) < 0) {
    close(fd);
    return io_sys_fall(EMFILE);
  }
  return io_sys_fall(0);
}

Term udp_bind_run(Env e, Term* f, IoWork* w) {
  IoHand out;
  IoFall q = udp_bind((uint32_t)f[0], &out);
  if (q.code != 0) {
    return io_fail(e, q);
  }
  return io_done(e, io_hand(e, CID_SOCKET, out));
}

static void __attribute__((constructor)) udp_bind_use(void) {
  io_eff(FID_UDP_BIND, CID_UDP_BIND, udp_bind_run, 0);
}

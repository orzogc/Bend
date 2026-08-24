// UDP
// ===
//! use ./sys.c

IoFall udp_recv_from(IoHand socket, uint32_t max, char* buf,
  uint32_t* len, char* host, uint32_t* port) {
  int fd = io_sys_read(socket, IO_UDPS);
  if (fd < 0) {
    return io_sys_fall(EBADF);
  }
  struct sockaddr_in at;
  socklen_t alen = sizeof(at);
  io_sync();
  ssize_t n = recvfrom(fd, buf, max, 0, (struct sockaddr*)&at, &alen);
  if (n < 0) {
    return io_sys_fall((uint32_t)errno);
  }
  *len = (uint32_t)n;
  inet_ntop(AF_INET, &at.sin_addr, host, 16);
  *port = ntohs(at.sin_port);
  return io_sys_done();
}

Term udp_recv_from_run(Env e, Term* f) {
  IoHand socket = io_hand_c(e, f[0]);
  uint32_t max = (uint32_t)f[1];
  char* buf = io_mem(malloc((uint64_t)max + 1));
  uint32_t len = 0;
  char host[16] = "";
  uint32_t port = 0;
  IoFall q = udp_recv_from(socket, max, buf, &len, host, &port);
  Term r = 0;
  if (q.code != 0) {
    r = io_fail(e, q);
  } else {
    Term stamp = io_tup(e, io_str(e, host, strlen(host)),
      io_tup(e, (uint64_t)port, io_str(e, buf, len)));
    r = io_done(e, stamp);
  }
  free(buf);
  return io_tup(e, io_hand(e, CID_SOCKET, socket), r);
}

static void __attribute__((constructor)) udp_recv_from_use(void) {
  io_eff(FID_UDP_RECV_FROM, CID_UDP_RECV_FROM, udp_recv_from_run);
}

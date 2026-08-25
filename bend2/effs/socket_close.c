// Socket
// ======
//! use ./sys.c

void socket_close(IoHand socket) {
  int tcp = io_sys_read(socket, IO_TCPS);
  int udp = io_sys_read(socket, IO_UDPS);
  if (tcp >= 0 || udp >= 0) {
    close(io_sys_kill(socket));
  }
}

Term socket_close_run(Env e, Term* f) {
  socket_close(io_hand_c(e, f[0]));
  return term_pak(CID_UNIT, 0);
}

static void __attribute__((constructor)) socket_close_use(void) {
  io_eff(FID_SOCKET_CLOSE, CID_SOCKET_CLOSE, socket_close_run);
}

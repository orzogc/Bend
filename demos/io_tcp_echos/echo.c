// echo: the C twin of main.bend. One thread, non-blocking sockets,
// kqueue (macOS) or epoll (Linux), edge-triggered: an event on the
// listener accepts every pending connection, an event on a socket
// reads until EAGAIN and writes each chunk back (a short write
// spins on poll for room, which the load never causes), and a read
// of zero closes. usage: echo PORT
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#ifdef __linux__
#include <sys/epoll.h>
#else
#include <sys/event.h>
#endif

static void unblock(int fd) {
  fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
}

static int pol;

static void watch(int fd) {
#ifdef __linux__
  struct epoll_event ev;
  ev.events = EPOLLIN | EPOLLET;
  ev.data.fd = fd;
  epoll_ctl(pol, EPOLL_CTL_ADD, fd, &ev);
#else
  struct kevent ev;
  EV_SET(&ev, fd, EVFILT_READ, EV_ADD | EV_CLEAR, 0, 0, NULL);
  kevent(pol, &ev, 1, NULL, 0, NULL);
#endif
}

static void send_all(int fd, const char* buf, ssize_t n) {
  ssize_t at = 0;
  while (at < n) {
    ssize_t w = send(fd, buf + at, (size_t)(n - at), 0);
    if (w < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      struct pollfd p = { fd, POLLOUT, 0 };
      poll(&p, 1, -1);
      continue;
    }
    if (w <= 0) {
      return;
    }
    at += w;
  }
}

static void serve(int lfd, int fd) {
  if (fd == lfd) {
    for (;;) {
      int c = accept(lfd, NULL, NULL);
      if (c < 0) {
        return;
      }
      unblock(c);
      watch(c);
    }
  }
  char buf[65536];
  for (;;) {
    ssize_t n = recv(fd, buf, sizeof(buf), 0);
    if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      return;
    }
    if (n <= 0) {
      close(fd);
      return;
    }
    send_all(fd, buf, n);
  }
}

int main(int argc, char** argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: echo PORT\n");
    return 2;
  }
  signal(SIGPIPE, SIG_IGN);
  int lfd = socket(AF_INET, SOCK_STREAM, 0);
  int one = 1;
  setsockopt(lfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
  struct sockaddr_in at;
  memset(&at, 0, sizeof(at));
  at.sin_family = AF_INET;
  at.sin_port = htons((uint16_t)atoi(argv[1]));
  at.sin_addr.s_addr = htonl(INADDR_ANY);
  if (bind(lfd, (struct sockaddr*)&at, sizeof(at)) < 0 || listen(lfd, 16) < 0) {
    perror("listen");
    return 1;
  }
  unblock(lfd);
#ifdef __linux__
  pol = epoll_create1(0);
#else
  pol = kqueue();
#endif
  watch(lfd);
  printf("echoing on 127.0.0.1:%s\n", argv[1]);
  fflush(stdout);
  for (;;) {
#ifdef __linux__
    struct epoll_event evs[64];
    int n = epoll_wait(pol, evs, 64, -1);
    for (int i = 0; i < n; i += 1) {
      serve(lfd, evs[i].data.fd);
    }
#else
    struct kevent evs[64];
    int n = kevent(pol, NULL, 0, evs, 64, NULL);
    for (int i = 0; i < n; i += 1) {
      serve(lfd, (int)evs[i].ident);
    }
#endif
  }
}

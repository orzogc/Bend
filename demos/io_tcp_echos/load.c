// load: the load generator for the echo servers. It opens N
// connections to HOST:PORT, and on each runs M round trips of 64
// bytes (send, then read the echo back) with the connections
// interleaved through poll(2), then prints the round trips per
// second. usage: load HOST PORT N M
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

int main(int argc, char** argv) {
  if (argc != 5) {
    fprintf(stderr, "usage: load HOST PORT N M\n");
    return 2;
  }
  int n = atoi(argv[3]);
  int m = atoi(argv[4]);
  struct sockaddr_in at;
  memset(&at, 0, sizeof(at));
  at.sin_family = AF_INET;
  at.sin_port = htons((uint16_t)atoi(argv[2]));
  inet_pton(AF_INET, argv[1], &at.sin_addr);
  char msg[64];
  memset(msg, 'x', 64);
  int* fds = calloc((size_t)n, sizeof(int));
  int* left = calloc((size_t)n, sizeof(int));
  int* got = calloc((size_t)n, sizeof(int));
  struct pollfd* pfd = calloc((size_t)n, sizeof(struct pollfd));
  for (int i = 0; i < n; i += 1) {
    fds[i] = socket(AF_INET, SOCK_STREAM, 0);
    if (connect(fds[i], (struct sockaddr*)&at, sizeof(at)) < 0) {
      perror("connect");
      return 1;
    }
    fcntl(fds[i], F_SETFL, fcntl(fds[i], F_GETFL) | O_NONBLOCK);
    left[i] = m;
  }
  double t0 = now();
  for (int i = 0; i < n; i += 1) {
    if (send(fds[i], msg, 64, 0) != 64) {
      perror("send");
      return 1;
    }
  }
  long done = 0;
  int active = n;
  while (active > 0) {
    int k = 0;
    for (int i = 0; i < n; i += 1) {
      if (left[i] > 0) {
        pfd[k].fd = fds[i];
        pfd[k].events = POLLIN;
        pfd[k].revents = 0;
        k += 1;
      }
    }
    if (poll(pfd, (nfds_t)k, -1) < 0 && errno != EINTR) {
      perror("poll");
      return 1;
    }
    int j = 0;
    for (int i = 0; i < n; i += 1) {
      if (left[i] == 0) {
        continue;
      }
      if (pfd[j].revents != 0) {
        char buf[64];
        ssize_t r = recv(fds[i], buf, (size_t)(64 - got[i]), 0);
        if (r <= 0) {
          fprintf(stderr, "connection %d died after %d round trips\n", i,
            m - left[i]);
          return 1;
        }
        got[i] += (int)r;
        if (got[i] == 64) {
          got[i] = 0;
          left[i] -= 1;
          done += 1;
          if (left[i] > 0) {
            if (send(fds[i], msg, 64, 0) != 64) {
              perror("send");
              return 1;
            }
          } else {
            close(fds[i]);
            active -= 1;
          }
        }
      }
      j += 1;
    }
  }
  double secs = now() - t0;
  printf("N=%d M=%d round_trips=%ld secs=%.3f rt/s=%.0f\n", n, m, done,
    secs, (double)done / secs);
  return 0;
}

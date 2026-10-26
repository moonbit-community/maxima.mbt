#include <moonbit.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

MOONBIT_FFI_EXPORT
void maxima_write_stdout(moonbit_bytes_t b, int32_t len) {
  fwrite(b, 1, (size_t)len, stdout);
}

MOONBIT_FFI_EXPORT
void maxima_flush_stdout(void) { fflush(stdout); }

MOONBIT_FFI_EXPORT
void maxima_write_stderr(moonbit_bytes_t b, int32_t len) {
  fflush(stdout);
  fwrite(b, 1, (size_t)len, stderr);
  fflush(stderr);
}

/* Read one line from stdin (including the newline). Returns an empty byte
   string at EOF; *eof is set to 1 then. */
MOONBIT_FFI_EXPORT
moonbit_bytes_t maxima_read_line(int32_t *eof) {
  size_t cap = 256, n = 0;
  char *buf = malloc(cap);
  int c;
  *eof = 0;
  while ((c = fgetc(stdin)) != EOF) {
    if (n + 1 >= cap) { cap *= 2; buf = realloc(buf, cap); }
    buf[n++] = (char)c;
    if (c == '\n') break;
  }
  if (n == 0 && c == EOF) *eof = 1;
  moonbit_bytes_t r = moonbit_make_bytes((int32_t)n, 0);
  memcpy(r, buf, n);
  free(buf);
  return r;
}

MOONBIT_FFI_EXPORT
double maxima_cpu_time(void) { return (double)clock() / CLOCKS_PER_SEC; }

MOONBIT_FFI_EXPORT
void maxima_exit(int32_t code) { fflush(stdout); exit(code); }

#include <unistd.h>
#include <sys/socket.h>
#include <netdb.h>
#include <sys/wait.h>

/* Run a shell command; returns its exit status (or -1). */
MOONBIT_FFI_EXPORT
int32_t maxima_system(moonbit_bytes_t cmd) {
  fflush(stdout);
  int r = system((const char *)cmd);
  if (r == -1) return -1;
  if (WIFEXITED(r)) return WEXITSTATUS(r);
  return -1;
}

/* Run a shell command and capture its stdout. *status gets the exit code. */
MOONBIT_FFI_EXPORT
moonbit_bytes_t maxima_shell_output(moonbit_bytes_t cmd, int32_t *status) {
  fflush(stdout);
  FILE *p = popen((const char *)cmd, "r");
  size_t cap = 4096, n = 0;
  char *buf = malloc(cap);
  if (p) {
    size_t k;
    while ((k = fread(buf + n, 1, cap - n, p)) > 0) {
      n += k;
      if (n == cap) { cap *= 2; buf = realloc(buf, cap); }
    }
    int r = pclose(p);
    *status = (r != -1 && WIFEXITED(r)) ? WEXITSTATUS(r) : -1;
  } else {
    *status = -1;
  }
  moonbit_bytes_t out = moonbit_make_bytes((int32_t)n, 0);
  memcpy(out, buf, n);
  free(buf);
  return out;
}

MOONBIT_FFI_EXPORT
int32_t maxima_chdir(moonbit_bytes_t path) { return chdir((const char *)path); }

MOONBIT_FFI_EXPORT
moonbit_bytes_t maxima_getcwd(void) {
  char buf[4096];
  if (!getcwd(buf, sizeof buf)) buf[0] = 0;
  size_t n = strlen(buf);
  moonbit_bytes_t out = moonbit_make_bytes((int32_t)n, 0);
  memcpy(out, buf, n);
  return out;
}

MOONBIT_FFI_EXPORT
int32_t maxima_getpid(void) { return (int32_t)getpid(); }

/* TCP client socket: returns fd or -1. */
MOONBIT_FFI_EXPORT
int32_t maxima_tcp_connect(moonbit_bytes_t host, int32_t port) {
  char portstr[16];
  snprintf(portstr, sizeof portstr, "%d", (int)port);
  struct addrinfo hints, *res = 0;
  memset(&hints, 0, sizeof hints);
  hints.ai_socktype = SOCK_STREAM;
  if (getaddrinfo((const char *)host, portstr, &hints, &res) != 0) return -1;
  int fd = -1;
  for (struct addrinfo *a = res; a; a = a->ai_next) {
    fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
    if (fd < 0) continue;
    if (connect(fd, a->ai_addr, a->ai_addrlen) == 0) break;
    close(fd);
    fd = -1;
  }
  freeaddrinfo(res);
  return fd;
}

MOONBIT_FFI_EXPORT
int32_t maxima_fd_write(int32_t fd, moonbit_bytes_t b, int32_t len) {
  return (int32_t)write(fd, b, (size_t)len);
}

/* Read up to max bytes; returns empty bytes at EOF/error. */
MOONBIT_FFI_EXPORT
moonbit_bytes_t maxima_fd_read(int32_t fd, int32_t max) {
  char *buf = malloc(max > 0 ? max : 1);
  ssize_t k = read(fd, buf, (size_t)max);
  if (k < 0) k = 0;
  moonbit_bytes_t out = moonbit_make_bytes((int32_t)k, 0);
  memcpy(out, buf, (size_t)k);
  free(buf);
  return out;
}

MOONBIT_FFI_EXPORT
int32_t maxima_fd_close(int32_t fd) { return close(fd); }

/* Append LEN bytes to the file PATH (created if missing); 0 on success. */
MOONBIT_FFI_EXPORT
int32_t maxima_append_file(moonbit_bytes_t path, moonbit_bytes_t b, int32_t len) {
  FILE *f = fopen((const char *)path, "ab");
  if (!f) return -1;
  size_t w = fwrite(b, 1, (size_t)len, f);
  int r = fclose(f);
  return (w == (size_t)len && r == 0) ? 0 : -1;
}

/* Write pipes to child processes (popen "w"), addressed by a small handle.
   SIGPIPE is ignored so that writing to a process that has exited fails
   with an error instead of killing Maxima. */
#include <signal.h>
#define MAXIMA_MAX_PIPES 64
static FILE *maxima_pipes[MAXIMA_MAX_PIPES];

MOONBIT_FFI_EXPORT
int32_t maxima_pipe_open(moonbit_bytes_t cmd) {
  signal(SIGPIPE, SIG_IGN);
  fflush(stdout);
  fflush(stderr);
  for (int i = 0; i < MAXIMA_MAX_PIPES; i++) {
    if (!maxima_pipes[i]) {
      FILE *p = popen((const char *)cmd, "w");
      if (!p) return -1;
      maxima_pipes[i] = p;
      return i;
    }
  }
  return -1;
}

/* Write and flush; returns the number of bytes written or -1. */
MOONBIT_FFI_EXPORT
int32_t maxima_pipe_write(int32_t h, moonbit_bytes_t b, int32_t len) {
  if (h < 0 || h >= MAXIMA_MAX_PIPES || !maxima_pipes[h]) return -1;
  FILE *p = maxima_pipes[h];
  size_t n = fwrite(b, 1, (size_t)len, p);
  if (n < (size_t)len) return -1;
  if (fflush(p) != 0) return -1;
  return (int32_t)n;
}

/* Close the pipe and wait for the process; returns its exit status or -1. */
MOONBIT_FFI_EXPORT
int32_t maxima_pipe_close(int32_t h) {
  if (h < 0 || h >= MAXIMA_MAX_PIPES || !maxima_pipes[h]) return -1;
  int r = pclose(maxima_pipes[h]);
  maxima_pipes[h] = 0;
  if (r != -1 && WIFEXITED(r)) return WEXITSTATUS(r);
  return -1;
}

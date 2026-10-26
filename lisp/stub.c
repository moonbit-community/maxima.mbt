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

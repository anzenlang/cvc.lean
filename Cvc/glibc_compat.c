/*
 * TEMPORARY compatibility shim for the cvc5 static libraries lean-cvc5 downloads on Linux.
 * Remove it, with its target in the lakefile, once lean-cvc5 ships a cvc5 built against a glibc
 * older than 2.38.
 *
 * Those libraries were compiled against glibc 2.38 or later, whose headers redirect `strtol` and
 * `fscanf` to the C23 variants `__isoc23_strtol` and `__isoc23_fscanf`. Lean links executables
 * against its own, older glibc, which has neither, so any executable using cvc.lean fails to link:
 * `undefined symbol: __isoc23_strtol`. Shared libraries still link, leaving the symbols to the
 * system's glibc when they are loaded, which has them from 2.38 on. Those two are the only such
 * symbols in the whole release, on x86_64 and arm64 alike (`nm -u` over every library: `libcvc5.a`
 * and `libgmp.a` need `__isoc23_strtol`, `libcadical.a` needs `__isoc23_fscanf`).
 *
 * The C23 variants differ from the classic functions only in reading `0b` binary literals (`strtol`
 * with base 0 or 2, `fscanf`'s `%i`), which the callers — MiniSat's integer options, GMP's `scanf`,
 * CaDiCaL reading its resident set size from `/proc` — have no use for.
 *
 * Compiled as C11, without `_GNU_SOURCE`, so that glibc's headers do not redirect the classic calls
 * below to the very functions being defined. On any other platform the file is empty.
 */
#if defined(__linux__)

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

/* the calls below would otherwise become calls to the functions they are in, looping forever */
#ifdef __GLIBC_USE
#if __GLIBC_USE (C2X_STRTOL)
#error "glibc redirects strtol here: compile this file as C11, without _GNU_SOURCE"
#endif
#endif

long __isoc23_strtol(const char *nptr, char **endptr, int base) {
  return strtol(nptr, endptr, base);
}

int __isoc23_fscanf(FILE *stream, const char *format, ...) {
  va_list args;
  va_start(args, format);
  int result = vfscanf(stream, format, args);
  va_end(args);
  return result;
}

#endif

// Port of the process functions of src/server.lisp: GETPID,
// GETPID-FROM-ENVIRONMENT and XCHDIR (the socket client functions of
// server.lisp are not in this file).

///|
fn getpid_from_environment() -> Value raise {
  match maxima_getenv(Str("PID")) {
    Str(s) =>
      match parse_integer(s) {
        Some(v) => v
        None => Fix(-1L)
      }
    _ => Fix(-1L)
  }
}

///|
/// (sb-unix:unix-getpid)
fn getpid() -> Value raise {
  int(process_id())
}

///|
/// (sb-posix:chdir w)
fn xchdir(w : Value) -> Value raise {
  if !change_directory(lstring(w)) {
    raise LispError::Condition(
      intern("sb-posix:syscall-error"),
      "Error in SB-POSIX:CHDIR: cannot change to " + lstring(w),
      w,
    )
  }
  Fix(0L)
}

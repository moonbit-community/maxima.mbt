// Port of share/contrib/unicodedata/grind-patch.lisp (Leo Butler, 2015,
// 2025): redefine SLASH (src/mgrind.lisp) so that wide characters are not
// escaped.

///|
fn share_grind_patch__wide(c : Value) -> Bool raise {
  match c {
    Char(ch) => ch.to_int() > 128
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(c) + " is not of type CHARACTER",
      )
  }
}

///|
fn share_grind_patch__slash(x : Value) -> Value raise {
  if x is Nil {
    return x
  }
  let mut l = cdr(x)
  while l.truthy() {
    // Following test is the same (except backslash is not included, so
    // backslash is preceded by backslash) as in SCAN-TOKEN
    // (src/nparse.lisp). Any wide-char should not be escaped
    if ascii_numberp(car(l)).truthy() ||
      alphabetp(car(l)).truthy() ||
      share_grind_patch__wide(car(l)) {
      ()
    } else {
      rplacd(l, cons(car(l), cdr(l))) |> ignore
      rplaca(l, Char('\\')) |> ignore
      l = cdr(l)
    }
    l = cdr(l)
  }
  if alphabetp(car(x)).truthy() || share_grind_patch__wide(car(x)) {
    x
  } else {
    cons(Char('\\'), x)
  }
}

///|
fn init_share_grind_patch() -> Unit raise {
  mgrind__slash_redefined.val = Some(share_grind_patch__slash)
  defun(q_slash, a => share_grind_patch__slash(arg(a, 0)), name="slash")
}

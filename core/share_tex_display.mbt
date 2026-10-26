// Port of share/contrib/alt-display/tex-display.lisp (Leo Butler, 2014):
// a TeX display function for set_alt_display.

///|
fn get_tex_environment_star(x : Value) -> Value raise {
  if stringp(x) {
    cons(Str(""), Str(""))
  } else {
    get_tex_environment(x)
  }
}

///|
fn d_tex_displa(x : Value) -> Value raise {
  let s = lstring(d_tex1(list2(car(x), cadr(x))))
  let e = lstring(mfuncall(q_d_tex1, list1(caddr(x))))
  let env = get_tex_environment_star(caddr(x))
  let chars = s.to_array()
  let n = chars.length() - 14
  if n < 0 {
    raise LispError::SimpleError(
      format_to_string(
        "The bounding indices 0 and ~D are bad for a sequence of length ~D.",
        [int(n), int(chars.length())],
      ),
    )
  }
  Str(
    String::from_array(chars[0:n].to_array()) +
    lstring(car(env)) +
    e +
    lstring(cdr(env)),
  )
}

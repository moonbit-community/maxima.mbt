// Fortran CHARACTER support (f2cl-lib's F2CL-STRING, FREF-STRING,
// FSET-STRING, ICHAR, FCHAR).  Fortran strings are immutable MoonBit
// Strings here; an assignment to a substring builds the new string.

///|
/// F2CL-STRING: `s` truncated or blank-padded to length `n`.
pub fn f2cl_string(s : String, n : Int) -> String {
  let cs = s.to_array()
  let sb = StringBuilder()
  for k in 0..<n {
    sb.write_char(if k < cs.length() { cs[k] } else { ' ' })
  }
  sb.to_string()
}

///|
/// FREF-STRING: the substring S(A:B), i.e. (subseq s (1- a) b).
pub fn fstr_sub(s : String, a : Int, b : Int) -> String {
  let cs = s.to_array()
  let sb = StringBuilder()
  for k in (a - 1)..<b {
    sb.write_char(cs[k])
  }
  sb.to_string()
}

///|
/// FSET-STRING: `s` with S(A:B) replaced by `v`, as
/// (setf (subseq s (1- a) b) v) does (the shorter length is copied).
pub fn fstr_set(s : String, a : Int, b : Int, v : String) -> String {
  let cs = s.to_array()
  let vs = v.to_array()
  let mut k = 0
  while a - 1 + k < b && k < vs.length() {
    cs[a - 1 + k] = vs[k]
    k = k + 1
  }
  String::from_array(cs)
}

///|
/// ICHAR: the character code of the first character.
pub fn ichar(s : String) -> Int {
  s.to_array()[0].to_int()
}

///|
/// CHAR (f2cl's FCHAR): the one-character string with code `i`.
pub fn fchar(i : Int) -> String {
  Int::unsafe_to_char(i).to_string()
}

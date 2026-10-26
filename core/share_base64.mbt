// Port of share/stringproc/base64.lisp: base64 encoding of strings,
// non-negative integers and lists of octets, and decoding.

///|
fn d_base64(s : Value) -> Value raise {
  let mut bytes = if stringp(s) {
    string_to_octets(s)
  } else if integerp(s) && num_ge(s, int(0)) {
    number_to_octets(s)
  } else if d_listp(s).truthy() {
    cdr(s)
  } else {
    gf_merror(
      Str(
        "`base64': Argument must be a string, a non-negative integer or a list of octets.",
      ),
      Nil,
    )
  }
  let chr64 = symval(q_ear_chr64)
  let mut len = length(bytes)
  let base64 : Array[Char] = Array::make(4 * ((len + 2) / 3), '0')
  let mut k = 0
  let pop = fn() -> Value {
    let x = car(bytes)
    bytes = cdr(bytes)
    x
  }
  while !(bytes is Nil) {
    let b0 = pop()
    let b1 = if bytes is Nil { int(0) } else { pop() }
    let b2 = if bytes is Nil { int(0) } else { pop() }
    let ind = [
      ash(b0, -2),
      logior(logand(ash(b0, 4), int(0x30)), ash(b1, -4)),
      logior(logand(ash(b1, 2), int(0x3c)), ash(b2, -6)),
      logand(b2, int(0x3f)),
    ]
    for i in 0..<4 {
      base64[k] = match aref1(chr64, to_int(ind[i])) {
        Char(c) => c
        _ => '0'
      }
      k += 1
    }
  }
  len = len % 3
  if len != 0 {
    k -= 1
    base64[k] = '='
  }
  if len == 1 {
    k -= 1
    base64[k] = '='
  }
  Str(chars_to_string(base64))
}

///|
fn d_base64_decode(s : Value, rtype? : Value = q_d_string) -> Value raise {
  let err_str = "`base64_decode': Argument must be a base64 encoded string."
  if !stringp(s) {
    merr(err_str, []) |> ignore
  }
  let cs = string_chars(lstring(s))
  let len = cs.length()
  if len < 2 {
    raise LispError::SimpleError(
      "The bounding indices \{len - 2} and NIL are bad for a sequence of length \{len}.",
    )
  }
  let mut nrof_eq = 0
  for c in cs[len - 2:] {
    if c == '=' {
      nrof_eq += 1
    }
  }
  let size = ((3 * len) >> 2) - nrof_eq
  if size < 0 {
    raise LispError::SimpleError(
      "The value \{size} is not of type (MOD 4611686018427387901)",
    )
  }
  let res : Array[Value] = Array::make(size, int(0))
  let w : Array[Int] = Array::make(4, 0)
  let num64 = symval(q_ear_num64)
  let mut bi = 0
  let pop_num = fn() raise {
    // (svref *num64* (pop bytes))
    if bi >= len {
      raise LispError::SimpleError("The value NIL is not of type (MOD 4611686018427387901)")
    }
    let code = cs[bi].to_int()
    bi += 1
    to_int(aref1(num64, code))
  }
  if nrof_eq > 2 || (len & 0x3) != 0 {
    merr(err_str, []) |> ignore
  }
  let mut j = 0
  while true {
    w[0] = pop_num()
    w[1] = pop_num()
    if w[0] == -1 || w[1] == -1 {
      merr(err_str, []) |> ignore
    }
    res[j] = int(((w[0] << 2) & 0xff) | (w[1] >> 4))
    j += 1
    if j == size {
      break
    }
    w[2] = pop_num()
    if w[2] == -1 {
      merr(err_str, []) |> ignore
    }
    res[j] = int(((w[1] << 4) & 0xff) | (w[2] >> 2))
    j += 1
    if j == size {
      break
    }
    w[3] = pop_num()
    if w[3] == -1 {
      merr(err_str, []) |> ignore
    }
    res[j] = int(((w[2] << 6) & 0xff) | w[3])
    j += 1
    if j == size {
      break
    }
  }
  let res = list(res)
  if equal(rtype, q_d_list) {
    cons(list2(q_mlist, q_simp), res)
  } else if equal(rtype, q_d_number) {
    octets_to_number(res)
  } else if equal(rtype, q_d_string) {
    octets_to_string(res)
  } else {
    gf_merror(
      Str(
        "`base64_decode': Optional argument must be 'list, 'number or 'string.",
      ),
      Nil,
    )
  }
}

///|
fn init_share_base64() -> Unit raise {
  // encode :  0 (6bit) --> base64 = *chr64*[0] = 'A' = 65
  let str64 = string_chars(lstring(symval(q_ear_str64)))
  defvar_init(q_ear_chr64, vector(str64.map(c => Value::Char(c))))
  // decode :  'A' = 65 --> *num64*[65] = 0 (6bit); range '+' = 43 ... 'z' = 122
  let num64 : Array[Value] = Array::make(123, int(-1))
  for i, c in str64 {
    num64[c.to_int()] = int(i)
  }
  defvar_init(q_ear_num64, vector(num64))
}

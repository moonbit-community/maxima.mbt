// Port of share/stringproc/md5.lisp: md5sum returns the md5 checksum of a
// string, a non-negative integer, a list of octets or a stream.
//
// The default return value is a string that guarantees 32 hex characters.
// An optional argument allows md5sum to return the corresponding number or
// list of octets.

///|
/// *k5*[i] = (floor (* (abs (sin (+ i 1.0))) #x100000000)), i = 0..63
let share_md5__k : Array[UInt] = [
  0xD76AA478, 0xE8C7B756, 0x242070DB, 0xC1BDCEEE, 0xF57C0FAF, 0x4787C62A, 0xA8304613,
  0xFD469501, 0x698098D8, 0x8B44F7AF, 0xFFFF5BB1, 0x895CD7BE, 0x6B901122, 0xFD987193,
  0xA679438E, 0x49B40821, 0xF61E2562, 0xC040B340, 0x265E5A51, 0xE9B6C7AA, 0xD62F105D,
  0x02441453, 0xD8A1E681, 0xE7D3FBC8, 0x21E1CDE6, 0xC33707D6, 0xF4D50D87, 0x455A14ED,
  0xA9E3E905, 0xFCEFA3F8, 0x676F02D9, 0x8D2A4C8A, 0xFFFA3942, 0x8771F681, 0x6D9D6122,
  0xFDE5380C, 0xA4BEEA44, 0x4BDECFA9, 0xF6BB4B60, 0xBEBFBC70, 0x289B7EC6, 0xEAA127FA,
  0xD4EF3085, 0x04881D05, 0xD9D4D039, 0xE6DB99E5, 0x1FA27CF8, 0xC4AC5665, 0xF4292244,
  0x432AFF97, 0xAB9423A7, 0xFC93A039, 0x655B59C3, 0x8F0CCC92, 0xFFEFF47D, 0x85845DD1,
  0x6FA87E4F, 0xFE2CE6E0, 0xA3014314, 0x4E0811A1, 0xF7537E82, 0xBD3AF235, 0x2AD7D2BB,
  0xEB86D391,
]

///|
let share_md5__s : Array[Int] = [
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 5, 9, 14, 20, 5, 9, 14, 20,
  5, 9, 14, 20, 5, 9, 14, 20, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
]

///|
fn share_md5__u32(v : Value) -> UInt raise {
  to_big(logand(v, Fix(0xffffffffL))).to_uint()
}

///|
fn share_md5__val(u : UInt) -> Value {
  Fix(u.to_uint64().reinterpret_as_int64())
}

///|
fn md5_not(i32 : Value) -> Value raise {
  logand(lognot(i32), Fix(0xffffffffL))
}

///|
fn md5_plus(args : Value) -> Value raise {
  let mut s = int(0)
  for a in args.iter() {
    s = num_add(s, a)
  }
  logand(s, Fix(0xffffffffL))
}

///|
fn md5_left_rotation(i32 : Value, k : Value) -> Value raise {
  let k = to_int(k)
  logior(logand(ash(i32, k), Fix(0xffffffffL)), ash(i32, k - 32))
}

///|
fn md5_worker() -> Value raise {
  let h : Array[UInt] = []
  for v in symval(q_ear_h5).iter() {
    h.push(share_md5__u32(v))
  }
  let w = as_array(symval(q_ear_w5)).data
  let ws : Array[UInt] = []
  for x in w {
    ws.push(share_md5__u32(x))
  }
  let mut a = h[0]
  let mut b = h[1]
  let mut c = h[2]
  let mut d = h[3]
  for i in 0..<64 {
    let (f, g) = if i < 16 {
      ((b & c) | (b.lnot() & d), i)
    } else if i < 32 {
      ((b & d) | (c & d.lnot()), (5 * i + 1) & 0xf)
    } else if i < 48 {
      (b ^ c ^ d, (3 * i + 5) & 0xf)
    } else {
      (c ^ (b | d.lnot()), (7 * i) & 0xf)
    }
    let tmp = d
    d = c
    c = b
    let hlp = a + f + share_md5__k[i] + ws[g]
    let k = share_md5__s[i]
    let hlp = (hlp << k) | (hlp >> (32 - k))
    b = b + hlp
    a = tmp
  }
  let r = [a + h[0], b + h[1], c + h[2], d + h[3]]
  set(q_ear_h5, list(r.map(u => share_md5__val(u))))
}

///|
/// little-endian <--> big-endian
fn swap_endian64(i64 : Value) -> Value raise {
  let mut masq = int(0xff)
  let mut sh = 0
  let mut w : Value = Nil
  while sh != -64 {
    w = cons(ash(logand(i64, masq), sh), w)
    masq = ash(masq, 8)
    sh -= 8
  }
  nreverse(w)
}

///|
fn swap_endian32(i32 : Value) -> Value raise {
  logior(
    logior(
      ash(logand(i32, int(0xff)), 24),
      ash(logand(i32, int(0xff00)), 8),
    ),
    logior(
      ash(logand(i32, int(0xff0000)), -8),
      ash(logand(i32, Fix(0xff000000L)), -24),
    ),
  )
}

///|
/// 32 bit little-endian
fn md5_words(vec : Value) -> Value raise {
  let v = as_array(vec).data
  let w : Array[Value] = []
  let mut inc = -1
  for _ in 0..<16 {
    let b0 = v[inc + 1]
    let b1 = v[inc + 2]
    let b2 = v[inc + 3]
    let b3 = v[inc + 4]
    inc += 4
    w.push(logior(logior(b0, ash(b1, 8)), logior(ash(b2, 16), ash(b3, 24))))
  }
  vector(w)
}

///|
fn md5_update(bytes : Value) -> Value raise {
  set(q_ear_w5, md5_words(vector(list_to_array(bytes)))) |> ignore
  md5_worker()
}

///|
fn md5_final(bytes : Value, off : Value, len : Value) -> Value raise {
  let mut bytes = bytes
  // don't modify bytes
  if bytes.truthy() {
    bytes = append(bytes, list1(int(0x80)))
  }
  if num_eq(off, int(0)) {
    bytes = list1(int(0x80))
  }
  if num_le(off, int(55)) {
    let bits = ash(len, 3)
    let len64 = swap_endian64(bits)
    let pad = list(Array::make(55 - to_int(off), int(0)))
    md5_update(append(bytes, append(pad, len64)))
  } else {
    let pad = list(Array::make(63 - to_int(off), int(0)))
    md5_update(append(bytes, pad)) |> ignore
    md5_final(Nil, int(-1), len)
  }
}

///|
fn md5sum_return(rtype : Value) -> Value raise {
  let h = symval(q_ear_h5)
  if equal(rtype, q_d_list) {
    let c = Collector::new()
    for x in h.iter() {
      c.append_list(word_to_octets(x))
    }
    cons(list2(q_mlist, q_simp), c.result())
  } else if equal(rtype, q_d_number) {
    let mut acc = car(h)
    for y in cdr(h).iter() {
      acc = logior(ash(acc, 32), y)
    }
    acc
  } else if equal(rtype, q_d_string) {
    let sb = StringBuilder::new()
    for x in h.iter() {
      sb.write_string(share_cryptools__hex(x, 8))
    }
    Str(string_downcase(sb.to_string()))
  } else {
    gf_merror(
      Str("`md5sum': Optional argument must be 'list, 'number or 'string."),
      Nil,
    )
  }
}

///|
/// (read-sequence bytes s) into a list of 64 elements: the number of
/// elements read. The port has no binary streams: a character read from a
/// character stream is not an octet.
fn share_md5__read_sequence(s : Value, bytes : Array[Value]) -> Int raise {
  for i in 0..<bytes.length() {
    match read_char(stream=s, eof_value=Nil) {
      Char(c) =>
        raise LispError::SimpleError(
          "The value " + prin1_to_string(Char(c)) + " is not of type (UNSIGNED-BYTE 8)",
        )
      _ => return i
    }
  }
  bytes.length()
}

///|
fn md5sum_stream(s : Value, rtype : Value) -> Value raise {
  set(
    q_ear_h5,
    list([
      Fix(0x67452301L),
      Fix(0xefcdab89L),
      Fix(0x98badcfeL),
      Fix(0x10325476L),
    ]),
  )
  |> ignore
  let bytes : Array[Value] = Array::make(64, Nil)
  let mut len = 0
  let mut len_1 = share_md5__read_sequence(s, bytes)
  while len_1 >= 64 {
    md5_update(list(bytes)) |> ignore
    len = len + len_1
    len_1 = share_md5__read_sequence(s, bytes)
  }
  md5_final(list(bytes[0:len_1].to_array()), int(len_1), int(len + len_1))
  |> ignore
  set(q_ear_h5, mapcar(x => swap_endian32(x), symval(q_ear_h5))) |> ignore
  md5sum_return(rtype)
}

///|
/// (last l n): the last N conses of L.
fn share_md5__last(l : Value, n : Int) -> Value {
  nthcdr((length(l) - n).max(0), l)
}

///|
fn d_md5sum(s : Value, rtype? : Value = q_d_string) -> Value raise {
  let mut bytes = if stringp(s) {
    string_to_octets(s)
  } else if integerp(s) && num_ge(s, int(0)) {
    number_to_octets(s)
  } else if d_listp(s).truthy() {
    cdr(s)
  } else if streamp(s) {
    return md5sum_stream(s, rtype)
  } else {
    gf_merror(
      Str(
        "`md5sum': Argument must be a string, non-negative integer, list of octets, or stream.",
      ),
      Nil,
    )
  }
  let len = length(bytes)
  set(
    q_ear_h5,
    list([
      Fix(0x67452301L),
      Fix(0xefcdab89L),
      Fix(0x98badcfeL),
      Fix(0x10325476L),
    ]),
  )
  |> ignore
  let mut off = len
  while off >= 64 {
    off = off - 64
    md5_update(butlast(bytes, n=off)) |> ignore
    bytes = share_md5__last(bytes, off)
  }
  md5_final(bytes, int(off), int(len)) |> ignore
  set(q_ear_h5, mapcar(x => swap_endian32(x), symval(q_ear_h5))) |> ignore
  md5sum_return(rtype)
}

///|
fn init_share_md5() -> Unit raise {
  defvar_init(q_ear_k5, vector(share_md5__k.map(u => share_md5__val(u))))
  defvar_init(q_ear_s5, vector(share_md5__s.map(n => int(n))))
}

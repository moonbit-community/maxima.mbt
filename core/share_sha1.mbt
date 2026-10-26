// Port of share/stringproc/sha1.lisp: sha1sum, sha256sum and mgf1_sha1
// (pseudorandom number generation according to RFC 3447, appendix B.2.1).

///|
fn share_sha1__u32(v : Value) -> UInt raise {
  to_big(logand(v, Fix(0xffffffffL))).to_uint()
}

///|
fn share_sha1__val(u : UInt) -> Value {
  Fix(u.to_uint64().reinterpret_as_int64())
}

///|
fn sha_not(i32 : Value) -> Value raise {
  logand(lognot(i32), Fix(0xffffffffL))
}

///|
fn sha_plus(args : Value) -> Value raise {
  let mut s = int(0)
  for a in args.iter() {
    s = num_add(s, a)
  }
  logand(s, Fix(0xffffffffL))
}

///|
fn sha_left_rotation(i32 : Value, k : Value) -> Value raise {
  let k = to_int(k)
  logior(logand(ash(i32, k), Fix(0xffffffffL)), ash(i32, k - 32))
}

///|
fn sha_right_rotation(i32 : Value, k : Value) -> Value raise {
  let k = to_int(k)
  logior(ash(i32, -k), logand(ash(i32, 32 - k), Fix(0xffffffffL)))
}

///|
/// The first 32 bits of the fractional parts of the cube roots of the
/// first 64 primes (2,..,311).
let share_sha1__k2 : Array[UInt] = [
  0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B, 0x59F111F1, 0x923F82A4,
  0xAB1C5ED5, 0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3, 0x72BE5D74, 0x80DEB1FE,
  0x9BDC06A7, 0xC19BF174, 0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC, 0x2DE92C6F,
  0x4A7484AA, 0x5CB0A9DC, 0x76F988DA, 0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7,
  0xC6E00BF3, 0xD5A79147, 0x06CA6351, 0x14292967, 0x27B70A85, 0x2E1B2138, 0x4D2C6DFC,
  0x53380D13, 0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85, 0xA2BFE8A1, 0xA81A664B,
  0xC24B8B70, 0xC76C51A3, 0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070, 0x19A4C116,
  0x1E376C08, 0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3,
  0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208, 0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7,
  0xC67178F2,
]

///|
/// Copy a 512 bit message into 16 32 bit big-endian words.
fn share_sha1__words16(vec : Value) -> Array[UInt] raise {
  let v = as_array(vec).data
  let w : Array[UInt] = []
  let mut inc = -1
  for _ in 0..<16 {
    let x = logior(
      logior(ash(v[inc + 1], 24), ash(v[inc + 2], 16)),
      logior(ash(v[inc + 3], 8), v[inc + 4]),
    )
    inc += 4
    w.push(share_sha1__u32(x))
  }
  w
}

///|
fn share_sha1__rotr(x : UInt, k : Int) -> UInt {
  (x >> k) | (x << (32 - k))
}

///|
fn sha256_words(vec : Value) -> Value raise {
  let w = share_sha1__words16(vec)
  // expand:
  for i in 16..<64 {
    let x = w[i - 15]
    let s0 = share_sha1__rotr(x, 7) ^ share_sha1__rotr(x, 18) ^ (x >> 3)
    let y = w[i - 2]
    let s1 = share_sha1__rotr(y, 17) ^ share_sha1__rotr(y, 19) ^ (y >> 10)
    w.push(w[i - 16] + s0 + w[i - 7] + s1)
  }
  set(q_ear_w2, vector(w.map(u => share_sha1__val(u))))
}

///|
fn sha256_worker() -> Value raise {
  let h : Array[UInt] = []
  for v in symval(q_ear_h2).iter() {
    h.push(share_sha1__u32(v))
  }
  let w : Array[UInt] = []
  for v in as_array(symval(q_ear_w2)).data {
    w.push(share_sha1__u32(v))
  }
  let mut a = h[0]
  let mut b = h[1]
  let mut c = h[2]
  let mut d = h[3]
  let mut e = h[4]
  let mut f = h[5]
  let mut g = h[6]
  let mut hh = h[7]
  for i in 0..<64 {
    let s1 = share_sha1__rotr(e, 6) ^
      share_sha1__rotr(e, 11) ^
      share_sha1__rotr(e, 25)
    let t1 = (e & f) ^ (e.lnot() & g)
    let t1 = hh + s1 + t1 + share_sha1__k2[i] + w[i]
    let s2 = share_sha1__rotr(a, 2) ^
      share_sha1__rotr(a, 13) ^
      share_sha1__rotr(a, 22)
    let t2 = (a & b) ^ (a & c) ^ (b & c)
    let t2 = s2 + t2
    hh = g
    g = f
    f = e
    e = d + t1
    d = c
    c = b
    b = a
    a = t1 + t2
  }
  let r = [a, b, c, d, e, f, g, hh]
  for i in 0..<8 {
    r[i] = r[i] + h[i]
  }
  set(q_ear_h2, list(r.map(u => share_sha1__val(u))))
}

///|
fn sha_update(bytes : Value, nr : Value) -> Value raise {
  let bytes = vector(list_to_array(bytes))
  if num_eq(nr, int(160)) {
    sha1_words(bytes) |> ignore
    sha1_worker()
  } else if num_eq(nr, int(256)) {
    sha256_words(bytes) |> ignore
    sha256_worker()
  } else {
    Nil
  }
}

///|
fn sha_len64(bits : Value) -> Value raise {
  let mut bits = bits
  let mut lst : Value = Nil
  for i = 1; ; i = i + 1 {
    lst = cons(logand(bits, int(0xff)), lst)
    if i == 8 {
      return lst
    }
    bits = ash(bits, -8)
  }
}

///|
fn sha_final(bytes : Value, off : Value, len : Value, nr : Value) -> Value raise {
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
    let len64 = sha_len64(bits)
    let pad = list(Array::make(55 - to_int(off), int(0)))
    sha_update(append(bytes, append(pad, len64)), nr)
  } else {
    let pad = list(Array::make(63 - to_int(off), int(0)))
    sha_update(append(bytes, pad), nr) |> ignore
    sha_final(Nil, int(-1), len, nr)
  }
}

// *** SHA1 *******************************************************************

///|
fn sha1_worker() -> Value raise {
  let h : Array[UInt] = []
  for v in symval(q_ear_h1).iter() {
    h.push(share_sha1__u32(v))
  }
  let w : Array[UInt] = []
  for v in as_array(symval(q_ear_w1)).data {
    w.push(share_sha1__u32(v))
  }
  let mut a = h[0]
  let mut b = h[1]
  let mut c = h[2]
  let mut d = h[3]
  let mut e = h[4]
  for i in 0..<80 {
    let (f, k) = if i < 20 {
      ((b & c) | (b.lnot() & d), 0x5a827999U)
    } else if i < 40 {
      (b ^ c ^ d, 0x6ed9eba1U)
    } else if i < 60 {
      ((b & c) | (b & d) | (c & d), 0x8f1bbcdcU)
    } else {
      (b ^ c ^ d, 0xca62c1d6U)
    }
    let tmp = ((a << 5) | (a >> 27)) + f + e + k + w[i]
    e = d
    d = c
    c = (b << 30) | (b >> 2)
    b = a
    a = tmp
  }
  let r = [a, b, c, d, e]
  for i in 0..<5 {
    r[i] = r[i] + h[i]
  }
  set(q_ear_h1, list(r.map(u => share_sha1__val(u))))
}

///|
fn sha1_words(vec : Value) -> Value raise {
  let w = share_sha1__words16(vec)
  // expand:
  for i in 16..<80 {
    let x = w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]
    w.push((x << 1) | (x >> 31))
  }
  set(q_ear_w1, vector(w.map(u => share_sha1__val(u))))
}

///|
/// The octets of a sha1sum/sha256sum argument.
fn share_sha1__bytes(s : Value, name : String) -> Value raise {
  if stringp(s) {
    string_to_octets(s)
  } else if integerp(s) && num_ge(s, int(0)) {
    number_to_octets(s)
  } else if d_listp(s).truthy() {
    cdr(s)
  } else {
    gf_merror(
      Str(
        "`" + name +
        "': Argument must be a string, a non-negative integer or a list of octets.",
      ),
      Nil,
    )
  }
}

///|
/// Hash BYTES with the SHA function NR (160 or 256).
fn share_sha1__digest(bytes : Value, nr : Int) -> Unit raise {
  let mut bytes = bytes
  let len = length(bytes)
  let mut off = len
  while off >= 64 {
    off = off - 64
    sha_update(butlast(bytes, n=off), int(nr)) |> ignore
    bytes = nthcdr((length(bytes) - off).max(0), bytes)
  }
  sha_final(bytes, int(off), int(len), int(nr)) |> ignore
}

///|
fn share_sha1__return(h : Value, rtype : Value, name : String) -> Value raise {
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
      Str("`" + name + "': Optional argument must be 'list, 'number or 'string."),
      Nil,
    )
  }
}

///|
fn d_sha1sum(s : Value, rtype? : Value = q_d_string) -> Value raise {
  let bytes = share_sha1__bytes(s, "sha1sum")
  set(
    q_ear_h1,
    list([
      Fix(0x67452301L),
      Fix(0xefcdab89L),
      Fix(0x98badcfeL),
      Fix(0x10325476L),
      Fix(0xc3d2e1f0L),
    ]),
  )
  |> ignore
  share_sha1__digest(bytes, 160)
  share_sha1__return(symval(q_ear_h1), rtype, "sha1sum")
}

// *** MGF1_SHA1 **************************************************************

///|
fn d_mgf1_sha1(seed : Value, len : Value, rtype? : Value = q_d_number) -> Value raise {
  let err_msg : Value = Str("Unsuitable arguments to `mgf1_sha1': ~m, ~m")
  let s = if integerp(seed) && num_ge(seed, int(0)) {
    number_to_octets(seed)
  } else if d_listp(seed).truthy() {
    cdr(seed)
  } else {
    gf_merror(err_msg, list([seed, len]))
  }
  if !(integerp(len) && num_gt(len, int(0))) {
    gf_merror(err_msg, list([seed, len])) |> ignore
  }
  let ii = num_ceiling(Flo(to_double(len) / 20.0)).0
  let c = Collector::new()
  for i in 0..<to_int(ii) {
    let s_i = cons(list2(q_mlist, q_simp), append(s, word_to_octets(int(i))))
    c.append_list(cdr(d_sha1sum(s_i, rtype=q_d_list)))
  }
  let res = c.result()
  let n = to_int(len)
  if length(res) < n {
    raise LispError::SimpleError(
      "The bounding indices 0 and \{n} are bad for a sequence of length \{length(res)}.",
    )
  }
  let res = firstn(len, res)
  if equal(rtype, q_d_number) {
    octets_to_number(res)
  } else if equal(rtype, q_d_list) {
    cons(list2(q_mlist, q_simp), res)
  } else {
    gf_merror(
      Str("`mgf1_sha1': Optional argument must be 'number or 'list."),
      Nil,
    )
  }
}

// *** SHA256 *****************************************************************

///|
fn d_sha256sum(s : Value, rtype? : Value = q_d_string) -> Value raise {
  let bytes = share_sha1__bytes(s, "sha256sum")
  // the first 32 bits of the fractional parts of the square roots of the
  // first 8 primes (2,..,19)
  set(
    q_ear_h2,
    list([
      Fix(0x6a09e667L),
      Fix(0xbb67ae85L),
      Fix(0x3c6ef372L),
      Fix(0xa54ff53aL),
      Fix(0x510e527fL),
      Fix(0x9b05688cL),
      Fix(0x1f83d9abL),
      Fix(0x5be0cd19L),
    ]),
  )
  |> ignore
  share_sha1__digest(bytes, 256)
  share_sha1__return(symval(q_ear_h2), rtype, "sha256sum")
}

///|
fn init_share_sha1() -> Unit raise {
  defvar_init(q_ear_k2, vector(share_sha1__k2.map(u => share_sha1__val(u))))
}

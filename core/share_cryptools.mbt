// Port of share/stringproc/cryptools.lisp: tools for cryptography.
//
//  1. string_to_octets(string [,encoding]), octets_to_string(octets [,enc])
//  2. number_to_octets(number), octets_to_number(octets)
//  3. octets_to_oid(octets), oid_to_octets(string): object identifiers
//  4. crc24sum(octets): the crc24 checksum of an octet list (OpenPGP)
//
// The encoder/decoder of external formats is the one of stringproc
// (share_stringproc__encode_chars / share_stringproc__decode_bytes).

///|
/// Hexadecimal digits of the integer N (upper case), left padded with #\0
/// to WIDTH: (format nil "~width,'0x" n).
fn share_cryptools__hex(n : Value, width : Int) -> String raise {
  let s = string_upcase(to_big(n).to_string(radix=16))
  "0".repeat((width - s.length()).max(0)) + s
}

// -- string-octet-conversions: ----------------------------------------------

///|
fn d_string_to_octets(str : Value, enc? : Value = Nil) -> Value raise {
  if !stringp(str) {
    gf_merror(Str("`string_to_octets': argument must be a string."), Nil)
    |> ignore
  }
  cons(list2(q_mlist, q_simp), string_to_octets(str, enc~))
}

///|
fn string_to_octets(str : Value, enc? : Value = Nil) -> Value raise {
  let enc = get_encoding(enc, Str("string_to_octets"))
  let ov = share_stringproc__encode_chars(string_chars(lstring(str)), enc)
  list(ov.map(b => int(b)))
}

///|
fn d_octets_to_string(ol : Value, enc? : Value = Nil) -> Value raise {
  if !d_listp(ol).truthy() {
    gf_merror(Str("`octets_to_string': argument must be a list of octets."), Nil)
    |> ignore
  }
  octets_to_string(cdr(ol), enc~)
}

///|
fn octets_to_string(ol : Value, enc? : Value = Nil) -> Value raise {
  let enc = get_encoding(enc, Str("octets_to_string"))
  // (map-into (make-array (length ol) :element-type '(unsigned-byte 8)) ...)
  let ov : Array[Int] = []
  for o in ol.iter() {
    match o {
      Fix(n) if n >= 0L && n < 256L => ov.push(n.to_int())
      _ =>
        raise LispError::SimpleError(
          "The value " + prin1_to_string(o) + " is not of type (UNSIGNED-BYTE 8)",
        )
    }
  }
  Str(chars_to_string(share_stringproc__decode_bytes(ov, enc)))
}

// -- number-octet-conversions: ----------------------------------------------

///|
/// Assume that n fits into a word.
fn word_to_octets(n : Value) -> Value raise {
  let mut n = n
  let mut octs : Value = Nil
  for _ in 0..<4 {
    octs = cons(logand(n, int(0xff)), octs)
    n = ash(n, -8)
  }
  octs
}

///|
fn number_to_octets(n : Value) -> Value raise {
  let mut n = n
  let mut octs : Value = Nil
  while true {
    octs = cons(logand(n, int(0xff)), octs)
    n = ash(n, -8)
    if num_eq(n, int(0)) {
      break
    }
  }
  octs
}

///|
fn octets_to_number(octs : Value) -> Value raise {
  // (reduce #'(lambda (x y) (logior (ash x 8.) y)) octs)
  if octs is Nil {
    raise LispError::SimpleError(
      "invalid number of arguments: 0",
    )
  }
  let mut acc = car(octs)
  for y in cdr(octs).iter() {
    acc = logior(ash(acc, 8), y)
  }
  acc
}

///|
fn d_number_to_octets(n : Value) -> Value raise {
  if !(integerp(n) && num_ge(n, int(0))) {
    gf_merror(
      Str("`number_to_octets': Argument must be a non-negative integer."),
      Nil,
    )
    |> ignore
  }
  cons(list2(q_mlist, q_simp), number_to_octets(n))
}

///|
fn d_octets_to_number(octs : Value) -> Value raise {
  if !d_listp(octs).truthy() {
    gf_merror(
      Str("`octets_to_number': Argument must be a list of octets."),
      Nil,
    )
    |> ignore
  }
  octets_to_number(cdr(octs))
}

// -- object identifiers (OID): ----------------------------------------------
//
// 1.2.840.113549.1.1.1    -  RSA encryption
// 1.3.14.3.2.26           -  SHA-1 hash algorithm
// 2.16.840.1.101.3.4.2.1  -  SHA-256 hash algorithm
// 1.3.132.0.6             -  secp112r1 - SEC 2 recommended elliptic curve

///|
fn oid_number_to_7bit(n : Value) -> Value raise {
  let mut n = n
  let mut lst : Value = Nil
  while true {
    lst = cons(logand(n, int(127)), lst)
    n = ash(n, -7)
    if num_eq(n, int(0)) {
      break
    }
  }
  lst = nreverse(lst)
  let mut res = list1(car(lst))
  for bit7 in cdr(lst).iter() {
    res = cons(logior(bit7, int(128)), res)
  }
  res
}

///|
/// (read a) of a component with *read-base* 10.
fn share_cryptools__read_number(s : Value) -> Value raise {
  let x = lread(lstring(s))
  if !numberp(x) {
    raise LispError::SimpleError(
      "The value " + prin1_to_string(x) + " is not of type NUMBER",
    )
  }
  x
}

///|
fn oid_to_octets(str : Value) -> Value raise {
  // stringproc.lisp/split
  let lst = mapcar(s => share_cryptools__read_number(s), split(str, Str(".")))
  if length(lst) < 2 {
    gf_merror(Str("No valid OID: ~m"), list([str])) |> ignore
  }
  let oct = num_add(num_mul(int(40), car(lst)), cadr(lst))
  let mut octs = list1(oct)
  for n in cddr(lst).iter() {
    octs = append(octs, oid_number_to_7bit(n))
  }
  octs
}

///|
fn d_oid_to_octets(str : Value) -> Value raise {
  cons(list2(q_mlist, q_simp), oid_to_octets(str))
}

///|
fn oid_split(lst : Value) -> (Value, Value) raise {
  let mut lst = lst
  let mut res : Value = Nil
  while true {
    let n = car(lst)
    res = cons(n, res)
    lst = cdr(lst)
    if lst is Nil || !logbitp(7, n) {
      break
    }
  }
  (nreverse(res), lst)
}

///|
fn octets_to_oid_1(lst : Value) -> Value raise {
  let mut res = int(0)
  for n in lst.iter() {
    res = logior(logand(n, int(127)), res)
    if !logbitp(7, n) {
      return res
    }
    res = ash(res, 7)
  }
  Nil
}

///|
fn octets_to_oid(lst : Value) -> Value raise {
  if length(lst) == 0 {
    return Str("")
  }
  with_special(q_ear_print_base, int(10), () => {
    let tmp = car(lst)
    let mut lst = cdr(lst)
    let (q, r) = num_truncate(tmp, b=int(40))
    let mut str = d_sconcat(list([q, Str("."), r]))
    while !(lst is Nil) {
      let (tmp, rest) = oid_split(lst)
      lst = rest
      str = d_sconcat(list([str, Str("."), octets_to_oid_1(tmp)]))
    }
    str
  })
}

///|
fn d_octets_to_oid(octets : Value) -> Value raise {
  octets_to_oid(cdr(octets))
}

// -- CRC24 checksum: ---------------------------------------------------------

///|
fn crc24sum(lst : Value) -> Value raise {
  let mut r = int(0xb704ce)
  let poly = int(0x1864cfb)
  for oct in lst.iter() {
    r = logxor(r, ash(oct, 16))
    for _ in 0..<8 {
      r = ash(r, 1)
      if logbitp(24, r) {
        r = logxor(r, poly)
      }
    }
  }
  r
}

///|
fn d_crc24sum(octets : Value, rtype? : Value = q_d_string) -> Value raise {
  if d_listp(octets).truthy() {
    let crc24 = crc24sum(cdr(octets))
    if equal(rtype, q_d_list) {
      cons(list2(q_mlist, q_simp), number_to_octets(crc24))
    } else if equal(rtype, q_d_number) {
      crc24
    } else if equal(rtype, q_d_string) {
      Str(string_downcase(share_cryptools__hex(crc24, 6)))
    } else {
      gf_merror(
        Str("`crc24sum': Optional argument must be 'list, 'number or 'string."),
        Nil,
      )
    }
  } else {
    gf_merror(Str("`crc24sum': Argument must be a list of octets."), Nil)
  }
}

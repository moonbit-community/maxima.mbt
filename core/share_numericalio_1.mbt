// Port of share/numericalio/encode-decode-float.lisp (Robert Dodier, 2007):
// encode 64 bit IEEE 754 floats as integers and back, and read/write
// unsigned integers and floats on binary streams.
//
// The port has no binary streams of its own: a binary stream is a character
// stream whose characters are the octets (codes 0..255), opened by
// $openr_binary / $openw_binary / $opena_binary or by numericalio itself
// (see share_numericalio__binary_* below).

///|
/// (ldb (byte size pos) x)
fn share_numericalio__ldb(size : Int, pos : Int, x : Value) -> Value raise {
  logand(ash(x, -pos), num_sub(ash(Fix(1L), size), Fix(1L)))
}

///|
/// (dpb new (byte size pos) x)
fn share_numericalio__dpb(
  new : Value,
  size : Int,
  pos : Int,
  x : Value,
) -> Value raise {
  let mask = num_sub(ash(Fix(1L), size), Fix(1L))
  logior(
    logand(x, lognot(ash(mask, pos))),
    ash(logand(new, mask), pos),
  )
}

///|
fn smash_float_into_integer(x : Value) -> Value raise {
  let (significand, exponent, sign) = match x {
    Flo(d) => integer_decode_float(d)
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(x) + " is not of type FLOAT",
      )
  }
  // This logic cannot be guaranteed to work -- there is no necessary
  // correlation between IEEE 754 and CL floats. All port floats are doubles.
  smash_decoded_float_64_into_integer(
    from_big(significand),
    int(exponent),
    int(sign),
  )
}

///|
fn smash_decoded_float_32_into_integer(
  significand : Value,
  exponent : Value,
  sign : Value,
) -> Value raise {
  if num_eq(significand, Fix(0L)) {
    Fix(0L)
  } else {
    share_numericalio__dpb(
      if num_gt(sign, Fix(0L)) {
        Value::Fix(0L)
      } else {
        Value::Fix(1L)
      },
      1,
      23 + 8,
      share_numericalio__dpb(
        num_add(exponent, Fix(127L + 23L)),
        8,
        23,
        share_numericalio__ldb(23, 0, significand),
      ),
    )
  }
}

///|
fn construct_float_32_from_integer(x : Value) -> Value raise {
  let (significand, exponent, sign) = extract_smashed_float_32_from_integer(x)
  num_mul(
    sign,
    Flo(scale_float(to_double(lfloat(significand)), to_int(exponent))),
  )
}

///|
fn extract_smashed_float_32_from_integer(
  x : Value,
) -> (Value, Value, Value) raise {
  if eql(x, Fix(0L)) {
    (Fix(0L), Fix(0L), Fix(0L))
  } else {
    let significand = share_numericalio__dpb(x, 23, 0, Fix(0x800000L))
    let exponent = num_sub(share_numericalio__ldb(8, 23, x), Fix(127L + 23L))
    let sign = if eql(share_numericalio__ldb(1, 31, x), Fix(0L)) {
      Value::Fix(1L)
    } else {
      Value::Fix(-1L)
    }
    (significand, exponent, sign)
  }
}

///|
fn smash_decoded_float_64_into_integer(
  significand : Value,
  exponent : Value,
  sign : Value,
) -> Value raise {
  if num_eq(significand, Fix(0L)) {
    Fix(0L)
  } else {
    share_numericalio__dpb(
      if num_gt(sign, Fix(0L)) {
        Value::Fix(0L)
      } else {
        Value::Fix(1L)
      },
      1,
      52 + 11,
      share_numericalio__dpb(
        num_add(exponent, Fix(1023L + 52L)),
        11,
        52,
        share_numericalio__ldb(52, 0, significand),
      ),
    )
  }
}

///|
fn construct_float_64_from_integer(x : Value) -> Value raise {
  let (significand, exponent, sign) = extract_smashed_float_64_from_integer(x)
  num_mul(
    sign,
    Flo(scale_float(to_double(lfloat(significand)), to_int(exponent))),
  )
}

///|
fn extract_smashed_float_64_from_integer(
  x : Value,
) -> (Value, Value, Value) raise {
  if eql(x, Fix(0L)) {
    (Fix(0L), Fix(0L), Fix(0L))
  } else {
    let significand = share_numericalio__dpb(
      x,
      52,
      0,
      Fix(0x10000000000000L),
    )
    let exponent = num_sub(
      share_numericalio__ldb(11, 52, x),
      Fix(1023L + 52L),
    )
    let sign = if eql(share_numericalio__ldb(1, 63, x), Fix(0L)) {
      Value::Fix(1L)
    } else {
      Value::Fix(-1L)
    }
    (significand, exponent, sign)
  }
}

// Stream input and output

///|
fn write_float(x : Value, s : Value) -> Value raise {
  write_unsigned_integer(smash_float_into_integer(x), size_in_bytes(x), s)
}

///|
fn size_in_bytes(x : Value) -> Value raise {
  // AUGHHHH!! THIS IS TERRIBLE!
  if floatp(x) {
    Fix(8L)
  } else {
    Fix(4L)
  }
}

///|
fn read_float_64(s : Value) -> Value raise {
  let x = read_unsigned_integer(Fix(8L), s)
  if eq(x, q_eof) {
    q_eof
  } else {
    construct_float_64_from_integer(x)
  }
}

///|
fn define_external_byte_order(x : Value) -> Value raise {
  if !(eq(x, q_kw_msb) || eq(x, q_kw_lsb)) {
    raise LispError::SimpleError(
      "The value of X is " + prin1_to_string(x) +
      ", which is not of type EXTERNAL-BYTE-ORDER.",
    )
  }
  set(q_ear_external_byte_order, x)
}

///|
/// Read an unsigned integer of size NB-BYTES bytes from input stream S.
fn read_unsigned_integer(nb_bytes : Value, s : Value) -> Value raise {
  if num_eq(nb_bytes, Fix(0L)) {
    return Fix(0L)
  }
  let bytes : Array[Value] = []
  for _ in 0..<to_int(nb_bytes) {
    let x = share_numericalio__read_byte(s)
    if eq(x, q_eof) {
      return q_eof
    }
    bytes.push(x)
  }
  let mut y : Value = Fix(0L)
  let order = symval(q_ear_external_byte_order)
  if eq(order, q_kw_lsb) {
    bytes.rev_in_place()
  }
  if eq(order, q_kw_lsb) || eq(order, q_kw_msb) {
    for x in bytes {
      y = num_add(x, ash(y, 8))
    }
  }
  y
}

///|
/// Write an unsigned integer of size NB-BYTES bytes to output stream S.
fn write_unsigned_integer(
  quantity : Value,
  nb_bytes : Value,
  s : Value,
) -> Value raise {
  let order = symval(q_ear_external_byte_order)
  if eq(order, q_kw_lsb) {
    if !num_eq(nb_bytes, Fix(0L)) {
      share_numericalio__write_byte(logand(quantity, Fix(0xffL)), s)
      write_unsigned_integer(
        ash(quantity, -8),
        num_sub(nb_bytes, Fix(1L)),
        s,
      )
      |> ignore
    }
  } else if eq(order, q_kw_msb) {
    if !num_eq(nb_bytes, Fix(0L)) {
      write_unsigned_integer(
        ash(quantity, -8),
        num_sub(nb_bytes, Fix(1L)),
        s,
      )
      |> ignore
      share_numericalio__write_byte(logand(quantity, Fix(0xffL)), s)
    }
  }
  Nil
}

///|
fn init_share_encode_decode_float() -> Unit raise {
  // (defvar *external-byte-order* :msb): set by init_vars.
  ()
}

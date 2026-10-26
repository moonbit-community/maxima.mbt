// Port of src/float.lisp, part 1: the bigfloat representation and the
// basic arithmetic (rounding, shifting, +, -, *, /, powers, roots).
//
// EXPERIMENTAL BIGFLOAT PACKAGE VERSION 2- USING BINARY MANTISSA AND
// POWER-OF-2 EXPONENT.  EXPONENTS MAY BE BIG NUMBERS.
//
// Representation of a Bigfloat:  ((BIGFLOAT SIMP precision) mantissa exponent)
// precision -- number of bits of precision in the mantissa.
//              precision = (integer-length mantissa)
// mantissa -- a signed integer representing a fractional portion computed by
//             fraction = (// mantissa (^ 2 precision)).
// exponent -- a signed integer representing the scale of the number.
//             The actual number represented is (* fraction (^ 2 exponent)).
//
// Internal specials: *M is set by FPROUND to the number of binary digits its
// input had to be shifted right to be aligned into the mantissa (a second
// return value).  *DECFP is true when the computation is done in decimal
// radix (only during output).

///|
fn float__prec() -> Value {
  symval(q_fpprec)
}

///|
fn float__iprec() -> Int raise {
  to_int(symval(q_fpprec))
}

///|
fn float__decfp() -> Bool {
  symval(q_n_stardecfp).truthy()
}

///|
/// `(ash x n)` for an arbitrary integer shift count N.
fn float__ash(x : Value, n : Value) -> Value raise {
  match n {
    Fix(k) if k >= -2147483647L && k <= 2147483647L => ash(x, k.to_int())
    _ =>
      if minusp(n) {
        if minusp(x) {
          Fix(-1L)
        } else {
          Fix(0L)
        }
      } else if zerop(x) {
        Fix(0L)
      } else {
        raise LispError::SimpleError("ash: shift count too large")
      }
  }
}

///|
/// Maclisp QUOTIENT (clmacs.lisp QUOT): TRUNCATE for integers, else `/`.
fn float__quot(a : Value, b : Value) -> Value raise {
  if integerp(a) && integerp(b) {
    num_truncate(a, b~).0
  } else {
    num_div(a, b)
  }
}

///|
/// `(- a b)` etc. on integers given as Value and Int.
fn float__addi(a : Value, n : Int) -> Value raise {
  num_add(a, int(n))
}

///|
/// The widest byte whose mask is certainly a fixnum.
fn float__hipart_fixnum_width() -> Int raise {
  logcount(most_positive_fixnum)
}

///|
fn float__machine_fixnum_precision() -> Int raise {
  integer_length(most_positive_fixnum)
}

///|
fn hipart(x : Value, nn : Value) -> Value raise {
  if bignump(nn) {
    num_abs(x)
  } else {
    haipart(x, nn)
  }
}

///|
/// Equivalent to (ZEROP (HIPART ...)), but cheaper in common cases.
fn hipart_zerop(x : Value, nn : Value) -> Value raise {
  if zerop(x) {
    // HIPART of 0 is always 0 for all NN.
    t
  } else if !minusp(nn) {
    // NN >= 0: The NN most significant bits of X # 0 vanish only when NN = 0.
    lbool(zerop(nn))
  } else {
    // NN < 0, so let K = -NN: are the K least significant bits of X zero?
    let k = num_neg(nn)
    let w = float__hipart_fixnum_width()
    if num_le(k, int(w)) {
      lbool(zerop(logand(x, one_minus(float__ash(Fix(1L), k)))))
    } else if !zerop(logand(x, one_minus(ash(Fix(1L), w)))) {
      Nil
    } else if num_lt(int(integer_length(x)), k) {
      // |X| < 2^K means the low K bits are all of X, which is non-zero.
      Nil
    } else {
      lbool(zerop(logand(x, one_minus(float__ash(Fix(1L), k)))))
    }
  }
}

///|
fn fpprec1(assign_var : Value, q : Value) -> Value raise {
  ignore(assign_var)
  if !fixnump(q) || num_lt(q, Fix(1L)) {
    merr("fpprec: value must be a positive integer; found: ~M", [q]) |> ignore
  }
  set(q_fpprec, int(2 + integer_length(expt(Fix(10L), q)))) |> ignore
  set(q_ear_bigfloatone, d_bfloat(Fix(1L))) |> ignore
  set(q_ear_bigfloatzero, d_bfloat(Fix(0L))) |> ignore
  let one = symval(q_ear_bigfloatone)
  set(q_ear_bfhalf, list([car(one), cadr(one), Fix(0L)])) |> ignore
  set(q_ear_bfmhalf, list([car(one), num_neg(cadr(one)), Fix(0L)])) |> ignore
  q
}

///|
/// Assume that X has the form ((BIGFLOAT ... <prec>) ...).  Return <prec>.
fn bigfloat_prec(x : Value) -> Value raise {
  car(last(car(x)))
}

///|
/// Tells you if you have a bigfloat object.  BUT, if it is a bigfloat, it
/// will normalize it by making the precision of the bigfloat match the
/// current precision setting in fpprec, and convert bogus zeroes (mantissa
/// zero, exponent not) to a true zero.
fn bigfloatp(x0 : Value) -> Value raise {
  let mut x = x0
  if !d_bfloatp(x).truthy() {
    return Nil
  }
  let x_prec = bigfloat_prec(x)
  let prec = float__prec()
  if num_eq(prec, x_prec) {
    // Precision matches.
    return x
  } else if num_gt(prec, x_prec) {
    // Current precision is higher than bigfloat precision.  Scale up
    // mantissa and adjust exponent to get the correct precision.
    x = bcons(list([fpshift(cadr(x), num_sub(prec, x_prec)), caddr(x)]))
  } else {
    // Current precision is LOWER than bigfloat precision.  Round the number
    // to the desired precision.
    let m = fpround(cadr(x))
    let e = num_sub(
      num_add(num_add(caddr(x), symval(q_n_starm)), prec),
      x_prec,
    )
    x = bcons(list([m, e]))
  }
  // Fix up any bogus zeros that we might have created.
  if equal(cadr(x), Fix(0L)) {
    bcons(list([Fix(0L), Fix(0L)]))
  } else {
    x
  }
}

///|
/// CL FLOAT-PRECISION of a double.
fn float__float_precision(d : Double) -> Int {
  if d == 0.0 {
    0
  } else {
    let (m, _, _) = integer_decode_float(d)
    m.bit_length()
  }
}

///|
/// Convert a floating point number into a bigfloat.
fn floattofp(x : Value) -> Value raise {
  if float_nan_p(x).truthy() {
    merr(
      "bfloat: attempted conversion of floating point NaN (not-a-number).~%",
      [],
    )
    |> ignore
  }
  if float_inf_p(x).truthy() {
    merr("bfloat: attempted conversion of floating-point infinity.~%", [])
    |> ignore
  }
  let d = to_double(x)
  if !symval(q_d_float2bf).truthy() {
    let p = float__float_precision(d)
    if num_lt(float__prec(), int(p)) {
      mtell(list([Str("bfloat: converting float ~S to bigfloat.~%"), x]))
      |> ignore
    }
  }
  // A bigfloat zero needs to have an exponent and mantissa of zero.
  if zerop(x) {
    list([Fix(0L), Fix(0L)])
  } else {
    let (frac, exp, sign) = integer_decode_float(d)
    let fracv = from_big(frac)
    // Scale frac to the desired number of bits, and adjust the exponent
    // accordingly.
    let scale = num_sub(float__prec(), int(integer_length(fracv)))
    list([
      float__ash(num_mul(int(sign), fracv), scale),
      num_add(float__prec(), num_sub(int(exp), scale)),
    ])
  }
}

///|
/// Convert a bigfloat into a floating point number.
fn fp2flo(l : Value) -> Value raise {
  let precision = bigfloat_prec(l)
  let mantissa0 = cadr(l)
  let exponent = caddr(l)
  let mmp = symval(q_machine_mantissa_precision)
  with_specials([(q_fpprec, mmp), (q_n_starm, Fix(0L))], () => {
    // Round the mantissa to the number of bits of precision of the machine,
    // and then convert it to a floating point fraction: 0.5 <= mantissa < 1
    let mantissa = float__quot(fpround(mantissa0), expt(Flo(2.0), mmp))
    // 0.5 <= mantissa < 1.  The largest double-float is .999999 * 2^1024.
    // So if the exponent is 1025 or higher, we have an overflow.
    let e = num_add(
      num_add(num_add(exponent, num_neg(precision)), symval(q_n_starm)),
      mmp,
    )
    if num_ge(e, Fix(1025L)) {
      merr("float: floating point overflow converting ~:M", [l])
    } else {
      let ei = if num_lt(e, Fix(-100000L)) { -100000 } else { to_int(e) }
      Flo(scale_float(to_double(mantissa), ei))
    }
  })
}

///|
/// New machine-independent version of FIXFLOAT.
fn fixfloat(x : Value) -> Value raise {
  with_special(
    q_d_ratepsilon,
    expt(Flo(2.0), num_neg(symval(q_machine_mantissa_precision))),
    () => maxima_rationalize(x),
  )
}

///|
fn bcons(s : Value) -> Value raise {
  let prec = float__prec()
  if !eql(prec, symval(q_ear_bfloat_header_prec)) {
    // Precision was changed, make a new header.
    set(q_ear_bfloat_header, list([q_bigfloat, q_simp, prec])) |> ignore
    set(q_ear_bfloat_header_prec, prec) |> ignore
  }
  cons(symval(q_ear_bfloat_header), s)
}

///|
fn d_bfloat(x : Value) -> Value raise {
  let r = bigfloatp(x)
  if r.truthy() {
    return r
  }
  if eq(x, q_d__pcti) {
    // Return 1.0b0*%i rather than %i, so that the simplifier evaluates
    // f(%i) numerically, as $FLOAT does with 1.0*%i.
    return mul2(d_bfloat(Fix(1L)), q_d__pcti)
  }
  if numberp(x) || memq(x, symval(q_ear_builtin_numeric_constants)).truthy() {
    return bcons(intofp(x))
  }
  if atom(x) || memq(q_array, cdar(x)).truthy() {
    return x
  }
  let op = caar(x)
  if eq(op, q_mexpt) {
    if equal(cadr(x), q_d__pcte) {
      n_starfpexp(d_bfloat(caddr(x)))
    } else {
      exptbigfloat(d_bfloat(cadr(x)), caddr(x))
    }
  } else if eq(op, q_mncexpt) {
    mk(q_mncexpt, [d_bfloat(cadr(x)), caddr(x)])
  } else if eq(op, q_rat) {
    ratbigfloat(cdr(x))
  } else if eq(op, q_mtimes) && eql(cadr(x), Fix(-1L)) && cddr(x).truthy() {
    // -X reaches us as ((MTIMES) -1 X).  Negating the result is a sign flip
    // and much cheaper than a full precision multiplication by -1.
    let args = mapcar(a => d_bfloat(a), cddr(x))
    let fun = get(q_mtimes, q_floatprog)
    let prod = funcall(fun, [args])
    if d_bfloatp(prod).truthy() {
      bcons(fpminus(cdr(prod)))
    } else {
      funcall(fun, [cons(d_bfloat(Fix(-1L)), args)])
    }
  } else {
    let y = safe_get(op, q_floatprog)
    if y.truthy() {
      funcall(y, [mapcar(a => d_bfloat(a), cdr(x))])
    } else if trigp(op).truthy() || arcp(op).truthy() || eq(op, q_d_entier) {
      let y = d_bfloat(cadr(x))
      if d_bfloatp(y).truthy() {
        if eq(op, q_d_entier) {
          d_entier(y)
        } else if eq(op, q_p_acot) && zerop1(y).truthy() {
          d_bfloat(div(q_d__pctpi, Fix(2L)))
        } else if eq(op, q_p_acoth) && zerop1(y).truthy() {
          d_bfloat(div(mul2(q_d__pcti, q_d__pctpi), Fix(-2L)))
        } else if zerop1(y).truthy() &&
          memq(op, list([q_p_acsc, q_p_acsch, q_p_asec, q_p_asech])).truthy() {
          // These are computed from 1/y, so catch a zero argument.
          domain_error(y, op)
        } else if arcp(op).truthy() {
          let y2 = d_bfloat(logarc(op, y))
          if free(y2, q_d__pcti).truthy() {
            y2
          } else {
            with_special(q_d_ratprint, Nil, () => fparcsimp(d_rectform(y2)))
          }
        } else if eq(op, q_p_sec) {
          // sec(x) = 1/cos(x).  cos(x) /= 0 for any bfloat value of x.
          invertbigfloat(d_bfloat(list2(ncons(safe_get(op, q_recip)), y)))
        } else if eq(op, q_p_cot) || eq(op, q_p_csc) {
          // cot(x) = 1/tan(x) and csc(x) = 1/sin(x), but x = 0 is not in
          // the domain.
          if zerop1(second(x)).truthy() {
            domain_error(second(x), op) |> ignore
          }
          invertbigfloat(d_bfloat(list2(ncons(safe_get(op, q_recip)), y)))
        } else {
          d_bfloat(exponentialize(op, y))
        }
      } else {
        subst0(list2(ncons(op), y), x)
      }
    } else {
      recur_apply(q_d_bfloat, x)
    }
  }
}

///|
fn addbigfloat(h : Value) -> Value raise {
  let tst = symval(q_ear_bigfloatzero)
  let mut fans = tst
  let mut nfans : Value = Nil
  for e in h.iter() {
    let r = bigfloatp(e)
    if r.truthy() {
      fans = bcons(fpplus(cdr(r), cdr(fans)))
    } else {
      nfans = cons(e, nfans)
    }
  }
  nfans = nreverse(nfans)
  if nfans is Nil {
    fans
  } else if equal(fans, tst) {
    simplify(cons(list1(q_mplus), nfans))
  } else {
    simplify(cons(list1(q_mplus), cons(fans, nfans)))
  }
}

///|
/// R is a Maxima ratio, represented as a list of the numerator and
/// denominator.  FLOAT-RATIO doesn't like it if the numerator is 0.
fn ratbigfloat(r : Value) -> Value raise {
  if zerop(car(r)) {
    bcons(list([Fix(0L), Fix(0L)]))
  } else {
    bcons(float_ratio(r))
  }
}

///|
/// Borrowed from CMUCL (float-ratio-float), modified for converting ratios
/// to Maxima's bfloat numbers.
fn float_ratio(x : Value) -> Value raise {
  let signed_num = first(x)
  let plusp_ = plusp(signed_num)
  let num = if plusp_ { signed_num } else { num_neg(signed_num) }
  let mut den = second(x)
  let digits = float__iprec()
  let mut scale = 0
  // Strip any trailing zeros from the denominator and move it into the
  // scale factor (to minimize the size of the operands.)
  let den_twos = integer_length(logxor(den, one_minus(den))) - 1
  scale -= den_twos
  den = ash(den, -den_twos)
  // Guess how much we need to scale by from the magnitudes of the numerator
  // and denominator.  We want one extra bit for a guard bit.
  let num_len = integer_length(num)
  let den_len = integer_length(den)
  let delta = den_len - num_len
  let shift = 1 + (delta + digits)
  let mut shifted_num = ash(num, shift)
  scale -= delta
  let sign : Value = if plusp_ { Fix(1L) } else { Fix(-1L) }
  fn float_and_scale(bits0 : Value, scale : Int) -> Value raise {
    let bits = ash(bits0, -1)
    let len = integer_length(bits)
    if len > digits {
      list([num_mul(sign, ash(bits, -1)), int(0 + (1 + scale))])
    } else {
      list([num_mul(sign, bits), int(0 + scale)])
    }
  }

  while true {
    let (fraction_and_guard, rem) = num_truncate(shifted_num, b=den)
    let extra = integer_length(fraction_and_guard) - digits
    if extra != 1 {
      if !(extra > 1) {
        raise LispError::SimpleError("float-ratio: assertion failed")
      }
    } else if oddp(fraction_and_guard) {
      return if zerop(rem) {
        float_and_scale(
          if zerop(logand(fraction_and_guard, Fix(2L))) {
            fraction_and_guard
          } else {
            one_plus(fraction_and_guard)
          },
          scale,
        )
      } else {
        float_and_scale(one_plus(fraction_and_guard), scale)
      }
    } else {
      return float_and_scale(fraction_and_guard, scale)
    }
    shifted_num = ash(shifted_num, -1)
    scale += 1
  }
  Nil
}

///|
fn decimalsin(x : Value) -> Value raise {
  // log[10](2)=.301029
  let mut i = float__quot(num_mul(Fix(59L), x), Fix(196L))
  while true {
    if num_gt(int(integer_length(expt(Fix(10L), i))), x) {
      return one_minus(i)
    }
    i = one_plus(i)
  }
  Nil
}

///|
/// Returns a list of a mantissa and an exponent.  This function MUST
/// recognize any symbol in *builtin-numeric-constants* and compute a bfloat
/// value for it.
fn intofp(l : Value) -> Value raise {
  if !atom(l) {
    d_bfloat(l)
  } else if floatp(l) {
    floattofp(l)
  } else if equal(Fix(0L), l) {
    list([Fix(0L), Fix(0L)])
  } else if eq(l, q_d__pctpi) {
    float__fppi()
  } else if eq(l, q_d__pcte) {
    float__fpe()
  } else if eq(l, q_d__pctgamma) {
    float__fpgamma()
  } else if eq(l, q_d__pctcatalan) {
    float__fpcatalan()
  } else if eq(l, q_d__pctphi) {
    float__fpphi()
  } else {
    let m = fpround(l)
    list([m, num_add(symval(q_n_starm), float__prec())])
  }
}

///|
/// The number of bits in the magnitude of L.
fn fpmagnitude_length(l : Value) -> Value raise {
  int(integer_length(if minusp(l) { one_minus(l) } else { l }))
}

///|
/// Round the integer L to FPPREC bits ("STICKY BIT" calculation), setting
/// *M to the number of bits shifted off (and *CANCELLED).
fn fpround(l : Value) -> Value raise {
  let prec = float__prec()
  if !float__decfp() {
      // *M will be positive if the precision of the argument is greater
      // than the current precision being used.
      let m = num_sub(fpmagnitude_length(l), prec)
      set(q_n_starm, m) |> ignore
      if zerop(m) {
        set(q_n_starcancelled, Fix(0L)) |> ignore
        return l
      }
      if minusp(m) {
        // Nothing is shifted off the low end: an exact left shift.
        set(q_n_starcancelled, num_neg(m)) |> ignore
        return float__ash(l, num_neg(m))
      }
      // *M > 0. Round the magnitude of L to FPPREC bits, half to even.  Bit
      // *M-1 of the magnitude is the round bit, bits 0 to *M-2 are the
      // sticky bits.
      let minus = minusp(l)
      let u = if minus { num_neg(l) } else { l }
      let mut q = float__ash(u, num_neg(m))
      let mut mm = m
      if logbitp(to_int(one_minus(mm)), u) &&
        // The round bit is set, so round up - unless L is exactly halfway
        // and Q is even already.
        (logbitp(0, q) || !hipart_zerop(u, num_sub(Fix(1L), mm)).truthy()) {
        q = one_plus(q)
        if num_gt(int(integer_length(q)), prec) {
          // The carry ran off the top: Q is 2^FPPREC and needs one more
          // shift to fit, which costs another cancelled bit.
          q = ash(q, -1)
          mm = one_plus(mm)
          set(q_n_starm, mm) |> ignore
        }
      }
      set(q_n_starcancelled, mm) |> ignore
      if minus {
        num_neg(q)
      } else {
        q
      }
  } else {
    // FLATSIZE counts decimal digits: bind *PRINT-BASE* as FPROUND's &AUX.
    with_specials([(q_ear_print_base, Fix(10L)), (q_ear_print_radix, Nil)], () => {
      let mut l = l
      let m = num_sub(flatsize(num_abs(l)), prec)
      set(q_n_starm, m) |> ignore
      let mut adjust = fpshift(Fix(1L), one_minus(m))
      if minusp(l) {
        adjust = num_neg(adjust)
      }
      adjust = num_mul(Fix(5L), adjust)
      l = num_add(l, adjust)
      let m2 = num_sub(flatsize(num_abs(l)), prec)
      set(q_n_starm, m2) |> ignore
      fpshift(l, num_neg(m2))
    })
  }
}

///|
/// Compute (* L (expt d n)) where D is 2 or 10 depending on *decfp.  Throw
/// away any fractional part by truncating to zero.
fn fpshift(l : Value, n : Value) -> Value raise {
  if !float__decfp() {
    if minusp(n) && minusp(l) {
      // Right shift of a negative number: this truncates towards zero,
      // while ASH floors.  The two differ by exactly 1 iff a shifted-off bit
      // is set.
      let q = float__ash(l, n)
      if hipart_zerop(l, n).truthy() {
        q
      } else {
        one_plus(q)
      }
    } else {
      float__ash(l, n)
    }
  } else if plusp(n) {
    num_mul(l, expt(Fix(10L), n))
  } else if minusp(n) {
    float__quot(l, expt(Fix(10L), num_neg(n)))
  } else {
    l
  }
}

///|
/// Bignum LSH: computes (* X (EXPT 2 N)), truncating towards zero.
fn biglsh(x : Value, n : Value) -> Value raise {
  let p = float__machine_fixnum_precision()
  if !bignump(x) && num_lt(n, int(-p)) {
    Fix(0L)
  } else if !bignump(x) &&
    (!plusp(n) || num_lt(num_add(int(integer_length(x)), n), int(p))) {
    // Nearly identical to (ASH X N), however (ASH -100 -20) = -1, whereas
    // (BIGLSH -100 -20) = 0.
    if !minusp(x) {
      float__ash(x, n)
    } else {
      num_neg(biglsh(num_neg(x), n))
    }
  } else if minusp(n) {
    if num_gt(num_abs(n), int(integer_length(x))) {
      Fix(0L)
    } else if plusp(x) {
      hipart(x, num_add(int(integer_length(x)), n))
    } else {
      num_neg(hipart(x, num_add(int(integer_length(x)), n)))
    }
  } else if zerop(n) {
    x
  } else if num_lt(n, int(p - 1)) {
    num_mul(x, float__ash(Fix(1L), n))
  } else {
    num_mul(x, expt(Fix(2L), n))
  }
}

///|
/// Does one higher precision to round correctly.  A and B are each a list
/// of a mantissa and an exponent.
fn fpquotient(a : Value, b : Value) -> Value raise {
  if equal(car(b), Fix(0L)) {
    merr("pquotient: attempted quotient by zero.", [])
  } else if equal(car(a), Fix(0L)) {
    list([Fix(0L), Fix(0L)])
  } else {
    let m = fpround(
      float__quot(fpshift(car(a), float__addi(float__prec(), 3)), car(b)),
    )
    list([
      m,
      num_add(num_add(Fix(-3L), num_sub(cadr(a), cadr(b))), symval(q_n_starm)),
    ])
  }
}

///|
fn fpgreaterp(a : Value, b : Value) -> Value raise {
  fpposp(fpdifference(a, b))
}

///|
fn fplessp(a : Value, b : Value) -> Value raise {
  fpposp(fpdifference(b, a))
}

///|
fn fpposp(x : Value) -> Value raise {
  lbool(plusp(car(x)))
}

///|
fn fpmin(arg1 : Value, args : Value) -> Value raise {
  let mut min = arg1
  for u in args.iter() {
    if fplessp(u, min).truthy() {
      min = u
    }
  }
  min
}

///|
fn fpmax(arg1 : Value, args : Value) -> Value raise {
  let mut max = arg1
  for u in args.iter() {
    if fpgreaterp(u, max).truthy() {
      max = u
    }
  }
  max
}

///|
/// 1 is always an exact bfloat, so no table is needed.
fn fpone() -> Value raise {
  if float__decfp() {
    intofp(Fix(1L))
  } else if num_eq(float__prec(), bigfloat_prec(symval(q_ear_bigfloatone))) {
    cdr(symval(q_ear_bigfloatone))
  } else {
    intofp(Fix(1L))
  }
}

///|
/// Computes A+B or A-B, depending on whether SUBTRACT is NIL or non-NIL.
fn fpplusminus(a : Value, b : Value, subtract : Value) -> Value raise {
  with_special(q_n_starm, Nil, () => {
    set(q_n_starcancelled, Fix(0L)) |> ignore
    if equal(car(a), Fix(0L)) {
      return if subtract.truthy() && !equal(car(b), Fix(0L)) {
        list([num_neg(car(b)), cadr(b)])
      } else {
        b
      }
    } else if equal(car(b), Fix(0L)) {
      return a
    }
    let exp = num_sub(cadr(a), cadr(b))
    let mut sticky : Value = Fix(0L)
    let mut man = if equal(exp, Fix(0L)) {
      sticky = Fix(0L)
      fpshift(
        if subtract.truthy() {
          num_sub(car(a), car(b))
        } else {
          num_add(car(a), car(b))
        },
        Fix(2L),
      )
    } else if plusp(exp) {
      // COMPUTE STICKY BIT
      sticky = if hipart_zerop(car(b), num_sub(Fix(1L), exp)).truthy() {
        Fix(0L)
      } else if (
          // the sign B enters the sum with
          if subtract.truthy() {
            plusp(car(b))
          } else {
            minusp(car(b))
          }
        ) {
        Fix(-1L)
      } else {
        Fix(1L)
      }
      // MAKE ROOM FOR GUARD DIGIT & STICKY BIT
      let ma = fpshift(car(a), Fix(2L))
      let mb = fpshift(car(b), num_sub(Fix(2L), exp))
      if subtract.truthy() {
        num_sub(ma, mb)
      } else {
        num_add(ma, mb)
      }
    } else {
      sticky = if hipart_zerop(car(a), one_plus(exp)).truthy() {
        Fix(0L)
      } else if minusp(car(a)) {
        Fix(-1L)
      } else {
        Fix(1L)
      }
      let ma = fpshift(car(a), num_add(Fix(2L), exp))
      let mb = fpshift(car(b), Fix(2L))
      if subtract.truthy() {
        num_sub(ma, mb)
      } else {
        num_add(ma, mb)
      }
    }
    if !zerop(sticky) {
      man = num_add(man, sticky)
    }
    if equal(man, Fix(0L)) {
      list([Fix(0L), Fix(0L)])
    } else {
      man = fpround(man)
      let e = num_add(
        num_add(Fix(-2L), symval(q_n_starm)),
        num_max(cadr(a), cadr(b)),
      )
      list([man, e])
    }
  })
}

///|
fn fpdifference(a : Value, b : Value) -> Value raise {
  fpplusminus(a, b, t)
}

///|
fn fpminus(x : Value) -> Value raise {
  if equal(car(x), Fix(0L)) {
    x
  } else {
    list([num_neg(car(x)), cadr(x)])
  }
}

///|
fn fpplus(a : Value, b : Value) -> Value raise {
  fpplusminus(a, b, Nil)
}

///|
fn fptimes_star(a : Value, b : Value) -> Value raise {
  if zerop(car(a)) || zerop(car(b)) {
    list([Fix(0L), Fix(0L)])
  } else {
    let m = fpround(num_mul(car(a), car(b)))
    list([
      m,
      num_sub(
        num_add(num_add(symval(q_n_starm), cadr(a)), cadr(b)),
        float__prec(),
      ),
    ])
  }
}

///|
/// INT is an integer, NN is positive.
fn fpintexpt(int_ : Value, nn : Value, fixprec0 : Value) -> Value raise {
  let fixprec = num_truncate(fixprec0, b=int(integer_length(int_) - 1)).0
  let bas = intofp(expt(int_, num_min(nn, fixprec)))
  if num_gt(nn, fixprec) {
    fptimes_star(
      intofp(expt(int_, num_rem(nn, fixprec))),
      fpexpt(bas, float__quot(nn, fixprec)),
    )
  } else {
    bas
  }
}

///|
/// NN is positive or negative integer
fn fpexpt(p0 : Value, nn : Value) -> Value raise {
  if zerop(nn) {
    fpone()
  } else if eql(nn, Fix(1L)) {
    p0
  } else if minusp(nn) {
    fpquotient(fpone(), fpexpt(p0, num_neg(nn)))
  } else {
    let mut p = p0
    let mut u : Value = Nil
    if oddp(nn) {
      u = p
    }
    let mut ii = float__quot(nn, Fix(2L))
    while !zerop(ii) {
      p = fptimes_star(p, p)
      if oddp(ii) {
        u = if u.truthy() { fptimes_star(u, p) } else { p }
      }
      ii = float__quot(ii, Fix(2L))
    }
    u
  }
}

///|
fn exptbigfloat(p0 : Value, n0 : Value) -> Value raise {
  let mut p = p0
  let mut n = n0
  if equal(n, Fix(1L)) {
    p
  } else if equal(n, Fix(0L)) {
    d_bfloat(Fix(1L))
  } else if !d_bfloatp(p).truthy() {
    mk(q_mexpt, [p, n])
  } else if equal(cadr(p), Fix(0L)) {
    d_bfloat(Fix(0L))
  } else if minusp(cadr(p)) && ratnump(n).truthy() {
    mul2(
      with_specials(
        [
          (q_d_numer, Nil),
          (q_d_float, Nil),
          (q_d_keepfloat, Nil),
          (q_d_ratprint, Nil),
        ],
        () => power(Fix(-1L), n),
      ),
      exptbigfloat(bcons(fpminus(cdr(p))), n),
    )
  } else if minusp(cadr(p)) && !integerp(n) {
    if equal(n, Flo(0.5)) || equal(n, symval(q_ear_bfhalf)) {
      exptbigfloat(p, mk_simp(q_rat, [Fix(1L), Fix(2L)]))
    } else if equal(n, Flo(-0.5)) || equal(n, symval(q_ear_bfmhalf)) {
      exptbigfloat(p, mk_simp(q_rat, [Fix(-1L), Fix(2L)]))
    } else {
      n = d_bfloat(n)
      if !d_bfloatp(n).truthy() {
        return mk(q_mexpt, [p, n])
      }
      if equal(n, d_bfloat(fpentier(n))) {
        exptbigfloat(p, fpentier(n))
      } else {
        // for P<0: P^N = (-P)^N*cos(pi*N) + i*(-P)^N*sin(pi*N)
        p = exptbigfloat(bcons(fpminus(cdr(p))), n)
        n = d_bfloat(mk(q_mtimes, [q_d__pctpi, n]))
        add2(
          d_bfloat(mk(q_mtimes, [p, n_starfpsin(n, Nil)])),
          mk_simp(q_mtimes, [
            d_bfloat(mk(q_mtimes, [p, n_starfpsin(n, t)])),
            q_d__pcti,
          ]),
        )
      }
    }
  } else if ratnump(n).truthy() && num_lt(caddr(n), Fix(10L)) {
    bcons(fpexpt(fproot(p, caddr(n)), cadr(n)))
  } else if !integerp(n) {
    n = d_bfloat(n)
    if !d_bfloatp(n).truthy() {
      mk(q_mexpt, [p, n])
    } else {
      // The number of extra bits required
      let extrabits = num_max(
        Fix(1L),
        num_add(caddr(n), int(integer_length(caddr(p)))),
      )
      p = with_special(q_fpprec, num_add(extrabits, float__prec()), () => fpexp(
        fptimes_star(cdr(bigfloatp(n)), fplog(cdr(bigfloatp(p)))),
      ))
      let m = fpround(car(p))
      p = list([
        m,
        num_add(num_add(num_neg(extrabits), symval(q_n_starm)), cadr(p)),
      ])
      bcons(p)
    }
  } else if minusp(n) {
    invertbigfloat(exptbigfloat(p, num_neg(n)))
  } else {
    bcons(fpexpt(cdr(p), n))
  }
}

///|
/// Computes a^(1/n), see Fitch, SIGSAM Bull Nov 74.  FPROOT is called with
/// an argument like ((BIGFLOAT ...) FOO BAR) but returns (FOO BAR).
fn fproot(a0 : Value, n0 : Value) -> Value raise {
  // Square roots are much faster and correctly rounded with FPROOT-SQRT.
  if eql(n0, Fix(2L)) && !float__decfp() && plusp(cadr(a0)) {
    return fproot_sqrt(a0)
  }
  if eql(cadr(a0), Fix(0L)) {
    // Special case for a = 0b0. General algorithm loops endlessly.
    return list([Fix(0L), Fix(0L)])
  }
  let ofprec = float__prec()
  let a = with_special(q_fpprec, num_add(float__prec(), Fix(2L)), () => {
    // assumes a>0 n>=2
    let a = cdr(bigfloatp(a0))
    let mut bk = fpexpt(intofp(Fix(2L)), one_plus(float__quot(cadr(a), n0)))
    let mut x = bk
    let n1 = one_minus(n0)
    let n = intofp(n0)
    while true {
      if equal(bk, list([Fix(0L), Fix(0L)])) ||
        num_gt(num_sub(cadr(x), cadr(bk)), ofprec) {
        break x
      }
      bk = fpquotient(fpdifference(x, fpquotient(a, fpexpt(x, n1))), n)
      x = fpdifference(x, bk)
    } nobreak {
      x
    }
  })
  let m = fpround(car(a))
  list([m, num_add(num_add(Fix(-2L), symval(q_n_starm)), cadr(a))])
}

///|
/// Correctly rounded square root of the positive bigfloat A, given and
/// returned like the argument and the result of FPROOT.
///
/// A is M*2^(E-FPPREC). With M shifted left by SHIFT bits,
///   sqrt(A) = sqrt(M*2^SHIFT) * 2^((E-FPPREC-SHIFT)/2).
fn fproot_sqrt(a : Value) -> Value raise {
  let me = cdr(bigfloatp(a))
  let m = car(me)
  let e = cadr(me)
  let prec = float__prec()
  // Enough bits for the integer root to have FPPREC+1 bits.
  let shift0 = num_max(
    Fix(0L),
    num_sub(num_mul(Fix(2L), one_plus(prec)), int(integer_length(m))),
  )
  // One more if needed, so that the exponent can be halved.
  let shift = if oddp(num_sub(num_sub(e, prec), shift0)) {
    one_plus(shift0)
  } else {
    shift0
  }
  let scaled = float__ash(m, shift)
  // The root, rounded down to an integer.
  let root = isqrt(scaled)
  // 1 if ROOT is not exact.
  let sticky : Value = if num_eq(num_mul(root, root), scaled) {
    Fix(0L)
  } else {
    Fix(1L)
  }
  // Round ROOT with the sticky bit appended to FPPREC bits.
  let mantissa = fpround(num_add(num_mul(Fix(2L), root), sticky))
  // The result is MANTISSA*2^(*M-1+(E-FPPREC-SHIFT)/2).
  list([
    mantissa,
    num_add(
      num_add(
        num_add(symval(q_n_starm), Fix(-1L)),
        num_div(num_sub(num_sub(e, prec), shift), Fix(2L)),
      ),
      prec,
    ),
  ])
}

///|
fn timesbigfloat(h : Value) -> Value raise {
  let mut fans : Value = Nil
  let mut nfans : Value = Nil
  for e in h.iter() {
    let r = bigfloatp(e)
    if r.truthy() {
      fans = if fans.truthy() {
        bcons(fptimes_star(cdr(r), cdr(fans)))
      } else {
        r
      }
    } else {
      nfans = cons(e, nfans)
    }
  }
  if fans is Nil {
    fans = bcons(fpone())
  }
  nfans = nreverse(nfans)
  if nfans.truthy() {
    simplify(cons(list1(q_mtimes), cons(fans, nfans)))
  } else {
    fans
  }
}

///|
fn invertbigfloat(a : Value) -> Value raise {
  // If A is a bigfloat, be sure to round it to the current precision.
  let b = bigfloatp(a)
  if b.truthy() {
    bcons(fpquotient(fpone(), cdr(b)))
  } else {
    simplify(mk(q_mexpt, [a, Fix(-1L)]))
  }
}

///|
fn fpend(a0 : Value) -> Value raise {
  if equal(car(a0), Fix(0L)) {
    bcons(a0)
  } else if numberp(car(a0)) {
    let m = fpround(car(a0))
    let a = list([m, num_add(num_add(Fix(-8L), symval(q_n_starm)), cadr(a0))])
    bcons(a)
  } else {
    a0
  }
}

///|
fn fpabs(x : Value) -> Value raise {
  if !minusp(car(x)) {
    x
  } else {
    cons(num_neg(car(x)), cdr(x))
  }
}

///|
fn fpentier(f : Value) -> Value raise {
  with_special(q_fpprec, bigfloat_prec(f), () => fpintpart(cdr(f)))
}

///|
/// Calculate the integer part of a floating point number that is
/// represented as a list (MANTISSA EXPONENT), denoting
/// MANTISSA * 2^(EXPONENT - FPPREC), of which FPPREC bits are known.  If
/// EXPONENT >= FPPREC we only know the integer part when
/// SKIP-EXPONENT-CHECK-P is true; otherwise signal a Maxima error.
fn fpintpart(f : Value, skip_exponent_check_p? : Value = Nil) -> Value raise {
  let mantissa = car(f)
  let exponent = cadr(f)
  let prec = float__prec()
  let m = num_sub(prec, exponent)
  if plusp(m) {
    float__quot(mantissa, expt(Fix(2L), num_sub(prec, exponent)))
  } else if !skip_exponent_check_p.truthy() && num_lt(exponent, prec) {
    merr("~M doesn't have enough precision to compute its integer part", [
      list([list2(q_bigfloat, prec), mantissa, exponent]),
    ])
  } else {
    num_mul(mantissa, expt(Fix(2L), num_neg(m)))
  }
}

///|
fn init_float() -> Unit raise {
  putprop(q_mplus, q_addbigfloat, q_floatprog) |> ignore
  putprop(q_mtimes, q_timesbigfloat, q_floatprog) |> ignore
  putprop(q_p_sin, q_sinbigfloat, q_floatprog) |> ignore
  putprop(q_p_cos, q_cosbigfloat, q_floatprog) |> ignore
  putprop(q_rat, q_ratbigfloat, q_floatprog) |> ignore
  putprop(q_p_atan, q_atanbigfloat, q_floatprog) |> ignore
  putprop(q_p_tan, q_tanbigfloat, q_floatprog) |> ignore
  putprop(q_p_log, q_logbigfloat, q_floatprog) |> ignore
  putprop(q_mabs, q_mabsbigfloat, q_floatprog) |> ignore
  // defmfun ($bfloat :properties ((evfun t)))
  putprop(q_d_bfloat, t, q_evfun) |> ignore
  // Set up user's precision
  fpprec1(Nil, symval(q_d_fpprec)) |> ignore
}

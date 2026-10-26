// Port of share/numeric/decfp-core.lisp (R. J. Fateman, 2016): decimal
// bigfloats.
//
// Representation of a decimal bigfloat:
//   ((BIGFLOAT SIMP precision DECIMAL) significand exponent)
// where precision is the number of decimal digits ($fpprec) and the number
// represented is significand * 10^exponent.
//
// The Lisp file redefines a number of functions of the core (BIGFLOATP,
// $BFLOAT, FP2FLO, MAKE-NUMBER, FPPREC1, ...).  The port keeps their decfp
// versions here as share_decfp_core__<name> and installs them, when the
// file is loaded, in the redefinition hooks of the core functions
// (`<file>__redefined_<name>`), so that every caller sees the new
// definition, as after a Lisp redefinition.  $REMAINDER, which the Lisp
// redefines in terms of its old function object, is replaced in its
// function cell only.

///|
/// Reduce the number of decimal digits in a decimal bigfloat B to the
/// number specified.
fn d_decimalfptrim(b : Value) -> Value raise {
  if decimalfpp(b).truthy() {
    // trim excess digits
    cons(car(b), decimalfptrim(cdr(b), flag=t))
  } else {
    // if its binary, $bfloat should trim it
    d_bfloat(b)
  }
}

///|
/// decimalfptrim will carefully round. f is (significand exponent).
fn decimalfptrim(f : Value, flag? : Value) -> Value raise {
  let flag = match flag {
    Some(v) => v
    None => symval(q_d_rounddecimalfloats)
  }
  let mut s = car(f)
  let mut e = cadr(f)
  if eql(s, Fix(0L)) {
    return list2(Fix(0L), Fix(0L))
  }
  // first remove trailing zeros
  while num_eq(num_mod(s, Fix(10L)), Fix(0L)) {
    s = num_truncate(s, b=Fix(10L)).0
    e = num_add(e, Fix(1L))
  }
  // there may still be more digits than allowed by $fpprec
  if flag.truthy() {
    let adjust = num_sub(flatsize10(s), symval(q_d_fpprec))
    if num_le(adjust, Fix(0L)) {
      list2(s, e)
    } else {
      decimalround(s, e, adjust)
    }
  } else {
    // don't round!
    list2(s, e)
  }
}

///|
/// We want to remove ad digits from the right of s.
fn decimalround(s : Value, e : Value, ad : Value) -> Value raise {
  let sign = signum(s)
  // significand with one extra (guard_) digit; sticky has the rest
  let (swithguard, sticky) = num_truncate(
    s,
    b=expt(Fix(10L), num_sub(ad, Fix(1L))),
  )
  // now have last digit of s, the one to drop off, at left end of
  // swithguard
  let guard_ = num_mod(swithguard, Fix(10L))
  let lt5 = num_lt(guard_, Fix(5L))
  let gt5 = num_gt(guard_, Fix(5L))
  let eq5 = num_eq(guard_, Fix(5L))
  let s1 = if num_eq(sign, Fix(1L)) {
    if lt5 {
      // no sweat
      num_truncate(swithguard, b=Fix(10L)).0
    } else if gt5 || (eq5 && num_gt(sticky, Fix(0L))) {
      // in case we have 96 b0 we round up and get 10b0. too many digits
      // so in the case of xxxx99X, or worse 9999.999X we need to re-trim.
      num_add(num_truncate(swithguard, b=Fix(10L)).0, Fix(1L))
    } else {
      // guard digit is 5 and sticky is 0 (cannot be negative if sign is 1)
      // so find the even digit at or above this number
      let snoguard = num_truncate(swithguard, b=Fix(10L)).0
      let checkthis = num_mod(snoguard, Fix(10L))
      if evenp(checkthis) {
        // this is already even
        list2(snoguard, num_add(e, ad))
      } else {
        num_add(snoguard, Fix(1L))
      }
    }
  } else if gt5 {
    // i.e. sign=-1, because sign=0 can't happen
    num_truncate(swithguard, b=Fix(10L)).0
  } else if lt5 || (eq5 && num_lt(sticky, Fix(0L))) {
    num_sub(num_truncate(swithguard, b=Fix(10L)).0, Fix(1L))
  } else {
    // guard digit is 5 and sticky is 0 (cannot be pos if sign is -1)
    let snoguard = num_truncate(swithguard, b=Fix(10L)).0
    let checkthis = num_mod(snoguard, Fix(10L))
    if evenp(checkthis) {
      // this is already even
      snoguard
    } else {
      num_sub(snoguard, Fix(1L))
    }
  }
  decimalfptrim(list2(s1, num_add(e, ad)))
}

///|
/// The number of decimal digits of r, estimated as
/// (ceiling (* #.(log 2) (integer-length (abs r))) #.(log 10)), computed
/// in single-float as in the Lisp.
fn flatsize10(r : Value) -> Value raise {
  if num_eq(r, Fix(0L)) {
    Fix(1L)
  } else {
    let log2 = Float::from_double(@math.ln(2.0))
    let log10 = Float::from_double(@math.ln(10.0))
    let a = log2 * Float::from_int(integer_length(num_abs(r)))
    let q = a / log10
    let c = q.to_double().ceil()
    int(c.to_int())
  }
}

///|
/// (defun dim-bigfloat ...) of decfp-core.lisp.
fn share_decfp_core__dim_bigfloat(form : Value, result : Value) -> Value raise {
  with_special(q_d_lispdisp, Nil, () => dimension_atom(
    maknam(decfpformat(form)),
    result,
  ))
}

///|
/// needed for wxmaxima front end.
fn wxxml_bigfloat(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    append(list1(Str("<n>")), append(decfpformat(x), append(list1(Str("</n>")), r))),
  )
}

///|
/// decimal bigfloat predicate
fn decimalfpp(x : Value) -> Value raise {
  if consp(x) && eq(caar(x), q_bigfloat) {
    member(q_decimal, cddar(x))
  } else {
    Nil
  }
}

///|
/// binary bigfloat predicate
fn binaryfpp(x : Value) -> Value raise {
  lbool(
    consp(x) && eq(caar(x), q_bigfloat) && member(q_decimal, cddar(x)) is Nil,
  )
}

///|
/// Converts the bigfloat L to list of digits including |.| and the
/// exponent marker. Uses L marker instead of b:  123L0 prints 1.23L2
fn decfpformat(l : Value) -> Value raise {
  if decimalfpp(l).truthy() {
    if num_eq(cadr(l), Fix(0L)) {
      list([q_n0, q_op_dot, q_n_cl_, q_n0])
    } else if num_gt(cadr(l), Fix(0L)) {
      let m = explodec(format(Nil, "~s", [cadr(l)]))
      append(
        cons(car(m), cons(q_op_dot, cdr(m))),
        append(
          list1(q_n_cl_),
          explodec(num_add(num_add(caddr(l), int(length(m))), Fix(-1L))),
        ),
      )
    } else {
      let m = explodec(format(Nil, "~s", [cadr(l)]))
      append(
        cons(q_op_h_, cons(car(m), cons(q_op_dot, cdr(m)))),
        append(
          list1(q_n_cl_),
          explodec(num_add(num_add(caddr(l), int(length(m))), Fix(-1L))),
        ),
      )
    }
  } else {
    // oh, it's a binary bigfloat
    fpformat(l)
  }
}

///|
/// (defun bigfloatp ...) of decfp-core.lisp: decimal bigfloats are
/// returned as they are; a binary bigfloat is normalized to the current
/// precision.
fn share_decfp_core__bigfloatp(x0 : Value) -> Value raise {
  let mut x = x0
  if decimalfpp(x).truthy() {
    return x
  }
  if !d_bfloatp(x).truthy() {
    return Nil
  }
  let fpprec = symval(q_fpprec)
  let xprec = caddar(x)
  if num_eq(fpprec, xprec) {
    // Precision matches.
    return x
  } else if num_gt(fpprec, xprec) {
    // Current precision is higher than bigfloat precision.  Scale up
    // mantissa and adjust exponent to get the correct precision.
    x = bcons(list2(fpshift(cadr(x), num_sub(fpprec, xprec)), caddr(x)))
  } else {
    // Current precision is LOWER than bigfloat precision.  Round the
    // number to the desired precision.
    let m = fpround(cadr(x))
    x = bcons(
      list2(
        m,
        num_add(
          num_add(num_add(caddr(x), symval(q_n_starm)), symval(q_fpprec)),
          num_neg(xprec),
        ),
      ),
    )
  }
  // Fix up any bogus zeros that we might have created.
  if equal(cadr(x), Fix(0L)) {
    bcons(list2(Fix(0L), Fix(0L)))
  } else {
    x
  }
}

///|
/// (defun bigfloat2rat ...) of decfp-core.lisp.
fn share_decfp_core__bigfloat2rat(x0 : Value) -> Value raise {
  if decimalfpp(x0).truthy() {
    let k = num_mul(cadr(x0), expt(Fix(10L), caddr(x0)))
    return cons(numerator(k), denominator(k))
  }
  let x = bigfloatp(x0)
  with_special(q_d_float2bf, t, () => {
    let mut sign = false
    let exp = if minusp(cadr(x)) {
      sign = true
      let y = fpration1(cons(car(x), fpabs(cdr(x))))
      rplaca(y, num_mul(Fix(-1L), car(y)))
    } else {
      fpration1(x)
    }
    if symval(q_d_ratprint).truthy() {
      princ(Str("`rat' replaced ")) |> ignore
      if sign {
        princ(Str("-")) |> ignore
      }
      princ(maknam(fpformat(cons(car(x), fpabs(cdr(x)))))) |> ignore
      princ(Str(" by ")) |> ignore
      princ(car(exp)) |> ignore
      write_char('/', stream=symval(standard_output))
      princ(cdr(exp)) |> ignore
      princ(Str(" = ")) |> ignore
      let x = d_bfloat(list3(list2(q_rat, q_simp), car(exp), cdr(exp)))
      if sign {
        princ(Str("-")) |> ignore
      }
      princ(maknam(fpformat(cons(car(x), fpabs(cdr(x)))))) |> ignore
      terpri() |> ignore
    }
    exp
  })
}

///|
/// Convert a machine floating point number into a bigfloat.  Since it is
/// a binary float, no point in making it decimal.
fn decfloat_from_fp(x : Value) -> Value raise {
  d_binarybfloat(d_rationalize(x))
}

///|
/// (defun fp2flo (l) (decfp2flo l))
fn share_decfp_core__fp2flo(l : Value) -> Value raise {
  decfp2flo(l)
}

///|
/// Convert a bigfloat into a floating point number.
fn decfp2flo(l : Value) -> Value raise {
  if decimalfpp(l).truthy() {
    let r = num_mul(cadr(l), expt(Fix(10L), caddr(l)))
    return Flo(to_double(r))
  }
  let precision = caddar(l)
  let mantissa0 = cadr(l)
  let exponent = caddr(l)
  let mmp = symval(q_machine_mantissa_precision)
  with_specials([(q_fpprec, mmp), (q_n_starm, Fix(0L))], () => {
    // Round the mantissa to the number of bits of precision of the
    // machine, and then convert it to a floating point fraction.  We have
    // 0.5 <= mantissa < 1
    let mantissa = num_div(fpround(mantissa0), expt(Flo(2.0), mmp))
    // The largest double-float is .999999 * 2^1024.  So if the exponent is
    // 1025 or higher, we have an overflow.
    let e = num_add(
      num_add(num_add(exponent, num_neg(precision)), symval(q_n_starm)),
      mmp,
    )
    if num_ge(e, Fix(1025L)) {
      merror(Str("float: floating point overflow converting ~:M"), list1(l))
    } else {
      let ei = if num_lt(e, Fix(-100000L)) { -100000 } else { to_int(e) }
      Flo(scale_float(to_double(mantissa), ei))
    }
  })
}

///|
fn decbcons(s : Value) -> Value raise {
  if !eql(symval(q_d_fpprec), symval(q_ear_decbfloat_header_prec)) {
    // Precision was changed, make a new header.
    set(
      q_ear_decbfloat_header,
      list([q_bigfloat, q_simp, symval(q_d_fpprec), q_decimal]),
    )
    |> ignore
    set(q_ear_decbfloat_header_prec, symval(q_d_fpprec)) |> ignore
  }
  cons(symval(q_ear_decbfloat_header), decimalfptrim(s))
}

///|
/// (defmfun $bfloat ...) of decfp-core.lisp.
fn share_decfp_core__bfloat(x : Value) -> Value raise {
  // return x, possibly changed precision
  let r = bigfloatp(x)
  if r.truthy() {
    r
  } else if numberp(x) {
    // favors decimal conversion for CL numbers
    decintofp(x)
  } else if atom(x) {
    // %pi, %phi
    d_binarybfloat(x)
  } else if eq(caar(x), q_rat) {
    decrat2fp(x)
  } else if eq(caar(x), q_mexpt) &&
    decimalfpp(cadr(x)).truthy() &&
    integerp(caddr(x)) &&
    num_ge(caddr(x), Fix(0L)) {
    // float^integer
    decfppower(cadr(x), caddr(x))
  } else if eq(caar(x), q_mtimes) {
    dectimesbigfloat(mapcar(y => d_decbfloat(y), cdr(x)))
  } else if eq(caar(x), q_mplus) {
    decaddbigfloat(mapcar(y => d_decbfloat(y), cdr(x)))
  } else {
    // here we return to the previous program
    d_binarybfloat(x)
  }
}

///|
fn d_decbfloat(x : Value) -> Value raise {
  if decimalfpp(x).truthy() {
    if symval(q_d_rounddecimalfloats) is Nil {
      // just return it
      x
    } else {
      // possibly chop/round it
      decbcons(cdr(x))
    }
  } else if numberp(x) {
    // favors decimal conversion for CL numbers
    decrat2fp(x)
  } else if atom(x) {
    // %pi, %phi
    d_binarybfloat(x)
  } else if eq(caar(x), q_rat) {
    decrat2fp(x)
  } else if eq(caar(x), q_mexpt) &&
    decimalfpp(cadr(x)).truthy() &&
    integerp(caddr(x)) &&
    num_ge(caddr(x), Fix(0L)) {
    // float^integer
    decfppower(cadr(x), caddr(x))
  } else {
    // here we return to the previous program
    d_binarybfloat(x)
  }
}

///|
/// ba^e,  e is nonneg int
fn decfppower(ba : Value, e : Value) -> Value raise {
  let mut ans = list2(Fix(1L), Fix(0L))
  let b = cdr(ba)
  let mut i : Value = Fix(0L)
  while num_lt(i, e) {
    ans = decfptimes(ans, b)
    i = num_add(i, Fix(1L))
  }
  decbcons(ans)
}

///|
fn d_binarybfloat(x : Value) -> Value raise {
  let y = bigfloatp(x)
  if y.truthy() {
    return y
  }
  if numberp(x) ||
    member(x, list3(q_d__pcte, q_d__pctpi, q_d__pctgamma)).truthy() {
    bcons(intofp(x))
  } else if atom(x) || member(q_array, cdar(x)).truthy() {
    if eq(x, q_d__pctphi) {
      d_binarybfloat(
        list3(
          list2(q_mtimes, q_simp),
          list3(list2(q_rat, q_simp), Fix(1L), Fix(2L)),
          list3(
            list2(q_mplus, q_simp),
            Fix(1L),
            list3(
              list2(q_mexpt, q_simp),
              Fix(5L),
              list3(list2(q_rat, q_simp), Fix(1L), Fix(2L)),
            ),
          ),
        ),
      )
    } else {
      x
    }
  } else if eq(caar(x), q_mexpt) {
    if equal(cadr(x), q_d__pcte) {
      // exp(x)
      n_starfpexp(decfp2binfp(caddr(x)))
    } else {
      exptbigfloat(decfp2binfp(cadr(x)), caddr(x))
    }
  } else if eq(caar(x), q_mncexpt) {
    list3(list1(q_mncexpt), d_binarybfloat(cadr(x)), caddr(x))
  } else if eq(caar(x), q_rat) {
    ratbigfloat(cdr(x))
  } else {
    let y = safe_get(caar(x), q_floatprog)
    if y.truthy() {
      funcall(y, [mapcar(a => d_binarybfloat(a), cdr(x))])
    } else {
      recur_apply(q_d_binarybfloat, x)
    }
  }
}

///|
/// (defun bigfloat-prec (z) (third (car z))): assumes ((bigfloat simp #)
/// ...) or ((bigfloat simp # decimal) ...).
fn share_decfp_core__bigfloat_prec(z : Value) -> Value raise {
  third(car(z))
}

///|
/// Make the floatprog of J (a function name) also work for a decimal
/// bigfloat argument.
fn make_decimalfp_prog(j : Value) -> Value raise {
  let k = get(j, q_floatprog)
  if k.truthy() && symbolp(k) {
    format(t, "~%redefining bigfloat ~a to also work for decimal bigfloat", [
      Str(invert_case(symbol_name(j))),
    ])
    |> ignore
    let program = lfunc("decimalfp-prog", args => {
      let f = arg(args, 0)
      let a = car(f)
      funcall(k, [
        if decimalfpp(a).truthy() {
          list1(decfp2binfp(a))
        } else {
          f
        },
      ])
    })
    setf_get(j, q_floatprog, program)
  } else {
    Nil
  }
}

///|
/// exceptions to the uniform treatment above...
fn decmabsbigfloat(l : Value) -> Value raise {
  let a = car(l)
  let r = bigfloatp(a)
  if r is Nil {
    list2(list1(q_mabs), a)
  } else if decimalfpp(a).truthy() {
    decbcons(list2(num_abs(cadr(a)), caddr(a)))
  } else {
    // probably never used
    bcons(fpabs(cdr(r)))
  }
}

///|
/// convert integer or rational or decimal fp to binary fp
fn decfp2binfp(f : Value) -> Value raise {
  if numberp(f) {
    d_binarybfloat(f)
  } else if decimalfpp(f).truthy() {
    // check if decimal
    let r = num_mul(cadr(f), expt(Fix(10L), caddr(f)))
    d_binarybfloat(list3(list1(q_rat), numerator(r), denominator(r)))
  } else {
    d_binarybfloat(f)
  }
}

///|
/// h is a list of bigfloats. It will return one bigfloat, maybe decimal:
/// if there is at least one binary, convert all to binary.
fn decaddbigfloat(h : Value) -> Value raise {
  let mut h = h
  let anybin = h.iter().any(z => binaryfpp(z).truthy())
  if anybin && h.iter().any(z => decimalfpp(z).truthy()) {
    // then there are some of each: convert everything to binary
    h = mapcar(z => decfp2binfp(z), h)
  }
  if anybin {
    // all are in binary
    let mut fans = bcons(list2(Fix(0L), Fix(0L)))
    for z in h.iter() {
      let r = bigfloatp(z)
      fans = bcons(fpplus(cdr(r), cdr(fans)))
    }
    fans
  } else {
    // all are decimal
    let mut fans = decbcons(list2(Fix(0L), Fix(0L)))
    for z in h.iter() {
      let r = d_bfloat(z)
      fans = decbcons(decfpplus(cdr(r), cdr(fans)))
    }
    fans
  }
}

///|
/// Convert a maxima rat to a decimal float: for n/d divide(n*10^expon,d).
fn decrat2fp(r : Value) -> Value raise {
  if decimalfpp(r).truthy() {
    r
  } else if consp(r) && eq(caar(r), q_rat) {
    let n = cadr(r)
    let d = caddr(r)
    let expon = num_add(flatsize10(d), symval(q_d_fpprec))
    let shifter = expt(Fix(10L), expon)
    // add expon zeros to the numerator, divide by d (actually, truncate)
    // then mult by 10^ expon
    decbcons(list2(num_truncate(num_mul(n, shifter), b=d).0, num_neg(expon)))
  } else if integerp(r) {
    decbcons(list2(r, Fix(0L)))
  } else {
    // other numbers
    decrat2fp(d_rationalize(r))
  }
}

///|
/// intofp takes any expression and return a bigfloat, decintofp modifies
/// that so that the answer is decimal if possible.  %pi is not returned
/// as decimal.  Returns a bigfloat with header.
fn decintofp(l : Value) -> Value raise {
  if !atom(l) {
    d_bfloat(l)
  } else if floatp(l) {
    decfloat_from_fp(l)
  } else if equal(Fix(0L), l) {
    decbcons(list2(Fix(0L), Fix(0L)))
  } else if eq(l, q_d__pctpi) {
    bcons(float__fppi())
  } else if eq(l, q_d__pcte) {
    bcons(float__fpe())
  } else if eq(l, q_d__pctgamma) {
    bcons(float__fpgamma())
  } else {
    decbcons(list2(l, Fix(0L)))
  }
}

///|
/// decimal version just a hack
fn decfpquotient(a : Value, b : Value) -> Value raise {
  if equal(car(b), Fix(0L)) {
    merror(Str("pquotient: attempted quotient by zero."), Nil)
  } else if equal(car(a), Fix(0L)) {
    list2(Fix(0L), Fix(0L))
  } else {
    decimalfptrim(
      list2(
        num_truncate(
          num_div(num_mul(expt(Fix(10L), symval(q_d_fpprec)), car(a)), car(b)),
        ).0,
        num_sub(num_sub(cadr(a), cadr(b)), symval(q_d_fpprec)),
      ),
    )
  }
}

///|
fn decfpdifference(a : Value, b : Value) -> Value raise {
  fpplus(a, fpminus(b))
}

///|
fn decfpminus(x : Value) -> Value raise {
  if equal(car(x), Fix(0L)) {
    x
  } else {
    list2(num_neg(car(x)), cadr(x))
  }
}

///|
/// totally without rounding
fn decfpplus(a : Value, b : Value) -> Value raise {
  let exp = num_sub(cadr(a), cadr(b))
  if num_eq(exp, Fix(0L)) {
    list2(num_add(car(a), car(b)), cadr(a))
  } else if num_gt(exp, Fix(0L)) {
    list2(num_add(num_mul(expt(Fix(10L), exp), car(a)), car(b)), cadr(b))
  } else {
    list2(num_add(num_mul(car(b), expt(Fix(10L), num_neg(exp))), car(a)), cadr(a))
  }
}

///|
/// h is a list of bigfloats. It will return one bigfloat, maybe decimal:
/// if there is at least one binary, convert all to binary.
fn dectimesbigfloat(h : Value) -> Value raise {
  let mut h = h
  // anybin is T if there is a binary bigfloat
  let anybin = h.iter().any(z => binaryfpp(z).truthy())
  if anybin && h.iter().any(z => decimalfpp(z).truthy()) {
    // some binary and some dec: convert everything to binary
    h = mapcar(z => decfp2binfp(z), h)
  }
  if anybin {
    // all are in binary
    let mut fans = bcons(fpone())
    for z in h.iter() {
      let r = bigfloatp(z)
      fans = bcons(fptimes_star(cdr(r), cdr(fans)))
    }
    fans
  } else {
    // all are decimal
    let mut fans = decbcons(list2(Fix(1L), Fix(0L)))
    for z in h.iter() {
      let r = d_bfloat(z)
      fans = decbcons(decfptimes(cdr(r), cdr(fans)))
    }
    fans
  }
}

///|
fn decfptimes(a : Value, b : Value) -> Value raise {
  decimalfptrim(decfptimes_star(a, b))
}

///|
/// totally without rounding
fn decfptimes_star(a : Value, b : Value) -> Value raise {
  list2(num_mul(car(a), car(b)), num_add(cadr(a), cadr(b)))
}

///|
/// INT is integer, NN is pos
fn decfpintexpt(int_ : Value, nn : Value, fixprec : Value) -> Value raise {
  let fixprec = num_truncate(fixprec, b=int(integer_length(int_) - 1)).0
  let bas = decintofp(expt(int_, num_min(nn, fixprec)))
  if num_gt(nn, fixprec) {
    fptimes_star(
      decintofp(expt(int_, num_rem(nn, fixprec))),
      fpexpt(bas, num_truncate(nn, b=fixprec).0),
    )
  } else {
    bas
  }
}

///|
fn decfpone() -> Value raise {
  list2(Fix(1L), Fix(0L))
}

///|
/// (defun timesbigfloat ...) of decfp-core.lisp: modeled on addbigfloat.
fn share_decfp_core__timesbigfloat(h : Value) -> Value raise {
  let mut fans = decbcons(fpone())
  let mut nfans : Value = Fix(1L)
  for e in h.iter() {
    let r = bigfloatp(e)
    if r.truthy() {
      fans = decbcons(fptimes_star(cdr(r), cdr(fans)))
    } else {
      nfans = list3(list1(q_mtimes), e, nfans)
    }
  }
  if equal(nfans, Fix(1L)) {
    fans
  } else {
    simplifya(list3(list1(q_mtimes), fans, nfans), Nil)
  }
}

///|
/// (defun invertbigfloat ...) of decfp-core.lisp: this has 1/3.0L0 in
/// binary.
fn share_decfp_core__invertbigfloat(a : Value) -> Value raise {
  bcons(
    fpquotient(
      fpone(),
      if decimalfpp(a).truthy() {
        cdr(decfp2binfp(a))
      } else {
        cdr(a)
      },
    ),
  )
}

///|
/// `(readlist (or l '(#\0)))`
fn share_decfp_core__readlist0(l : Value) -> Value raise {
  readlist(if l.truthy() { l } else { list1(Char('0')) })
}

///|
/// (defun make-number ...) of decfp-core.lisp: an L exponent marker reads
/// a decimal bigfloat.
fn share_decfp_core__make_number(data : Value) -> Value raise {
  let data = nreverse(data)
  // Maxima really wants to read in any number as a flonum (except when we
  // have a bigfloat, of course!).  So convert exponent markers to the
  // flonum-exponent-marker.
  let marker = car(nth(3, data))
  if !eql(marker, Char('D')) {
    match marker {
      Char('E' | 'F' | 'S' | 'D') =>
        setf_car(nthcdr(3, data), list1(Char('D'))) |> ignore
      _ => ()
    }
  }
  let is_minus = (c : Value) => eql(c, Char('-'))
  if equal(nth(3, data), list1(Char('B'))) {
    let int_part = share_decfp_core__readlist0(first(data))
    let frac_part = share_decfp_core__readlist0(third(data))
    let frac_len = length(third(data))
    let exp_sign = first(fifth(data))
    let exp_ = readlist(nth(5, data))
    if symval(q_d_fast_bfloat_conversion).truthy() &&
      num_gt(num_abs(exp_), symval(q_d_fast_bfloat_threshold)) {
      // Exponent is large enough that we don't want to do exact rational
      // arithmetic.  Instead we do bfloat arithmetic.
      let extra_prec = num_add(
        symval(q_ear_fast_bfloat_extra_bits),
        int((@math.ln(to_double(exp_)) / @math.ln(2.0)).ceil().to_int()),
      )
      let result = with_special(
        q_fpprec,
        num_add(symval(q_fpprec), extra_prec),
        () => {
          let mant = num_add(
            num_mul(int_part, expt(Fix(10L), int(frac_len))),
            frac_part,
          )
          let bf_mant = bcons(intofp(mant))
          let p = power(
            bcons(intofp(Fix(10L))),
            num_sub(if is_minus(exp_sign) { num_neg(exp_) } else { exp_ }, int(frac_len)),
          )
          // Compute the product using extra precision.
          mul2(bf_mant, p)
        },
      )
      // Now round the product back to the desired precision.
      with_special(q_fpprec, num_sub(symval(q_fpprec), extra_prec), () => {
        bigfloatp(result)
      })
    } else {
      // For bigfloats, turn them into rational numbers then convert to
      // bigfloat.
      let ratio = num_mul(
        num_add(int_part, num_mul(frac_part, expt(Fix(10L), int(-frac_len)))),
        expt(Fix(10L), if is_minus(exp_sign) { num_neg(exp_) } else { exp_ }),
      )
      d_binarybfloat(cl_rat_to_maxima(ratio))
    }
  } else if equal(nth(3, data), list1(Char('L'))) {
    // decimal input
    let int_part = share_decfp_core__readlist0(first(data))
    let frac_part = share_decfp_core__readlist0(third(data))
    let frac_len = length(third(data))
    let exp_sign = first(fifth(data))
    let exp_ = readlist(nth(5, data))
    let bigmant = num_add(frac_part, num_mul(int_part, expt(Fix(10L), int(frac_len))))
    let bigexp = num_sub(
      if is_minus(exp_sign) {
        num_neg(exp_)
      } else {
        exp_
      },
      int(frac_len),
    )
    decbcons(list2(bigmant, bigexp))
  } else {
    let parts : Array[Value] = []
    for d in data.iter() {
      parts.push(d)
    }
    readlist(append_n(parts))
  }
}

///|
/// (defmfun $rationalize ...) of decfp-core.lisp (from maxmin.lisp).
fn share_decfp_core__rationalize(e : Value) -> Value raise {
  let e = ratdisrep(e)
  match e {
    Flo(d) => {
      let (significand, expon, sign) = integer_decode_float(d)
      return cl_rat_to_maxima(
        num_mul(
          num_mul(int(sign), from_big(significand)),
          expt(Fix(2L), int(expon)),
        ),
      )
    }
    _ => ()
  }
  if binaryfpp(e).truthy() {
    cl_rat_to_maxima(
      num_mul(cadr(e), expt(Fix(2L), num_sub(caddr(e), third(car(e))))),
    )
  } else if decimalfpp(e).truthy() {
    cl_rat_to_maxima(num_mul(cadr(e), expt(Fix(10L), caddr(e))))
  } else if d_mapatom(e).truthy() {
    e
  } else if d_subvarp(mop(e)).truthy() {
    // subscripted function
    subfunmake(
      subfunname(e),
      mapcar(x => d_rationalize(x), subfunsubs(e)),
      mapcar(x => d_rationalize(x), subfunargs(e)),
    )
  } else {
    recur_apply(q_d_rationalize, e)
  }
}

///|
/// (defun big-float-eval ...) of decfp-core.lisp (from trigi.lisp).
fn share_decfp_core__big_float_eval(op : Value, z : Value) -> Value raise {
  let z = if decimalfpp(z).truthy() { decfp2binfp(z) } else { z }
  if !complex_number_p(z, ntypep=q_bigfloat_or_number_p).truthy() {
    return Nil
  }
  let x = d_realpart(z)
  let y = d_imagpart(z)
  let bop = gethash(op, symval(q_ear_big_float_op))
  let afloatp = (u : Value) => floatp(u) || d_bfloatp(u).truthy()
  // If bop is non-NIL, we want to try that first.  If bop declines (by
  // returning NIL), we silently give up and use the rectform version.
  if afloatp(x) && like(Fix(0L), y).truthy() {
    let v = if bop.truthy() { funcall(bop, [d_bfloat(x)]) } else { Nil }
    if v.truthy() {
      v
    } else {
      d_bfloat(list2(list2(op, q_simp), x))
    }
  } else if afloatp(x) || afloatp(y) {
    let v = if bop.truthy() {
      funcall(bop, [d_bfloat(x), d_bfloat(y)])
    } else {
      Nil
    }
    if v.truthy() {
      v
    } else {
      let z = add2(d_bfloat(x), mul2(q_d__pcti, d_bfloat(y)))
      let z = d_rectform(list2(list2(op, q_simp), z))
      d_bfloat(z)
    }
  } else {
    Nil
  }
}

///|
/// A minimal evaluator for the forms ADVISE-FUN-SIMP compiles: the
/// variable, numbers, and calls of a few CL functions (others are called
/// through their function cells).
fn share_decfp_core__eval(form : Value, var_ : Value, val : Value) -> Value raise {
  if eq(form, var_) {
    return val
  }
  if form is Nil || eq(form, t) || !consp(form) {
    return form
  }
  let op = car(form)
  if eq(op, q_quote) {
    return cadr(form)
  }
  let args = mapcar(a => share_decfp_core__eval(a, var_, val), cdr(form))
  match op {
    Sym(_) =>
      match symbol_name(op) {
        "car" => car(first(args))
        "cdr" => cdr(first(args))
        "cadr" => cadr(first(args))
        "caddr" => caddr(first(args))
        "cadadr" => cadadr(first(args))
        "*" => args.iter().fold(init=Fix(1L), (a, b) => num_mul(a, b))
        "+" => args.iter().fold(init=Fix(0L), (a, b) => num_add(a, b))
        "expt" => expt(first(args), second(args))
        "truncate" => num_truncate(first(args)).0
        "floor" => num_floor(first(args)).0
        "ceiling" => num_ceiling(first(args)).0
        "decimalfpp" => decimalfpp(first(args))
        _ => apply(op, args)
      }
    _ => apply(op, args)
  }
}

///|
/// hack the simplification: sort of like tellsimp
fn advise_fun_simp(
  r : Value,
  test_ : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  if get(r, q_orig) is Nil {
    // get the simplification program
    setf_get(r, q_orig, get(r, q_operators)) |> ignore
  }
  let orig = get(r, q_orig)
  setf_get(
    r,
    q_operators,
    lfunc("advise-fun-simp", args => {
      let v = arg(args, 0)
      if share_decfp_core__eval(test_, var_, v).truthy() {
        share_decfp_core__eval(val, var_, v)
      } else {
        funcall(orig, [v, Fix(1L), t])
      }
    }),
  )
}

///|
/// (defmfun $remainder (x y) ...) of decfp-core.lisp: convert decimal
/// bigfloat arguments to rationals; remainder is always 0 in the
/// rational field.
fn share_decfp_core__remainder(x : Value, y : Value) -> Value raise {
  let fix_arg = (v : Value) => if decimalfpp(v).truthy() {
    let r = bigfloat2rat(v)
    list3(list2(q_rat, q_simp), car(r), cdr(r))
  } else {
    v
  }
  funcall(symval(q_n_staroldremainder), [fix_arg(x), fix_arg(y)])
}

///|
fn d_decimalfpp(x : Value) -> Value raise {
  if decimalfpp(x).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// (defun fpprec1 ...) of decfp-core.lisp: uses $BINARYBFLOAT so that
/// fundamental binary constants remain base-2 bigfloats.
fn share_decfp_core__fpprec1(assign_var : Value, q : Value) -> Value raise {
  ignore(assign_var)
  if !fixnump(q) || num_lt(q, Fix(1L)) {
    merror(Str("fpprec: value must be a positive integer; found: ~M"), list1(q))
    |> ignore
  }
  set(q_fpprec, int(2 + integer_length(expt(Fix(10L), q)))) |> ignore
  set(q_ear_bigfloatone, d_binarybfloat(Fix(1L))) |> ignore
  set(q_ear_bigfloatzero, d_binarybfloat(Fix(0L))) |> ignore
  let one = symval(q_ear_bigfloatone)
  set(q_ear_bfhalf, list3(car(one), cadr(one), Fix(0L))) |> ignore
  set(q_ear_bfmhalf, list3(car(one), num_neg(cadr(one)), Fix(0L))) |> ignore
  q
}

///|
/// (defun fpration1 ...) of decfp-core.lisp: uses $BINARYBFLOAT.
fn share_decfp_core__fpration1(x : Value) -> Value raise {
  let fprateps = cdr(
    d_binarybfloat(
      if symval(q_d_bftorat).truthy() {
        list3(
          list2(q_rat, q_simp),
          Fix(1L),
          exptrl(Fix(2L), num_sub(symval(q_fpprec), Fix(1L))),
        )
      } else {
        symval(q_d_ratepsilon)
      },
    ),
  )
  if equal(x, symval(q_ear_bigfloatzero)) {
    return cons(Fix(0L), Fix(1L))
  }
  let mut xx = x
  let mut a = fpentier(x)
  let mut num = a
  let mut den : Value = Fix(1L)
  let mut onum : Value = Fix(1L)
  let mut oden : Value = Fix(0L)
  while true {
    if !zerop(den) &&
      !fpgreaterp(
        fpabs(
          fpquotient(
            fpdifference(
              cdr(x),
              fpquotient(cdr(d_binarybfloat(num)), cdr(d_binarybfloat(den))),
            ),
            cdr(x),
          ),
        ),
        fprateps,
      ).truthy() {
      return cons(num, den)
    }
    let y = invertbigfloat(
      bcons(fpdifference(cdr(xx), cdr(d_binarybfloat(a)))),
    )
    a = fpentier(y)
    let new_num = num_add(num_mul(a, num), onum)
    let new_den = num_add(num_mul(a, den), oden)
    onum = num
    oden = den
    num = new_num
    den = new_den
    xx = y
  }
  Nil
}

///|
/// (defun bigfloat (re &optional im) ...) of decfp-core.lisp (package
/// BIGFLOAT): convert RE to a BIGFLOAT.  If IM is given, return a
/// COMPLEX-BIGFLOAT.
fn share_decfp_core__bf_bigfloat(re : Value, im : Value) -> Value raise {
  let re = if decimalfpp(re).truthy() { decfp2binfp(re) } else { re }
  let im = if decimalfpp(im).truthy() { decfp2binfp(im) } else { im }
  if im.truthy() {
    bf_make_complex_bigfloat(bf_intofp(re), bf_intofp(im))
  } else if numeric__clrealp(re) {
    bf_make_bigfloat(bf_intofp(re))
  } else if re is Cplx(r, i) {
    bf_make_complex_bigfloat(bf_intofp(r), bf_intofp(i))
  } else if d_bfloatp(re).truthy() {
    bf_make_bigfloat(re)
  } else if complex_number_p(re, ntypep=q_bigfloat_or_number_p).truthy() {
    bf_make_complex_bigfloat(
      decfp2binfp(d_realpart(re)),
      decfp2binfp(d_imagpart(re)),
    )
  } else if bf_is_bigfloat(re) {
    // Done this way so the new bigfloat updates the precision of the
    // given bigfloat, if necessary.
    bf_make_bigfloat(bf_real_value(re))
  } else if bf_is_complex_bigfloat(re) {
    bf_make_complex_bigfloat(bf_real_value(re), bf_imag_value(re))
  } else {
    bf_make_bigfloat(decimalfpp(re))
  }
}

///|
fn init_share_decfp_core() -> Unit raise {
  // The redefinitions of core functions.
  float__redefined_bigfloatp.val = Some(share_decfp_core__bigfloatp)
  float__redefined_bigfloat_prec.val = Some(share_decfp_core__bigfloat_prec)
  float__redefined_dim_bigfloat.val = Some(share_decfp_core__dim_bigfloat)
  float__redefined_bigfloat2rat.val = Some(share_decfp_core__bigfloat2rat)
  float__redefined_fp2flo.val = Some(share_decfp_core__fp2flo)
  float__redefined_bfloat.val = Some(share_decfp_core__bfloat)
  float__redefined_timesbigfloat.val = Some(share_decfp_core__timesbigfloat)
  float__redefined_invertbigfloat.val = Some(share_decfp_core__invertbigfloat)
  nparse__redefined_make_number.val = Some(share_decfp_core__make_number)
  maxmin__redefined_rationalize.val = Some(share_decfp_core__rationalize)
  trigi__redefined_big_float_eval.val = Some(share_decfp_core__big_float_eval)
  // Make the floatprogs also work for decimal bigfloats.
  for j in all_symbols() {
    let j = Value::Sym(j)
    if !memq(j, list([q_mabs, q_mplus, q_mtimes, q_rat])).truthy() {
      make_decimalfp_prog(j) |> ignore
    }
  }
  // exceptions to the uniform treatment above...
  putprop(q_mabs, q_decmabsbigfloat, q_floatprog) |> ignore
  putprop(q_mplus, q_decaddbigfloat, q_floatprog) |> ignore
  putprop(q_mtimes, q_dectimesbigfloat, q_floatprog) |> ignore
  // this appears to not be used..
  putprop(q_rat, q_decrat2fp, q_floatprog) |> ignore
  // Set up user's precision (FPPREC1 is redefined only further down the
  // file, so this is still the core's FPPREC1).
  fpprec1(Nil, symval(q_d_fpprec)) |> ignore
  // sort of like tellsimp
  let f = sym("f")
  let t_ = sym("truncate")
  let fl = sym("floor")
  let ce = sym("ceiling")
  let st = sym("*")
  let ex = sym("expt")
  let test_ = list2(q_decimalfpp, list2(q_cadr, f))
  let val = (op : Value) => list2(
    op,
    list3(
      st,
      list2(q_cadadr, f),
      list3(ex, Fix(10L), list2(q_caddr, list2(q_cadr, f))),
    ),
  )
  advise_fun_simp(q_p_truncate, test_, f, val(t_)) |> ignore
  advise_fun_simp(q_d_floor, test_, f, val(fl)) |> ignore
  advise_fun_simp(q_d_ceiling, test_, f, val(ce)) |> ignore
  // why $floor but %truncate? historical accident..
  // $remainder is a function...  another inconsistency..
  if !boundp(q_n_staroldremainder) {
    set(q_n_staroldremainder, symbol_function(q_d_remainder)) |> ignore
  }
  defun(q_d_remainder, args => {
    check_arity("$remainder", args, 2)
    share_decfp_core__remainder(args[0], args[1])
  })
  putprop(q_d_remainder, t, q_translated) |> ignore
  // Redefine FPPREC1 and FPRATION1 to use $BINARYBFLOAT, and BIGFLOAT.
  float__redefined_fpprec1.val = Some(share_decfp_core__fpprec1)
  float__redefined_fpration1.val = Some(share_decfp_core__fpration1)
  numeric__redefined_bigfloat.val = Some(share_decfp_core__bf_bigfloat)
}

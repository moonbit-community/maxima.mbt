// Port of src/numeric.lisp, part 1: the BIGFLOAT package's numeric
// classes, conversions and basic arithmetic.
//
// This package contains a numeric class for use with Maxima.  The purpose
// is to allow users to write numerical algorithms that support
// double-float, (complex double-float) and Maxima bfloat and complex bfloat
// arithmetic, without having to write separate versions for each.
//
// Representation in the port (see docs/BIGFLOAT.md):
//   BIGFLOAT          = make_struct("bigfloat", [real])
//   COMPLEX-BIGFLOAT  = make_struct("complex-bigfloat", [real, imag])
// where each slot holds a full Maxima bigfloat ((bigfloat simp prec) m e).
// CL numbers are the runtime's Fix/Big/Ratio/Flo/Cplx values.
//
// Every CLOS generic function is one MoonBit function `bf_<name>` that
// dispatches on the runtime types, choosing the method CLOS would choose
// (most specific first).  When no method applies, an error is raised as
// CLOS's NO-APPLICABLE-METHOD would.

// ---------------------------------------------------------------------------
// Type tests and constructors

///|
/// `(typep x 'bigfloat)`
fn numeric__bfp(x : Value) -> Bool {
  struct_typep(x, "bigfloat")
}

///|
/// `(typep x 'complex-bigfloat)`
fn numeric__cbfp(x : Value) -> Bool {
  struct_typep(x, "complex-bigfloat")
}

///|
/// `(typep x 'numeric)`: a BIGFLOAT or COMPLEX-BIGFLOAT instance.
fn numeric__numericp(x : Value) -> Bool {
  numeric__bfp(x) || numeric__cbfp(x)
}

///|
/// `(typep x 'cl:number)`
fn numeric__clnump(x : Value) -> Bool {
  match x {
    Fix(_) | Big(_) | Ratio(_, _) | Flo(_) | Cplx(_, _) => true
    _ => false
  }
}

///|
/// `(typep x 'cl:rational)`
fn numeric__ratp(x : Value) -> Bool {
  match x {
    Fix(_) | Big(_) | Ratio(_, _) => true
    _ => false
  }
}

///|
/// `(typep x 'cl:real)`
fn numeric__clrealp(x : Value) -> Bool {
  match x {
    Fix(_) | Big(_) | Ratio(_, _) | Flo(_) => true
    _ => false
  }
}

///|
/// `(make-instance 'bigfloat :real re)`
fn numeric__mkbf(re : Value) -> Value {
  make_struct("bigfloat", [re])
}

///|
/// `(make-instance 'complex-bigfloat :real re :imag im)`
fn numeric__mkcbf(re : Value, im : Value) -> Value {
  make_struct("complex-bigfloat", [re, im])
}

///|
/// The error CLOS signals when no method of a generic function applies.
fn numeric__no_method(name : String, args : Array[Value]) -> Value raise {
  let sb = StringBuilder()
  sb.write_string(
    "There is no applicable method for the generic function bigfloat::",
  )
  sb.write_string(name)
  sb.write_string(" when called with arguments (")
  for i, a in args {
    if i > 0 {
      sb.write_string(" ")
    }
    sb.write_string(prin1_to_string(a))
  }
  sb.write_string(")")
  raise LispError::SimpleError(sb.to_string())
}

///|
/// `(cdr (real-value x))`: mantissa and exponent of the real part.
fn numeric__rvc(x : Value) -> Value raise {
  cdr(bf_real_value(x))
}

///|
/// `(cdr (imag-value x))`
fn numeric__ivc(x : Value) -> Value raise {
  cdr(bf_imag_value(x))
}

///|
/// `(cdr (intofp x))`
fn numeric__fpc(x : Value) -> Value raise {
  cdr(bf_intofp(x))
}

///|
/// `(list 0 0)`
fn numeric__zero_fp() -> Value {
  list2(Fix(0L), Fix(0L))
}

// Memoized values of pi and e at the current precision (float.lisp's
// FPPI and FPE are defined by its MEMOIZE macrolet and are not part of
// the contract).

///|
let numeric__fppi_table : Map[Int64, Value] = {}

///|
let numeric__fpe_table : Map[Int64, Value] = {}

///|
/// `(maxima::fppi)`: (mantissa exponent) of pi at precision fpprec.
fn numeric__fppi() -> Value raise {
  let key = to_int64(symval(q_fpprec))
  match numeric__fppi_table.get(key) {
    Some(v) => v
    None => {
      let v = cdr(fppi1())
      numeric__fppi_table[key] = v
      v
    }
  }
}

///|
/// `(maxima::fpe)`: (mantissa exponent) of %e at precision fpprec.
fn numeric__fpe() -> Value raise {
  let key = to_int64(symval(q_fpprec))
  match numeric__fpe_table.get(key) {
    Some(v) => v
    None => {
      let v = cdr(fpe1())
      numeric__fpe_table[key] = v
      v
    }
  }
}

///|
let numeric__q_use_accurate_complex_div : Value = sym(
  "bigfloat::*use-accurate-complex-div*",
)

///|
let numeric__q_debug_cf_eval : Value = sym("bigfloat::*debug-cf-eval*")

///|
let numeric__q_max_cf_iterations : Value = sym("bigfloat::*max-cf-iterations*")

// ---------------------------------------------------------------------------
// INTOFP, BIGFLOAT, REAL-VALUE, MAXIMA::TO

///|
/// Kind of like Maxima's INTOFP, but we only handle numeric types.  We
/// return a Maxima bigfloat object (list of bigfloat marker, mantissa, and
/// exponent).
fn bf_intofp(re : Value) -> Value raise {
  match re {
    Flo(_) => bcons(floattofp(re))
    Fix(0L) => bcons(numeric__zero_fp())
    Fix(_) | Big(_) => {
      let m = fpround(re)
      bcons(list2(m, num_add(symval(q_n_starm), symval(q_fpprec))))
    }
    Ratio(n, d) =>
      // Should we do something better than converting the numerator and
      // denominator to floats and dividing?
      bcons(
        fpquotient(
          cdr(bf_intofp(from_big(n))),
          cdr(bf_intofp(from_big(d))),
        ),
      )
    _ =>
      if d_bfloatp(re).truthy() {
        // Call bigfloatp to make sure we round/scale the bigfloat to the
        // correct precision!
        bigfloatp(re)
      } else {
        raise LispError::SimpleError(
          "Don't know how to convert " +
          prin1_to_string(re) +
          " to a BIGFLOAT",
        )
      }
  }
}

///|
/// `real-value`: the internal representation of a bigfloat (or of the
/// real part of a complex-bigfloat), adjusted to the current fpprec.
fn bf_real_value(b : Value) -> Value raise {
  if numeric__numericp(b) {
    bigfloatp(struct_ref(b, 0))
  } else {
    numeric__no_method("real-value", [b])
  }
}

///|
/// `imag-value`: the imaginary part of a complex-bigfloat, adjusted to the
/// current fpprec.
fn bf_imag_value(b : Value) -> Value raise {
  if numeric__cbfp(b) {
    bigfloatp(struct_ref(b, 1))
  } else {
    numeric__no_method("imag-value", [b])
  }
}

///|
/// The definition of BIGFLOAT:BIGFLOAT installed by
/// share/numeric/decfp-core.lisp, which redefines it when loaded.
let numeric__redefined_bigfloat : Ref[((Value, Value) -> Value raise)?] = Ref::new(None)

///|
/// BIGFLOAT converts a number to a BIGFLOAT or COMPLEX-BIGFLOAT.  This is
/// intended to convert CL numbers or Maxima (internal) numbers to a
/// bigfloat object.
fn bf_bigfloat(re : Value, im? : Value = Nil) -> Value raise {
  if numeric__redefined_bigfloat.val is Some(redefined) {
    return redefined(re, im)
  }
  if im.truthy() {
    let r = bf_intofp(re)
    numeric__mkcbf(r, bf_intofp(im))
  } else if numeric__clrealp(re) {
    numeric__mkbf(bf_intofp(re))
  } else if re is Cplx(r, i) {
    let rr = bf_intofp(r)
    numeric__mkcbf(rr, bf_intofp(i))
  } else if d_bfloatp(re).truthy() {
    numeric__mkbf(bf_intofp(re))
  } else if complex_number_p(re, ntypep=q_bigfloat_or_number_p).truthy() {
    let rr = bf_intofp(d_realpart(re))
    numeric__mkcbf(rr, bf_intofp(d_imagpart(re)))
  } else if numeric__bfp(re) {
    // Done this way so the new bigfloat updates the precision of the given
    // bigfloat, if necessary.
    numeric__mkbf(bf_real_value(re))
  } else if numeric__cbfp(re) {
    let rr = bf_real_value(re)
    numeric__mkcbf(rr, bf_imag_value(re))
  } else {
    numeric__mkbf(bf_intofp(re))
  }
}

///|
/// MAXIMA::TO: convert a CL number, a BIGFLOAT, or a COMPLEX-BIGFLOAT to
/// Maxima's internal representation of the number.  Anything else is
/// returned unchanged.
fn maxima_to(z : Value) -> Value raise {
  match z {
    Flo(_) => z
    Ratio(n, d) => mk_simp(q_rat, [from_big(n), from_big(d)])
    Fix(_) | Big(_) => z
    Cplx(r, i) => add2(maxima_to(r), mul2(q_d__pcti, maxima_to(i)))
    _ =>
      if numeric__bfp(z) {
        bf_real_value(z)
      } else if numeric__cbfp(z) {
        add2(bf_real_value(z), mul2(q_d__pcti, bf_imag_value(z)))
      } else {
        z
      }
  }
}

///|
/// MAX-EXPONENT roughly computes log2(|x|).  If x is real and x = 2^n*f,
/// with |f| < 1, MAX-EXPONENT returns |n|.  For complex numbers, we return
/// one more than the max of the exponent of the real and imaginary parts.
fn bf_max_exponent(x : Value) -> Value raise {
  match x {
    Flo(d) =>
      if d == 0.0 {
        Fix(0L)
      } else {
        let (_, e, _) = decode_float(d)
        num_abs(int(e))
      }
    Fix(_) | Big(_) | Ratio(_, _) =>
      if zerop(x) {
        Fix(0L)
      } else {
        num_ceiling(llog2(num_abs(x), Fix(2L))).0
      }
    Cplx(r, i) => {
      let a = bf_max_exponent(r)
      one_plus(num_max(a, bf_max_exponent(i)))
    }
    _ =>
      if numeric__bfp(x) {
        // The third element is the exponent of a bigfloat.
        num_abs(third(struct_ref(x, 0)))
      } else if numeric__cbfp(x) {
        one_plus(
          num_max(
            num_abs(third(struct_ref(x, 0))),
            num_abs(third(struct_ref(x, 1))),
          ),
        )
      } else {
        numeric__no_method("max-exponent", [x])
      }
  }
}

///|
/// When computing x^a using exp(a*log(x)), we need extra bits because the
/// integer part of a*log(x) doesn't contribute to the accuracy of the
/// result.  The number of extra bits needed is basically the "size" of a
/// plus the number of bits for ceiling(log(x)).
fn bf_expt_extra_bits(x : Value, a : Value) -> Value raise {
  let ix = int(integer_length(bf_max_exponent(x)))
  bf_max(Fix(1L), list1(bf_add(ix, bf_max_exponent(a))))
}

///|
/// WITH-EXTRA-PRECISION ((extra (vars...)) body): execute `body` with
/// fpprec increased by `extra`.  The variables in `vars` are converted to
/// the new precision and passed to `body` (in the same order); the result
/// of `body` is converted back to the normal precision.
fn bf_with_extra_precision(
  extra : Value,
  vars : Array[Value],
  body : (Array[Value]) -> Value raise,
) -> Value raise {
  let old_fpprec = symval(q_fpprec)
  let result = with_special(q_fpprec, num_add(symval(q_fpprec), extra), () => {
    // Conversion to a maxima form automatically increases the precision
    // of the bigfloat to the new precision.  Conversion of that to a
    // bigfloat object preserves the precision.
    let vs : Array[Value] = []
    for v in vars {
      vs.push(bf_to(maxima_to(v)))
    }
    body(vs)
  }) catch {
    e => {
      set(q_fpprec, old_fpprec) |> ignore
      raise e
    }
  }
  set(q_fpprec, old_fpprec) |> ignore
  // Conversion of the result to a maxima number adjusts the precision
  // appropriately.
  bf_to(maxima_to(result))
}

// ---------------------------------------------------------------------------
// REALP, COMPLEXP, NUMBERP

///|
/// bigfloat::realp: CL reals and BIGFLOATs.
fn bf_realp(x : Value) -> Bool {
  numeric__clrealp(x) || numeric__bfp(x)
}

///|
/// bigfloat::complexp: CL complexes and COMPLEX-BIGFLOATs.
fn bf_complexp(x : Value) -> Bool {
  x is Cplx(_, _) || numeric__cbfp(x)
}

///|
/// bigfloat::numberp: CL numbers, BIGFLOATs and COMPLEX-BIGFLOATs.
fn bf_numberp(x : Value) -> Bool {
  numeric__clnump(x) || numeric__numericp(x)
}

// ---------------------------------------------------------------------------
// 1+ and 1-

///|
/// Generic ADD1: a + 1.
fn bf_add1(a : Value) -> Value raise {
  if numeric__clnump(a) {
    one_plus(a)
  } else if numeric__bfp(a) {
    numeric__mkbf(bcons(fpplus(numeric__rvc(a), fpone())))
  } else if numeric__cbfp(a) {
    let r = bcons(fpplus(numeric__rvc(a), fpone()))
    numeric__mkcbf(r, bf_imag_value(a))
  } else {
    numeric__no_method("add1", [a])
  }
}

///|
/// Generic SUB1: a - 1.
fn bf_sub1(a : Value) -> Value raise {
  if numeric__clnump(a) {
    one_minus(a)
  } else if numeric__bfp(a) {
    numeric__mkbf(bcons(fpdifference(numeric__rvc(a), fpone())))
  } else if numeric__cbfp(a) {
    let r = bcons(fpdifference(numeric__rvc(a), fpone()))
    numeric__mkcbf(r, bf_imag_value(a))
  } else {
    numeric__no_method("sub1", [a])
  }
}

///|
/// bigfloat::1+
fn bf_1_plus(x : Value) -> Value raise {
  bf_add1(x)
}

///|
/// bigfloat::1-
fn bf_1_(x : Value) -> Value raise {
  bf_sub1(x)
}

// ---------------------------------------------------------------------------
// Addition

///|
/// TWO-ARG-+: a + b.
fn bf_add(a : Value, b : Value) -> Value raise {
  if numeric__clnump(a) && numeric__clnump(b) {
    return num_add(a, b)
  }
  if numeric__bfp(a) {
    if numeric__bfp(b) {
      return numeric__mkbf(bcons(fpplus(numeric__rvc(a), numeric__rvc(b))))
    }
    if numeric__clrealp(b) {
      return numeric__mkbf(bcons(fpplus(numeric__rvc(a), numeric__fpc(b))))
    }
    if b is Cplx(br, bi) {
      let r = bcons(fpplus(numeric__rvc(a), numeric__fpc(br)))
      return numeric__mkcbf(r, bf_intofp(bi))
    }
    if numeric__cbfp(b) {
      return bf_add(b, a)
    }
  } else if numeric__cbfp(a) {
    if numeric__cbfp(b) {
      let r = bcons(fpplus(numeric__rvc(a), numeric__rvc(b)))
      return numeric__mkcbf(r, bcons(fpplus(numeric__ivc(a), numeric__ivc(b))))
    }
    if numeric__bfp(b) {
      let r = bcons(fpplus(numeric__rvc(a), numeric__rvc(b)))
      return numeric__mkcbf(r, bf_imag_value(a))
    }
    if numeric__clnump(b) {
      let r = bcons(fpplus(numeric__rvc(a), numeric__fpc(realpart(b))))
      return numeric__mkcbf(
        r,
        bcons(fpplus(numeric__ivc(a), numeric__fpc(imagpart(b)))),
      )
    }
  } else if numeric__clnump(a) && numeric__numericp(b) {
    return bf_add(b, a)
  }
  numeric__no_method("two-arg-+", [a, b])
}

///|
/// bigfloat::+ (&rest args)
fn bf_op_plus(args : Value) -> Value raise {
  if args is Nil {
    return Fix(0L)
  }
  let mut res = car(args)
  for x in cdr(args).iter() {
    res = bf_add(res, x)
  }
  res
}

///|
/// Convenience n-ary form of bigfloat::+ over an array.
fn bf_addn(xs : Array[Value]) -> Value raise {
  bf_op_plus(list(xs))
}

// ---------------------------------------------------------------------------
// Negation and subtraction

///|
/// UNARY-MINUS: -a.
fn bf_neg(a : Value) -> Value raise {
  if numeric__clnump(a) {
    num_neg(a)
  } else if numeric__bfp(a) {
    numeric__mkbf(bcons(fpminus(numeric__rvc(a))))
  } else if numeric__cbfp(a) {
    let r = bcons(fpminus(numeric__rvc(a)))
    numeric__mkcbf(r, bcons(fpminus(numeric__ivc(a))))
  } else {
    numeric__no_method("unary-minus", [a])
  }
}

///|
/// TWO-ARG--: a - b.
fn bf_sub(a : Value, b : Value) -> Value raise {
  if numeric__clnump(a) && numeric__clnump(b) {
    return num_sub(a, b)
  }
  if numeric__bfp(a) {
    if numeric__bfp(b) {
      return numeric__mkbf(
        bcons(fpdifference(numeric__rvc(a), numeric__rvc(b))),
      )
    }
    if numeric__clrealp(b) {
      return numeric__mkbf(
        bcons(fpdifference(numeric__rvc(a), numeric__fpc(b))),
      )
    }
    if b is Cplx(br, bi) {
      let r = bcons(fpdifference(numeric__rvc(a), numeric__fpc(br)))
      return numeric__mkcbf(r, bcons(fpminus(numeric__fpc(bi))))
    }
    if numeric__cbfp(b) {
      let r = bcons(fpdifference(numeric__rvc(a), numeric__rvc(b)))
      return numeric__mkcbf(r, bcons(fpminus(numeric__ivc(b))))
    }
  } else if numeric__cbfp(a) {
    if numeric__cbfp(b) {
      let r = bcons(fpdifference(numeric__rvc(a), numeric__rvc(b)))
      return numeric__mkcbf(
        r,
        bcons(fpdifference(numeric__ivc(a), numeric__ivc(b))),
      )
    }
    if numeric__bfp(b) {
      let r = bcons(fpdifference(numeric__rvc(a), numeric__rvc(b)))
      return numeric__mkcbf(r, bf_imag_value(a))
    }
    if b is Cplx(br, bi) {
      return bf_sub(a, bf_bigfloat(br, im=bi))
    }
    if numeric__clnump(b) {
      return bf_sub(a, bf_bigfloat(b))
    }
  } else if numeric__clnump(a) {
    if numeric__bfp(b) {
      match a {
        Cplx(ar, ai) => return bf_sub(bf_bigfloat(ar, im=ai), b)
        _ =>
          return numeric__mkbf(
            bcons(fpdifference(numeric__fpc(a), numeric__rvc(b))),
          )
      }
    }
    if numeric__cbfp(b) {
      match a {
        Cplx(ar, ai) => return bf_sub(bf_bigfloat(ar, im=ai), b)
        _ => return bf_sub(bf_bigfloat(a), b)
      }
    }
  }
  numeric__no_method("two-arg--", [a, b])
}

///|
/// bigfloat::- (number &rest more-numbers)
fn bf_op_(number : Value, more_numbers : Value) -> Value raise {
  if more_numbers.truthy() {
    let mut result = number
    for x in more_numbers.iter() {
      result = bf_sub(result, x)
    }
    result
  } else {
    bf_neg(number)
  }
}

// ---------------------------------------------------------------------------
// Multiplication

///|
/// TWO-ARG-*: a * b.
fn bf_mul(a : Value, b : Value) -> Value raise {
  if numeric__clnump(a) && numeric__clnump(b) {
    return num_mul(a, b)
  }
  if numeric__bfp(a) {
    if numeric__bfp(b) {
      return numeric__mkbf(
        bcons(fptimes_star(numeric__rvc(a), numeric__rvc(b))),
      )
    }
    if numeric__clrealp(b) {
      return numeric__mkbf(
        bcons(fptimes_star(numeric__rvc(a), numeric__fpc(b))),
      )
    }
    if b is Cplx(br, bi) {
      let r = bcons(fptimes_star(numeric__rvc(a), numeric__fpc(br)))
      return numeric__mkcbf(
        r,
        bcons(fptimes_star(numeric__rvc(a), numeric__fpc(bi))),
      )
    }
    if numeric__cbfp(b) {
      return bf_mul(b, a)
    }
  } else if numeric__cbfp(a) {
    if numeric__cbfp(b) {
      let a_re = numeric__rvc(a)
      let a_im = numeric__ivc(a)
      let b_re = numeric__rvc(b)
      let b_im = numeric__ivc(b)
      let r = bcons(
        fpdifference(fptimes_star(a_re, b_re), fptimes_star(a_im, b_im)),
      )
      return numeric__mkcbf(
        r,
        bcons(fpplus(fptimes_star(a_re, b_im), fptimes_star(a_im, b_re))),
      )
    }
    if numeric__bfp(b) {
      let r = bcons(fptimes_star(numeric__rvc(a), numeric__rvc(b)))
      return numeric__mkcbf(
        r,
        bcons(fptimes_star(numeric__ivc(a), numeric__rvc(b))),
      )
    }
    if b is Cplx(br, bi) {
      return bf_mul(a, bf_bigfloat(br, im=bi))
    }
    if numeric__clnump(b) {
      return bf_mul(a, bf_bigfloat(b))
    }
  } else if numeric__clnump(a) && numeric__numericp(b) {
    return bf_mul(b, a)
  }
  numeric__no_method("two-arg-*", [a, b])
}

///|
/// bigfloat::* (&rest args)
fn bf_op_star(args : Value) -> Value raise {
  if args is Nil {
    return Fix(1L)
  }
  let mut res = car(args)
  for x in cdr(args).iter() {
    res = bf_mul(res, x)
  }
  res
}

///|
/// Convenience n-ary form of bigfloat::* over an array.
fn bf_muln(xs : Array[Value]) -> Value raise {
  bf_op_star(list(xs))
}

// ---------------------------------------------------------------------------
// Division

///|
/// UNARY-DIVIDE: 1/a.
fn bf_inv(a : Value) -> Value raise {
  if numeric__clnump(a) {
    return num_div(Fix(1L), a)
  }
  if numeric__bfp(a) {
    return numeric__mkbf(bcons(fpquotient(fpone(), numeric__rvc(a))))
  }
  if numeric__cbfp(a) {
    // Could just call two-arg-/, but let's optimize this a little
    let a_re = fpone()
    let b_re = numeric__rvc(a)
    let b_im = numeric__ivc(a)
    if fpgreaterp(fpabs(b_re), fpabs(b_im)).truthy() {
      let r = fpquotient(b_im, b_re)
      let dn = fpplus(b_re, fptimes_star(r, b_im))
      let re = bcons(fpquotient(a_re, dn))
      return numeric__mkcbf(re, bcons(fpquotient(fpminus(r), dn)))
    } else {
      let r = fpquotient(b_re, b_im)
      let dn = fpplus(b_im, fptimes_star(r, b_re))
      let re = bcons(fpquotient(r, dn))
      return numeric__mkcbf(re, bcons(fpquotient(fpminus(a_re), dn)))
    }
  }
  numeric__no_method("unary-divide", [a])
}

///|
/// An implementation of Baudin and Smith's robust complex division for
/// double-floats (https://arxiv.org/pdf/1210.4539), including iterations 1
/// and 3 of McGehearty's improvements.
fn bf_cdiv_double_float(x : Value, y : Value) -> Value raise {
  // This is the value of Scilab's %eps variable.
  let eps = scale_float(1.0, -52)
  let rmin = least_positive_normalized_double_float
  let rbig = most_positive_double_float / 2.0
  let rmin2 = scale_float(1.0, -53)
  let rminscal = scale_float(1.0, 51)
  let rmax2 = rbig * rmin2
  let be = 2.0 / (eps * eps)
  let two_eps = 2.0 / eps
  // Compute the real part of the complex division (a+ib)/(c+id), assuming
  // |c| <= |d|.  r = d/c and tt = c + d*r.  The realpart is
  // (a*c+b*d)/(c^2+d^2) = (a + b*r)/(c + d*r).
  fn internal_compreal(
    a : Double,
    b : Double,
    c : Double,
    d : Double,
    r : Double,
    tt : Double,
  ) -> Double {
    if r.abs() >= rmin {
      let br = b * r
      if br != 0.0 {
        (a + br) / tt
      } else {
        // b*r underflows.
        a / tt + b / tt * r
      }
    } else {
      // r = 0 so d is very tiny compared to c.
      (a + d * (b / c)) / tt
    }
  }

  fn robust_subinternal(
    a : Double,
    b : Double,
    c : Double,
    d : Double,
  ) -> (Double, Double) {
    let r = d / c
    let tt = c + d * r
    // The imaginary part of (a+i*b)/(c+i*d) is the real part of
    // (b-i*a)/(c+i*d).
    let e = internal_compreal(a, b, c, d, r, tt)
    let f = internal_compreal(b, -a, c, d, r, tt)
    (e, f)
  }

  // McGehearty's iteration 3: scale values that are too big or too tiny.
  fn maybe_scale(
    abs_tst : Double,
    a : Double,
    b : Double,
    c : Double,
    d : Double,
  ) -> (Double, Double, Double, Double) {
    let abs_a = a.abs()
    let abs_b = b.abs()
    if abs_tst > rbig || abs_a > rbig || abs_b > rbig {
      (a * 0.5, b * 0.5, c * 0.5, d * 0.5)
    } else if abs_tst < rmin2 {
      (a * rminscal, b * rminscal, c * rminscal, d * rminscal)
    } else if (abs_a < rmin && abs_b < rmax2 && abs_tst < rmax2) ||
      (abs_b < rmin && abs_a < rmax2 && abs_tst < rmax2) {
      (a * rminscal, b * rminscal, c * rminscal, d * rminscal)
    } else {
      (a, b, c, d)
    }
  }

  fn robust_internal(
    a : Double,
    b : Double,
    c : Double,
    d : Double,
  ) -> (Double, Double) {
    if d.abs() <= c.abs() {
      let (a, b, c, d) = maybe_scale(c.abs(), a, b, c, d)
      robust_subinternal(a, b, c, d)
    } else {
      // |d| > |c|: compute (b + i*a)/(d + i*c) instead and negate the
      // imaginary part.
      let (a, b, c, d) = maybe_scale(d.abs(), a, b, c, d)
      let (e, f) = robust_subinternal(b, a, d, c)
      (e, -f)
    }
  }

  let mut a = to_double(realpart(x))
  let mut b = to_double(imagpart(x))
  let mut c = to_double(realpart(y))
  let mut d = to_double(imagpart(y))
  let ab = a.abs().max(b.abs())
  let cd = c.abs().max(d.abs())
  let mut s = 1.0
  // If a or b is big, scale down a and b.
  if ab >= rbig {
    a = a / 2.0
    b = b / 2.0
    s = s * 2.0
  }
  // If c or d is big, scale down c and d.
  if cd >= rbig {
    c = c / 2.0
    d = d / 2.0
    s = s / 2.0
  }
  // If a or b is tiny, scale up a and b.
  if ab <= rmin * two_eps {
    a = a * be
    b = b * be
    s = s / be
  }
  // If c or d is tiny, scale up c and d.
  if cd <= rmin * two_eps {
    c = c * be
    d = d * be
    s = s * be
  }
  let (e, f) = robust_internal(a, b, c, d)
  Cplx(Flo(s * e), Flo(s * f))
}

///|
/// Smith's algorithm for complex division for (complex single-float).  The
/// port has no single floats; the computation is done in double precision.
fn bf_cdiv_single_float(x : Value, y : Value) -> Value raise {
  let a = to_double(realpart(x))
  let b = to_double(imagpart(x))
  let c = to_double(realpart(y))
  let d = to_double(imagpart(y))
  if c.abs() < d.abs() {
    let r = c / d
    let denom = c * r + d
    let e = (a * r + b) / denom
    let f = (b * r - a) / denom
    Cplx(Flo(e), Flo(f))
  } else {
    let r = d / c
    let denom = c + d * r
    let e = (a + b * r) / denom
    let f = (b - a * r) / denom
    Cplx(Flo(e), Flo(f))
  }
}

///|
/// TWO-ARG-/: a / b.
fn bf_div(a : Value, b : Value) -> Value raise {
  if a is Cplx(ar, ai) && b is Cplx(br, bi) {
    if ar is Flo(_) &&
      ai is Flo(_) &&
      br is Flo(_) &&
      bi is Flo(_) &&
      symval(numeric__q_use_accurate_complex_div).truthy() {
      return bf_cdiv_double_float(a, b)
    }
    return num_div(a, b)
  }
  if numeric__clnump(a) && numeric__clnump(b) {
    return num_div(a, b)
  }
  if numeric__bfp(a) {
    if numeric__bfp(b) {
      return numeric__mkbf(bcons(fpquotient(numeric__rvc(a), numeric__rvc(b))))
    }
    if numeric__clrealp(b) {
      return numeric__mkbf(bcons(fpquotient(numeric__rvc(a), numeric__fpc(b))))
    }
    if b is Cplx(_, _) {
      return bf_div(bf_complex(a), b)
    }
    if numeric__cbfp(b) {
      let re = bf_real_value(a)
      return bf_div(numeric__mkcbf(re, bf_intofp(Fix(0L))), b)
    }
  } else if numeric__cbfp(a) {
    if numeric__cbfp(b) {
      let a_re = numeric__rvc(a)
      let a_im = numeric__ivc(a)
      let b_re = numeric__rvc(b)
      let b_im = numeric__ivc(b)
      if fpgreaterp(fpabs(b_re), fpabs(b_im)).truthy() {
        let r = fpquotient(b_im, b_re)
        let dn = fpplus(b_re, fptimes_star(r, b_im))
        let re = bcons(fpquotient(fpplus(a_re, fptimes_star(a_im, r)), dn))
        return numeric__mkcbf(
          re,
          bcons(fpquotient(fpdifference(a_im, fptimes_star(a_re, r)), dn)),
        )
      } else {
        let r = fpquotient(b_re, b_im)
        let dn = fpplus(b_im, fptimes_star(r, b_re))
        let re = bcons(fpquotient(fpplus(fptimes_star(a_re, r), a_im), dn))
        return numeric__mkcbf(
          re,
          bcons(fpquotient(fpdifference(fptimes_star(a_im, r), a_re), dn)),
        )
      }
    }
    if numeric__bfp(b) {
      let re = bcons(fpquotient(numeric__rvc(a), numeric__rvc(b)))
      return numeric__mkcbf(
        re,
        bcons(fpquotient(numeric__ivc(a), numeric__rvc(b))),
      )
    }
    if b is Cplx(br, bi) {
      return bf_div(a, bf_bigfloat(br, im=bi))
    }
    if numeric__clnump(b) {
      return bf_div(a, bf_bigfloat(b))
    }
  } else if numeric__clnump(a) {
    if numeric__bfp(b) {
      if a is Cplx(_, _) {
        return bf_div(bf_bigfloat(a), b)
      }
      return numeric__mkbf(bcons(fpquotient(numeric__fpc(a), numeric__rvc(b))))
    }
    if numeric__cbfp(b) {
      match a {
        Cplx(ar, ai) => return bf_div(bf_bigfloat(ar, im=ai), b)
        _ => return bf_div(bf_bigfloat(a), b)
      }
    }
  }
  numeric__no_method("two-arg-/", [a, b])
}

///|
/// bigfloat::/ (number &rest more-numbers)
fn bf_op_sl(number : Value, more_numbers : Value) -> Value raise {
  if more_numbers.truthy() {
    let mut result = number
    for x in more_numbers.iter() {
      result = bf_div(result, x)
    }
    result
  } else {
    bf_inv(number)
  }
}

// ---------------------------------------------------------------------------
// ZEROP, PLUSP, MINUSP

///|
/// bigfloat::zerop
fn bf_zerop(x : Value) -> Bool raise {
  if numeric__clnump(x) {
    return zerop(x)
  }
  if numeric__bfp(x) {
    let r = numeric__rvc(x)
    return bf_zerop(first(r)) && bf_zerop(second(r))
  }
  if numeric__cbfp(x) {
    return equal(numeric__rvc(x), numeric__zero_fp()) &&
      equal(numeric__ivc(x), numeric__zero_fp())
  }
  numeric__no_method("zerop", [x]) |> ignore
  false
}

///|
/// bigfloat::plusp (reals and BIGFLOATs only)
fn bf_plusp(x : Value) -> Bool raise {
  if numeric__clrealp(x) {
    return plusp(x)
  }
  if numeric__bfp(x) {
    return plusp(first(numeric__rvc(x)))
  }
  numeric__no_method("plusp", [x]) |> ignore
  false
}

///|
/// bigfloat::minusp (reals and BIGFLOATs only)
fn bf_minusp(x : Value) -> Bool raise {
  if numeric__clrealp(x) {
    return minusp(x)
  }
  if numeric__bfp(x) {
    return minusp(first(numeric__rvc(x)))
  }
  numeric__no_method("minusp", [x]) |> ignore
  false
}

// ---------------------------------------------------------------------------
// Equality

///|
/// TWO-ARG-=: a = b?
fn bf_eq(a : Value, b : Value) -> Bool raise {
  if numeric__clnump(a) && numeric__clnump(b) {
    return num_eq(a, b)
  }
  if numeric__bfp(a) && numeric__bfp(b) {
    return bf_zerop(bf_sub(a, b))
  }
  if numeric__cbfp(a) && numeric__cbfp(b) {
    return bf_zerop(bf_sub(a, b))
  }
  // Handle contagion.  This needs some work.  CL says floats and rationals
  // are compared by converting the float to a rational before converting.
  if numeric__bfp(a) && numeric__clnump(b) {
    return bf_zerop(bf_sub(a, b))
  }
  if numeric__clnump(a) && numeric__bfp(b) {
    return bf_eq(b, a)
  }
  if numeric__cbfp(a) && numeric__clnump(b) {
    return bf_zerop(bf_sub(a, b))
  }
  if numeric__clnump(a) && numeric__cbfp(b) {
    return bf_eq(b, a)
  }
  numeric__no_method("two-arg-=", [a, b]) |> ignore
  false
}

///|
/// bigfloat::= (number &rest more-numbers): T if all of its arguments are
/// numerically equal.
fn bf_op_eq(number : Value, more_numbers : Value) -> Value raise {
  for x in more_numbers.iter() {
    if !bf_eq(x, number) {
      return Nil
    }
  }
  t
}

///|
/// bigfloat::/= (number &rest more-numbers): T if no two of its arguments
/// are numerically equal.
fn bf_op_sl_eq(number : Value, more_numbers : Value) -> Value raise {
  let mut head = number
  let mut nlist = more_numbers
  while nlist is Cons(_) {
    for x in nlist.iter() {
      if bf_eq(head, x) {
        return Nil
      }
    }
    head = car(nlist)
    nlist = cdr(nlist)
  }
  t
}

// ---------------------------------------------------------------------------
// Comparisons

///|
/// Shared dispatch of the TWO-ARG-<, >, <=, >= methods.  `clop` is the CL
/// comparison; `fpop` the bigfloat comparison (FPLESSP or FPGREATERP);
/// `or_equal` selects the <= / >= variants.
fn numeric__compare(
  name : String,
  x : Value,
  y : Value,
  clop : (Value, Value) -> Bool raise,
  fpop : (Value, Value) -> Value raise,
  or_equal : Bool,
) -> Bool raise {
  if numeric__clrealp(x) && numeric__clrealp(y) {
    return clop(x, y)
  }
  let xbf = numeric__bfp(x)
  let ybf = numeric__bfp(y)
  if (xbf && (ybf || numeric__clrealp(y))) || (ybf && numeric__clrealp(x)) {
    if or_equal && bf_zerop(bf_sub(x, y)) {
      return true
    }
    let xf = if xbf { numeric__rvc(x) } else { numeric__fpc(x) }
    let yf = if ybf { numeric__rvc(y) } else { numeric__fpc(y) }
    return fpop(xf, yf).truthy()
  }
  numeric__no_method(name, [x, y]) |> ignore
  false
}

///|
/// TWO-ARG-<: a < b (reals and BIGFLOATs).
fn bf_lt(a : Value, b : Value) -> Bool raise {
  numeric__compare("two-arg-<", a, b, (x, y) => num_lt(x, y), fplessp, false)
}

///|
/// TWO-ARG->: a > b
fn bf_gt(a : Value, b : Value) -> Bool raise {
  numeric__compare("two-arg->", a, b, (x, y) => num_gt(x, y), fpgreaterp, false)
}

///|
/// TWO-ARG-<=: a <= b
fn bf_le(a : Value, b : Value) -> Bool raise {
  numeric__compare("two-arg-<=", a, b, (x, y) => num_le(x, y), fplessp, true)
}

///|
/// TWO-ARG->=: a >= b
fn bf_ge(a : Value, b : Value) -> Bool raise {
  numeric__compare("two-arg->=", a, b, (x, y) => num_ge(x, y), fpgreaterp, true)
}

///|
/// Shared body of the n-ary comparison functions: T if `cmp` holds between
/// every pair of consecutive arguments.
fn numeric__chain(
  number : Value,
  more_numbers : Value,
  cmp : (Value, Value) -> Bool raise,
) -> Value raise {
  let mut n = number
  for x in more_numbers.iter() {
    if !cmp(n, x) {
      return Nil
    }
    n = x
  }
  t
}

///|
/// bigfloat::< (number &rest more-numbers): T if its arguments are in
/// strictly increasing order.
fn bf_op_lt(number : Value, more_numbers : Value) -> Value raise {
  numeric__chain(number, more_numbers, bf_lt)
}

///|
/// bigfloat::> (number &rest more-numbers)
fn bf_op_gt(number : Value, more_numbers : Value) -> Value raise {
  numeric__chain(number, more_numbers, bf_gt)
}

///|
/// bigfloat::<= (number &rest more-numbers)
fn bf_op_lt_eq(number : Value, more_numbers : Value) -> Value raise {
  numeric__chain(number, more_numbers, bf_le)
}

///|
/// bigfloat::>= (number &rest more-numbers)
fn bf_op_gt_eq(number : Value, more_numbers : Value) -> Value raise {
  numeric__chain(number, more_numbers, bf_ge)
}

///|
/// bigfloat::max (number &rest more-numbers): the greatest argument.
fn bf_max(number : Value, more_numbers : Value) -> Value raise {
  let mut number = number
  for real in more_numbers.iter() {
    if bf_gt(real, number) {
      number = real
    }
  }
  number
}

///|
/// bigfloat::min (number &rest more-numbers): the least argument.
fn bf_min(number : Value, more_numbers : Value) -> Value raise {
  let mut result = number
  for x in more_numbers.iter() {
    if bf_lt(x, result) {
      result = x
    }
  }
  result
}

// ---------------------------------------------------------------------------
// Public type tests and constructors for other bigfloat-package code.

///|
/// `(typep x 'bigfloat)`
fn bf_is_bigfloat(x : Value) -> Bool {
  numeric__bfp(x)
}

///|
/// `(typep x 'complex-bigfloat)`
fn bf_is_complex_bigfloat(x : Value) -> Bool {
  numeric__cbfp(x)
}

///|
/// `(typep x 'numeric)`: a BIGFLOAT or COMPLEX-BIGFLOAT instance.
fn bf_is_numeric(x : Value) -> Bool {
  numeric__numericp(x)
}

///|
/// `(make-instance 'bigfloat :real re)`, `re` a Maxima bigfloat.
fn bf_make_bigfloat(re : Value) -> Value {
  numeric__mkbf(re)
}

///|
/// `(make-instance 'complex-bigfloat :real re :imag im)`, `re` and `im`
/// Maxima bigfloats.
fn bf_make_complex_bigfloat(re : Value, im : Value) -> Value {
  numeric__mkcbf(re, im)
}

// Port of src/sinc.lisp: sinc function support for Maxima.

///|
let sinc__q_bf_sin : Value = sym("bigfloat::sin")

///|
/// Return true if `e` is either a Maxima number or a sum, product, or power
/// whose arguments are all pure constants. Symbolic constants such as %pi,
/// %e, and %i are not considered numeric.
fn pure_constant_p(e : Value) -> Value raise {
  if mnump(e).truthy() {
    t
  } else if mplusp(e).truthy() || mtimesp(e).truthy() || mexptp(e).truthy() {
    lbool(every(x => pure_constant_p(x).truthy(), cdr(e)))
  } else {
    Nil
  }
}

///|
/// Multiple-value version of `complex-number-p` (numerical-utils.lisp):
/// is `u` a complex number whose real and imaginary parts satisfy `ntypep`?
/// Returns (flag, re, im).
fn sinc__complex_number_p(
  u : Value,
  ntypep : (Value) -> Bool raise,
) -> (Bool, Value, Value) raise {
  let mut r = int(0)
  let mut i_ = int(0)
  let is_i = fn(x : Value) -> Bool raise { eq(x, q_d__pcti) && ntypep(int(1)) }
  let n_times_i = fn(x : Value) -> Bool raise {
    if !(cdddr(x) is Nil) {
      return false
    }
    i_ = cadr(x)
    ntypep(i_) && eq(caddr(x), q_d__pcti)
  }
  let n_plus_i = fn(x : Value) -> Bool raise {
    if !(cdddr(x) is Nil) {
      return false
    }
    r = cadr(x)
    if !ntypep(r) {
      return false
    }
    if is_i(caddr(x)) {
      i_ = int(1)
      true
    } else {
      mtimesp(caddr(x)).truthy() && n_times_i(caddr(x))
    }
  }
  if ntypep(u) {
    (true, u, int(0))
  } else if atom(u) {
    if is_i(u) {
      (true, int(0), int(1))
    } else {
      (false, Nil, Nil)
    }
  } else if mplusp(u).truthy() {
    if n_plus_i(u) {
      (true, r, i_)
    } else {
      (false, Nil, Nil)
    }
  } else if mtimesp(u).truthy() {
    if n_times_i(u) {
      (true, r, i_)
    } else {
      (false, Nil, Nil)
    }
  } else {
    (false, Nil, Nil)
  }
}

///|
/// Evaluate sinc(x) for float, bigfloat, or complex float or bigfloat
/// input. When $numer is true, all numeric inputs are coerced to IEEE
/// floats. Exception: for x = 0, return an exact 1 when $numer is false;
/// otherwise return an IEEE float 1.0.
fn sinc_float(x : Value) -> Value raise {
  if zerop1(x).truthy() {
    if floatp(x) || symval(q_d_numer).truthy() {
      Flo(1.0)
    } else if d_bfloatp(x).truthy() {
      symval(q_ear_bigfloatone)
    } else {
      int(1)
    }
  } else {
    let (flag, re0, im0) = sinc__complex_number_p(x, v => mnump(v).truthy())
    if !flag {
      Nil
    } else {
      let mut re = re0
      let mut im = im0
      if symval(q_d_numer).truthy() {
        re = d_float(re)
        im = d_float(im)
      }
      if !(float_or_bigfloat_p(re).truthy() || float_or_bigfloat_p(im).truthy()) {
        Nil
      } else {
        let z = if zerop1(im).truthy() { bf_to(re) } else { bf_to(re, imag=im) }
        funcall(q_to, [bf_op_sl(funcall(sinc__q_bf_sin, [z]), list1(z))])
      }
    }
  }
}

///|
fn simp__pctsinc(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=int(1),
      pretty_name=mk(q_p_sinc, [q_d_x]),
    )
    |> ignore
  }
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  if zerop1(x).truthy() {
    return sinc_float(x)
  }
  let tv = taylorize(mop(form), second(form))
  if tv.truthy() {
    return tv
  }
  let sv = sinc_float(x)
  if sv.truthy() {
    return sv
  }
  let z = ftake(q_p_sin, [x])
  if z.truthy() && pure_constant_p(z).truthy() && eq(t, mnqp(int(0), x)) {
    // When sin(x) is a pure constant and x is not zero, return sin(x)/x.
    div(z, x)
  } else if great(neg(x), x).truthy() {
    // even reflection rule: sinc(-x) = sinc(x)
    ftake(q_p_sinc, [neg(x)])
  } else {
    eqtest(cons(list1(q_p_sinc), list1(x)), form)
  }
}

///|
/// Return limit(sinc(X),x,pt).
fn simplim_pctsinc(e : Value, x : Value, pt : Value) -> Value raise {
  with_special(q_ear_preserve_direction, t, () => {
    let lim = limit(cadr(e), x, pt, q_think)
    if eq(lim, q_d_ind) {
      q_d_ind
    } else if eq(lim, q_d_minf) || eq(lim, q_d_inf) {
      int(0)
    } else if zerop2(lim).truthy() {
      int(1)
    } else if eq(lim, q_d_und) || eq(lim, q_d_infinity) {
      throw_tag(q_limit, Nil)
    } else {
      ftake(q_p_sinc, [lim])
    }
  })
}

///|
/// Return a list of dotted pairs (p . q), where p = (2k . 1) and
/// q = ((-1)^k . (2k+1)!) for k from 0 to n-1, where n = 1+(floor (car a) 2).
fn taylor_sinc(a : Value, b : Value) -> Value raise {
  ignore(b)
  let ord = num_add(int(1), num_floor(car(a), b=int(2)).0)
  let mut cfs : Value = Nil
  let mut w = int(1)
  let mut sgn = int(1)
  let mut k = int(0)
  while num_lt(k, ord) {
    let k2 = num_mul(int(2), k)
    let p = cons(k2, int(1))
    let q = cons(sgn, w)
    cfs = cons(cons(p, q), cfs)
    // update (-1)^k and (2k+1)!
    sgn = num_neg(sgn)
    w = num_mul(num_mul(w, num_add(k2, int(2))), num_add(k2, int(3)))
    k = num_add(k, int(1))
  }
  nreverse(cfs)
}

///|
/// Return the rectangular form of sinc(x); x is ((%sinc) z).
fn risplit_sinc(x : Value) -> Value raise {
  let z = cadr(x)
  risplit(div(ftake(q_p_sin, [z]), z))
}

///|
/// When -%pi <= x & x <= %pi, this code handles sign(sinc(x)).
fn sign_sinc(e : Value) -> Value raise {
  let mut x = cadr(e)
  let mut y = int(0)
  if symval(q_ear_complexsign).truthy() {
    x = risplit(x)
    y = cdr(x)
    x = car(x)
  }
  if eql(y, int(0)) &&
    eq(t, mgrp(x, mul2(int(-1), q_d__pctpi))) &&
    eq(t, mgrp(q_d__pctpi, x)) {
    set(q_sign, q_d_pos) |> ignore
  } else if eql(y, int(0)) &&
    eq(t, mgqp(x, mul2(int(-1), q_d__pctpi))) &&
    eq(t, mgqp(q_d__pctpi, x)) {
    set(q_sign, q_d_pz) |> ignore
  } else if symval(q_ear_complexsign).truthy() && !eql(y, int(0)) {
    set(q_sign, q_d_complex) |> ignore
  } else {
    set(q_sign, q_d_pnz) |> ignore
  }
  Nil
}

///|
fn init_sinc() -> Unit raise {
  setf_get(q_p_sinc, q_commutes_with_conjugate, t) |> ignore
  setf_get(q_p_sinc, q_simplim_pctfunction, q_simplim_pctsinc) |> ignore
  // (defgrad %sinc ($x) #$$ (cos(x)-sinc(x))/x$)
  push_special(q_p_sinc, q_ear_defgrad_syms) |> ignore
  setf_get(
    q_p_sinc,
    q_grad,
    list2(list1(q_d_x), maxima_lit("(cos(x)-sinc(x))/x")),
  )
  |> ignore
  putprop(q_p_sinc, lread("((x) ((%expintegral_si) x))"), q_integral)
  |> ignore
  setf_get(
    q_p_sinc,
    q_exp_form,
    list2(
      list2(q_taylor_sinc, cons(int(1), int(1))),
      cons(cons(int(0), int(1)), Nil),
    ),
  )
  |> ignore
  setf_get(
    q_p_sinc,
    q_sp2,
    lread(
      "((%sum) ((mtimes) ((mexpt) -1 *index) ((mexpt) ((mfactorial) ((mplus) 1 ((mtimes) 2 *index))) -1) ((mexpt) sp2var ((mtimes) 2 *index))) *index 0 $inf)",
    ),
  )
  |> ignore
  putprop(q_p_sinc, q_risplit_sinc, q_risplit_function) |> ignore
  putprop(q_p_sinc, q_sign_sinc, q_sign_function) |> ignore
  putprop(q_p_sinc, Str("\\sinc"), q_texword) |> ignore
}

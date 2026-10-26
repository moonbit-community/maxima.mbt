// Port of src/hstep.lisp: Heaviside step function support for Maxima.

///|
/// Unlike `signum`, we do not extend hstep to the complex plane. Maxima
/// defines hstep(0) = 1/2, but the DLMF defines hstep(0) = 0.
fn simp__pcthstep(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=int(1),
      pretty_name=mk(q_p_hstep, [q_d_z]),
    )
    |> ignore
  }
  let mut z = simpcheck(nth(1, form), p__pctsimpflag)
  let fn_ = fn(s : Value) -> Value raise {
    let sgn = d_csign(s)
    if eq(sgn, q_d_neg) {
      int(-1)
    } else if eq(sgn, q_d_pos) {
      int(1)
    } else {
      s
    }
  }
  // When z is a product, replace all negative terms by -1 and all positive
  // terms by 1.
  if mtimesp(z).truthy() {
    z = fapply(q_mtimes, mapcar(fn_, cdr(z)))
  }
  let sgn = d_csign(z)
  if eq(sgn, q_d_neg) {
    int(0)
  } else if eq(sgn, q_d_zero) {
    mk_simp(q_rat, [int(1), int(2)])
  } else if eq(sgn, q_d_pos) {
    int(1)
  } else if great(neg(z), z).truthy() {
    // hstep(-z) = 1 - hstep(z)
    sub(int(1), ftake(q_p_hstep, [neg(z)]))
  } else {
    eqtest(cons(list1(q_p_hstep), list1(z)), form)
  }
}

///|
/// Return limit(e,x,pt), where e = hstep(X).
fn simplim_pcthstep(e : Value, x : Value, pt : Value) -> Value raise {
  with_special(q_ear_preserve_direction, t, () => {
    let lim = limit(cadr(e), x, pt, q_think)
    let sgn = mnqp(lim, int(0))
    if eq(lim, q_d_zerob) {
      int(0)
    } else if eq(lim, q_d_zeroa) {
      int(1)
    } else if eq(t, sgn) {
      ftake(q_p_hstep, [lim])
    } else if sgn is Nil {
      q_d_und
    } else {
      throw_tag(q_limit, Nil)
    }
  })
}

///|
/// Return an antiderivative of hstep: integrate(hstep(x),x) = x*hstep(x).
fn hstep_integral(x : Value) -> Value raise {
  mul2(x, ftake(q_p_hstep, [x]))
}

///|
/// A sign function for hstep.
fn hstep_sign(q : Value) -> Value raise {
  let sgn = d_csign(cadr(q))
  let v = if eq(sgn, q_d_zero) {
    q_d_pos
  } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
    q_d_pos
  } else if eq(sgn, q_d_neg) {
    q_d_zero
  } else if eq(sgn, q_d_nz) {
    q_d_pz
  } else if eq(sgn, q_d_pnz) {
    q_d_pz
  } else if eq(sgn, q_d_pn) {
    q_d_pz
  } else if symval(q_ear_complexsign).truthy() {
    merr("The csign of ~M is undefined ~%", [q])
  } else {
    merr("The sign of ~M is undefined ~%", [q])
  }
  set(q_sign, v)
}

///|
fn init_hstep() -> Unit raise {
  d_put(q_d_hstep, int(1), q_d_version) |> ignore
  setf_get(q_p_hstep, q_simplim_pctfunction, q_simplim_pcthstep) |> ignore
  setf_get(q_p_hstep, q_real_valued, t) |> ignore
  // (defgrad %hstep ($x) #$$ delta(x)$)
  push_special(q_p_hstep, q_ear_defgrad_syms) |> ignore
  setf_get(q_p_hstep, q_grad, list2(list1(q_d_x), maxima_lit("delta(x)")))
  |> ignore
  putprop(q_d_delta, lread("((x) ((%hstep) x))"), q_integral) |> ignore
  putprop(q_p_hstep, list2(list1(q_x), q_hstep_integral), q_integral) |> ignore
  setf_get(q_p_hstep, q_sign_function, q_hstep_sign) |> ignore
}

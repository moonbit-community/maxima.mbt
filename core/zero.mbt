// Port of src/zero.lisp: $zeroequiv, a heuristic zero-equivalence test.

///|
fn d_zeroequiv(exp_ : Value, var_ : Value) -> Value raise {
  // VAR is special here; S and V are declared special; VARLIST and GENVAR
  // are global specials.
  with_specials(
    [
      (q_var, var_),
      (q_s, Nil),
      (q_v, Nil),
      (q_varlist, Nil),
      (q_genvar, Nil),
    ],
    () => {
      let exp = specrepcheck(exp_)
      let r = with_special(q_d_listconstvars, Nil, () => d_listofvars(exp))
      if cdr(r).truthy() &&
        (cddr(r).truthy() || !alike1(cadr(r), var_).truthy()) {
        return q_d_dontknow
      }
      let exp = d_exponentialize(exp)
      let r = sdiff(exp, var_)
      if isinop(r, q_p_derivative).truthy() {
        return q_d_dontknow
      }
      d_rat(r, Nil) |> ignore
      let r = d_rat(exp, Nil)
      set(q_s, car(r)) |> ignore
      set(q_v, ratnumerator(cdr(r))) |> ignore
      zeroequiv1(symval(q_v))
    },
  )
}

///|
fn zeroequiv1(v : Value) -> Value raise {
  // V is special (as are VAR and S); V1 and V2 are declared special.
  with_specials([(q_v, v), (q_v1, Nil), (q_v2, Nil)], () => {
    if atom(symval(q_v)) {
      return lbool(equal(symval(q_v), Fix(0L)))
    }
    // coeffloop
    while true {
      let v = symval(q_v)
      if cdr(v) is Nil {
        return t
      }
      let deg = cadr(v)
      if equal(deg, Fix(0L)) {
        return zeroequiv1(caddr(v))
      }
      let coeff = caddr(v)
      if zeroequiv1(coeff).truthy() {
        set(q_v, cons(car(v), cdddr(v))) |> ignore
        continue
      }
      break
    }
    let v = symval(q_v)
    let s = symval(q_s)
    let var_ = symval(q_var)
    set(q_v1, d_rat(sdiff(ratdisrep(cons(s, cons(v, caddr(v)))), var_), Nil))
    |> ignore
    set(q_v2, cadr(d_rat(ratdisrep(symval(q_v1)), Nil))) |> ignore
    let v2 = symval(q_v2)
    if equal(pdegree(v2, car(v)), cadr(v)) {
      return zeroequiv2(v)
    }
    if num_lt(pdegree(v2, car(v)), cadr(v)) {
      return if zeroequiv1(v2).truthy() { zeroequiv2(symval(q_v)) } else { Nil }
    }
    q_d_dontknow
  })
}

///|
/// uses random value between 0.1 and 0.9 for var and checks that v is
/// within $rootsepsilon of zero
fn zeroequiv2(v : Value) -> Value raise {
  // V is special (as are VAR and S); R1 and R2 are declared special.
  with_specials([(q_v, v), (q_r1, Nil), (q_r2, Nil)], () => {
    let r = num_add(Flo(0.1), mt_random(Flo(0.8)))
    let s = symval(q_s)
    set(
      q_v,
      maxima_substitute(
        r,
        symval(q_var),
        ratdisrep(cons(s, cons(symval(q_v), Fix(1L)))),
      ),
    )
    |> ignore
    set(q_v, meval(list([list1(q_d_ev), q_v, q_d_numer]))) |> ignore
    let v = symval(q_v)
    let eps = symval(q_d_rootsepsilon)
    if numberp(v) && num_lt(num_abs(v), eps) {
      return t
    } else if numberp(v) {
      return Nil
    }
    if free(v, q_d__pcti).truthy() && !isinop(v, q_p_log).truthy() {
      return q_d_dontknow
    }
    set(q_r1, d_realpart(v)) |> ignore
    set(q_r1, meval(list([list1(q_d_ev), q_r1, q_d_numer]))) |> ignore
    if !numberp(symval(q_r1)) {
      return q_d_dontknow
    }
    set(q_r2, d_imagpart(v)) |> ignore
    set(q_r2, meval(list([list1(q_d_ev), q_r2, q_d_numer]))) |> ignore
    if !numberp(symval(q_r2)) {
      return q_d_dontknow
    }
    if num_lt(num_abs(symval(q_r1)), eps) && num_lt(num_abs(symval(q_r2)), eps) {
      t
    } else {
      Nil
    }
  })
}

///|
/// No top-level forms.
fn init_zero() -> Unit raise {
  ()
}

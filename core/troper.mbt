// Port of src/troper.lisp: the basic OPERATORS properties translators.

///|
/// CL:SIGNUM (shadowed in the MAXIMA package by Maxima's SIGNUM); the
/// reader maps `cl:signum` to this symbol.
let troper__q_cl_signum : Value = sym("cl::signum")

///|
/// DEF%TR MMINUS
fn troper__tr_mminus(form : Value) -> Value raise {
  let form = translate(cadr(form))
  if numberp(cdr(form)) {
    cons(car(form), num_neg(cdr(form)))
  } else if eq(q_d_fixnum, car(form)) {
    list3(q_d_fixnum, q_op_h_, cdr(form))
  } else if eq(q_d_float, car(form)) {
    list3(q_d_float, q_op_h_, cdr(form))
  } else if eq(q_d_number, car(form)) {
    list3(q_d_number, q_op_h_, cdr(form))
  } else if eq(q_d_rational, car(form)) {
    if !atom(caddr(form)) && eq(q_rat, caar(caddr(form))) {
      let form = cdr(caddr(form))
      list3(
        q_d_rational,
        q_quote,
        list3(list1(q_rat), num_neg(car(form)), cadr(form)),
      )
    } else {
      list4(q_d_rational, q_rtimes, Fix(-1L), cdr(form))
    }
  } else {
    cons(q_d_any, list2(q_n_starmminus, cdr(form)))
  }
}

///|
/// DEF%TR MPLUS
fn troper__tr_mplus(form : Value) -> Value raise {
  let r = translate_args_slunion_mode(cdr(form))
  let mode = car(r)
  let args = cdr(r)
  if eq(q_d_fixnum, mode) {
    cons(q_d_fixnum, cons(q_op_plus, mapcar(x => cdr(x), args)))
  } else if eq(q_d_float, mode) {
    cons(q_d_float, cons(q_op_plus, mapcar(x => dconv__dolfloat(x), args)))
  } else if eq(q_d_rational, mode) {
    cons(q_d_rational, cons(q_rplus, mapcar(x => cdr(x), args)))
  } else if eq(q_d_number, mode) {
    cons(q_d_number, cons(q_op_plus, mapcar(x => cdr(x), args)))
  } else {
    cons(q_d_any, cons(q_add_star, mapcar(x => dconvx(x), args)))
  }
}

///|
/// DEF%TR MTIMES
fn troper__tr_mtimes(form : Value) -> Value raise {
  if equal(Fix(-1L), cadr(form)) {
    return translate(
      list2(list1(q_mminus), cons(list1(q_mtimes), cddr(form))),
    )
  }
  let r = translate_args_slunion_mode(cdr(form))
  let mode = car(r)
  let args = cdr(r)
  if eq(q_d_fixnum, mode) {
    cons(q_d_fixnum, cons(q_op_star, mapcar(x => cdr(x), args)))
  } else if eq(q_d_float, mode) {
    cons(q_d_float, cons(q_op_star, mapcar(x => dconv__dolfloat(x), args)))
  } else if eq(q_d_rational, mode) {
    cons(q_d_rational, cons(q_rtimes, mapcar(x => cdr(x), args)))
  } else if eq(q_d_number, mode) {
    cons(q_d_number, cons(q_op_star, mapcar(x => cdr(x), args)))
  } else {
    cons(q_d_any, cons(q_mul_star, mapcar(x => dconvx(x), args)))
  }
}

///|
/// DEF%TR MQUOTIENT
fn troper__tr_mquotient(form : Value) -> Value raise {
  let arg1 = translate(cadr(form))
  let arg2 = translate(caddr(form))
  let mode = n_starunion_mode(car(arg1), car(arg2))
  let arg1 = dconv(arg1, mode)
  let arg2 = dconv(arg2, mode)
  if eq(q_d_float, mode) {
    let args = if member_equal(arg1, list2(Fix(1L), Flo(1.0))).truthy() {
      list1(arg2)
    } else {
      list2(arg1, arg2)
    }
    cons(q_d_float, cons(q_op_sl, args))
  } else if eq(mode, q_d_fixnum) && symval(q_d_tr_numer).truthy() {
    cons(
      q_d_float,
      list3(q_op_sl, list2(q_float, arg1), list2(q_float, arg2)),
    )
  } else if memq(mode, list2(q_d_fixnum, q_d_rational)).truthy() {
    list4(q_d_rational, q_rremainder, arg1, arg2)
  } else {
    list4(q_d_any, q_div, arg1, arg2)
  }
}

///|
/// DEF%TR MEXPT
fn troper__tr_mexpt(form : Value) -> Value raise {
  if eq(q_d__pcte, cadr(form)) {
    return translate(list2(list1(q_d_exp), caddr(form)))
  }
  let bas = translate(cadr(form))
  let mut exp_ = translate(caddr(form))
  if eq(q_d_fixnum, car(exp_)) {
    let e = cdr(exp_)
    if eq(q_d_float, car(bas)) {
      list4(q_d_float, q_expt, cdr(bas), e)
    } else if eq(car(bas), q_d_fixnum) && symval(q_d_tr_numer).truthy() {
      // when NUMER:TRUE we have 1/2 evaluating to 0.5 therefore we have a
      // TR_NUMER switch to control this form numerical hackers at translate
      // time where it does the most good. -gjc
      cons(q_d_float, list3(q_expt, list2(q_float, cdr(bas)), e))
    } else if symval(q_d_tr_exponent).truthy() &&
      memq(car(bas), list2(q_d_fixnum, q_d_number)).truthy() {
      // It seems to me we can do this, although 2^-3 would result in a "cl
      // rat'l number"
      list4(q_d_number, q_expt, cdr(bas), e)
    } else {
      list4(q_d_any, q_power, cdr(bas), e)
    }
  } else {
    let mut clause2 : Value = Nil
    if eq(q_d_float, car(bas)) &&
      eq(q_d_rational, car(exp_)) &&
      !atom(caddr(exp_)) {
      clause2 = if equal(Fix(2L), caddr(caddr(exp_))) {
        exp_ = cadr(caddr(exp_))
        if num_eq(Fix(1L), exp_) {
          list3(q_d_float, q_sqrt, cdr(bas))
        } else if num_eq(Fix(-1L), exp_) {
          list3(q_d_float, q_op_sl, list2(q_sqrt, cdr(bas)))
        } else {
          list4(q_d_float, q_expt, list2(q_sqrt, cdr(bas)), exp_)
        }
      } else if eq(q_rat, caar(caddr(exp_))) {
        list4(q_d_float, q_expt, cdr(bas), d_float(caddr(exp_)))
      } else {
        Nil
      }
    }
    if clause2.truthy() {
      return clause2
    }
    // If the exponent is a float, we can't just translate straight to a
    // float because the base might be negative. However, if the base
    // happens to be a literal then we can check its sign. If it's
    // non-negative we know that the result of calling POWER will indeed be
    // a float.
    if eq(q_d_float, car(exp_)) &&
      (
        numberp(car(bas)) ||
        (
          eq(q_d_rational, car(bas)) &&
          eq(q_quote, second(bas)) &&
          !atom(third(bas)) &&
          eq(q_rat, caar(third(bas))) &&
          integerp(second(third(bas))) &&
          integerp(third(third(bas)))
        ) ||
        (
          memq(car(bas), list2(q_d_float, q_d_fixnum)).truthy() &&
          numberp(cdr(bas))
        )
      ) {
      let cl_base = if numberp(car(bas)) {
        car(bas)
      } else if eq(q_d_rational, car(bas)) {
        num_div(second(third(bas)), third(third(bas)))
      } else {
        cdr(bas)
      }
      if num_lt(cl_base, Fix(0L)) {
        list4(q_d_any, q_power, cdr(bas), cdr(exp_))
      } else {
        list4(q_d_float, q_power, cdr(bas), cdr(exp_))
      }
    } else {
      list4(q_d_any, q_power, cdr(bas), cdr(exp_))
    }
  }
}

///|
/// DEF%TR MABS
fn troper__tr_mabs(form : Value) -> Value raise {
  let form = translate(cadr(form))
  if covers(q_d_number, car(form)).truthy() {
    list3(car(form), q_abs, cdr(form))
  } else {
    list3(
      q_d_any,
      q_simplify,
      list3(q_list, transl__quote(list1(q_mabs)), dconvx(form)),
    )
  }
}

///|
/// DEF%TR %SIGNUM
fn troper__tr_signum(form : Value) -> Value raise {
  let r = translate(cadr(form))
  let mode = car(r)
  let arg = cdr(r)
  if memq(mode, list2(q_d_fixnum, q_d_float)).truthy() {
    cons(mode, list2(troper__q_cl_signum, arg))
  } else {
    // even in this unknown case we can do a hell of a lot better than
    // consing up a form to call the macsyma simplifier.
    list3(
      q_d_any,
      q_simplify,
      list3(q_list, transl__quote(list1(q_p_signum)), arg),
    )
  }
}

///|
/// DEF%TR $ENTIER
fn troper__tr_entier(form : Value) -> Value raise {
  let form = translate(cadr(form))
  if eq(q_d_fixnum, car(form)) {
    form
  } else if memq(car(form), list2(q_d_float, q_d_number)).truthy() {
    list3(q_d_fixnum, q_floor, cdr(form))
  } else {
    list3(
      if eq(car(form), q_d_rational) {
        q_d_fixnum
      } else {
        q_d_any
      },
      q_d_entier,
      cdr(form),
    )
  }
}

///|
/// DEF%TR $FLOAT
fn troper__tr_float(form : Value) -> Value raise {
  let form = translate(cadr(form))
  if covers(q_d_float, car(form)).truthy() {
    cons(q_d_float, dconv__dolfloat(form))
  } else {
    list3(q_d_any, q_d_float, cdr(form))
  }
}

///|
fn init_troper() -> Unit raise {
  defun(troper__q_cl_signum, args => signum(arg(args, 0)), name="cl:signum")
  transl__deftr(q_mminus, troper__tr_mminus)
  transl__deftr(q_mplus, troper__tr_mplus)
  transl__deftr(q_mtimes, troper__tr_mtimes)
  transl__deftr(q_mquotient, troper__tr_mquotient)
  transl__deftr(q_mexpt, troper__tr_mexpt)
  transl__deftr(q_rat, form => cons(q_d_rational, transl__quote(form)))
  transl__deftr(q_bigfloat, form => cons(q_d_any, transl__quote(form)))
  transl__deftr(q_mabs, troper__tr_mabs)
  transl__deftr(q_p_signum, troper__tr_signum)
  transl__deftr(q_d_entier, troper__tr_entier)
  transl__deftr(q_d_float, troper__tr_float)
}

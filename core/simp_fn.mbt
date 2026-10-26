// Port of src/simp-fn.lisp: assorted user-level functions of the
// simplifier ($numfactor, $constantp, $multthru, $expand, $integrate ...).

///|
fn d_polysign(x : Value) -> Value raise {
  let x = cadr(ratf(x))
  if equal(x, Fix(0L)) {
    Fix(0L)
  } else if pminusp(x).truthy() {
    Fix(-1L)
  } else {
    Fix(1L)
  }
}

///|
fn d_numfactor(x : Value) -> Value raise {
  let x = specrepcheck(x)
  if mnump(x).truthy() {
    x
  } else if atom(x) {
    Fix(1L)
  } else if !eq(caar(x), q_mtimes) {
    Fix(1L)
  } else if mnump(cadr(x)).truthy() {
    cadr(x)
  } else {
    Fix(1L)
  }
}

///|
fn d_constantp(x : Value) -> Value raise {
  if numberp(x) {
    t
  } else if atom(x) {
    if symbolp(x) {
      let v = get(x, q_sysconst)
      if v.truthy() {
        v
      } else {
        kindp(x, q_d_constant)
      }
    } else {
      Nil
    }
  } else if memq(caar(x), list2(q_rat, q_bigfloat)).truthy() {
    t
  } else if specrepp(x).truthy() {
    d_constantp(specdisrep(x))
  } else if mopp(caar(x)).truthy() || kindp(caar(x), q_d_constant).truthy() {
    for a in cdr(x).iter() {
      if !d_constantp(a).truthy() {
        return Nil
      }
    }
    t
  } else {
    Nil
  }
}

///|
fn d_scalarp(x : Value) -> Value raise {
  let v = consttermp(x)
  if v.truthy() {
    v
  } else {
    lbool(eq(scalarclass(x), q_d_scalar))
  }
}

///|
fn d_nonscalarp(x : Value) -> Value raise {
  lbool(eq(scalarclass(x), q_d_nonscalar))
}

///|
/// Resimplifies the expression EXPR based on the current environment.
/// This function is useful when the fact database, option variables, or
/// tellsimp rules have changed since the expression was last simplified.
fn d_resimplify(expr : Value) -> Value raise {
  resimplify(expr)
}

///|
fn d_sqrt(z : Value) -> Value raise {
  simplify(list2(list1(q_p_sqrt), z))
}

///|
/// Define a verb function $abs
fn d_abs(x : Value) -> Value raise {
  simplify(list2(list1(q_mabs), x))
}

///|
fn d_exp(z : Value) -> Value raise {
  simplify(list2(list1(q_p_exp), z))
}

///|
/// Support a function for code, which depends on an unsimplified noun form.
fn d_exp_form(z : Value) -> Value raise {
  list([list1(q_mexpt), q_d__pcte, z])
}

///|
fn d_orderlessp(a : Value, b : Value) -> Value raise {
  let a = d_totaldisrep(specrepcheck(a))
  let b = d_totaldisrep(specrepcheck(b))
  if !alike1(a, b).truthy() && great(b, a).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn d_ordergreatp(a : Value, b : Value) -> Value raise {
  let a = d_totaldisrep(specrepcheck(a))
  let b = d_totaldisrep(specrepcheck(b))
  if !alike1(a, b).truthy() && great(a, b).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn simp_fn__constp_or_inf(a : Value) -> Bool raise {
  constp(a).truthy() || memq(a, list2(q_d_inf, q_d_minf)).truthy()
}

///|
/// Test function to order a and b by magnitude. If it is not possible to
/// order a and b by magnitude they are ordered by great. This function can
/// be used by sort, e.g. sort([3,1,7,x,sin(1),minf],ordermagnitudep)
fn d_ordermagnitudep(a : Value, b : Value) -> Value raise {
  let a = d_totaldisrep(specrepcheck(a))
  let b = d_totaldisrep(specrepcheck(b))
  let mut sgn = Value::Nil
  if simp_fn__constp_or_inf(a) &&
    simp_fn__constp_or_inf(b) &&
    {
      sgn = d_csign(sub(b, a))
      memq(sgn, list([q_d_pos, q_d_neg, q_d_zero])).truthy()
    } {
    if eq(sgn, q_d_pos) {
      t
    } else if eq(sgn, q_d_zero) {
      if !alike1(a, b).truthy() {
        great(b, a)
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else if simp_fn__constp_or_inf(a) {
    t
  } else if simp_fn__constp_or_inf(b) {
    Nil
  } else if !alike1(a, b).truthy() {
    great(b, a)
  } else {
    Nil
  }
}

///|
fn d_multthru(e1 : Value, e2? : Value = Nil) -> Value raise {
  if e2.truthy() {
    // called with two args
    let arg1 = specrepcheck(e1)
    let arg2 = specrepcheck(e2)
    if atom(arg2) ||
      memq(caar(arg2), list2(q_mplus, q_mequal)) is Nil {
      mul2(arg1, arg2)
    } else if eq(caar(arg2), q_mequal) {
      list([
        car(arg2),
        d_multthru(arg1, e2=cadr(arg2)),
        d_multthru(arg1, e2=caddr(arg2)),
      ])
    } else {
      expandterms(arg1, cdr(arg2))
    }
  } else {
    // called with only one arg
    let arg2 = specrepcheck(e1)
    let mut arg1 = arg2
    let mut l1 = Value::Nil
    if atom(arg1) {
      return arg1
    } else if eq(caar(arg1), q_mnctimes) {
      arg1 = cdr(arg1)
      // nct
      while true {
        if mplusp(car(arg1)).truthy() {
          l1 = nreverse(l1)
          let rest = cdr(arg1)
          return addn(
            mapcar(
              u => simplifya(
                cons(list1(q_mnctimes), append_n([l1, list1(u), rest])),
                t,
              ),
              cdar(arg1),
            ),
            t,
          )
        }
        l1 = cons(car(arg1), l1)
        arg1 = cdr(arg1)
        if arg1 is Nil {
          return arg2
        }
      }
      Nil
    } else if !eq(caar(arg1), q_mtimes) {
      return arg1
    } else {
      arg1 = reverse(cdr(arg1))
      // times
      while true {
        if mplusp(car(arg1)).truthy() {
          l1 = nconc(l1, cdr(arg1))
          return expandterms(muln(l1, t), cdar(arg1))
        }
        l1 = cons(car(arg1), l1)
        arg1 = cdr(arg1)
        if arg1 is Nil {
          return arg2
        }
      }
      Nil
    }
  }
}

///|
fn d_expand(exp_ : Value, expop? : Value, expon? : Value) -> Value raise {
  let expop = match expop {
    Some(v) => v
    None => symval(q_d_maxposex)
  }
  let expon = match expon {
    Some(v) => v
    None => symval(q_d_maxnegex)
  }
  expand1(exp_, expop, expon)
}

///|
/// `(unwind-protect (body) (cleanup))`
fn simp_fn__unwind_protect(
  body : () -> Value raise,
  cleanup : () -> Unit raise,
) -> Value raise {
  let r = body() catch {
    e => {
      cleanup()
      raise e
    }
  }
  cleanup()
  r
}

///|
/// The expansion of the WITH-NEW-CONTEXT macro (maxmac.lisp).
fn simp_fn__with_new_context(
  sub_context : Value,
  body : () -> Value raise,
) -> Value raise {
  let my_context = gensym(prefix="$ctxt")
  mfuncall(q_d_supcontext, cons(my_context, sub_context)) |> ignore
  simp_fn__unwind_protect(body, () => d_killcontext(list1(my_context)) |> ignore)
}

///|
/// The following was formerly in SININT; it is needed in-core because of
/// the various calls to it.
fn d_integrate(
  expr : Value,
  x : Value,
  lo? : Value = Nil,
  hi? : Value = Nil,
) -> Value raise {
  if lo.truthy() && hi is Nil {
    wna_err(q_d_integrate) |> ignore
  }
  with_special(q_d_ratfac, Nil, () => if hi is Nil {
    simp_fn__with_new_context(list1(symval(q_context)), () => if memq(
        q_p_risch,
        symval(q_ear_nounl),
      ).truthy() {
      if symval(q_ear_in_risch_p).truthy() {
        // Give up; we're being called from RISCHINT by some path.
        list([list1(q_p_integrate), expr, x])
      } else {
        rischint(expr, x)
      }
    } else {
      sinint(expr, x)
    })
  } else {
    d_defint(expr, x, lo, hi)
  })
}

///|
/// No top-level forms.
fn init_simp_fn() -> Unit raise {
  ()
}

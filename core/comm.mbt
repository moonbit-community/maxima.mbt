// Port of src/comm.lisp: substitute, depends, gradef, diff, display, part
// and friends, list functions (first, rest, append, ...), num/denom,
// float, coeff, hipow/lopow, push/pop.

///|
fn d_substitute(new_ : Value, old : Value, expr? : Value) -> Value raise {
  match expr {
    Some(e) => maxima_substitute(new_, old, e)
    None => {
      let l = new_
      let mut z = old
      if d_listp(l).truthy() && d_listp(cadr(l)).truthy() && cddr(l) is Nil {
        d_substitute(cadr(l), z)
      } else if notloreq(l).truthy() {
        improper_arg_err(l, q_d_substitute)
      } else if eq(caar(l), q_mequal) {
        maxima_substitute(caddr(l), cadr(l), z)
      } else {
        for e in cdr(l).iter() {
          z = d_substitute(e, z)
        }
        z
      }
    }
  }
}

///|
/// $psubstitute is similar to $substitute. In distinction from $substitute
/// the function $psubstitute does parallel substitution, if the first
/// argument is a list of equations.
fn d_psubstitute(old : Value, new_ : Value, expr? : Value) -> Value raise {
  match expr {
    Some(e) => maxima_substitute(old, new_, e)
    None => {
      let l = old
      let z = new_
      if d_listp(l).truthy() && d_listp(cadr(l)).truthy() && cddr(l) is Nil {
        // A nested list.
        d_psubstitute(cadr(l), z)
      } else if d_listp(l).truthy() &&
        cddr(l) is Nil &&
        !atom(cadr(l)) &&
        eq(caar(cadr(l)), q_mequal) {
        // A list with one equation.
        d_psubstitute(cadr(l), z)
      } else if notloreq(l).truthy() {
        improper_arg_err(l, q_d_psubstitute)
      } else if eq(caar(l), q_mequal) {
        // Do a substitution for one equation.
        maxima_substitute(caddr(l), cadr(l), z)
      } else {
        // We have a list of equations. We do parallel substitution.
        with_special(q_d_simp, Nil, () => {
          let mut z = z
          let mut genlist : Value = Nil
          // At first substitute a gensym for the expressions of the left
          // hand side of the equations.
          for eqn in cdr(l).iter() {
            if !eq(q_mequal, caar(eqn)) {
              improper_arg_err(old, q_d_psubstitute) |> ignore
            }
            let gensymbol = gensym()
            // Store the gensym and the new expression into a list.
            genlist = cons(cons(gensymbol, caddr(eqn)), genlist)
            // Substitute a gensym for the old expression.
            z = maxima_substitute(gensymbol, cadr(eqn), z)
          }
          // Substitute the new expressions for the gensyms.
          for g in genlist.iter() {
            z = maxima_substitute(cdr(g), car(g), z)
          }
          // Resimplify the result.
          with_special(q_d_simp, t, () => resimplify(z))
        })
      }
    }
  }
}

///|
fn expthack(y : Value, z : Value) -> Value raise {
  if mnump(y).truthy() && mnump(z).truthy() {
    let y = div_star(z, y)
    return if numberp(y) { y } else { Nil }
  } else if atom(z) {
    if !mnump(y).truthy() {
      return Nil
    }
  } else if ratnump(z).truthy() || eq(caar(z), q_mplus) {
    return Nil
  }
  // (CSIMP) sets NN* and DN*
  let (yn, yd) = numden(y)
  let (zn, zd) = numden(z)
  let qd : Value = if equal(zd, Fix(1L)) && equal(yd, Fix(1L)) {
    Fix(1L)
  } else {
    let (nn, dn) = numden(div_star(zd, yd))
    if equal(dn, Fix(1L)) && equal(nn, Fix(1L)) {
      Fix(1L)
    } else if equal(nn, Fix(1L)) {
      div_star(Fix(1L), dn)
    } else if equal(dn, Fix(1L)) {
      nn
    } else {
      return Nil
    }
  }
  let (nn, dn) = numden(div_star(zn, yn))
  if equal(dn, Fix(1L)) {
    div_star(nn, qd)
  } else {
    Nil
  }
}

///|
fn subst_diff_match(l1 : Value, l2 : Value) -> Value raise {
  let l2 = copy_list(l2)
  let mut l = l1
  while l is Cons(_) {
    let mut failed = false
    let mut c = l2
    while true {
      if cdr(c) is Nil {
        failed = true
        break
      }
      if alike1(car(l), cadr(c)).truthy() {
        if fixnump(cadr(l)) && fixnump(caddr(c)) {
          if num_lt(cadr(l), caddr(c)) {
            rplacd(cdr(c), cons(num_sub(caddr(c), cadr(l)), cdddr(c))) |> ignore
          } else if num_eq(cadr(l), caddr(c)) {
            rplacd(c, cdddr(c)) |> ignore
          } else {
            failed = true
          }
        } else {
          failed = true
        }
        break
      }
      c = cddr(c)
    }
    if failed {
      return Nil
    }
    l = cddr(l)
  }
  l2
}

///|
/// This probably should be a subst or macro.
fn at_substp(z : Value) -> Value raise {
  lbool(
    symval(q_ear_atp).truthy() &&
    (
      eq(caar(z), q_p_derivative) ||
      eq(caar(z), q_p_del) ||
      memq(caar(z), symval(q_dummy_variable_operators)).truthy()
    ),
  )
}

///|
fn d_depends(args : Value) -> Value raise {
  if oddp(int(length(args))) {
    merr("depends: number of arguments must be even.", []) |> ignore
  }
  let mut args = args
  let mut l : Value = Nil
  while args is Cons(_) {
    if d_listp(first(args)).truthy() {
      for e in cdr(first(args)).iter() {
        l = cons(depends1(e, second(args)), l)
      }
    } else {
      l = cons(depends1(first(args), second(args)), l)
    }
    args = cddr(args)
  }
  i__doldependencies(nreverse(l))
}

///|
fn depends1(x : Value, y : Value) -> Value raise {
  nonsymchk(x, q_d_depends) |> ignore
  cons(
    list1(x),
    if d_listp(y).truthy() {
      cdr(y)
    } else {
      list1(y)
    },
  )
}

///|
fn d_dependencies(form : Value) -> Value raise {
  i__doldependencies(cdr(form))
}

///|
/// Port: share packages redefine DERIV, SDIFF and I-$DEPENDENCIES when
/// loaded (share/tensor/itensor.lisp); in CL every caller then reaches the
/// new definition through the function cell. Such a package installs its
/// definition in these hooks.
let comm__deriv_hook : Ref[((Value) -> Value raise)?] = Ref(None)

///|
let comm__sdiff_hook : Ref[((Value, Value) -> Value raise)?] = Ref(None)

///|
let comm__dependencies_hook : Ref[((Value) -> Value raise)?] = Ref(None)

///|
fn i__doldependencies(l : Value) -> Value raise {
  if comm__dependencies_hook.val is Some(f) {
    return f(l)
  }
  let mut res : Value = Nil
  for z in l.iter() {
    if atom(z) {
      merr("depends: argument must be a non-atomic expression; found ~M", [z])
      |> ignore
    } else {
      let mut zz = z
      let mut y : Value = Nil
      while zz is Cons(_) {
        let v = cadr(zz)
        if d_subvarp(v).truthy() && !member(caar(v), y).truthy() {
          y = cons(v, y)
        } else if !symbolp(v) {
          merr("depends: argument must be a symbol; found ~M", [v]) |> ignore
        } else if v.truthy() && !member(v, y).truthy() {
          y = cons(v, y)
        }
        zz = cdr(zz)
      }
      y = reverse(y)
      mputprop(caar(z), y, q_depends) |> ignore
      res = cons(cons(list1(caar(z)), y), res)
      if cdr(symval(q_d_dependencies)) is Nil {
        set(q_d_dependencies, list1(list2(q_mlist, q_simp))) |> ignore
      }
      add2lnc(cons(list1(caar(z)), y), symval(q_d_dependencies)) |> ignore
    }
  }
  cons(list2(q_mlist, q_simp), reverse(res))
}

///|
fn d_gradef(l : Value) -> Value raise {
  let mut l = cdr(l)
  let z = car(l)
  if atom(z) {
    if length(l) != 3 {
      merr("gradef: expected exactly three arguments.", []) |> ignore
    }
    let g = cons(cadr(l), meval(caddr(l)))
    mputprop(z, cons(g, mget(z, q_d_atomgrad)), q_d_atomgrad) |> ignore
    i__doldependencies(
      // Append existing dependencies
      list1(cons(list1(z), cons(cadr(l), mget(z, q_depends)))),
    )
    |> ignore
    add2lnc(z, symval(q_d_props)) |> ignore
    z
  } else if mopp1(caar(z)).truthy() || memq(q_array, cdar(z)).truthy() {
    merr(
      "gradef: argument cannot be a built-in operator or subscripted expression; found ~M",
      [z],
    )
  } else {
    let n = length(z) - length(l)
    if n < 0 {
      return wna_err(q_d_gradef)
    }
    for v in cdr(z).iter() {
      if !symbolp(v) {
        merr("gradef: argument must be a symbol; found ~M", [v]) |> ignore
      }
    }
    l = nconc(
      mapcar(x => remsimp(meval(x)), cdr(l)),
      mapcar(
        x => list4(list1(q_p_derivative), z, x, Fix(1L)),
        nthcdr(length(z) - n, z),
      ),
    )
    putprop(
      caar(z),
      sublis(
        mapcar2((a, b) => cons(a, b), cdr(z), mapcar(x => stripdollar(x), cdr(z))),
        cons(cdr(z), l),
      ),
      q_grad,
    )
    |> ignore
    if cdr(symval(q_d_gradefs)) is Nil {
      set(q_d_gradefs, list1(list2(q_mlist, q_simp))) |> ignore
    }
    add2lnc(cons(list1(caar(z)), cdr(z)), symval(q_d_gradefs)) |> ignore
    z
  }
}

///|
fn d_diff(args : Value) -> Value raise {
  with_special(q_derivlist, Nil, () => deriv(args))
}

///|
fn d_del(e : Value) -> Value raise {
  stotaldiff(e)
}

///|
fn deriv(e : Value) -> Value raise {
  if comm__deriv_hook.val is Some(f) {
    return f(e)
  }
  let mut e = e
  if e is Nil {
    wna_err(q_d_diff) |> ignore
  } else if cdr(e) is Nil {
    return stotaldiff(car(e))
  } else if cddr(e) is Nil {
    nconc(e, list1(Fix(1L))) |> ignore
  }
  let mut exp_ = car(e)
  e = copy_list(e)
  let mut z = e
  let mut count = 0L
  // labels: 0 = loop, 1 = loop2, 2 = doit, 3 = loop1, 4 = noun
  let mut lbl = 0
  while true {
    match lbl {
      0 => {
        let dl = symval(q_derivlist)
        if dl is Nil || member_equal(cadr(z), dl).truthy() {
          lbl = 2
          continue
        }
        z = cdr(z)
        lbl = 1
      }
      1 =>
        if cdr(z).truthy() {
          lbl = 0
        } else if cdr(e) is Nil {
          return exp_
        } else {
          lbl = 4
        }
      2 => {
        if nonvarcheck(cadr(z), q_d_diff).truthy() {
          ()
        } else if cddr(z) is Nil {
          wna_err(q_d_diff) |> ignore
        } else if !fixnump(caddr(z)) {
          lbl = 4
          continue
        } else {
          count = to_int64(caddr(z))
          if count < 0L {
            merr(
              "diff: order of derivative must be a nonnegative integer; found ~M",
              [caddr(z)],
            )
            |> ignore
          }
        }
        lbl = 3
      }
      3 => {
        if count == 0L {
          rplacd(z, cdddr(z)) |> ignore
          lbl = 1
          continue
        }
        exp_ = sdiff(exp_, cadr(z))
        if equal(exp_, Fix(0L)) {
          return Fix(0L)
        }
        count -= 1L
      }
      _ => return diff_pctderiv(cons(exp_, cdr(e)))
    }
  }
  Nil
}

///|
fn chainrule(e : Value, x : Value) -> Value raise {
  if symval(q_ear_islinp).truthy() {
    // sdiff is called from the function islinear.
    if !atom(e) && eq(caar(e), q_p_derivative) && !freel(cdr(e), x).truthy() {
      diff_pctderiv(list3(e, x, Fix(1L)))
    } else {
      Fix(0L)
    }
  } else {
    let ag = atomgrad(e, x)
    if ag.truthy() {
      return ag
    }
    let w = mget(
      if atom(e) {
        e
      } else if memq(q_array, cdar(e)).truthy() {
        caar(e)
      } else if atom(cadr(e)) {
        cadr(e)
      } else {
        caaadr(e)
      },
      q_depends,
    )
    if w is Nil {
      Fix(0L)
    } else {
      with_special(q_derivflag, Nil, () => addn(
        mapcar(
          u => {
            let y = sdiff(u, x)
            if equal(y, Fix(0L)) {
              Fix(0L)
            } else {
              let g = atomgrad(e, u)
              list3(
                list1(q_mtimes),
                if g.truthy() {
                  g
                } else {
                  list4(list1(q_p_derivative), e, u, Fix(1L))
                },
                y,
              )
            }
          },
          w,
        ),
        Nil,
      ))
    }
  }
}

///|
fn atomgrad(e : Value, x : Value) -> Value raise {
  if atom(e) {
    let y = mget(e, q_d_atomgrad)
    if y.truthy() {
      return assolike(x, y)
    }
  }
  Nil
}

///|
/// The args to SDIFF are assumed to be simplified.
fn sdiff(e : Value, x : Value) -> Value raise {
  if comm__sdiff_hook.val is Some(f) {
    return f(e, x)
  }
  // Remove a special representation from the variable of differentiation
  let x = specrepcheck(x)
  if alike1(e, x).truthy() {
    Fix(1L)
  } else if mnump(e).truthy() {
    Fix(0L)
  } else if atom(e) || memq(q_array, cdar(e)).truthy() {
    chainrule(e, x)
  } else if eq(caar(e), q_mrat) {
    ratdx(e, x)
  } else if eq(caar(e), q_mpois) {
    // Poisson series
    d_poisdiff(e, x)
  } else if eq(caar(e), q_mplus) {
    addn(sdiffmap(cdr(e), x), t)
  } else if mbagp(e).truthy() {
    cons(car(e), sdiffmap(cdr(e), x))
  } else if eq(caar(e), q_p_sum) || eq(caar(e), q_p_product) {
    diffsumprod(e, x)
  } else if eq(caar(e), q_p_at) {
    diff__pctat(e, x)
  } else if !depends(e, x).truthy() {
    Fix(0L)
  } else if eq(caar(e), q_mtimes) {
    addn(sdifftimes(cdr(e), x), t)
  } else if eq(caar(e), q_mexpt) {
    diffexpt(e, x)
  } else if eq(caar(e), q_mnctimes) {
    with_special(q_d_dotdistrib, t, () => add2(
      ncmuln(cons(sdiff(cadr(e), x), cddr(e)), t),
      ncmul2(cadr(e), sdiff(cons(list1(q_mnctimes), cddr(e)), x)),
    ))
  } else if symval(q_d_vect_cross).truthy() && eq(caar(e), q_d_op_tl) {
    add2_star(
      list3(list1(q_d_op_tl), cadr(e), sdiff(caddr(e), x)),
      list3(list1(q_d_op_tl), sdiff(cadr(e), x), caddr(e)),
    )
  } else if eq(caar(e), q_mncexpt) {
    diffncexpt(e, x)
  } else if eq(caar(e), q_p_log) || eq(caar(e), q_p_plog) {
    sdiffgrad(
      if !atom(cadr(e)) && eq(caaadr(e), q_mabs) {
        cons(car(e), cdadr(e))
      } else {
        e
      },
      x,
    )
  } else if eq(caar(e), q_p_derivative) {
    if atom(cadr(e)) || memq(q_array, cdr(caadr(e))).truthy() {
      chainrule(e, x)
    } else if freel(cddr(e), x).truthy() {
      diff_pctderiv(cons(sdiff(cadr(e), x), cddr(e)))
    } else {
      diff_pctderiv(list3(e, x, Fix(1L)))
    }
  } else if eq(caar(e), q_p_binomial) || eq(caar(e), q_p_beta) {
    let efact = d_makefact(e)
    mul2(factor(sdiff(efact, x)), div(e, efact))
  } else if eq(caar(e), q_p_integrate) {
    diffint(e, x)
  } else if eq(caar(e), q_p_laplace) {
    difflaplace(e, x)
  } else if eq(caar(e), q_mqapply) && eq(caaadr(e), q_d__pctf) {
    // Handle %f, hypergeometric function
    //
    // The derivative of %f[p,q]([a1,...,ap],[b1,...,bq],z) is
    //
    // a1*a2*...*ap/(b1*b2*...*bq)
    //   *%f[p,q]([a1+1,a2+1,...,ap+1],[b1+1,b2+1,...,bq+1],z)
    let arg1 = cdr(third(e))
    let arg2 = cdr(fourth(e))
    let v = fifth(e)
    muln_([
      sdiff(v, x),
      div(mull(arg1), mull(arg2)),
      list([
        list1(q_mqapply),
        list3(list2(q_d__pctf, q_array), int(length(arg1)), int(length(arg2))),
        cons(list1(q_mlist), incr1(arg1)),
        cons(list1(q_mlist), incr1(arg2)),
        v,
      ]),
    ])
  } else {
    sdiffgrad(e, x)
  }
}

///|
fn sdiffgrad(e : Value, x : Value) -> Value raise {
  let fun = caar(e)
  if eq(fun, q_mqapply) && zl_get(caaadr(e), q_grad).truthy() {
    // Change the array function f[n](x) to f(n,x), call sdiffgrad again.
    let result = sdiffgrad(
      cons(list1(caaadr(e)), append(cdadr(e), cddr(e))),
      x,
    )
    // If noun form for f(n,x), adjust the noun form for f[n](x)
    return if isinop(result, q_p_derivative).truthy() {
      if !depends(e, x).truthy() {
        Fix(0L)
      } else {
        diff_pctderiv(list3(e, x, Fix(1L)))
      }
    } else {
      result
    }
  }
  // extension for pdiff.
  if get(q_d_pderivop, q_operators).truthy() {
    let r = mfuncall(q_sdiffgrad_pdiff, list2(e, x))
    if r.truthy() {
      return r
    }
  }
  // two line extension for hypergeometric.
  if equal(fun, q_p_hypergeometric) && get(q_p_hypergeometric, q_operators).truthy() {
    return diff_hypergeometric(second(e), third(e), fourth(e), x)
  }
  let grad : Value = if eq(fun, q_mqapply) { Nil } else { zl_get(fun, q_grad) }
  if grad is Nil {
    return if !depends(e, x).truthy() {
      Fix(0L)
    } else {
      diff_pctderiv(list3(e, x, Fix(1L)))
    }
  }
  if length(cdr(e)) != length(car(grad)) {
    return merr("~:M: expected exactly ~M arguments.", [
      fun,
      int(length(car(grad))),
    ])
  }
  let args = sdiffmap(cdr(e), x)
  // A derivative given as an expression is in the placeholder names of the
  // DEFGRAD and gets the arguments substituted for them, in parallel, as an
  // argument may itself be a placeholder name.  A derivative given as a
  // function gets the arguments; its result is substituted into the same
  // way, unless it is returned with a second value of T, which says that
  // it was built from the arguments and is final (the port's function
  // values return one value: the function sets `comm__grad_final`).
  let subst = cons(
    list1(q_mlist),
    mapcar2((a, b) => list3(list1(q_mequal), a, b), car(grad), cdr(e)),
  )
  let mut l1 = cdr(grad)
  let mut as_ = args
  let mut l2 : Value = Nil
  while l1 is Cons(_) {
    l2 = cons(
      if equal(car(as_), Fix(0L)) {
        Fix(0L)
      } else if functionp_(car(l1)).truthy() {
        comm__grad_final.val = false
        let d = apply(car(l1), cdr(e))
        let final = comm__grad_final.val
        comm__grad_final.val = false
        if final {
          d
        } else {
          d_psubstitute(subst, d)
        }
      } else {
        d_psubstitute(subst, car(l1))
      },
      l2,
    )
    l1 = cdr(l1)
    as_ = cdr(as_)
  }
  let result = addn(mapcar2((a, b) => mul2(a, b), nreverse(l2), args), t)
  if result is Nil || !freeof(Nil, result).truthy() {
    // A derivative has returned NIL. Return a noun form.
    if !depends(e, x).truthy() {
      Fix(0L)
    } else {
      diff_pctderiv(list3(e, x, Fix(1L)))
    }
  } else {
    result
  }
}

///|
/// Second value of a DEFGRAD derivative function (see SDIFFGRAD): set to
/// true by a derivative function whose result is final.
let comm__grad_final : Ref[Bool] = Ref(false)

///|
fn sdiffmap(e : Value, x : Value) -> Value raise {
  mapcar(term => sdiff(term, x), e)
}

///|
fn sdifftimes(l : Value, x : Value) -> Value raise {
  let mut l = l
  let mut left : Value = Nil
  let mut out : Value = Nil
  while true {
    let term = car(l)
    l = cdr(l)
    out = cons(muln(cons(sdiff(term, x), append(left, l)), t), out)
    if l is Nil {
      break
    }
    left = cons(term, left)
  }
  out
}

///|
fn diffexpt(e : Value, x : Value) -> Value raise {
  if mnump(caddr(e)).truthy() {
    mul3(
      caddr(e),
      power(cadr(e), addk(caddr(e), Fix(-1L))),
      sdiff(cadr(e), x),
    )
  } else {
    mul2(
      e,
      add2(
        mul3(power(cadr(e), Fix(-1L)), caddr(e), sdiff(cadr(e), x)),
        mul2(simplifya(list2(list1(q_p_log), cadr(e)), t), sdiff(caddr(e), x)),
      ),
    )
  }
}

///|
fn diff_pctderiv(e : Value) -> Value raise {
  with_special(q_derivflag, Nil, () => simplifya(
    cons(list1(q_p_derivative), e),
    t,
  ))
}

///|
fn atvarschk(argl : Value) -> Value raise {
  let mut largl = length(argl)
  let latvrs = length(symval(q_atvars))
  let mut l : Value = Nil
  while latvrs < largl {
    l = cons(
      implode(cons(Char('$'), cons(Char('@'), mexploden(int(largl))))),
      l,
    )
    largl -= 1
  }
  nconc(symval(q_atvars), l)
}

///|
fn notloreq(x : Value) -> Value raise {
  lbool(
    atom(x) ||
    !(eq(caar(x), q_mlist) || eq(caar(x), q_mequal)) ||
    (eq(caar(x), q_mlist) && some(u => !mequalp(u).truthy(), cdr(x))),
  )
}

///|
fn remsimp(e : Value) -> Value raise {
  if atom(e) {
    e
  } else {
    cons(delsimp(car(e)), mapcar(x => remsimp(x), cdr(e)))
  }
}

///|
fn d_trunc(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) {
    cons(append(car(e), list1(q_trunc)), cdr(e))
  } else if mbagp(e).truthy() {
    cons(car(e), mapcar(x => d_trunc(x), cdr(e)))
  } else if specrepp(e).truthy() {
    d_trunc(specdisrep(e))
  } else {
    e
  }
}

///|
fn nonvarcheck(e : Value, fn_ : Value) -> Value raise {
  if mnump(e).truthy() ||
    maxima_integerp(e).truthy() ||
    d_constantp(e).truthy() ||
    (!atom(e) && !eq(caar(e), q_mqapply) && mopp1(caar(e)).truthy()) {
    merr("~:M: second argument must be a variable; found ~M", [fn_, e])
  } else {
    Nil
  }
}

///|
fn d_ldisplay(form : Value) -> Value raise {
  disp1(cdr(form), t, t)
}

///|
fn d_ldisp(args : Value) -> Value raise {
  disp1(args, t, Nil)
}

///|
fn d_display(form : Value) -> Value raise {
  disp1(cdr(form), Nil, t)
}

///|
fn d_disp(args : Value) -> Value raise {
  disp1(args, Nil, Nil)
}

///|
fn disp1(ll : Value, lablist : Value, eqnsp : Value) -> Value raise {
  let lablist = if lablist.truthy() {
    list1(list2(q_mlist, q_simp))
  } else {
    Nil
  }
  with_special(q_d_dispflag, t, () => {
    for l in ll.iter() {
      let mut ans = if eqnsp.truthy() { meval(l) } else { l }
      if eqnsp.truthy() && !mequalp(ans).truthy() {
        ans = list3(list2(q_mequal, q_simp), disp2(l), ans)
      }
      if lablist.truthy() {
        nconc(lablist, list1(elabel(ans))) |> ignore
      }
      let tim = acall__get_internal_run_time()
      with_special(q_ear_display_labels_p, lbool(lablist.truthy()), () => displa(
        list3(
          list1(q_mlabel),
          if lablist.truthy() {
            symval(q_ear_linelabel)
          } else {
            Nil
          },
          ans,
        ),
      ))
      |> ignore
      mterpri() |> ignore
      timeorg(tim) |> ignore
    }
    if lablist.truthy() {
      lablist
    } else {
      q_d_done
    }
  })
}

///|
fn disp2(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mqapply) {
    cons(
      list1(q_mqapply),
      cons(
        cons(caadr(e), mapcar(x => meval(x), cdadr(e))),
        mapcar(x => meval(x), cddr(e)),
      ),
    )
  } else if eq(caar(e), q_msetq) {
    disp2(cadr(e))
  } else if eq(caar(e), q_mset) {
    disp2(meval(cadr(e)))
  } else if eq(caar(e), q_mlist) {
    cons(car(e), mapcar(x => disp2(x), cdr(e)))
  } else if mspecfunp(caar(e)).truthy() {
    e
  } else {
    cons(car(e), mapcar(x => meval(x), cdr(e)))
  }
}

///|
/// Construct a new intermediate result label, and bind it to the
/// expression e. The global flag $NOLABELS is ignored; the label is always
/// bound. Otherwise (if ELABEL were to observe $NOLABELS) it would be
/// impossible to programmatically refer to intermediate result expression.
fn elabel(e : Value) -> Value raise {
  if !checklabel(symval(q_d_linechar)).truthy() {
    set(q_d_linenum, num_add(symval(q_d_linenum), Fix(1L))) |> ignore
  }
  // <-- This is pretty ugly. MAKELABEL should take another argument.
  with_special(q_d_nolabels, Nil, () => makelabel(symval(q_d_linechar)))
  |> ignore
  set(symval(q_ear_linelabel), e) |> ignore
  symval(q_ear_linelabel)
}

///|
fn d_dispterms(e : Value) -> Value raise {
  if atom(e) || eq(caar(e), q_bigfloat) {
    displa(e) |> ignore
  } else if specrepp(e).truthy() {
    d_dispterms(specdisrep(e)) |> ignore
  } else {
    with_special(q_d_dispflag, t, () => {
      mterpri() |> ignore
      displa(getop(mop(e))) |> ignore
      let terms = if eq(caar(e), q_mplus) && !symval(q_d_powerdisp).truthy() {
        reverse(cdr(e))
      } else {
        margs(e)
      }
      for x in terms.iter() {
        mterpri() |> ignore
        displa(x) |> ignore
        mterpri() |> ignore
      }
    })
    mterpri() |> ignore
  }
  q_d_done
}

///|
fn d_dispform(e : Value, flag? : Value) -> Value raise {
  match flag {
    Some(f) =>
      if !eq(f, q_d_all) {
        merr("dispform: second argument, if present, must be 'all'; found ~M", [
          f,
        ])
        |> ignore
      }
    None => ()
  }
  if atom(e) {
    return e
  }
  let e = if flag is Some(_) { nformat_all(e) } else { nformat(e) }
  if atom(e) || memq(q_simp, cdar(e)).truthy() {
    e
  } else {
    cons(
      cons(caar(e), cons(q_simp, cdar(e))),
      if eq(caar(e), q_mplus) && !symval(q_d_powerdisp).truthy() {
        reverse(cdr(e))
      } else {
        cdr(e)
      },
    )
  }
}

///|
/// These functions implement the Macsyma functions $op and $operatorp.
fn d_op(expr : Value) -> Value raise {
  with_special(q_d_partswitch, Nil, () => d_part(list2(expr, Fix(0L))))
}

///|
fn d_operatorp(expr : Value, oplist : Value) -> Value raise {
  if d_listp(oplist).truthy() {
    d_member(d_op(expr), oplist)
  } else {
    alike1(d_op(expr), oplist)
  }
}

///|
fn d_part(args : Value) -> Value raise {
  mpart(args, Nil, Nil, symval(q_d_inflag), q_d_part)
}

///|
fn d_inpart(args : Value) -> Value raise {
  mpart(args, Nil, Nil, t, q_d_inpart)
}

///|
fn d_substpart(l : Value) -> Value raise {
  with_special(q_substp, t, () => mpart(
    cdr(l),
    t,
    Nil,
    symval(q_d_inflag),
    q_d_substpart,
  ))
}

///|
fn d_substinpart(l : Value) -> Value raise {
  with_special(q_substp, t, () => mpart(cdr(l), t, Nil, t, q_d_substinpart))
}

///|
/// called only by TRANSLATE
fn part1(
  arglist : Value,
  substflag : Value,
  dispflag : Value,
  inflag : Value,
  fn_ : Value,
) -> Value raise {
  with_special(q_substp, t, () => mpart(arglist, substflag, dispflag, inflag, fn_))
}

///|
fn make_mbox_for_mpart(e : Value, label : Value) -> Value raise {
  if eq(label, t) {
    list2(list1(q_mbox), e)
  } else {
    make_mbox(e, l=car(label))
  }
}

///|
fn comm__set_piece(v : Value) -> Value {
  set(q_d_piece, v)
}

///|
fn mpart(
  arglist : Value,
  substflag : Value,
  dispflag : Value,
  inflag : Value,
  fn_ : Value,
) -> Value raise {
  let specp = substflag.truthy() || dispflag.truthy()
  let mut arglist = arglist
  let mut inflag = inflag.truthy()
  let mut substitem : Value = Nil
  if substflag.truthy() {
    substitem = car(arglist)
    arglist = cdr(arglist)
  }
  if arglist is Nil {
    wna_err(fn_) |> ignore
  }
  let mut exp_ = if substflag.truthy() {
    meval(car(arglist))
  } else {
    car(arglist)
  }
  arglist = cdr(arglist)
  if arglist is Nil {
    comm__set_piece(exp_) |> ignore
    return if substflag.truthy() {
      meval(substitem)
    } else if dispflag.truthy() {
      make_mbox_for_mpart(exp_, dispflag)
    } else {
      exp_
    }
  }
  if !inflag {
    if (d_listp(exp_).truthy() && cdr(arglist) is Nil) ||
      (
        d_matrixp(exp_).truthy() &&
        (cdr(arglist) is Nil || cddr(arglist) is Nil)
      ) {
      inflag = true
    } else if !specp {
      exp_ = nformat(exp_)
    } else {
      exp_ = nformat_all(exp_)
    }
  } else if specrepp(exp_).truthy() {
    exp_ = specdisrep(exp_)
  }
  if atom(exp_) && !symval(q_d_partswitch).truthy() {
    merr("~:M: argument must be a non-atomic expression; found ~:M", [fn_, exp_])
    |> ignore
  }
  if inflag && specp {
    exp_ = copy_tree(exp_)
  }
  if substflag.truthy() {
    // Replace all occurrences of 'rat with 'mquotient when in subst.
    let e0 = exp_
    exp_ = with_special(q_d_simp, Nil, () => maxima_substitute(
      q_mquotient,
      q_rat,
      e0,
    ))
  }
  let exp_star = exp_
  let mut arg : Value = Nil
  let mut argn = 0L
  let mut arg1 : Value = Nil
  let mut exp1 : Value = Nil
  let mut sevlist : Value = Nil
  let mut count = 0L
  let mut prevcount = 0L
  let mut lastelem = 0L
  let mut lastcount = 0L
  // labels: 0 start, 1 loop, 2 a, 3 err, 4 bad, 5 several, 6 sevloop,
  // 7 count, 8 end
  let mut lbl = 0
  while true {
    match lbl {
      0 => {
        // start
        if atom(exp_) || eq(caar(exp_), q_bigfloat) {
          lbl = 3
          continue
        }
        arg = if substflag.truthy() {
          meval(car(arglist))
        } else {
          car(arglist)
        }
        if equal(arg, Fix(0L)) {
          arglist = cdr(arglist)
          if mnump(substitem).truthy() {
            merr("~:M: argument cannot be a number; found ~M", [fn_, substitem])
            |> ignore
          } else if specp && arglist.truthy() {
            if eq(caar(exp_), q_mqapply) {
              exp_ = cadr(exp_)
              lbl = 0
              continue
            } else {
              merr("~:M: invalid operator.", [fn_]) |> ignore
            }
          }
          comm__set_piece(getop(mop(exp_))) |> ignore
          if substflag.truthy() {
            substitem = getopr(meval(substitem))
            if mnump(substitem).truthy() {
              merr("~:M: argument cannot be a number; found ~M", [fn_, substitem])
              |> ignore
            } else if !atom(substitem) {
              if !eq(caar(exp_), q_mqapply) {
                rplaca(rplacd(exp_, cons(car(exp_), cdr(exp_))), list1(q_mqapply))
                |> ignore
              }
              rplaca(cdr(exp_), substitem) |> ignore
              return resimplify(exp_star)
            } else if eq(caar(exp_), q_mqapply) {
              rplacd(exp_, cddr(exp_)) |> ignore
            }
            rplaca(
              exp_,
              cons(
                substitem,
                if memq(q_array, cdar(exp_)).truthy() && !mopp(substitem).truthy() {
                  list1(q_array)
                } else {
                  Nil
                },
              ),
            )
            |> ignore
            return resimplify(exp_star)
          } else if dispflag.truthy() {
            rplacd(exp_, cdr(make_mbox_for_mpart(copy_tree(exp_), dispflag)))
            |> ignore
            rplaca(
              exp_,
              if eq(dispflag, t) {
                list1(q_mbox)
              } else {
                list1(q_mlabox)
              },
            )
            |> ignore
            return resimplify(exp_star)
          } else {
            if arglist.truthy() {
              exp_ = symval(q_d_piece)
              lbl = 2
              continue
            }
            return symval(q_d_piece)
          }
        } else if !atom(arg) {
          lbl = 5
          continue
        } else if !fixnump(arg) {
          merr("~:M: argument must be an integer; found ~M", [fn_, arg]) |> ignore
        } else if num_lt(arg, Fix(0L)) {
          lbl = 4
          continue
        }
        argn = to_int64(arg)
        if eq(caar(exp_), q_mqapply) {
          exp_ = cdr(exp_)
        }
        lbl = 1
      }
      1 => {
        // loop
        if argn != 0L {
          argn -= 1L
          exp_ = cdr(exp_)
          if exp_ is Nil {
            lbl = 3
          }
          continue
        }
        arglist = cdr(arglist)
        if arglist is Nil {
          return if substflag.truthy() {
            comm__set_piece(resimplify(car(exp_))) |> ignore
            rplaca(exp_, meval(substitem)) |> ignore
            resimplify(exp_star)
          } else if dispflag.truthy() {
            comm__set_piece(resimplify(car(exp_))) |> ignore
            rplaca(exp_, make_mbox_for_mpart(car(exp_), dispflag)) |> ignore
            resimplify(exp_star)
          } else if inflag {
            comm__set_piece(car(exp_))
          } else {
            comm__set_piece(simplify(car(exp_)))
          }
        }
        exp_ = car(exp_)
        lbl = 2
      }
      2 => {
        // a
        if !inflag && !specp {
          exp_ = nformat(exp_)
        } else if specrepp(exp_).truthy() {
          exp_ = specdisrep(exp_)
        }
        lbl = 0
      }
      3 => {
        // err
        let ps = symval(q_d_partswitch)
        if eq(ps, q_mapply) {
          return merr("~M: invalid index ~M of list or matrix.", [
            fn_,
            car(arglist),
          ])
        } else if ps.truthy() {
          return comm__set_piece(q_d_end)
        } else {
          return merr("~:M: fell off the end.", [fn_])
        }
      }
      4 =>
        // bad
        return improper_arg_err(arg, fn_)
      5 => {
        // several
        if !(eq(caar(arg), q_mlist) || eq(caar(arg), q_d_allbut)) ||
          cdr(arglist).truthy() {
          lbl = 4
          continue
        }
        exp1 = cons(
          caar(exp_),
          if memq(q_array, cdar(exp_)).truthy() {
            list1(q_array)
          } else {
            Nil
          },
        )
        if eq(caar(exp_), q_mqapply) {
          sevlist = list2(cadr(exp_), exp1)
          exp_ = cddr(exp_)
        } else {
          sevlist = list1(exp1)
          exp_ = cdr(exp_)
        }
        arg1 = cdr(arg)
        prevcount = 0L
        exp1 = exp_
        for a in arg1.iter() {
          if !fixnump(a) {
            merr("~:M: argument must be an integer; found ~M", [fn_, a]) |> ignore
          }
        }
        if specp && eq(caar(arg), q_mlist) {
          if substflag.truthy() {
            lastelem = to_int64(car(last(arg1)))
          }
          arg1 = sort_list(copy_list(arg1), (a, b) => num_lt(a, b))
        }
        if eq(caar(arg), q_d_allbut) {
          let n = length(exp_)
          for i in arg1.iter() {
            if num_lt(i, Fix(1L)) || num_gt(i, int(n)) {
              merr("~:M: index must be in range 1 to ~M, inclusive; found ~M", [
                fn_,
                int(n),
                i,
              ])
              |> ignore
            }
          }
          let mut arg2 : Value = Nil
          let mut i = n
          while i != 0 {
            if !member_equal(int(i), arg1).truthy() {
              arg2 = cons(int(i), arg2)
            }
            i -= 1
          }
          arg1 = arg2
          if substflag.truthy() {
            lastelem = to_int64(car(last(arg1)))
          }
        }
        if arg1 is Nil {
          lbl = if specp { 4 } else { 8 }
          continue
        }
        if substflag.truthy() {
          lastcount = lastelem
        }
        lbl = 6
      }
      6 => {
        // sevloop
        let a1 = to_int64(car(arg1))
        if specp {
          count = a1 - prevcount
          prevcount = a1
        } else {
          count = a1
        }
        if count < 1L {
          lbl = 4
          continue
        }
        if substflag.truthy() && a1 < lastelem {
          lastcount -= 1L
        }
        lbl = 7
      }
      7 => {
        // count
        if exp_ is Nil {
          lbl = 3
          continue
        }
        if count != 1L {
          count -= 1L
          exp_ = cdr(exp_)
          continue
        }
        sevlist = cons(car(exp_), sevlist)
        arg1 = cdr(arg1)
        lbl = 8
      }
      _ => {
        // end
        if arg1 is Nil {
          sevlist = nreverse(sevlist)
          comm__set_piece(
            if inflag || !specp {
              simplify(sevlist)
            } else {
              resimplify(sevlist)
            },
          )
          |> ignore
          return if substflag.truthy() {
            rplaca(nthcdr(lastcount.to_int() - 1, exp1), meval(substitem))
            |> ignore
            resimplify(exp_star)
          } else if dispflag.truthy() {
            rplaca(exp_, make_mbox_for_mpart(car(exp_), dispflag)) |> ignore
            resimplify(exp_star)
          } else {
            symval(q_d_piece)
          }
        } else if substflag.truthy() {
          if cdr(exp_) is Nil {
            lbl = 3
            continue
          }
          rplaca(exp_, cadr(exp_)) |> ignore
          rplacd(exp_, cddr(exp_)) |> ignore
        } else if dispflag.truthy() {
          rplaca(exp_, make_mbox_for_mpart(car(exp_), dispflag)) |> ignore
          exp_ = cdr(exp_)
        } else {
          exp_ = exp1
        }
        lbl = 6
      }
    }
  }
  Nil
}

///|
fn getop(x : Value) -> Value raise {
  if symbolp(x) {
    let o = get(x, q_op)
    if o.truthy() {
      return o
    }
  }
  x
}

///|
fn d_cons(x : Value, e : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, q_d_cons, t) |> ignore
  simplifya(mcons_exp_args(e, cons(x, margs(e))), t)
}

///|
fn d_endcons(x : Value, e : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, q_d_endcons, t) |> ignore
  simplifya(mcons_exp_args(e, append(margs(e), list1(x))), t)
}

///|
fn d_reverse(e : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, q_d_reverse, Nil) |> ignore
  simplifya(mcons_exp_args(e, reverse(margs(e))), t)
}

///|
fn d_append(args : Value) -> Value raise {
  if args is Nil {
    simplifya(list1(list1(q_mlist)), t)
  } else {
    let arg1 = specrepcheck(first(args))
    atomchk(arg1, q_d_append, Nil) |> ignore
    let op = mop(arg1)
    let arrp = memq(q_array, cdar(arg1)).truthy()
    let parts = mapcar(
      u => {
        let u = specrepcheck(u)
        atomchk(u, q_d_append, Nil) |> ignore
        if !(
            alike1(op, mop(u)).truthy() &&
            arrp == memq(q_array, cdar(u)).truthy()
          ) {
          merr("append: operators of arguments must all be the same.", [])
          |> ignore
        }
        margs(u)
      },
      args,
    )
    simplifya(mcons_exp_args(arg1, append_n(list_to_array(parts))), t)
  }
}

///|
fn mcons_exp_args(e : Value, args : Value) -> Value raise {
  if eq(caar(e), q_mqapply) {
    list_star([delsimp(car(e)), cadr(e), args])
  } else {
    cons(delsimp(car(e)), args)
  }
}

///|
fn format1(e : Value) -> Value raise {
  if d_listp(e).truthy() {
    e
  } else if symval(q_d_inflag).truthy() {
    specrepcheck(e)
  } else {
    nformat(e)
  }
}

///|
fn d_first(e : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, q_d_first, Nil) |> ignore
  if cdr(e) is Nil {
    merr("first: empty argument.", []) |> ignore
  }
  car(margs(e))
}

///|
/// The functions second thru tenth (MAKE-NTH in the Lisp code).
fn comm__make_nth(e : Value, sim : Value, i : Int) -> Value raise {
  let e = format1(e)
  atomchk(e, sim, Nil) |> ignore
  if length(margs(e)) < i {
    merr("~:M: no such element in ~M", [sim, e]) |> ignore
  }
  nth(i - 1, margs(e))
}

///|
fn d_rest(e : Value, n? : Value) -> Value raise {
  let n_supplied = n is Some(_)
  let mut n = n.unwrap_or(Fix(1L))
  if n_supplied && equal(n, Fix(0L)) {
    return e
  }
  let mut m = format1(e)
  atomchk(m, q_d_rest, Nil) |> ignore
  let mut revp = false
  if n_supplied && !fixnump(n) {
    merr("rest: second argument, if present, must be an integer; found ~M", [n])
    |> ignore
  } else if minusp(n) {
    n = num_neg(n)
    revp = true
  }
  if num_lt(int(length(margs(m))), n) {
    if symval(q_d_partswitch).truthy() {
      return q_d_end
    } else {
      merr("rest: fell off the end.", []) |> ignore
    }
  }
  let fun = car(m)
  let mut fun1 : Value = Nil
  if eq(car(fun), q_mqapply) {
    fun1 = cadr(m)
    m = cdr(m)
  }
  m = cdr(m)
  if revp {
    m = reverse(m)
  }
  m = nthcdr(to_int(n), m)
  m = cons(
    if eq(car(fun), q_mlist) {
      fun
    } else {
      delsimp(fun)
    },
    if revp {
      nreverse(m)
    } else {
      m
    },
  )
  if eq(car(fun), q_mqapply) {
    return cons(car(m), cons(fun1, cdr(m)))
  }
  m
}

///|
fn d_last(e : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, q_d_last, Nil) |> ignore
  if cdr(e) is Nil {
    merr("last: empty argument.", []) |> ignore
  }
  car(last(e))
}

///|
fn d_firstn(e : Value, n : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, q_d_firstn, Nil) |> ignore
  if !fixnump(n) || minusp(n) {
    merr("firstn: second argument must be a nonnegative integer; found: ~M", [n])
    |> ignore
  }
  let m = d_length(e)
  if num_gt(n, m) {
    d_rest(e, n=Fix(0L))
  } else {
    d_rest(e, n=num_sub(n, m))
  }
}

///|
fn d_lastn(e : Value, n : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, q_d_lastn, Nil) |> ignore
  if !fixnump(n) || minusp(n) {
    merr("lastn: second argument must be a nonnegative integer; found: ~M", [n])
    |> ignore
  }
  let m = d_length(e)
  if num_gt(n, m) {
    d_rest(e, n=Fix(0L))
  } else {
    d_rest(e, n=num_sub(m, n))
  }
}

///|
fn d_args(e : Value) -> Value raise {
  let formatted = format1(e)
  atomchk(formatted, q_d_args, Nil) |> ignore
  simplifya(cons(list1(q_mlist), margs(formatted)), lbool(eq(e, formatted)))
}

///|
fn d_delete(x : Value, l : Value, n? : Value) -> Value raise {
  let n_supplied = n is Some(_)
  let n = n.unwrap_or(Fix(-1L))
  // if n is set, it must be a nonneg fixnum
  if n_supplied && (!fixnump(n) || minusp(n)) {
    merr(
      "delete: third argument, if present, must be a nonnegative integer; found ~M",
      [n],
    )
    |> ignore
  }
  let l = specrepcheck(l)
  atomchk(l, q_d_delete, t) |> ignore
  let x = specrepcheck(x)
  let l = cons(delsimp(car(l)), copy_list(cdr(l)))
  let mut n = to_int64(n)
  let mut l1 = if eq(caar(l), q_mqapply) { cdr(l) } else { l }
  while !(cdr(l1) is Nil || n == 0L) {
    if alike1(x, specrepcheck(cadr(l1))).truthy() {
      n -= 1L
      rplacd(l1, cddr(l1)) |> ignore
    } else {
      l1 = cdr(l1)
    }
  }
  l
}

///|
fn d_length(e : Value) -> Value raise {
  let e = if d_listp(e).truthy() {
    e
  } else if symval(q_d_inflag).truthy() || !d_ratp(e).truthy() {
    specrepcheck(e)
  } else {
    d_ratdisrep(e)
  }
  if symbolp(e) {
    merr("length: argument cannot be a symbol; found ~:M", [e])
  } else if numberp(e) || eq(caar(e), q_bigfloat) {
    if !symval(q_d_inflag).truthy() && mnegp(e).truthy() {
      Fix(1L)
    } else {
      merr("length: argument cannot be a number; found ~:M", [e])
    }
  } else if symval(q_d_inflag).truthy() ||
    !(eq(caar(e), q_mtimes) || eq(caar(e), q_mexpt)) {
    int(length(margs(e)))
  } else if eq(caar(e), q_mexpt) {
    if alike1(caddr(e), mk_simp(q_rat, [Fix(1L), Fix(2L)])).truthy() &&
      symval(q_d_sqrtdispflag).truthy() {
      Fix(1L)
    } else {
      Fix(2L)
    }
  } else {
    int(length(cdr(nformat(e))))
  }
}

///|
fn d_atom(x : Value) -> Value raise {
  let x = specrepcheck(x)
  lbool(atom(x) || eq(caar(x), q_bigfloat))
}

///|
fn d_symbolp(x : Value) -> Value raise {
  lbool(symbolp(specrepcheck(x)))
}

///|
/// Return ($NUM E) and ($DENOM E) as two values, more efficiently.
fn num_denom_split(e : Value) -> (Value, Value) raise {
  if atom(e) {
    return (e, Fix(1L))
  }
  let op = caar(e)
  if eq(op, q_mrat) {
    let e = taychk2rat(e)
    (cons(car(e), cons(cadr(e), Fix(1L))), cons(car(e), cons(cddr(e), Fix(1L))))
  } else if eq(op, q_rat) {
    (cadr(e), caddr(e))
  } else {
    let x = nformat(e)
    let op = caar(x)
    if eq(op, q_mquotient) {
      (simplify(cadr(x)), simplify(caddr(x)))
    } else if eq(op, q_mminus) {
      let x = cadr(x)
      if consp(x) && eq(caar(x), q_mquotient) {
        (
          simplify(list3(list1(q_mtimes), Fix(-1L), cadr(x))),
          simplify(caddr(x)),
        )
      } else {
        (e, Fix(1L))
      }
    } else {
      (e, Fix(1L))
    }
  }
}

///|
/// Return numerator and denominator of E as a list. Equivalent to
/// [num(e), denom(e)], but more efficient.
fn d_num_denom(e : Value) -> Value raise {
  let (num, denom) = num_denom_split(e)
  list3(list2(q_mlist, q_simp), num, denom)
}

///|
fn d_num(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mrat) {
    d_ratnumer(e)
  } else if eq(caar(e), q_rat) {
    cadr(e)
  } else {
    let x = nformat(e)
    if eq(caar(x), q_mquotient) {
      simplify(cadr(x))
    } else if eq(caar(x), q_mminus) &&
      !atom(cadr(x)) &&
      eq(caar(cadr(x)), q_mquotient) {
      simplify(list3(list1(q_mtimes), Fix(-1L), cadr(cadr(x))))
    } else {
      e
    }
  }
}

///|
fn d_denom(e : Value) -> Value raise {
  if atom(e) {
    Fix(1L)
  } else if eq(caar(e), q_mrat) {
    d_ratdenom(e)
  } else if eq(caar(e), q_rat) {
    caddr(e)
  } else {
    let e = nformat(e)
    if eq(caar(e), q_mquotient) {
      simplify(caddr(e))
    } else if eq(caar(e), q_mminus) &&
      !atom(cadr(e)) &&
      eq(caar(cadr(e)), q_mquotient) {
      simplify(caddr(cadr(e)))
    } else {
      Fix(1L)
    }
  }
}

///|
fn d_entier(e : Value) -> Value raise {
  take(list1(q_d_floor), [e])
}

///|
fn d_fix(e : Value) -> Value raise {
  take(list1(q_d_floor), [e])
}

///|
fn comm__bad_number_p(num : Value) -> Bool raise {
  match num {
    Cplx(re, im) => comm__bad_number_p(re) || comm__bad_number_p(im)
    _ => float_inf_p(num).truthy() || float_nan_p(num).truthy()
  }
}

///|
/// Evaluate THUNK ignoring any error that might occur.  If the THUNK
/// returns a good number (not infinity or NaN), then return the number.
/// Otherwise, return NIL to indicate that we the computation failed.  This
/// is a pretty brute-force approach.
fn try_float_computation(thunk : Value) -> Value raise {
  with_specials(
    [
      (q_errset, Nil),
      (q_errcatch, cons(symval(q_bindlist), symval(q_loclist))),
      (q_ear_mdebug, Nil),
    ],
    () => match errset(() => funcall0(thunk)) {
      Some(v) => if comm__bad_number_p(v) { Nil } else { v }
      None => Nil
    },
  )
}

///|
/// MAXIMA::TO: convert a CL number to Maxima's representation.
fn comm__to(z : Value) -> Value raise {
  match z {
    Ratio(_, _) => list3(list2(q_rat, q_simp), numerator(z), denominator(z))
    Cplx(re, im) => add2(comm__to(re), mul2(q_d__pcti, comm__to(im)))
    _ => z
  }
}

///|
/// `(float x)` of a CL rational, as a double.
fn comm__float(x : Value) -> Value raise {
  lfloat(x)
}

///|
fn d_float(e : Value) -> Value raise {
  if numberp(e) {
    let e1 = lfloat(e)
    if float_inf_p(e1).truthy() {
      raise LispError::Condition(
        intern("floating-point-overflow"),
        "arithmetic error FLOATING-POINT-OVERFLOW signalled",
        Nil,
      )
    }
    return e1
  }
  if eq(e, q_d__pcti) {
    // Handle %i specially.
    return mul2(Flo(1.0), q_d__pcti)
  }
  if symbolp(e) {
    let v = mget(e, q_d_numer)
    if v.truthy() {
      return v
    }
  }
  let float_fn = lfunc("$float", a => d_float(arg(a, 0)))
  if atom(e) || memq(q_array, cdar(e)).truthy() {
    e
  } else if eq(caar(e), q_rat) {
    fpcofrat(e)
  } else if eq(caar(e), q_bigfloat) {
    fp2flo(e)
  } else if eq(caar(e), q_mexpt) || eq(caar(e), q_mncexpt) {
    // avoid x^2 -> x^2.0, allow %e^%pi -> 23.14
    let res = recur_apply(float_fn, e)
    if floatp(res) {
      res
    } else {
      list3(list1(caar(e)), d_float(cadr(e)), caddr(e))
    }
  } else if eq(caar(e), q_p_log) &&
    complex_number_p(second(e), ntypep=q_d_ratnump).truthy() {
    // Basically we try to compute float(log(x)) as directly as possible,
    // expecting Lisp to return some error if it can't. Then we do a more
    // complicated approach to compute the result.
    let n = second(e)
    let log2 = llog(Flo(2.0))
    if integerp(n) {
      // float(log(int)).  First try to compute (log (float n)).  If that
      // works, we're done. Otherwise we need to do more.
      let r = try_float_computation(lfunc("log", _ => llog(comm__float(n))))
      comm__to(
        if r.truthy() {
          r
        } else {
          // Write n as (n/2^m)*2^m where m is the number of bits in n. Then
          // log(n) = log(2^m) + log(n/2^m). n/2^m is approximately 1, so
          // converting that to a float is no problem.  log(2^m) = m *
          // log(2).
          let m = integer_length(n)
          num_add(
            num_mul(int(m), log2),
            llog(comm__float(num_div(n, ash(Fix(1L), m)))),
          )
        },
      )
    } else if d_ratnump(n).truthy() {
      // float(log(n/m)) where n and m are integers.  Try computing it first.
      // If it fails, compute as log(n) - log(m).
      let try_ = try_float_computation(lfunc("log", _ => llog(fpcofrat(n))))
      if try_.truthy() {
        comm__to(try_)
      } else {
        sub(
          d_float(list2(list1(q_p_log), second(n))),
          d_float(list2(list1(q_p_log), third(n))),
        )
      }
    } else if complex_number_p(
        n,
        ntypep=lfunc("integerp", a => lbool(integerp(arg(a, 0)))),
      ).truthy() {
      // float(log(n+m*%i)).
      let ri = trisplit(n)
      let re = car(ri)
      let im = cdr(ri)
      let r = try_float_computation(
        lfunc("log", _ => llog(complex(comm__float(re), i=comm__float(im)))),
      )
      comm__to(
        if r.truthy() {
          r
        } else {
          let size = {
            let a = integer_length(re)
            let b = integer_length(im)
            if a > b {
              a
            } else {
              b
            }
          }
          let scale = ash(Fix(1L), size)
          num_add(
            num_mul(int(size), log2),
            llog(
              complex(
                comm__float(num_div(re, scale)),
                i=comm__float(num_div(im, scale)),
              ),
            ),
          )
        },
      )
    } else {
      // log(n1/d1 + n2/d2*%i) =
      //   log((n+m*%i)/s) = log(n+m*%i) - log(s)
      //
      // where s = lcm(d1, d2), n and m are integers
      let ri = trisplit(n)
      let re = car(ri)
      let im = cdr(ri)
      let s = num_lcm(d_denom(re), d_denom(im))
      let p = d_expand(mul2(s, n))
      sub(
        d_float(list2(list1(q_p_log), p)),
        d_float(list2(list1(q_p_log), s)),
      )
    }
  } else if eq(caar(e), q_p_erf) && eq(second(e), q_d__pcti) {
    // Handle like erf(%i).  float(%i) (via recur-apply below) just returns
    // %i, so we never numerically evaluate it.
    complexify(complex_erf(complex(Fix(0L), i=Flo(1.0))))
  } else if eq(caar(e), q_p_derivative) || eq(caar(e), q_d_diff) {
    append(list2(remove(q_simp, first(e)), d_float(second(e))), rest(rest(e)))
  } else {
    recur_apply(float_fn, e)
  }
}

///|
fn d_coeff(e : Value, x : Value, n? : Value = Fix(1L)) -> Value raise {
  if equal(n, Fix(0L)) {
    coeff(e, x, Fix(0L))
  } else {
    coeff(e, power(x, n), Fix(1L))
  }
}

///|
fn coeff_contains_powers(e : Value, var_ : Value) -> Value raise {
  if alike1(e, var_).truthy() {
    t
  } else if atom(e) {
    Nil
  } else if eq(caar(e), q_mexpt) {
    alike1(cadr(e), var_)
  } else if eq(caar(e), q_mtimes) {
    member(t, mapcar(e => coeff_contains_powers(e, var_), cdr(e)))
  } else {
    Nil
  }
}

// hipow/lopow: MY-POWERS, MY-NUM and MY-FLAG are special variables bound by
// FINDPOWERS. These work best on expanded "simple" expressions.

///|
fn d_hipow(e : Value, var_ : Value) -> Value raise {
  findpowers(e, t, var_)
}

///|
fn d_lopow(e : Value, var_ : Value) -> Value raise {
  findpowers(e, Nil, var_)
}

///|
fn findpowers(e : Value, hiflg : Value, var_ : Value) -> Value raise {
  with_specials([(q_my_powers, Nil), (q_my_num, Nil), (q_my_flag, Nil)], () => {
    findpowers1(e, hiflg, var_) |> ignore
    let my_powers = symval(q_my_powers)
    let my_num = symval(q_my_num)
    if my_powers is Nil {
      if my_num is Nil {
        Fix(0L)
      } else {
        my_num
      }
    } else {
      if my_num.truthy() {
        set(q_my_powers, cons(my_num, my_powers)) |> ignore
      }
      maximin(
        symval(q_my_powers),
        if hiflg.truthy() {
          q_d_max
        } else {
          q_d_min
        },
      )
    }
  })
}

///|
fn findpowers1(e : Value, hiflg : Value, var_ : Value) -> Value raise {
  if alike1(e, var_).truthy() {
    checkpow(Fix(1L), hiflg)
  } else if atom(e) {
    t
  } else if eq(caar(e), q_mplus) {
    if !freel(cdr(e), var_).truthy() {
      for x in cdr(e).iter() {
        set(q_my_flag, Nil) |> ignore
        findpowers1(x, hiflg, var_) |> ignore
        if symval(q_my_flag) is Nil {
          checkpow(Fix(0L), hiflg) |> ignore
        }
      }
    }
    Nil
  } else if eq(caar(e), q_mexpt) && alike1(cadr(e), var_).truthy() {
    checkpow(caddr(e), hiflg)
  } else if specrepp(e).truthy() {
    findpowers1(specdisrep(e), hiflg, var_)
  } else {
    for x in cdr(e).iter() {
      findpowers1(x, hiflg, var_) |> ignore
    }
    cdr(e)
  }
}

///|
fn checkpow(pow : Value, hiflg : Value) -> Value raise {
  set(q_my_flag, t) |> ignore
  let my_num = symval(q_my_num)
  if !numberp(pow) {
    set(q_my_powers, cons(pow, symval(q_my_powers)))
  } else if my_num is Nil {
    set(q_my_num, pow)
  } else if hiflg.truthy() {
    if num_gt(pow, my_num) {
      set(q_my_num, pow)
    } else {
      Nil
    }
  } else if num_lt(pow, my_num) {
    set(q_my_num, pow)
  } else {
    Nil
  }
}

///|
/// push(x,l): The argument l must be a mapatom that is bound to a list.
/// Prepend x to the value of l and return this list. The arguments to push
/// are evaluated from left to right.
fn d_push(z : Value) -> Value raise {
  let o = caar(z)
  let mut z = cdr(z)
  let mut x = if z.truthy() {
    let v = car(z)
    z = cdr(z)
    v
  } else {
    wna_err(o)
  }
  let l = if z.truthy() {
    let v = car(z)
    z = cdr(z)
    v
  } else {
    wna_err(o)
  }
  if z.truthy() {
    wna_err(o) |> ignore
  }
  x = meval(x)
  let mut lo : Value = Nil
  let mut ll : Value = Nil
  if d_subvarp(l).truthy() {
    let h = list2(meval(mop(l)), q_array)
    lo = simplifya(cons(h, mevalargs(margs(l))), t)
    let lo2 = lo
    ll = with_special(q_noevalargs, t, () => meval(lo2))
  } else {
    lo = l
    ll = meval(l)
  }
  if d_mapatom(lo).truthy() && d_listp(ll).truthy() {
    ll = cons(x, cdr(ll))
    mset(lo, simplifya(cons(list1(q_mlist), ll), t))
  } else {
    merr("Second argument to push must be a mapatom that is bound to a list", [])
  }
}

///|
/// pop(l): The argument l must be a mapatom that is bound to a list. Remove
/// the first member of the value of l and return it.
fn d_pop(z : Value) -> Value raise {
  let o = caar(z)
  let mut z = cdr(z)
  let l = if z.truthy() {
    let v = car(z)
    z = cdr(z)
    v
  } else {
    wna_err(o)
  }
  if z.truthy() {
    wna_err(o) |> ignore
  }
  let mut lo : Value = Nil
  let mut ll : Value = Nil
  if d_subvarp(l).truthy() {
    let h = list2(meval(mop(l)), q_array)
    lo = simplifya(cons(h, mevalargs(margs(l))), t)
    let lo2 = lo
    ll = with_special(q_noevalargs, t, () => meval(lo2))
  } else {
    lo = l
    ll = meval(lo)
  }
  if d_mapatom(lo).truthy() && d_listp(ll).truthy() {
    if d_emptyp(ll).truthy() {
      merr("Pop called on an empty list", [])
    } else {
      ll = cdr(ll)
      let r = car(ll)
      ll = cdr(ll)
      mset(lo, simplifya(cons(list1(q_mlist), ll), t)) |> ignore
      r
    }
  } else {
    merr("Argument to pop must be a mapatom that is bound to a list", [])
  }
}

///|
/// The GRAD templates of comm.lisp (simplified, with the SIMP flags
/// removed), in the placeholder variable X.
let comm__grad_templates : String =
  #|((%log ((mexpt) x -1)) (%plog ((mexpt) x -1))
  #| (%gamma ((mtimes) ((mqapply) (($psi array) 0) x) ((%gamma) x)))
  #| (mfactorial ((mtimes) ((mqapply) (($psi array) 0) ((mplus) 1 x)) ((mfactorial) x)))
  #| (%sin ((%cos) x))
  #| (%cos ((mtimes) -1 ((%sin) x)))
  #| (%tan ((mexpt) ((%sec) x) 2))
  #| (%cot ((mtimes) -1 ((mexpt) ((%csc) x) 2)))
  #| (%sec ((mtimes) ((%sec) x) ((%tan) x)))
  #| (%csc ((mtimes) -1 ((%cot) x) ((%csc) x)))
  #| (%asin ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) ((rat) -1 2)))
  #| (%acos ((mtimes) -1 ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2)))
  #|                     ((rat) -1 2))))
  #| (%atan ((mexpt) ((mplus) 1 ((mexpt) x 2)) -1))
  #| (%acot ((mtimes) -1 ((mexpt) ((mplus) 1 ((mexpt) x 2)) -1)))
  #| (%acsc ((mtimes) -1
  #|         ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x -2)))
  #|          ((rat) -1 2))
  #|         ((mexpt) x -2)))
  #| (%asec ((mtimes)
  #|         ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x -2)))
  #|          ((rat) -1 2))
  #|         ((mexpt) x -2)))
  #| (%sinh ((%cosh) x))
  #| (%cosh ((%sinh) x))
  #| (%tanh ((mexpt) ((%sech) x) 2))
  #| (%coth ((mtimes) -1 ((mexpt) ((%csch) x) 2)))
  #| (%sech ((mtimes) -1 ((%sech) x) ((%tanh) x)))
  #| (%csch ((mtimes) -1 ((%coth) x) ((%csch) x)))
  #| (%asinh ((mexpt) ((mplus) 1 ((mexpt) x 2)) ((rat) -1 2)))
  #| (%acosh ((mtimes) ((mexpt) ((mplus) -1 x) ((rat) -1 2))
  #|          ((mexpt) ((mplus) 1 x) ((rat) -1 2))))
  #| (%atanh ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1))
  #| (%acoth ((mtimes) -1 ((mexpt) ((mplus) -1 ((mexpt) x 2)) -1)))
  #| (%asech ((mtimes) -1
  #|          ((mexpt) ((mplus) -1 ((mexpt) x -1)) ((rat) -1 2))
  #|          ((mexpt) ((mplus) 1 ((mexpt) x -1)) ((rat) -1 2))
  #|          ((mexpt) x -2)))
  #| (%acsch ((mtimes) -1
  #|          ((mexpt) ((mplus) 1 ((mexpt) x -2)) ((rat) -1 2))
  #|          ((mexpt) x -2)))
  #| (mabs ((mtimes) x ((mexpt) ((mabs) x) -1)))
  #| (%erf ((mtimes) 2 ((mexpt) $%pi ((rat) -1 2))
  #|        ((mexpt) $%e ((mtimes) -1 ((mexpt) x 2))))))

///|
/// DEFGRAD: record NAME on *DEFGRAD-SYMS* and store its GRAD property.
/// The derivatives are the parsed (unsimplified) #$...$ expressions;
/// PROCESS-DEFGRAD MEVAL*s them at startup.
fn comm__defgrad(name : Value, arguments : Value, body : Array[Value]) -> Unit {
  set(q_ear_defgrad_syms, cons(name, symval(q_ear_defgrad_syms))) |> ignore
  putprop(name, cons(arguments, list(body)), q_grad) |> ignore
}

///|
let comm__q_d_fourth : Value = sym("$fourth")

///|
let comm__q_d_fifth : Value = sym("$fifth")

///|
let comm__q_d_sixth : Value = sym("$sixth")

///|
let comm__q_d_seventh : Value = sym("$seventh")

///|
let comm__q_d_eighth : Value = sym("$eighth")

///|
let comm__q_d_ninth : Value = sym("$ninth")

///|
let comm__q_d_tenth : Value = sym("$tenth")

///|
let comm__q_findpowers : Value = sym("findpowers")

///|
let comm__q_checkpow : Value = sym("checkpow")

///|
fn init_comm() -> Unit raise {
  // This business about operator properties is terrible -- this stuff
  // should be in src/nparse.lisp, and it should be split up for each
  // operator.
  let ops : Array[(Value, String)] = [
    (q_mplus, "+"),
    (q_mminus, "-"),
    (q_mtimes, "*"),
    (q_mexpt, "**"),
    (q_mexpt, "^"),
    (q_mnctimes, "."),
    (q_rat, "/"),
    (q_mquotient, "/"),
    (q_mncexpt, "^^"),
    (q_mequal, "="),
    (q_mgreaterp, ">"),
    (q_mlessp, "<"),
    (q_mleqp, "<="),
    (q_mgeqp, ">="),
    (q_mnotequal, "#"),
    (q_mand, "and"),
    (q_mor, "or"),
    (q_mnot, "not"),
    (q_msetq, ":"),
    (q_mdefine, ":="),
    (q_mdefmacro, "::="),
    (q_mquote, "'"),
    (q_mlist, "["),
    (q_mset, "::"),
    (q_mfactorial, "!"),
    (q_p_genfact, "!!"),
    (q_marrow, "-->"),
    (q_mprogn, "("),
    (q_mcond, "if"),
    (q_mdo, "do"),
    (q_mdoin, "do_in"),
  ]
  for x in ops {
    let (s, name) = x
    let str : Value = Str(name)
    putprop(s, str, q_op) |> ignore
    // nounify not yet available
    putprop(sym("%" + symbol_name(s)), str, q_op) |> ignore
    putopr(str, s) |> ignore
    set(q_ear_mopl, cons(str, symval(q_ear_mopl))) |> ignore
  }
  putprop(q_mqapply, q_d_subvar, q_op) |> ignore
  putprop(q_bigfloat, q_d_bfloat, q_op) |> ignore
  // Define an alias $psubst and a reversealias for $psubstitute
  putprop(q_d_psubst, q_d_psubstitute, q_alias) |> ignore
  putprop(q_d_psubstitute, q_d_psubst, q_reversealias) |> ignore
  // grad properties
  let header = list1(q_x)
  for z in lread(comm__grad_templates).iter() {
    putprop(car(z), cons(header, cdr(z)), q_grad) |> ignore
  }
  comm__defgrad(q_p_atan2, list2(q_d_x, q_d_y), [
    lread("((mquotient) $y ((mplus) ((mexpt) $y 2) ((mexpt) $x 2)))"),
    lread(
      "((mminus) ((mquotient) $x ((mplus) ((mexpt) $y 2) ((mexpt) $x 2))))",
    ),
  ])
  comm__defgrad(q_d_li, list2(q_d_n, q_d_x), [
    // wrt n
    Value::Nil,
    // wrt x
    lread(
      "((mquotient) ((mqapply) (($li array) ((mplus) $n ((mminus) 1))) $x) $x)",
    ),
  ])
  comm__defgrad(q_d_psi, list2(q_d_n, q_d_x), [
    // wrt n
    Value::Nil,
    // wrt x
    lread("((mqapply) (($psi array) ((mplus) $n 1)) $x)"),
  ])
  // second thru tenth (MAKE-NTH)
  let nths : Array[(Value, Int)] = [
    (q_d_second, 2),
    (q_d_third, 3),
    (comm__q_d_fourth, 4),
    (comm__q_d_fifth, 5),
    (comm__q_d_sixth, 6),
    (comm__q_d_seventh, 7),
    (comm__q_d_eighth, 8),
    (comm__q_d_ninth, 9),
    (comm__q_d_tenth, 10),
  ]
  for x in nths {
    let (s, i) = x
    defun(s, args => {
      if args.length() != 1 {
        raise LispError::SimpleError(
          "invalid number of arguments: " + args.length().to_string(),
        )
      }
      comm__make_nth(args[0], s, i)
    })
  }
  defun(q_d_hipow, args => {
    check_arity("$hipow", args, 2)
    d_hipow(arg(args, 0), arg(args, 1))
  })
  defun(q_d_lopow, args => {
    check_arity("$lopow", args, 2)
    d_lopow(arg(args, 0), arg(args, 1))
  })
  defun(comm__q_findpowers, args => findpowers(arg(args, 0), arg(args, 1), arg(args, 2)))
  defun(q_findpowers1, args => findpowers1(arg(args, 0), arg(args, 1), arg(args, 2)))
  defun(comm__q_checkpow, args => checkpow(arg(args, 0), arg(args, 1)))
}

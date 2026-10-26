// Port of src/series.lisp: POWERSERIES.

// ---------------------------------------------------------------------------
// driver stage

///|
fn d_powerseries(expr : Value, var_ : Value, pt : Value) -> Value raise {
  with_special(q_var, var_, () => {
    if atom(var_) && !symbolp(var_) {
      improper_arg_err(var_, q_d_powerseries) |> ignore
    }
    powerseries(expr, var_, pt)
  })
}

///|
/// An error that can be raised deep in the bowels of POWERSERIES that we'll
/// catch and return a noun form. The condition payload is the message list
/// (MESSAGE . ARGUMENTS) or nil.
fn powerseries_expansion_error(message? : Value = Nil, arguments : Value) -> Value raise {
  raise LispError::Condition(
    intern("powerseries-expansion-error"),
    "powerseries-expansion-error",
    if message.truthy() {
      cons(message, arguments)
    } else {
      Nil
    },
  )
}

///|
/// `(powerseries-expansion-error msg args...)` with MoonBit strings.
fn series__pee(msg : String, args : Array[Value]) -> Value raise {
  powerseries_expansion_error(message=Str(msg), list(args))
}

///|
/// The top-level routine for $powerseries, which calls this function after
/// spotting invalid arguments.
fn powerseries(expr : Value, var_ : Value, pt : Value) -> Value raise {
  with_special(q_var, var_, () => {
    let pt = canonicalize_plus_inf(pt)
    let pt_zero = numberp(pt) && zerop(pt)
    (if pt_zero && symbolp(var_) {
      seriesexpand_star(expr)
    } else if pt_zero {
      sbstpt(expr, q_x, var_, var_)
    } else if eq(pt, q_d_inf) {
      sbstpt(expr, div_star(Fix(1L), q_x), var_, div_star(Fix(1L), var_))
    } else if eq(pt, q_d_minf) {
      sbstpt(
        expr,
        mul2_star(Fix(-1L), div_star(Fix(1L), q_x)),
        var_,
        mul2_star(Fix(-1L), div_star(Fix(1L), var_)),
      )
    } else {
      sbstpt(expr, add2_star(q_x, pt), var_, simplifya(sub_star(var_, pt), Nil))
    }) catch {
      LispError::Condition(s, _, message) if s.name ==
        "powerseries-expansion-error" => {
        // If expansion fails, print a message in verbose mode but then
        // return a noun form.
        if symval(q_d_verbose).truthy() {
          mtell(
            list([
              Str("Failed to expand ~M with respect to ~M at ~M.~%"),
              expr,
              var_,
              pt,
            ]),
          )
          |> ignore
          if message.truthy() {
            terpri()
            finish_output()
            mtell(message) |> ignore
          }
        }
        mk(q_p_powerseries, [expr, var_, pt])
      }
      e => raise e
    }
  })
}

///|
/// Return a list of the terms in the expression that are used as
/// integration or differentiation variables.
fn intdiff_vars_in_expr(expr : Value) -> Value raise {
  if atom(expr) {
    Nil
  } else if eq(caar(expr), q_p_integrate) {
    // Arguably, if this is a definite integral, the variable isn't free so
    // we shouldn't return it. But maxima-substitute doesn't know about bound
    // variables and this is a helper function to avoid silly substitutions.
    list1(caddr(expr))
  } else if eq(caar(expr), q_p_derivative) {
    let col = Collector::new()
    let mut l = cddr(expr)
    while !(l is Nil) {
      col.add(car(l))
      l = cddr(l)
    }
    col.result()
  } else {
    // (reduce #'union (cdr expr) :key #'intdiff-vars-in-expr)
    let args = cdr(expr)
    if args is Nil {
      raise LispError::SimpleError(
        "invalid number of arguments: 0 (UNION called by REDUCE)",
      )
    }
    let mut acc = intdiff_vars_in_expr(car(args))
    let mut l = cdr(args)
    while !(l is Nil) {
      acc = union_(acc, intdiff_vars_in_expr(car(l)))
      l = cdr(l)
    }
    acc
  }
}

///|
/// Series expand EXP after substituting in SEXP for VAR1, the main variable.
/// SEXP should be an expression in 'X and 'X will be replaced by a gensym
/// for the calculation. When the expansion is done, substitute USEXP for
/// the gensym.
fn sbstpt(exp_ : Value, sexp : Value, var1 : Value, usexp : Value) -> Value raise {
  with_special(q_usexp, usexp, () => {
    let v = gensym()
    with_special(q_var, v, () => {
      let sub_exp = maxima_substitute(subst(v, q_x, sexp), var1, exp_)
      let expanded = seriesexpand_star(sub_exp)
      // If we've ended up with diff(foo, var) then we give up (we can't
      // substitute arbitrary expressions for the differentiation /
      // integration variable).
      if memq(v, intdiff_vars_in_expr(expanded)).truthy() {
        series__pee(
          "Couldn't make substitution to evaluate at the given point because the~%power series expansion contained the expansion variable as an~%integration / differentiation variable.",
          [],
        )
      } else {
        maxima_substitute(usexp, v, expanded)
      }
    })
  })
}

///|
fn seriesexpand_star(x : Value) -> Value raise {
  with_specials(
    [
      (q_n_starindex, gensumindex()),
      (q_n_starn, Nil),
      (q_n_stara, Nil),
      (q_n_starm, Nil),
      (q_n_starc, Nil),
      (q_d_cauchysum, t),
      (q_d_ratsimpexpons, t),
      (q_d_ratexpand, Nil),
      (q_n_starinfsumsimp, Nil),
      (q_n_starratexp, Nil),
      (q_n_startrigred, Nil),
      (q_n_starnoexpand, Nil),
    ],
    () => {
      meval(list3(list1(q_d_declare), symval(q_n_starindex), q_d_integer))
      |> ignore
      sp2expand(seriespass1(x))
    },
  )
}

///|
fn out_of(e : Value) -> Value raise {
  let has_var = boundp(q_n_starvar) && symval(q_n_starvar).truthy()
  let e = if has_var {
    subst(
      list3(list1(q_mexpt), symval(q_n_starvar), symval(q_ear_gcd)),
      symval(q_var),
      e,
    )
  } else {
    e
  }
  let v = if has_var { symval(q_n_starvar) } else { symval(q_var) }
  if boundp(q_usexp) && symval(q_usexp).truthy() {
    subst(symval(q_usexp), v, e)
  } else {
    e
  }
}

///|
fn show_exp(e : Value) -> Value raise {
  mtell(list([Str("~%~%~M~%~%"), list3(list1(q_mlabel), Nil, out_of(e))]))
}

///|
fn seriespass1(e : Value) -> Value raise {
  let w = sratsimp(sp1(e))
  if symval(q_d_verbose).truthy() {
    terpri()
    finish_output()
    mtell(list1(Str("powerseries: first simplification returned ~%"))) |> ignore
    show_exp(w) |> ignore
  }
  w
}

// ---------------------------------------------------------------------------
// pass two		expansion phase

///|
fn sp2expand(exp_ : Value) -> Value raise {
  let var_ = symval(q_var)
  if free(exp_, var_).truthy() || atom(exp_) {
    exp_
  } else if mbagp(exp_).truthy() {
    cons(car(exp_), mapcar(x => sp2expand(x), cdr(exp_)))
  } else if eq(caar(exp_), q_mplus) {
    // was below 'mtimes test--fixes powerseries(1+x^n,x,0)
    addn(mapcar(x => sp2expand(x), cdr(exp_)), Nil)
  } else if sratp(exp_, var_).truthy() {
    ratexp(exp_)
  } else if eq(caar(exp_), q_mexpt) {
    sp2expt(exp_)
  } else if zl_get(caar(exp_), q_sp2).truthy() {
    sp2sub(sp2trig(exp_), cadr(exp_))
  } else if eq(caar(exp_), q_mtimes) {
    muln(mapcar(x => sp2expand(x), cdr(exp_)), Nil)
  } else if eq(caar(exp_), q_p_log) {
    sp2log(cadr(exp_))
  } else if eq(caar(exp_), q_p_derivative) {
    sp2diff(cadr(exp_), cddr(exp_))
  } else if eq(caar(exp_), q_p_integrate) {
    sp2integ(cadr(exp_), caddr(exp_), cdddr(exp_))
  } else if eq(caar(exp_), q_p_product) || eq(caar(exp_), q_p_sum) {
    list_star([car(exp_), sp2expand(cadr(exp_)), cddr(exp_)])
  } else {
    let index = symval(q_n_starindex)
    list([
      list1(q_p_sum),
      muln_star([
        power_star(var_, index),
        power_star(list2(list1(q_mfactorial), index), Fix(-1L)),
        list3(
          list1(q_p_at),
          list4(list1(q_p_derivative), exp_, var_, index),
          list3(list1(q_mequal), var_, Fix(0L)),
        ),
      ]),
      index,
      Fix(0L),
      q_d_inf,
    ])
  }
}

///|
fn sp2sub(s : Value, exp_ : Value) -> Value raise {
  if !smono(exp_, symval(q_var)).truthy() {
    series__pee(
      "Can't substitute the value~%~M~%into another expansion because it isn't a monomial in theexpansion variable.",
      [out_of(exp_)],
    )
    |> ignore
  }
  maxima_substitute(exp_, q_sp2var, simplify(s))
}

///|
fn ratexp(exp_ : Value) -> Value raise {
  with_special(q_ear_gcd, Nil, () => {
    if symval(q_d_verbose).truthy() {
      mtell(
        list([
          Str("powerseries: attempt rational function expansion of~%~M"),
          list3(list1(q_mlabel), Nil, exp_),
        ]),
      )
      |> ignore
    }
    let (n, d) = numden(exp_)
    sratexpnd(n, d)
  })
}

///|
/// A pattern that matches cc*(c*x^m + a)^n
let series__linpat : Value = try! lread(
  "((mtimes) ((coefftt) (cc not-zero-free var)) ((mexpt) ((mplus) ((coeffpt) (w m1 ((mexpt) (x equal var) (m not-zero-free var))) (c freevar)) ((coeffpp) (a freevar))) (n not-zero-free var)))",
)

///|
fn sratexpnd(n : Value, d : Value) -> Value raise {
  with_specials([(q_ear_schatc_ans, list1(Nil)), (q_ear_splist, Nil)], () => {
    let mut d = d
    let var_ = symval(q_var)
    let linpat = series__linpat
    if !equal(n, Fix(1L)) && smono(n, var_).truthy() {
      return mul2_star(n, sratexpnd(Fix(1L), d))
    }
    if free(d, var_).truthy() {
      return if poly_q(n, var_).truthy() {
        div_star(n, d)
      } else if m1(n, linpat).truthy() {
        div_star(srbinexpnd(cdr(symval(q_ear_schatc_ans))), d)
      } else {
        powerseries_expansion_error(Nil)
      }
    }
    if smonop(d, var_).truthy() {
      return if mplusp(n).truthy() {
        addn(mapcar(q => div_star(q, d), cdr(n)), Nil)
      } else {
        div_star(n, d)
      }
    }
    set(q_ear_gcd, ggcd(nconc(exlist(n), exlist(d)))) |> ignore
    if !equal(Fix(1L), symval(q_ear_gcd)) {
      return sratsubst(symval(q_ear_gcd), n, d)
    }
    // Rational expansion theorem for distinct roots. The main point of the
    // POLY? test here is that it guarantees $HIPOW will give the correct
    // degrees (in particular, it only allows known non-negative integer
    // exponents)
    if poly_q(n, var_).truthy() &&
      poly_q(d, var_).truthy() &&
      num_gt(funcall(q_d_hipow, [d, var_]), funcall(q_d_hipow, [n, var_])) &&
      has_distinct_nonzero_roots_p(d, var_).truthy() {
      return expand_distinct_roots(n, d)
    }
    // The SRBINEXPND call above dealt with expressions of the form
    // cc*(c*x^m+a)^n. Here, we deal with b/(cc*(c*x^m+a)^n).
    if free(n, var_).truthy() &&
      {
        let d0 = d
        d = with_special(q_d_ratfac, t, () => ratdisrep(
          d_rat(factor(d0), list1(var_)),
        ))
        m1(d, linpat).truthy()
      } {
      // We had num/den and LINPAT matched den. We need to replace cc with
      // num/cc and n with -n.
      let ans = symval(q_ear_schatc_ans)
      let nc = assq(q_n, ans)
      rplacd(nc, mul2_star(Fix(-1L), cdr(nc))) |> ignore
      let ccc = assq(q_cc, ans)
      rplacd(ccc, div_star(n, cdr(ccc))) |> ignore
      return srbinexpnd(cdr(symval(q_ear_schatc_ans)))
    }
    // *RATEXP is set by RATEXPAND1, which we call to do the general
    // expansion below. This check makes sure we can't end up recursing
    // infinitely.
    if symval(q_n_starratexp).truthy() {
      powerseries_expansion_error(Nil) |> ignore
    }
    // Look for a power of var (a zero root) as a term.
    let zero_root = if eq(caar(d), q_mtimes) {
      find_if(
        factor => eq(factor, var_) ||
          (mexptp(factor).truthy() && eq(cadr(factor), var_)),
        cdr(d),
      )
    } else {
      Nil
    }
    if !zero_root.truthy() {
      ratexpand1(n, d)
    } else {
      let other_factors = series__remove_first_eq(zero_root, cdr(d))
      mul2_star(
        sratexpnd(n, muln(other_factors, Nil)),
        list3(list1(q_mexpt), zero_root, Fix(-1L)),
      )
    }
  })
}

///|
/// `(remove x l :test #'eq :count 1)`
fn series__remove_first_eq(x : Value, l : Value) -> Value {
  let col = Collector::new()
  let mut p = l
  let mut done = false
  while p is Cons(c) {
    if !done && eq(c.car, x) {
      done = true
    } else {
      col.add(c.car)
    }
    p = c.cdr
  }
  col.result()
}

///|
/// Is a sum with index and bounds from psp2form?
fn psp2formp(exp_ : Value) -> Value raise {
  lbool(
    listp(exp_) &&
    listp(car(exp_)) &&
    eq(caar(exp_), q_p_sum) &&
    eq(caddr(exp_), symval(q_n_starindex)) &&
    eql(cadddr(exp_), Fix(0L)) &&
    eq(cadr(cdddr(exp_)), q_d_inf),
  )
}

///|
/// A stripped down version of (sumcontract (intosum EXP)). Coalesce
/// occurrences of ((%SUM) <FOO> *INDEX 0 '$INF), which are allowed to start
/// with multiplicative constants.
fn psp2foldsum(exp_ : Value) -> Value raise {
  if symval(q_d_verbose).truthy() {
    mtell(list1(Str("powerseries: preparing to fold sums~%"))) |> ignore
    show_exp(exp_) |> ignore
  }
  let (sums, others) = partition_by(
    lfunc("psp2foldsum-pred", args => {
      let e = arg(args, 0)
      lbool(
        psp2formp(e).truthy() ||
        (mtimesp(e).truthy() && psp2formp(caddr(e)).truthy()),
      )
    }),
    cdr(exp_),
  )
  if sums is Nil {
    // If there were no sums, just return the original expression.
    exp_
  } else {
    // Otherwise contract the sums
    let contracted = list([
      list1(q_p_sum),
      addn(
        mapcar(
          e => if eq(caar(e), q_mtimes) {
            mul2_star(cadr(e), cadr(caddr(e)))
          } else {
            cadr(e)
          },
          sums,
        ),
        Nil,
      ),
      symval(q_n_starindex),
      Fix(0L),
      q_d_inf,
    ])
    if others is Nil {
      contracted
    } else {
      addn(cons(contracted, others), Nil)
    }
  }
}

///|
/// Solve returns a list: (soln mult soln mult ...). Returns true if every
/// soln is nonzero and every mult is 1, and the roots are distinct.
fn distinct_nonzero_roots_p(roots : Value) -> Value raise {
  if roots is Nil {
    return t
  }
  // Check all roots have multiplicity one and are nonzero.
  let mut l = roots
  while !(l is Nil) {
    let root = car(l)
    let mult = cadr(l)
    if !(eql(Fix(1L), mult) &&
      eq(d_sign(list2(list1(q_mabs), caddr(root))), q_d_pos)) {
      return Nil
    }
    l = cddr(l)
  }
  // Now check that the roots are genuinely different from one another.
  let mut rest = roots
  while !(rest is Nil) {
    let a = car(rest)
    let mut bs = cddr(rest)
    while !(bs is Nil) {
      let b = car(bs)
      if !eq(
          q_d_pos,
          d_sign(list2(list1(q_mabs), sub_star(caddr(b), caddr(a)))),
        ) {
        return Nil
      }
      bs = cddr(bs)
    }
    rest = cddr(rest)
  }
  t
}

///|
/// Returns t if polynomial poly in variable var has all distinct roots.
fn has_distinct_nonzero_roots_p(poly : Value, var_ : Value) -> Value raise {
  with_specials(
    [(q_var, var_), (q_n_starroots, Nil), (q_n_starfailures, Nil)],
    () => {
      solve(poly, var_, Fix(1L)) |> ignore
      if symval(q_n_starfailures) is Nil {
        distinct_nonzero_roots_p(symval(q_n_starroots))
      } else {
        Nil
      }
    },
  )
}

///|
/// Rational Expansion Theorem for Distinct Roots
/// Graham, Knuth, Patashnik, "Concrete Math" 2nd ed, p 340
///
/// If R(z) = P(z)/Q(z), where Q(z) = q0*(1-r_1*z)*...*(1-r_l*z) and the
/// numbers (r_1 ... r_l) are distinct, and if P(z) is a polynomial of degree
/// less than l, then
///  [z^n]R(z) = a_1*r_1^n + ... + a_l*r_l^n,  where a_k = -r_k*P(1/r_k)/Q'(1/r_k)
fn expand_distinct_roots(num : Value, den : Value) -> Value raise {
  with_specials([(q_n_starroots, Nil), (q_n_starfailures, Nil)], () => {
    let var_ = symval(q_var)
    solve(den, var_, Fix(1L)) |> ignore
    if symval(q_n_starfailures).truthy() {
      raise LispError::SimpleError(
        "EXPAND-DISTINCT-ROOTS: failed to solve for roots.",
      )
    } else if distinct_nonzero_roots_p(symval(q_n_starroots)).truthy() {
      let index = symval(q_n_starindex)
      psp2form(
        addn(
          mapcar(
            r => {
              if symval(q_d_verbose).truthy() {
                mtell(list1(Str("powerseries: for root:~%"))) |> ignore
                show_exp(r) |> ignore
                mtell(list1(Str("powerseries: numerator at root =~%")))
                |> ignore
                show_exp(maxima_substitute(r, var_, num)) |> ignore
                mtell(
                  list1(
                    Str(
                      "powerseries: first derivative of denominator at root =~%",
                    ),
                  ),
                )
                |> ignore
                show_exp(
                  maxima_substitute(r, var_, d_diff(list2(den, var_))),
                )
                |> ignore
              }
              muln_star([
                Fix(-1L),
                div_star(Fix(1L), r),
                maxima_substitute(r, var_, num),
                div_star(
                  Fix(1L),
                  maxima_substitute(r, var_, d_diff(list2(den, var_))),
                ),
                power_star(div_star(Fix(1L), r), index),
              ])
            },
            mapcar(x => caddr(x), remove_mult(symval(q_n_starroots))),
          ),
          Nil,
        ),
        index,
        Fix(0L),
      )
    } else {
      raise LispError::SimpleError(
        "EXPAND-DISTINCT-ROOTS: roots are not distinct.\n",
      )
    }
  })
}

///|
/// Try to expand N/D as a power series in VAR about 0. Can safely assume
/// that D has no zero roots (we remove them in SRATEXPND before calling
/// this function).
fn ratexpand1(n : Value, d : Value) -> Value raise {
  let verbose = symval(q_d_verbose).truthy()
  if verbose {
    mtell(list1(Str("powerseries: attempt partial fraction expansion ")))
    |> ignore
    show_exp(list3(list1(q_mquotient), n, d)) |> ignore
    terpri()
    finish_output()
  }
  // *RATEXP serves as a recursion guard: if SRATEXPND is about to call us
  // recursively, the flag will be set and it gives up instead.
  with_special(q_n_starratexp, t, () => {
    let var_ = symval(q_var)
    let fractions = d_partfrac(div_star(n, d), var_)
    if mplusp(fractions).truthy() {
      // If $PARTFRAC succeeds, it will return a sum of terms. In that case,
      // expand each one and try to fold the result into a single power
      // series sum again.
      if symval(q_d_verbose).truthy() {
        mtell(list1(Str("which is ~%"))) |> ignore
        show_exp(fractions) |> ignore
      }
      psp2foldsum(addn(mapcar(x => ratexp(x), cdr(fractions)), Nil))
    } else if poly_q(n, var_).truthy() {
      // If that didn't work, maybe it's because the numerator messed things
      // up. If the numerator is actually a polynomial, factor it out and do
      // an expansion of 1/d on its own.
      if symval(q_d_verbose).truthy() {
        mtell(
          list1(
            Str(
              "powerseries: partial fraction expansion failed, expanding denominator only.~%",
            ),
          ),
        )
        |> ignore
      }
      mul2_star(n, ratexp(div_star(Fix(1L), d)))
    } else {
      // If n is complicated, there's not really much we can do to make
      // further progress, so give up and return a noun form.
      series__pee("Partial fraction expansion failed", [])
    }
  })
}

///|
fn sratsubst(gcd_ : Value, num : Value, den : Value) -> Value raise {
  let var_ = symval(q_var)
  if symval(q_d_verbose).truthy() {
    mtell(list1(Str("powerseries: substituting for the occurrences of")))
    |> ignore
    show_exp(list3(list1(q_mexpt), var_, gcd_)) |> ignore
    mtell(list1(Str("in"))) |> ignore
    show_exp(list3(list1(q_mquotient), num, den)) |> ignore
    terpri()
    finish_output()
  }
  let var_star = gensym()
  with_special(q_n_starvar, var_, () => {
    let sv = symval(q_n_starvar)
    let num = maxima_substitute(
      power_star(var_star, power_star(gcd_, Fix(-1L))),
      sv,
      num,
    )
    let den = maxima_substitute(
      power_star(var_star, power_star(gcd_, Fix(-1L))),
      sv,
      den,
    )
    maxima_substitute(
      power_star(sv, gcd_),
      var_star,
      with_special(q_var, var_star, () => sratexpnd(num, den)),
    )
  })
}

///|
fn ggcd(l : Value) -> Value raise {
  if l is Nil {
    Fix(1L)
  } else if cdr(l) is Nil {
    car(l)
  } else if equal(Fix(1L), car(l)) {
    Fix(1L)
  } else {
    d_gcd(ggcd(cdr(l)), car(l), Nil)
  }
}

///|
fn exlist(exp_ : Value) -> Value raise {
  if exp_ is Nil {
    Nil
  } else if atom(exp_) {
    if eq(exp_, symval(q_var)) {
      list1(Fix(1L))
    } else {
      Nil
    }
  } else if !atom(car(exp_)) && eq(caar(exp_), q_mplus) {
    exlist(cdr(exp_))
  } else if smono(car(exp_), symval(q_var)).truthy() {
    if equal(symval(q_n_starn), Fix(0L)) {
      exlist(cdr(exp_))
    } else {
      let n = symval(q_n_starn)
      cons(n, exlist(cdr(exp_)))
    }
  } else {
    exlist(cdr(exp_))
  }
}

///|
/// Perform a binomial expansion of (c x^m + a)^n.
///
/// If n isn't known to be an integer, we'd like to write a sum of terms
///    x^(mk) c^k a^(n-k) / ((n+1) beta(n-k+1, k+1))
/// But we have to be a bit careful: it only works if c, x and a are
/// nonzero.
fn srbinexpnd(ear_schatc_ans : Value) -> Value raise {
  with_special(q_ear_schatc_ans, ear_schatc_ans, () => {
    let al = ear_schatc_ans
    let n = cdr(assq(q_n, al))
    let a = cdr(assq(q_a, al))
    let m = cdr(assq(q_m, al))
    let c = cdr(assq(q_c, al))
    let cc = cdr(assq(q_cc, al))
    let x = cdr(assq(q_x, al))
    let var_ = symval(q_var)
    let index = symval(q_n_starindex)
    mul2_star(
      cc,
      if integerp(n) && minusp(n) {
        srintegexpd(neg(n), a, m, c)
      } else {
        let sgn_a = d_sign(list2(list1(q_mabs), a))
        let sgn_cx = d_sign(list2(list1(q_mabs), mk(q_mtimes, [c, x])))
        let sgn_n = d_sign(n)
        let general_term = div_star(
          muln_star([
            power_star(var_, mul2_star(m, index)),
            power_star(c, index),
            power_star(a, sub_star(n, index)),
          ]),
          mul2_star(
            ftake_star(q_p_beta, [
              sub_star(n, add2_star(Fix(-1L), index)),
              add2_star(Fix(1L), index),
            ]),
            add2_star(Fix(1L), n),
          ),
        )
        if eq(sgn_n, q_d_zero) {
          Fix(1L)
        } else if eq(sgn_cx, q_d_zero) {
          power_star(a, n)
        } else if eq(sgn_a, q_d_zero) {
          mul2_star(power_star(c, n), power_star(x, mul2_star(m, n)))
        } else if eq(sgn_a, q_d_pos) && eq(sgn_cx, q_d_pos) {
          if d_featurep(n, q_d_integer).truthy() &&
            (eq(sgn_n, q_d_pos) || eq(sgn_n, q_d_pz)) {
            mk(q_p_sum, [general_term, index, Fix(0L), n])
          } else {
            mk(q_p_sum, [general_term, index, Fix(0L), q_d_inf])
          }
        } else if eq(sgn_a, q_d_pos) {
          add2_star(
            power_star(a, n),
            mk(q_p_sum, [general_term, index, Fix(1L), q_d_inf]),
          )
        } else if d_featurep(n, q_d_integer).truthy() && eq(sgn_n, q_d_pos) {
          add2_star(
            mk(q_p_sum, [general_term, index, Fix(0L), add2_star(Fix(-1L), n)]),
            mul2_star(power_star(c, n), power_star(x, mul2_star(n, m))),
          )
        } else {
          series__pee(
            "Couldn't expand binomial~%~M~%as we didn't know which terms were nonzero.",
            [],
          )
        }
      },
    )
  })
}

///|
fn psp2form(coeff : Value, exp_ : Value, bas : Value) -> Value raise {
  list([
    list1(q_p_sum),
    mul2_star(coeff, power_star(symval(q_var), exp_)),
    symval(q_n_starindex),
    bas,
    q_d_inf,
  ])
}

///|
let series__srintegexpd_lit : Value = try! lread(
  "((mexpt) ((mplus) $a ((mtimes) $c ((mexpt) $var $m))) ((mminus) $n))",
)

///|
fn srintegexpd(n : Value, a : Value, m : Value, c : Value) -> Value raise {
  if symval(q_d_verbose).truthy() {
    mtell(list1(Str("powerseries: apply rule for expressions of ~%"))) |> ignore
    show_exp(series__srintegexpd_lit) |> ignore
    mtell(list1(Str("powerseries: here we have"))) |> ignore
    show_exp(
      list([
        list1(q_mlist),
        list3(list1(q_mequal), q_d_n, n),
        list3(list1(q_mequal), q_d_a, a),
        list3(list1(q_mequal), q_d_c, c),
        list3(list1(q_mequal), q_d_m, m),
      ]),
    )
    |> ignore
  }
  let index = symval(q_n_starindex)
  let expo = if equal(m, Fix(1L)) { index } else { mul2_star(index, m) }
  if num_eq(n, Fix(1L)) {
    psp2form(
      mul2_star(
        power_star(a, mul2_star(Fix(-1L), add2_star(Fix(1L), index))),
        power_star(mul2_star(Fix(-1L), c), index),
      ),
      expo,
      Fix(0L),
    )
  } else if num_eq(Fix(2L), n) {
    psp2form(
      muln_star([
        add2_star(Fix(1L), index),
        power_star(a, mul2_star(Fix(-1L), add2_star(Fix(2L), index))),
        power_star(mul2_star(Fix(-1L), c), index),
      ]),
      expo,
      Fix(0L),
    )
  } else {
    let prod = {
      let mut nn = num_sub(n, Fix(1L))
      let mut l : Value = Nil
      while !num_eq(nn, Fix(0L)) {
        l = cons(list3(list1(q_mplus), index, nn), l)
        nn = num_sub(nn, Fix(1L))
      }
      muln(cons(div_star(Fix(1L), factorial(num_sub(n, Fix(1L)))), l), Nil)
    }
    psp2form(
      muln_star([
        prod,
        power_star(muln_star([Fix(-1L), c, power_star(a, Fix(-1L))]), index),
        power_star(a, num_neg(n)),
      ]),
      expo,
      Fix(0L),
    )
  }
}

///|
fn sratp(a : Value, var_ : Value) -> Value raise {
  with_special(q_var, var_, () => if atom(a) {
    t
  } else if eq(caar(a), q_mplus) || eq(caar(a), q_mtimes) {
    sandmap(cdr(a))
  } else if eq(caar(a), q_mexpt) {
    if free(cadr(a), var_).truthy() {
      free(caddr(a), var_)
    } else if smono(a, var_).truthy() {
      t
    } else if free(caddr(a), var_).truthy() {
      sratp(cadr(a), var_)
    } else {
      Nil
    }
  } else if free(mop(a), var_).truthy() {
    lbool(every(s => free(s, var_).truthy(), margs(a)))
  } else {
    Nil
  })
}

///|
fn sandmap(l : Value) -> Value raise {
  if l is Nil {
    t
  } else if sratp(car(l), symval(q_var)).truthy() {
    sandmap(cdr(l))
  } else {
    Nil
  }
}

///|
fn sp2trig(exp_ : Value) -> Value raise {
  subst(symval(q_n_starindex), q_n_starindex, zl_get(caar(exp_), q_sp2))
}

///|
/// Take an expression, EXPR, and try to write it as a + b*VAR^c. On
/// success, returns (A, B, C). On failure, raise a
/// powerseries-expansion-error. We walk through the expression tree; if we
/// see anything other than +,* and ^, we give up. If we find we have more
/// than one different exponent in our terms, we give up.
fn split_two_term_poly(expr : Value) -> (Value, Value, Value) raise {
  let var_ = symval(q_var)
  if atom(expr) {
    if eq(expr, var_) {
      (Fix(0L), Fix(1L), Fix(1L))
    } else {
      (expr, Fix(0L), Fix(1L))
    }
  } else if freeof(var_, expr).truthy() {
    (expr, Fix(0L), Fix(1L))
  } else if eq(caar(expr), q_mplus) {
    let mut a : Value = Fix(0L)
    let mut b : Value = Nil
    let mut c : Value = Nil
    for arg in cdr(expr).iter() {
      let (aa, bb, cc) = split_two_term_poly(arg)
      a = add2_star(a, aa)
      if !eql(bb, Fix(0L)) {
        if b is Nil {
          // Is this the first nonzero power we've seen?
          b = bb
          c = cc
        } else if eql(c, cc) {
          // Is this another term with the same power as one we've seen
          // already?
          b = add2_star(b, bb)
        } else {
          // Otherwise, give up.
          powerseries_expansion_error(Nil) |> ignore
        }
      }
    }
    (a, b, c)
  } else if eq(caar(expr), q_mtimes) {
    let mut prod : Value = Fix(1L)
    let mut a : Value = Nil
    let mut b : Value = Nil
    let mut c : Value = Nil
    for arg in cdr(expr).iter() {
      let (aa, bb, cc) = split_two_term_poly(arg)
      if eql(bb, Fix(0L)) {
        prod = mul2_star(prod, aa)
      } else if a is Nil {
        a = aa
        b = bb
        c = cc
      } else {
        // This is the second term (a + b*x^c), so we know we'll end up with
        // mixed terms. (We don't try to spot e.g. (1-x)*(1+x))
        powerseries_expansion_error(Nil) |> ignore
      }
    }
    if a.truthy() {
      (mul2_star(a, prod), mul2_star(b, prod), c)
    } else {
      (prod, Fix(0L), Fix(1L))
    }
  } else if eq(caar(expr), q_mexpt) {
    // We know that EXPR isn't free of VAR. Check that VAR isn't in the
    // exponent.
    if !freeof(var_, caddr(expr)).truthy() {
      powerseries_expansion_error(Nil) |> ignore
    }
    let (a, b, c) = split_two_term_poly(cadr(expr))
    if eql(a, Fix(0L)) {
      (Fix(0L), power_star(b, caddr(expr)), mul2_star(c, caddr(expr)))
    } else if eql(b, Fix(0L)) {
      (power_star(a, caddr(expr)), Fix(0L), Fix(1L))
    } else {
      powerseries_expansion_error(Nil) |> ignore
      (Nil, Nil, Nil)
    }
  } else {
    powerseries_expansion_error(Nil) |> ignore
    (Nil, Nil, Nil)
  }
}

///|
/// Try to expand log(e) using the series for log(1+x). If a is nonzero
///   log(a + b*x^k) = log(a) + log(1 + b/a*x^k)
/// and we know a series for that.
fn sp2log(e : Value) -> Value raise {
  let var_ = symval(q_var)
  if atom(e) || free(e, var_).truthy() {
    return list2(list1(q_p_log), e)
  }
  let (a, b, k) = split_two_term_poly(specdisrep(e))
  // If a is zero, we can't expand
  if !eq(q_d_positive, asksign(list2(list1(q_mabs), a))) {
    powerseries_expansion_error(Nil) |> ignore
  }
  let mut coeff = mul2_star(b, power_star(a, Fix(-1L)))
  let coeff_sign = d_sign(coeff)
  let mut negate_coeff_p = false
  // If we know that the coefficient is not positive, switch the series
  // around (which gets rid of some ugly minus signs). If we're not sure, but
  // the coefficient "looks negative" (so is something like -7*k), switch it
  // around too.
  if eq(coeff_sign, q_d_neg) || eq(coeff_sign, q_d_nz) {
    negate_coeff_p = true
    coeff = mul2_star(Fix(-1L), coeff)
  } else if !(eq(coeff_sign, q_d_pos) || eq(coeff_sign, q_d_pz)) &&
    mtimesp(coeff).truthy() &&
    numberp(cadr(coeff)) &&
    minusp(cadr(coeff)) {
    negate_coeff_p = true
    coeff = simptimes(
      list_star([car(coeff), num_neg(cadr(coeff)), cddr(coeff)]),
      Fix(1L),
      t,
    )
  }
  let index = symval(q_n_starindex)
  list([
    list1(q_p_sum),
    muln_star([
      Fix(-1L),
      power_star(
        if negate_coeff_p {
          mul2_star(coeff, power_star(var_, k))
        } else {
          muln_star([Fix(-1L), coeff, power_star(var_, k)])
        },
        index,
      ),
      power_star(index, Fix(-1L)),
    ]),
    index,
    Fix(1L),
    q_d_inf,
  ])
}

///|
fn sp2expt(exp_ : Value) -> Value raise {
  let base = cadr(exp_)
  let power = caddr(exp_)
  let var_ = symval(q_var)
  if numberp(power) && mexptp(base).truthy() {
    // Do (a^b)^c = a^(bc) when c is a number
    sp2expt(power_star(cadr(base), mul2_star(power, caddr(base))))
  } else if free(power, var_).truthy() &&
    numberp(power) &&
    plusp(power) &&
    num_lt(power, symval(q_d_maxposex)) {
    // If a positive power which is free of the expansion variable and less
    // than the maximum expansion power then expand the base and do the
    // multiplication explicitly.
    muln(dup(sp2expand(base), power), Nil)
  } else if free(base, var_).truthy() {
    // If the base is free of VAR, rewrite as a^b = e^(b log(a)) if
    // necessary and then use the tabulated expansion of exp(x). If POWER is
    // a sum then do the rewrite a^(b+c) = a^b a^c
    let expansion = subst(
      symval(q_n_starindex),
      q_n_starindex,
      if eq(base, q_d__pcte) {
        get(q_mexpt, q_sp2)
      } else {
        subst(
          mk(q_mtimes, [mk(q_mlog, [base]), q_sp2var]),
          q_sp2var,
          get(q_mexpt, q_sp2),
        )
      },
    )
    if !mplusp(power).truthy() {
      sp2sub(expansion, power)
    } else {
      muln(mapcar(summand => sp2sub(expansion, summand), cdr(power)), Nil)
    }
  } else {
    powerseries_expansion_error(Nil)
  }
}

///|
fn dup(x : Value, p_n : Value) -> Value raise {
  if num_eq(p_n, Fix(1L)) {
    list1(x)
  } else {
    cons(x, dup(x, num_sub(p_n, Fix(1L))))
  }
}

///|
fn sp2diff(exp_ : Value, l : Value) -> Value raise {
  let var_ = symval(q_var)
  if free(exp_, var_).truthy() {
    return sp3form(sp2expand(exp_), cons(list1(q_p_derivative), l))
  }
  // If the expression isn't free of VAR, we know how to expand the result
  // if the orders of differentiation are all explicit non-negative
  // integers. Otherwise, give up.
  with_special(q_indl, Nil, () => {
    let mut exp_ = exp_
    let mut remaining_derivs : Value = Nil
    let mut ll = l
    while !(ll is Nil) {
      let y = car(ll)
      let order = cadr(ll)
      if !(integerp(order) && !minusp(order)) {
        powerseries_expansion_error(Nil) |> ignore
      } else if !eq(y, var_) {
        remaining_derivs = list_star([order, y, remaining_derivs])
      } else {
        let mut i : Value = Fix(0L)
        while num_lt(i, order) {
          set(q_indl, Nil) |> ignore
          exp_ = sp2diff1(sp2expand(exp_), Nil, Nil)
          i = one_plus(i)
        }
      }
      ll = cddr(ll)
    }
    if remaining_derivs.truthy() {
      sp3form(exp_, cons(list1(q_p_derivative), nreverse(remaining_derivs)))
    } else {
      exp_
    }
  })
}

///|
/// IND is a list of the indices, LOL is a list of the lower limits.
fn sp2diff1(exp_ : Value, ind : Value, lol : Value) -> Value raise {
  if atom(exp_) {
    sdiff(exp_, symval(q_var))
  } else if eq(caar(exp_), q_mplus) {
    cons(list1(q_mplus), mapcar(q => sp2diff1(q, ind, lol), cdr(exp_)))
  } else if eq(caar(exp_), q_p_sum) {
    set(q_indl, cons(copy_list(cddr(exp_)), symval(q_indl))) |> ignore
    sp2diff1(cadr(exp_), cons(caddr(exp_), ind), cons(cadddr(exp_), lol))
  } else {
    sp2diff2(exp_, ind, lol)
  }
}

///|
let series__frpat : Value = try! lread(
  "((mtimes) ((coefftt) (fr freevar)) ((coefftt) (e true)))",
)

///|
/// `(mbinding (vars vals) body)`
fn series__mbinding(vars : Value, vals : Value, body : () -> Value raise) -> Value raise {
  mbind(vars, vals, Nil) |> ignore
  let r = body() catch {
    e => {
      munbind(vars) |> ignore
      raise e
    }
  }
  munbind(vars) |> ignore
  r
}

///|
fn sp2diff2(exp_ : Value, ind : Value, lol : Value) -> Value raise {
  let var_ = symval(q_var)
  let m = m2(exp_, series__frpat)
  let fr = cdr(assq(q_fr, m))
  let e = cdr(assq(q_e, m))
  sp3reconst(
    if mexptp(e).truthy() && eq(cadr(e), var_) {
      if equal(
          Fix(0L),
          series__mbinding(ind, lol, () => meval(mul2_star(fr, caddr(e)))),
        ) {
        mul2_star(sp3substp1(ind, ind, mul2_star(fr, caddr(e))), e)
      } else if mgrp(
          Fix(1L),
          series__mbinding(ind, lol, () => simplify(mevalatoms(caddr(e)))),
        ).truthy() {
        muln_star([
          fr,
          caddr(e),
          power_star(cadr(e), sub_star(caddr(e), Fix(1L))),
        ])
      } else {
        sdiff(exp_, var_)
      }
    } else {
      sdiff(exp_, var_)
    },
  )
}

///|
fn sp2integ(exp_ : Value, v : Value, l : Value) -> Value raise {
  if l is Nil {
    if eq(symval(q_var), v) {
      sp2integ1(d_expand(sp2expand(exp_)))
    } else {
      sp3form(sp2expand(exp_), list2(list1(q_p_integrate), v))
    }
  } else {
    sp2integ2(exp_, v, car(l), cadr(l))
  }
}

///|
fn sp2integ1(exp_ : Value) -> Value raise {
  let mut exp_ = exp_
  let var_ = symval(q_var)
  if ratp(exp_, var_).truthy() {
    return ratint(exp_, var_)
  }
  if eq(caar(exp_), q_mplus) {
    return cons(list1(q_mplus), mapcar(x => sp2integ1(x), cdr(exp_)))
  }
  if eq(caar(exp_), q_mtimes) {
    let pair = partition(exp_, var_, Fix(1L))
    if !equal(car(pair), Fix(1L)) {
      return mul2_star(car(pair), sp2integ1(cdr(pair)))
    }
  }
  if eq(caar(exp_), q_mtimes) {
    exp_ = d_intosum(exp_)
  }
  if !eq(caar(exp_), q_p_sum) || !isinop(cadr(exp_), q_p_sum).truthy() {
    sinint(exp_, var_)
  } else {
    let e0 = exp_
    with_special(q_indl, list1(cddr(e0)), () => sp2integ12(
      cadr(e0),
      list1(caddr(e0)),
      list1(cadddr(e0)),
    ))
  }
}

///|
fn sp2integ12(exp_ : Value, ind : Value, lol : Value) -> Value raise {
  if atom(exp_) {
    sp3reconst(ratint(exp_, symval(q_var)))
  } else if eq(caar(exp_), q_mplus) {
    sp3reconst(addn(mapcar(q => sp2integ13(q, ind, lol), cdr(exp_)), Nil))
  } else if eq(caar(exp_), q_p_sum) {
    set(q_indl, cons(cddr(exp_), symval(q_indl))) |> ignore
    sp2integ12(cadr(exp_), cons(caddr(exp_), ind), cons(cadddr(exp_), lol))
  } else {
    sp3reconst(sp2integ13(exp_, ind, lol))
  }
}

///|
fn sp2integ13(exp_ : Value, ind : Value, lol : Value) -> Value raise {
  let var_ = symval(q_var)
  let m = m2(exp_, series__frpat)
  let fr = cdr(assq(q_fr, m))
  let e = cdr(assq(q_e, m))
  if mexptp(e).truthy() && eq(cadr(e), var_) {
    if mgrp(Fix(-1L), series__mbinding(ind, lol, () => meval(caddr(e)))).truthy() {
      mul2_star(sp3substpn(ind, ind, mul2_star(fr, caddr(e)), Fix(-1L)), e)
    } else {
      sinint(exp_, var_)
    }
  } else {
    sinint(exp_, var_)
  }
}

///|
/// Substitute NEW for OLD in the expression tree EXPRESSION. This is a bit
/// like MAXIMA-SUBSTITUTE, except it assumes OLD is a symbol, and it avoids
/// substituting for bound variables in %INTEGRATE and %AT forms. Returns
/// the new expression and a flag that says whether it has changed.
fn int_diff_substitute(
  new_ : Value,
  old : Value,
  expression : Value,
) -> (Value, Value) raise {
  if eq(expression, old) {
    return (new_, t)
  }
  if atom(expression) {
    return (expression, Nil)
  }
  let op = caar(expression)
  let args = cdr(expression)
  if (eq(op, q_p_integrate) && eq(old, second(args))) ||
    (
      eq(op, q_p_at) &&
      !atom(second(args)) &&
      (if eq(caar(second(args)), q_mlist) {
        // (second args) looks like ((mlist) ((mequal) ...) ...)
        memq(old, mapcar(x => second(x), rest(second(args)))).truthy()
      } else {
        // (second args) looks like ((mequal) ...)
        eq(old, second(second(args)))
      })
    ) {
    return (expression, Nil)
  }
  let mut some_changed_p = false
  let new_args = mapcar(
    x => {
      let (new_val, changed_p) = int_diff_substitute(new_, old, x)
      if changed_p.truthy() {
        some_changed_p = true
      }
      new_val
    },
    cdr(expression),
  )
  if !some_changed_p {
    (expression, Nil)
  } else {
    (simplifya(cons(list1(op), new_args), Nil), t)
  }
}

///|
/// Expand a definite integral, integrate(exp, v, lo, hi).
fn sp2integ2(exp_ : Value, v : Value, lo : Value, hi : Value) -> Value raise {
  let mut v = v
  let mut exp_ = exp_
  let var_ = symval(q_var)
  // Deal with the case where the integration variable is also the
  // expansion variable. We assume that the aliasing was accidental and that
  // the (bound) integration variable should be called something else.
  if eq(v, var_) {
    v = gensym()
    exp_ = subst(v, var_, exp_)
  }
  if boundp(q_ear_sp2integ_recursion_guard) {
    series__pee(
      "Recursion when trying to expand the definite integral: ~M",
      [out_of(symval(q_ear_sp2integ_recursion_guard))],
    )
    |> ignore
  }
  if !(free(lo, var_).truthy() && free(hi, var_).truthy()) {
    // Suppose one or both of the endpoints involves VAR. We'll give up
    // unless they are monomials in VAR. If they are, then we try to expand
    // the integral as a power series and find an antiderivative.
    let lo_exp = sp2expand(lo)
    let hi_exp = sp2expand(hi)
    let e0 = exp_
    let v0 = v
    with_special(q_ear_sp2integ_recursion_guard, e0, () => {
      if !(smono(lo_exp, var_).truthy() && smono(hi_exp, var_).truthy()) {
        series__pee(
          "Endpoints of definite integral ~M are not monomials in the expansion variable.",
          [out_of(e0)],
        )
        |> ignore
      }
      // Since this is a formal powerseries calculation, we needn't concern
      // ourselves with radii of convergence here. Just expand the integrand
      // about zero.
      let anti_derivative = sinint(d_powerseries(e0, v0, Fix(0L)), v0)
      sub_star(
        int_diff_substitute(hi_exp, v0, anti_derivative).0,
        int_diff_substitute(lo_exp, v0, anti_derivative).0,
      )
    })
  } else if free(exp_, var_).truthy() {
    list([list1(q_p_integrate), subst(var_, v, exp_), var_, lo, hi])
  } else {
    sp3form(sp2expand(exp_), list4(list1(q_p_integrate), v, lo, hi))
  }
}

// ---------------------------------------------------------------------------
// phase three		miscellaneous garbage and final simplification

///|
fn sp3reconst(e : Value) -> Value raise {
  let mut l = symval(q_indl)
  let mut e = e
  while !(l is Nil) {
    e = list_star([list1(q_p_sum), e, car(l)])
    l = cdr(l)
  }
  e
}

///|
fn sp3substpn(vars : Value, vals : Value, exp_ : Value, n : Value) -> Value raise {
  sp3subst(vars, mapcar(q => add2_star(q, n), vals), exp_)
}

///|
fn sp3substp1(vars : Value, vals : Value, exp_ : Value) -> Value raise {
  sp3substpn(vars, vals, exp_, Fix(1L))
}

///|
fn sp3subst(vars : Value, vals : Value, exp_ : Value) -> Value raise {
  simplify(
    sublis(
      mapcar2((a, b) => cons(a, b), cdr(vars), cdr(vals)),
      subst(car(vals), car(vars), exp_),
    ),
  )
}

///|
fn sp3form(e : Value, n_starform : Value) -> Value raise {
  with_special(q_n_starform, n_starform, () => sp3form1(e))
}

///|
fn sp3form1(e : Value) -> Value raise {
  let form = symval(q_n_starform)
  if atom(e) {
    list_star([car(form), e, cdr(form)])
  } else if eq(caar(e), q_mplus) {
    cons(list1(q_mplus), mapcar(x => sp3form1(x), cdr(e)))
  } else if eq(caar(e), q_p_sum) {
    list_star([list1(q_p_sum), sp3form1(cadr(e)), cddr(e)])
  } else {
    list_star([car(form), e, cdr(form)])
  }
}

// These are the series expansions for circular, exponential and arc
// trigonometric functions (SP2 properties).

///|
let series__sp2_table : String =
  #|(%sin
  #|    ((%sum) ((mtimes)
  #|	     ((mexpt) -1 *index)
  #|	     ((mexpt) ((mfactorial) ((mplus) ((mtimes) 2 *index) 1)) -1)
  #|	     ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) 1)))
  #|     *index 0 $inf)
  #| %cos
  #|    ((%sum) ((mtimes) ((mexpt) -1 *index)
  #|	     ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|	     ((mexpt) sp2var ((mtimes) 2 *index)))
  #|     *index 0 $inf)
  #| %tan
  #|    ((%sum) ((mtimes) ((mexpt) -1 ((mplus) *index -1))
  #|	     ((mexpt) 2 ((mtimes) 2 *index))
  #|	     ((mplus) ((mexpt) 2 ((mtimes) 2 *index)) -1)
  #|	     ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|	     ((%bern) ((mtimes) 2 *index))
  #|	     ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) -1)))
  #|     *index 0 $inf)
  #| %csc
  #|    ((%sum) ((mtimes) 2
  #|	     ((mexpt) -1 ((mplus) *index -1))
  #|	     ((mplus) ((mexpt) 2 ((mplus) ((mtimes) 2 *index) -1)) -1)
  #|	     ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|	     ((%bern) ((mtimes) 2 *index))
  #|	     ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) -1)))
  #|     *index 0 $inf)
  #| %cot
  #|    ((%sum) ((mtimes)
  #|	     ((mexpt) -1 *index)
  #|	     ((mexpt) 2 ((mtimes) 2 *index))
  #|	     ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|	     ((%bern) ((mtimes) 2 *index))
  #|	     ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) -1)))
  #|     *index 0 $inf)
  #| %sec
  #|    ((%sum) ((mtimes) ((mexpt) -1 *index)
  #|	     ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|	     ((%euler) ((mtimes) 2 *index))
  #|	     ((mexpt) sp2var ((mtimes) 2 *index)))
  #|     *index 0 $inf)
  #| mexpt
  #|    ((%sum)
  #|     ((mtimes) ((mexpt) ((mfactorial) *index) -1) ((mexpt) sp2var *index))
  #|     *index 0 $inf)
  #| %sinh
  #|    ((%sum) ((mtimes)
  #|	     ((mexpt) ((mfactorial) ((mplus) ((mtimes) 2 *index) 1)) -1)
  #|	     ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) 1)))
  #|     *index 0 $inf)
  #| %cosh
  #|    ((%sum) ((mtimes)
  #|	     ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|	     ((mexpt) sp2var ((mtimes) 2 *index)))
  #|     *index 0 $inf)
  #| %tanh
  #|    ((%sum)
  #|     ((mtimes) ((mexpt) 4 *index)
  #|      ((mplus) ((mexpt) 4 *index) -1)
  #|      ((%bern) ((mtimes) 2 *index))
  #|      ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) -1))
  #|      ((mexpt)
  #|       ((mfactorial) ((mtimes) 2 *index))
  #|       -1))
  #|     *index 0 $inf)
  #| %coth
  #|    ((%sum)
  #|     ((mtimes) ((mexpt) 4 *index)
  #|      ((%bern) ((mtimes) 2 *index))
  #|      ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|      ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) -1)))
  #|     *index 0 $inf)
  #| %sech
  #|    ((%sum)
  #|     ((mtimes) ((%euler) ((mtimes) 2 *index))
  #|      ((mexpt) ((mfactorial) ((mtimes) 2 *index)) -1)
  #|      ((mexpt) sp2var ((mtimes) 2 *index)))
  #|     *index 0 $inf)
  #| %csch
  #|    ((%sum)
  #|     ((mtimes) -2 ((mplus) ((mexpt) 2 ((mplus) ((mtimes) 2 *index) -1)) -1)
  #|      ((mexpt) ((mfactorial) ((mtimes) *index 2)) -1)
  #|      ((%bern) ((mtimes) 2 *index))
  #|      ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) -1)))
  #|     *index 0 $inf)
  #| %asin
  #|    ((%sum)
  #|     ((mtimes) ((%genfact) ((mplus) ((mtimes) 2 *index) -1) *index 2)
  #|      ((mexpt) ((%genfact) ((mtimes) 2 *index) *index 2) -1)
  #|      ((mexpt) ((mplus) ((mtimes) 2 *index) 1) -1)
  #|      ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) 1)))
  #|     *index 0 $inf)
  #| %atan
  #|    ((%sum)
  #|     ((mtimes) ((mexpt) -1 *index)
  #|      ((mexpt) ((mplus) ((mtimes) 2 *index) 1) -1)
  #|      ((mexpt) sp2var ((mplus) ((mtimes) 2 *index) 1)))
  #|     *index 0 $inf)
  #| %lambert_w
  #|    ((%sum)
  #|     ((mtimes) ((mexpt) -1 *index)
  #|	  ((mexpt) -1 1)
  #|	 ((mexpt) *index ( (mplus) *index -1))
  #|	 ((mexpt) ((mfactorial) *index) -1) ((mexpt) sp2var *index))
  #|     *index 1 $inf))

///|
fn init_series() -> Unit raise {
  let mut l = lread(series__sp2_table)
  while !(l is Nil) {
    putprop(car(l), cadr(l), q_sp2) |> ignore
    l = cddr(l)
  }
}

// Port of src/hayat.lisp, part 4: products, powers and logarithms of
// expressions (tstimes, tsexpt, tslog), get-lexp, sums/products,
// derivatives, the disrep routines, error handling and taylorinfo.

///|
fn hayat__cddadr(x : Value) -> Value {
  cddr(cadr(x))
}

///|
fn hayat__cdddar(x : Value) -> Value {
  cdddr(car(x))
}

///|
/// `(next-series l)` = `(cdadr l)`.
fn next_series(l : Value) -> Value raise {
  cdadr(l)
}

///|
fn tstimes_get_pw(l : Value, pw : Value) -> Value raise {
  let mut l = l
  let mut pw = pw
  while !(l is Nil) {
    let vect = ord_vector(cdar(l))
    pw = mapcar2((pwq, ple) => e_plus(pwq, ple), pw, vect)
    rplacd(car(l), cons(cdar(l), vect)) |> ignore
    l = cdr(l)
  }
  pw
}

///|
fn tstimes_l_mult(a : Value) -> Value raise {
  with_special(q_d_maxtayorder, t, () => {
    let mut l = cdr(a)
    let mut acc = car(a)
    while !(l is Nil) {
      acc = pstimes(acc, car(l))
      l = cdr(l)
    }
    acc
  })
}

///|
fn mzfree(e : Value, l : Value) -> Value raise {
  let mut l = l
  while !(l is Nil) {
    if !zfree(e, car(l)).truthy() {
      return Nil
    }
    l = cdr(l)
  }
  t
}

// The lists posl, negl and zerl have the following format:
//
//   ( (<expression> <expansion> <order vector>) . . . )

///|
fn tstimes(l : Value) -> Value raise {
  let mut l = l
  let mut funl : Value = Nil
  let mut expl : Value = Nil
  let mut zerl : Value = Nil
  let mut posl : Value = Nil
  let mut negfl = false
  let mut fixl = rcone()
  // find the exponentials
  for fun in l.iter() {
    if mexptp(fun).truthy() {
      expl = cons(
        if free(caddr(fun), car(symval(q_tvars))).truthy() {
          fun
        } else {
          list3(
            list1(q_mexpt),
            q_d__pcte,
            mul2_star(caddr(fun), list2(list1(q_p_log), cadr(fun))),
          )
        },
        expl,
      )
    } else {
      funl = cons(fun, funl)
    }
  }
  if expl.truthy() {
    expl = tsexp_comb(expl) // simplify exps
    expl = tsbase_comb(expl) // and again
  }
  l = nconc(expl, funl) // now try expanding
  let l0 = l
  expl = with_special(q_trunc_constants_q, Nil, () => cons(
    Fix(0L),
    mapcar(exp_ => cons(exp_, taylor2(exp_)), l0),
  ))
  // EXPL is now of the form (0 ( <form> . <taylor2(form)> ) ...)
  // L points behind the cons considered for destructive updating.
  let mut l = expl
  let mut zero_found = false
  while !(cdr(l) is Nil) {
    if rczerop(cdadr(l)).truthy() {
      // Consider taylor((a+1/x)*1/x,x,0,-2). Each factor will be on zerl.
      // Each factor will also appear to have le = 0 since its series is 0,
      // which would fool the get-pw routines below if they tried to handle
      // this case. The easiest fix for now appears to be to always call
      // get-lexp here.
      let tem = get_lexp(caadr(l), rcone(), Nil)
      if rczerop(tem).truthy() {
        zero_found = true
        break
      } else {
        posl = cons(cons(caadr(l), tem), posl)
        rplacd(l, cddr(l)) |> ignore
      }
    } else if pscoefp(cdadr(l)).truthy() {
      if mzfree(caadr(l), symval(q_tvars)).truthy() {
        // must be zfree to permit ratfuns
        fixl = pstimes(cdadr(l), fixl)
        rplacd(l, cddr(l)) |> ignore
      } else {
        zerl = cons(cadr(l), zerl)
        rplacd(l, cddr(l)) |> ignore
      }
    } else if rczerop(ps_le(cdadr(l))).truthy() {
      zerl = cons(cadr(l), zerl)
      rplacd(l, cddr(l)) |> ignore
    } else if e_gt(ps_le(cdadr(l)), rczero()).truthy() {
      posl = cons(cadr(l), posl)
      rplacd(l, cddr(l)) |> ignore
    } else {
      l = cdr(l)
    }
  }
  if zero_found {
    return rczero()
  }
  let negl = cdr(expl)
  let temp = ord_vector(fixl)
  for x in temp.iter() {
    if e_gt(rczero(), x).truthy() {
      negfl = true
    }
  }
  tstimes_get_pw(zerl, temp) |> ignore
  let pw = tstimes_get_pw(posl, tstimes_get_pw(negl, temp))
  if negl.truthy() || negfl {
    posl = mapcar(
      x => {
        let mut ds = symval(q_tlist)
        let mut lels = cddr(x)
        let mut pws = pw
        while !(ds is Nil) && !(lels is Nil) && !(pws is Nil) {
          let datum = car(ds)
          push_pw(datum, e_plus(current_trunc(datum), e_(car(lels), e2=car(pws))))
          |> ignore
          ds = cdr(ds)
          lels = cdr(lels)
          pws = cdr(pws)
        }
        let r = taylor2(car(x))
        mapc(datum => pop_pw(datum) |> ignore, symval(q_tlist)) |> ignore
        r
      },
      nconc_n([posl, zerl, negl]),
    )
  } else {
    posl = nconc_n([
      mapcar(x => cadr(x), posl),
      mapcar(x => cadr(x), zerl),
      mapcar(x => cadr(x), negl),
    ])
  }
  posl = tstimes_l_mult(posl)
  let ans = if fixl is Nil {
    posl
  } else if posl is Nil {
    fixl
  } else {
    pstimes(fixl, posl)
  }
  if symval(q_d_maxtayorder).truthy() {
    ans
  } else {
    pstrunc(ans)
  }
}

///|
/// This routine transforms a list of exponentials as follows:
///	a^c*b^(n*c) ===> (a*b^n)^c,   where n is free of var.
/// This transformation is only applicable when c is not free of var.
/// Clobbers L.
fn tsexp_comb(l : Value) -> Value raise {
  let l = cons(sym("*"), l)
  let mut a = l
  while !(cddr(a) is Nil) {
    let e = d_ratsimp(caddr(cadr(a)), Nil)
    rplaca(hayat__cddadr(a), e) |> ignore
    // Must delete e^0 lest we divide by the 0 below.
    if equal(e, Fix(0L)) {
      rplacd(a, cddr(a)) |> ignore
    } else if mfree(caddr(cadr(a)), symval(q_tvars)).truthy() {
      a = cdr(a)
    } else {
      let mut b = cddr(a)
      while true {
        if b is Nil {
          a = cdr(a)
          break
        }
        let n = d_ratsimp(div_star(caddar(b), caddr(cadr(a))), Nil)
        if mfree(n, symval(q_tvars)).truthy() {
          rplaca(
            b,
            list3(
              list2(q_mexpt, q_simp),
              mul2_star(cadadr(a), power_star(cadar(b), n)), // b^n
              caddr(cadr(a)),
            ),
          )
          |> ignore
          rplacd(a, cddr(a)) |> ignore // delete a^c
          break
        }
        b = cdr(b)
      }
    }
  }
  cdr(l) // get rid of the *
}

///|
/// This routine transforms a list of exponentials as follows:
///	a^b*a^c ===> a^(b+c),
/// this is only necessary when b and c depend on "var". Clobbers L.
fn tsbase_comb(l : Value) -> Value raise {
  let l = cons(sym("*"), l)
  let mut a = l
  while !(cddr(a) is Nil) {
    let mut b = cddr(a)
    while true {
      if b is Nil {
        // did not return early so pop.
        a = cdr(a)
        break
      }
      if alike1(cadar(b), cadadr(a)).truthy() {
        rplaca(b, power_star(cadar(b), add2_star(caddar(b), caddr(cadr(a)))))
        |> ignore
        rplacd(a, cddr(a)) |> ignore
        break
      }
      b = cdr(b)
    }
  }
  cdr(l)
}

///|
fn tsexpt(b : Value, e : Value) -> Value raise {
  if atom(b) &&
    mnump(e).truthy() &&
    get_datum(b).truthy() &&
    !eq(exp_pt(get_datum(b)), q_d_minf) {
    // one could remove this clause and let this case be handled by tsexpt1
    var_expand(b, e, Nil)
  } else if mfree(e, symval(q_tvars)).truthy() {
    tsexpt1(b, e)
  } else if eq(q_d__pcte, b) {
    tsexpt_red(list1(e))
  } else {
    tsexpt_red(list2(list2(list1(q_p_log), b), e))
  }
}

///|
fn tsexpt_red(l : Value) -> Value raise {
  with_specials(
    [
      (q_full_log, Nil),
      (q_log_1, mk(q_mtimes, [q_d__pcti, q_d__pctpi])),
      (
        q_log_pcti,
        mk(q_mtimes, [mk(q_rat, [Fix(1L), Fix(2L)]), q_d__pcti, q_d__pctpi]),
      ),
    ],
    () => {
      let mut l = l
      let mut free : Value = Nil
      let mut nfree : Value = Nil
      while true {
        // tag A
        let mut ll = l
        while !(ll is Nil) {
          if mtimesp(car(ll)).truthy() {
            ll = append(ll, cdar(ll))
          } else if mfree(car(ll), symval(q_tvars)).truthy() {
            free = cons(car(ll), free)
          } else {
            nfree = cons(car(ll), nfree)
          }
          ll = cdr(ll)
        }
        if cdr(nfree).truthy() || atom(car(nfree)) {
          break
        } else if eq(caaar(nfree), q_p_log) {
          return tsexpt1(cadar(nfree), muln(free, Nil))
        } else if memq(caaar(nfree), symval(q_n_starpsacirc)).truthy() {
          // simplify after removing simp flag and convert to logarithmic form
          let nf = nfree
          l = list1(
            with_special(q_d_logarc, t, () => simplifya(
              cons(list1(caaar(nf)), cdar(nf)),
              Nil,
            )),
          )
          nfree = cdr(nfree)
          continue
        } else {
          break
        }
      }
      // Must have truncs > 0 so that logs in the expt aren't trunc'd.
      // E.g, consider taylor(x^(x-1),x,0,-1).
      mhayat__tlist_mapc(d => push_pw(d, emax(current_trunc(d), rcone())) |> ignore)
      |> ignore
      let expt = muln(append(nfree, free), Nil)
      let mut ps = taylor2(expt)
      mhayat__tlist_mapc(d => pop_pw(d) |> ignore) |> ignore
      // Here we must account for the truncation gain or lossage that is
      // encountered in exp(c*log(x)+y) -> x^c*exp(y).
      let c0 = if pscoefp(ps).truthy() {
        ps
      } else {
        psterm(terms(ps), rczero())
      }
      let mut e_c0 : Value = Nil
      if !rczerop(c0).truthy() {
        e_c0 = psexpt_fn(c0)
        let ord_e_c0 = ord_vector(e_c0)
        // Must emax with 0 so that new singular kernels won't be trunc'd
        // e.g exp(1/x+...) to degree -2 should be exp(-1/x)+...
        mapcar2(
          (d, o) => push_pw(d, emax(e_(current_trunc(d), e2=o), rczero())),
          symval(q_tlist),
          ord_e_c0,
        )
        |> ignore
        ps = psdiff(taylor2(expt), c0)
      }
      ps = psexpt_fn(ps)
      if e_c0.truthy() {
        mhayat__tlist_mapc(d => pop_pw(d) |> ignore) |> ignore
        ps = pstimes(e_c0, ps)
      }
      pstrunc(ps)
    },
  )
}

///|
/// Taylor's b^e, where e is independent of tvars.
fn tsexpt1(b : Value, e : Value) -> Value raise {
  // Don't mod exponents! See WGM's bug of 3/6/83 for an example.
  let e = with_special(q_modulus, Nil, () => {
    mapc(
      datum => push_pw(datum, emax(current_trunc(datum), rczero())) |> ignore,
      symval(q_tlist),
    )
    |> ignore
    let r = taylor2(e)
    mapc(datum => pop_pw(datum) |> ignore, symval(q_tlist)) |> ignore
    r
  })
  let mut s = psfind_s(e)
  let mut tb = taylor2(b)
  let pw = if psp(tb).truthy() {
    current_trunc(get_datum(get_key_var(gvar(tb))))
  } else if rczerop(tb).truthy() {
    // Constant problem kludge.
    current_trunc(car(symval(q_tlist)))
  } else {
    rczero()
  }
  if floatp(car(s)) {
    s = maxima_rationalize(quot(car(s), cdr(s)))
  }
  // We must ensure that the lc is non-zero since it will be inverted in
  // psexpt.
  tb = strip_zeroes(tb, t)
  let mut le : Value = Nil
  if rczerop(tb).truthy() {
    // When 1 > s we need more terms since -le*(s-1) > 0.
    if e_gt(rcone(), s).truthy() ||
      (e_gt(rczero(), pw).truthy() && e_gt(s, rcone()).truthy()) {
      tb = get_lexp(b, Nil, t)
    }
    le = ps_le_star(tb)
  } else if psp(tb).truthy() {
    le = ps_le(tb)
  } else {
    return rcexpt(tb, e)
  }
  if e_gt(e_star(s, le), pw).truthy() && !symval(q_d_maxtayorder).truthy() {
    return rczero()
  }
  s = e_(pw, e2=e_star(le, e1_(s)))
  psexpt(
    if e_gt(pw, s).truthy() {
      if symval(q_d_maxtayorder).truthy() {
        tb
      } else {
        pstrunc1(tb, list1(cons(gvar(tb), s)))
      }
    } else if !psp(tb).truthy() {
      // because of constants not retaining info, have to just keep the
      // constant here
      tb
    } else {
      mhayat__let_pw(get_datum(get_key_var(gvar(tb))), s, () => strip_zeroes(
        taylor2(b),
        t,
      ))
    },
    e,
  )
}

// The method of calculating truncation levels below is incorrect (i.e.
// increment-truncs & decrement-truncs, also used above). Examples which
// exhibit this incorrectness are:
// taylor(log(sin(y)+x),x,0,2,y,0,1) is missing a y/6*x and -1/6*x^2
// taylor(log(sin(z)+sin(y)+x),x,0,f1,y,0,3,z,0,5) misses a z^5*y^3 term.
//
// TSLOG must find the lowest degree term in the expansion of the log arg,
// then expand with the orders of all var's in this low term incremented by
// their order in this low term. Note that this is only necessary for var's
// with ord > 0, since otherwise we have already expanded to a higher ord
// than required. Also we must not do this for var's with trunc < 0, since
// this may incorrectly truncate terms which should end up as logs.

///|
fn increment_truncs(ps : Value) -> Value raise {
  let mut ps = ps
  let mut trunc = t_o_var(gvar(ps))
  let mut data : Value = Nil
  while !pscoefp(ps).truthy() {
    if e_gt(ps_le(ps), rczero()).truthy() {
      data = cons(assq(get_key_var(gvar(ps)), symval(q_tlist)), data)
      push_pw(
        car(data),
        e_plus(e_star(e_plus(trunc, rctwo()), ps_le(ps)), current_trunc(car(data))),
      )
      |> ignore
      trunc = e_plus(trunc, current_trunc(car(data)))
    }
    ps = ps_lc(ps)
  }
  data
}

///|
fn decrement_truncs(data : Value) -> Value raise {
  mapc(d => pop_pw(d) |> ignore, data)
}

///|
fn tslog(arg : Value) -> Value raise {
  let mut psarg = taylor2(arg)
  let mut datum : Value = Nil
  if rczerop(psarg).truthy() {
    psarg = get_lexp(arg, Nil, t)
  }
  // We must ensure that the lc is non-zero since it will be inverted in
  // pslog
  psarg = strip_zeroes(psarg, t)
  let mut ps = psarg
  let mut shift = rcone()
  while !pscoefp(ps).truthy() {
    datum = cons(get_datum(get_key_var(gvar(ps))), datum)
    if e_gt(ps_le(ps), rczero()).truthy() &&
      e_gt(current_trunc(car(datum)), rczero()).truthy() {
      push_pw(car(datum), e_plus(e_star(shift, ps_le(ps)), current_trunc(car(datum))))
      |> ignore
    } else {
      datum = cdr(datum)
    }
    ps = ps_lc(ps)
    shift = e_star(shift, rctwo())
  }
  if datum.truthy() {
    psarg = taylor2(arg)
    if rczerop(psarg).truthy() {
      psarg = get_lexp(arg, Nil, t)
    }
    mapc(data => pop_pw(data) |> ignore, datum) |> ignore
  }
  pslog(psarg)
}

///|
/// When e-start is non-null we start expanding at order e-start, ... , 2^m,
/// then 2^m*pow, instead of the normal sequence pow, ... , 2^m*pow (where
/// m = $taylordepth, pow = ord of var). This is done because it is usually
/// much more efficient for large, non-trivial expansions when we only want
/// the lowest order term.
fn get_lexp(exp_ : Value, e_start : Value, zerocheck_q : Value) -> Value raise {
  let mut e_start = e_start
  if equal(exp_, Fix(0L)) {
    return if zerocheck_q.truthy() { tay_depth_err() } else { rczero() }
  }
  mhayat__tlist_mapc(d => push_pw(
      d,
      if e_start.truthy() {
        e_start
      } else {
        emax(orig_trunc(d), rcone())
      },
    )
    |> ignore)
  |> ignore
  let mut i = to_int64(symval(q_d_taylordepth)) + 1L
  while true {
    if i == 0L {
      mhayat__tlist_mapc(d => pop_pw(d) |> ignore) |> ignore
      return if zerocheck_q.truthy() {
        tay_depth_err()
      } else {
        if !symval(q_silent_taylor_flag).truthy() {
          zero_warn(exp_) |> ignore
        }
        rczero()
      }
    }
    let psexp = if zerocheck_q.truthy() {
      strip_zeroes(taylor2(exp_), t)
    } else {
      taylor2(exp_)
    }
    if rczerop(psexp).truthy() && memq(exp_, symval(q_zerolist)) is Nil {
      ()
    } else {
      mhayat__tlist_mapc(d => pop_pw(d) |> ignore) |> ignore
      return psexp
    }
    if i == 1L && e_start.truthy() {
      e_start = Nil
      i = 2L
      mhayat__tlist_mapc(d => {
        let v = e_star(orig_trunc(d), current_trunc(d))
        pop_pw(d) |> ignore
        push_pw(d, v) |> ignore
      })
      |> ignore
    } else {
      mhayat__tlist_mapc(d => {
        let v = e_star(rctwo(), current_trunc(d))
        pop_pw(d) |> ignore
        push_pw(d, v) |> ignore
      })
      |> ignore
    }
    i = i - 1L
  }
  Nil
}

///|
fn n1p(x : Value) -> Value raise {
  lbool(equal(x, Fix(1L)) || equal(x, Flo(1.0)))
}

///|
fn n_lbmax_trunc_rb() -> Value raise {
  // An infinite truncation level is represented as NIL and must not reach
  // the TRUNCATE call below, so skip it when maximizing.
  let mut l = symval(q_tlist)
  let mut emax = rczero()
  while !(l is Nil) {
    let trunc = current_trunc(car(l))
    if !(trunc is Nil) && e_gt(trunc, emax).truthy() {
      emax = trunc
    }
    l = cdr(l)
  }
  one_plus(num_truncate(car(emax), b=cdr(emax)).0)
}

///|
fn tsprsum(f : Value, l : Value, type_ : Value) -> Value raise {
  if mfree(f, symval(q_tvars)).truthy() {
    return newsym(f)
  }
  let li = list1(car(l))
  let hi = caddr(l)
  let lv = list1(cadr(l))
  // With numeric bounds the loop below is finite, so neither the early
  // exits nor the TAYLORDEPTH guard is needed.
  let finite_q = numberp(cadr(l)) && numberp(caddr(l))
  // $maxtayorder is bound to () since it is needed to determine when terms
  // are 0.
  with_special(q_d_maxtayorder, Nil, () => {
    if numberp(car(lv)) && numberp(hi) && num_gt(car(lv), hi) {
      return if eq(type_, q_p_sum) {
        taylor2(Fix(0L))
      } else {
        taylor2(Fix(1L))
      }
    }
    let mut type_ = type_
    if eq(type_, q_p_sum) {
      type_ = Nil
    }
    let m = num_mul(n_lbmax_trunc_rb(), ash(Fix(1L), to_int(symval(q_d_taylordepth))))
    let mut k : Value = Fix(0L)
    let mut ans = taylor2(maxima_substitute(car(lv), car(li), f))
    let mut a : Value = Nil
    let mut aa : Value = Nil
    while !equal(hi, car(lv)) {
      rplaca(lv, add2_star(Fix(1L), car(lv))) |> ignore
      // A cheap heuristic to catch infinite recursion when possible, should
      // be improved in the future
      if num_gt(k, m) && !finite_q {
        exp_pt_err() |> ignore
      } else {
        // AA is the unexpanded term, the early exits below check it to
        // leave identically zero or one terms alone. For finite bounds, it
        // is pinned to 0 or 1, which disables the early exits entirely.
        aa = if finite_q {
          if type_.truthy() {
            Fix(1L)
          } else {
            Fix(0L)
          }
        } else {
          maxima_substitute(car(lv), car(li), f)
        }
        a = taylor2(maxima_substitute(car(lv), car(li), f))
      }
      if type_.truthy() {
        if n1p(car(a)).truthy() && n1p(cdr(a)).truthy() && !n1p(aa).truthy() {
          return ans
        } else {
          ans = pstimes(a, ans)
        }
      } else if rczerop(a).truthy() && !(numberp(aa) && zerop(aa)) {
        return ans
      } else {
        ans = psplus(ans, a)
      }
      k = one_plus(k)
    }
    ans
  })
}

///|
fn tsdiff(e : Value, l : Value) -> Value raise {
  let mut e = e
  let mut n : Value = Nil
  let mut v : Value = Nil
  let mut u : Value = Nil
  let mut ll = l
  while !(ll is Nil) {
    if atom(car(ll)) &&
      numberp(cadr(ll)) &&
      assq(car(ll), symval(q_tlist)).truthy() {
      n = cons(cadr(ll), n)
      v = cons(car(ll), v)
    } else {
      u = cons(car(ll), cons(cadr(ll), u))
    }
    ll = cddr(ll)
  }
  // If N is null, it means that the derivative is wrt to some variable
  // other than one of the taylor variables. If so, give up; let the caller
  // handle it.
  if n is Nil {
    return Nil
  }
  // U holds the differentiations wrt non-Taylor variables only, the Taylor
  // variables in N/V are handled below via PSDP.
  if u.truthy() {
    e = meval(cons(list1(q_d_diff), cons(e, u)))
  }
  let data = mapcar(x => get_datum(x), v)
  mapcar2(
    (datum, pw) => push_pw(datum, e_plus(current_trunc(datum), prep1(pw))),
    data,
    n,
  )
  |> ignore
  e = taylor2(e)
  mapc(datum => pop_pw(datum) |> ignore, data) |> ignore
  let mut vl = v
  let mut nl = n
  while !(vl is Nil) {
    let mut i : Value = Fix(1L)
    while !num_gt(i, car(nl)) {
      let var_ = car(vl)
      mapcar2(
        (a, b) => {
          // (CAR VL) is the variable we are currently differentiating wrt.
          putprop(a, prep1(sdiff(b, var_)), q_diff) |> ignore
          Nil
        },
        symval(q_genvar),
        symval(q_varlist),
      )
      |> ignore
      e = psdp(e)
      i = one_plus(i)
    }
    vl = cdr(vl)
    nl = cdr(nl)
  }
  e
}

///|
/// Evaluate the form X, which is always `(meval '<expr>)` here.
fn hayat__eval_form(x : Value) -> Value raise {
  if eq(car(x), q_meval) && hayat__is_quote(cadr(x)) {
    meval(cadr(cadr(x)))
  } else {
    raise LispError::SimpleError("no-sing-err: cannot evaluate form")
  }
}

///|
fn hayat__is_quote(x : Value) -> Bool {
  match x {
    Cons({ car: Sym(_) as q, .. }) => eq(q, q_quote)
    _ => false
  }
}

///|
/// Try to catch all singularities.
fn no_sing_err(x : Value) -> Value raise {
  with_special(q_errorsw, t, () => {
    let ans = catch_tag(q_errorsw, () => hayat__eval_form(x))
    if eq(ans, t) {
      unfam_sing_err()
    } else {
      ans
    }
  })
}

///|
/// Evaluate deriv at location var2=pt.
fn eval_deriv(deriv : Value, var2 : Value, pt : Value) -> Value raise {
  with_special(q_errorsw, t, () => no_sing_err(
    list2(
      q_meval,
      list2(
        q_quote,
        list3(list1(q_d_at), deriv, list3(list1(q_mequal), var2, pt)),
      ),
    ),
  ))
}

///|
/// Don't know behavior of random fun's @ inf.
fn check_inf_sing(pt_list : Value) -> Value raise {
  if memq(q_d_inf, pt_list).truthy() || memq(q_d_minf, pt_list).truthy() {
    unfam_sing_err()
  } else {
    Nil
  }
}

///|
/// L is tlist.
fn diff_expand(exp_ : Value, l : Value) -> Value raise {
  check_inf_sing(mapcar(x => caddr(x), l)) |> ignore
  if l is Nil {
    return exp_
  }
  let exp_ = diff_expand(exp_, cdr(l))
  let mut deriv = sdiff(exp_, caar(l))
  let var2 = caar(l)
  let mut coef : Value = Fix(1L)
  let mut cnt : Value = Fix(1L)
  let pt = exp_pt(car(l))
  let lim = rcdisrep(current_trunc(car(l)))
  let mut ans = list1(
    no_sing_err(
      list2(
        q_meval,
        list2(
          q_quote,
          list3(
            list1(q_d_at),
            exp_,
            list3(list1(q_mequal), caar(l), exp_pt(car(l))),
          ),
        ),
      ),
    ),
  )
  while !(great(cnt, lim).truthy() || equal(deriv, Fix(0L))) {
    let new_deriv = sdiff(deriv, var2)
    let new_coef = num_mul(coef, one_plus(cnt))
    let new_cnt = one_plus(cnt)
    let new_ans = cons(
      list4(
        list1(q_mtimes),
        list3(list2(q_rat, q_simp), Fix(1L), coef),
        eval_deriv(deriv, var2, pt),
        list3(list1(q_mexpt), sub_star(var2, pt), cnt),
      ),
      ans,
    )
    deriv = new_deriv
    coef = new_coef
    cnt = new_cnt
    ans = new_ans
  }
  cons(list1(q_mplus), ans)
}

// Subtitle disreping routines

///|
fn edisrep(e : Value) -> Value raise {
  if num_eq(cdr(e), Fix(1L)) {
    car(e)
  } else {
    list3(list1(q_rat), car(e), cdr(e))
  }
}

///|
fn striptimes(a : Value) -> Value raise {
  if mtimesp(a).truthy() {
    cdr(a)
  } else {
    list1(a)
  }
}

///|
fn srdis(x : Value) -> Value raise {
  // Called only internally, no need to expand.
  with_special(q_d_psexpand, Nil, () => d_ratdisrep(
    cons(
      list([
        q_mrat,
        q_simp,
        symval(q_varlist),
        symval(q_genvar),
        symval(q_tlist),
        q_trunc,
      ]),
      x,
    ),
  ))
}

///|
fn srdisrep(r : Value) -> Value raise {
  with_specials(
    [(q_varlist, mrat_varlist(r)), (q_genvar, mrat_genvar(r))],
    () => {
      mapcar2(
        (exp_, genv) => {
          putprop(genv, exp_, q_disrep) |> ignore
          Nil
        },
        symval(q_varlist),
        symval(q_genvar),
      )
      |> ignore
      setup_multivar_disrep(r) |> ignore
      // This used to return 0 if psdisrep returned () but this is wrong
      // since taylor(false,x,0,0) would lose.
      if eq(symval(q_d_psexpand), q_d_multi) {
        psdisexpand(cdr(r))
      } else {
        psdisrep(cdr(r))
      }
    },
  )
}

///|
fn psdisrep(p : Value) -> Value raise {
  if psp(p).truthy() {
    psdisrep_plus(
      psdisrep2(terms(p), getdisrep(gvar_o(p)), trunc_lvl(p)),
      if symval(q_d_psexpand).truthy() || trunc_lvl(p).truthy() {
        list2(q_mplus, q_trunc)
      } else {
        list2(q_mplus, q_exact)
      },
    )
  } else {
    rcdisrep(p)
  }
}

///|
fn psdisrep_hat(n : Value, var2 : Value) -> Value raise {
  // If var2 = () then it is an internal var generated in a multivariate
  // expansion so it shouldn't be displayed. If var2 = 1 then it probably
  // resulted from the substitution in srdisrep, so it depends on an
  // internal var and likewise shouldn't be displayed.
  if rczerop(n).truthy() || var2 is Nil || equal(var2, Fix(1L)) {
    Fix(1L)
  } else if equal(n, rcone()) {
    var2
  } else if mexptp(var2).truthy() && equal(caddr(var2), Fix(-1L)) {
    psdisrep_hat(e_(n), cadr(var2))
  } else {
    list3(list2(q_mexpt, q_ratsimp), var2, edisrep(n))
  }
}

///|
fn psdisrep_plus(p : Value, plush : Value) -> Value raise {
  if p is Nil {
    // An empty sum is mathematically zero. If exact, return clean 0. If
    // truncated, return 0 + ...
    if eq(cadr(plush), q_exact) {
      Fix(0L)
    } else {
      cons(plush, list1(Fix(0L)))
    }
  } else if cdr(p) is Nil && eq(cadr(plush), q_exact) {
    // Exact sum of one arg is just that arg.
    car(p)
  } else {
    // Since the DISPLAY package prints trunc'd sum's arguments from right
    // to left we must put the terms of any constant term in decreasing
    // order. Note that only a constant (wrt to the mainvar) term can be a
    // term which is a sum.
    let lowest_degree_term = car(last(p))
    if mplusp(lowest_degree_term).truthy() {
      rplacd(lowest_degree_term, nreverse(cdr(lowest_degree_term))) |> ignore
    }
    cons(plush, p)
  }
}

///|
fn psdisrep_star(a : Value, b : Value) -> Value raise {
  if equal(a, Fix(1L)) {
    b
  } else if equal(b, Fix(1L)) {
    a
  } else {
    cons(list2(q_mtimes, q_ratsimp), nconc(striptimes(a), striptimes(b)))
  }
}

///|
fn psdisrep2(p : Value, var2 : Value, trunc : Value) -> Value raise {
  if symval(q_d_ratexpand).truthy() || symval(q_d_psexpand).truthy() {
    psdisrep2expand(p, var2)
  } else {
    let mut a : Value = Nil
    let mut p = p
    while !(p is Nil || e_gt(le(p), trunc).truthy()) {
      a = cons(psdisrep_star(psdisrep(lc(p)), psdisrep_hat(le(p), var2)), a)
      p = cdr(p)
    }
    a
  }
}

///|
fn psdisrep2expand(p : Value, var2 : Value) -> Value raise {
  let mut p = p
  let mut l : Value = Nil
  while !(p is Nil) {
    l = nconc(psdisrep_starexpand(psdisrep(lc(p)), psdisrep_hat(le(p), var2)), l)
    p = cdr(p)
  }
  l
}

///|
fn psdisrep_starexpand(a : Value, b : Value) -> Value raise {
  if equal(a, Fix(1L)) {
    list1(b)
  } else if equal(b, Fix(1L)) {
    list1(a)
  } else if !mplusp(a).truthy() {
    list1(cons(list2(q_mtimes, q_ratimes), nconc(striptimes(a), striptimes(b))))
  } else {
    mapcar(z => psdisrep_star(z, b), cdr(a))
  }
}

///|
fn psdisexpand(p : Value) -> Value raise {
  // ANS is special: used in psans-add
  with_special(q_ans, list1(Nil), () => {
    psdisexcnt(p, Nil, rczero()) |> ignore
    let ans = nreverse(
      mapcar(
        x => if cddr(x) is Nil {
          cadr(x)
        } else {
          cons(list2(q_mplus, q_trunc), cdr(x))
        },
        cdr(symval(q_ans)),
      ),
    )
    set(q_ans, ans) |> ignore
    if cdr(ans) is Nil {
      car(ans)
    } else {
      cons(list2(q_mplus, q_trunc), ans)
    }
  })
}

///|
fn psdisexcnt(p : Value, l : Value, n : Value) -> Value raise {
  if psp(p).truthy() {
    let var2 = getdisrep(gvar_o(p))
    let mut ll = terms(p)
    while !(ll is Nil) {
      if rczerop(le(ll)).truthy() {
        psdisexcnt(lc(ll), l, n) |> ignore
      } else {
        psdisexcnt(lc(ll), cons(psdisrep_hat(le(ll), var2), l), e_plus(le(ll), n))
        |> ignore
      }
      ll = n__term(ll)
    }
    Nil
  } else {
    psans_add(
      if l is Nil {
        rcdisrep(p)
      } else {
        psdisrep_star(
          rcdisrep(p),
          if cdr(l) is Nil {
            car(l)
          } else {
            cons(list2(q_mtimes, q_trunc), l)
          },
        )
      },
      n,
    )
  }
}

///|
fn psans_add(exp_ : Value, n : Value) -> Value raise {
  // ANS is bound in psdisexpand
  let mut l = symval(q_ans)
  while true {
    let done = if cdr(l) is Nil {
      rplacd(l, list1(list2(n, exp_)))
    } else if e_eq(caadr(l), n).truthy() {
      rplacd(cadr(l), cons(exp_, cdadr(l)))
    } else if e_gt(caadr(l), n).truthy() {
      rplacd(l, cons(list2(n, exp_), cdr(l)))
    } else {
      Nil
    }
    if done.truthy() {
      break
    }
    l = cdr(l)
  }
  Nil
}

///|
fn srconvert(r : Value) -> Value raise {
  if !atom(caadr(hayat__cdddar(r))) {
    cons(car(r), psdisextend(cdr(r)))
  } else {
    let vs = caddar(r)
    let gens = cadddr(car(r))
    with_specials([(q_trunclist, cadr(hayat__cdddar(r))), (q_tlist, Nil)], () => {
      let gps = mapcar2((a, b) => cons(a, b), gens, vs)
      let trunclist = symval(q_trunclist)
      let mut tl = cdr(trunclist)
      while !(tl is Nil) {
        let temp = cdr(assq(car(tl), gps))
        if memq(car(tl), cdr(trunclist)) is Nil {
          ()
        } else if mplusp(temp).truthy() {
          merr("SRCONVERT: internal error.", []) |> ignore
        } else {
          set(
            q_tlist,
            cons(
              list_star([
                temp,
                tay_order(cadr(tl)),
                Fix(0L),
                Nil,
                cons(car(tl), symval(car(tl))),
              ]),
              symval(q_tlist),
            ),
          )
          |> ignore
        }
        tl = cddr(tl)
      }
      cons(
        list([q_mrat, q_simp, vs, gens, symval(q_tlist), q_trunc]),
        srconvert1(cdr(r)),
      )
    })
  }
}

///|
fn srconvert1(p : Value) -> Value raise {
  if memq(car(p), symval(q_genvar)) is Nil {
    p
  } else {
    let mut l = cdr(p)
    let mut a : Value = Nil
    while !(l is Nil) {
      a = cons(term(prep1(car(l)), srconvert1(cadr(l))), a)
      l = cddr(l)
    }
    make_ps(
      cons(car(p), symval(car(p))),
      tay_order(zl_get(symval(q_trunclist), car(p))),
      terms=a,
    )
  }
}

// Subtitle error handling

///|
fn tay_error(msg : Value, exp_ : Value) -> Value raise {
  if symval(q_silent_taylor_flag).truthy() {
    throw_tag(q_taylor_catch, Nil)
  } else if exp_.truthy() {
    merr("taylor: ~A~%~M", [msg, exp_])
  } else {
    merr("taylor: ~A", [msg])
  }
}

///|
fn exp_pt_err() -> Value raise {
  tay_err(Str("unable to expand at a point specified in:"))
}

///|
fn essen_sing_err() -> Value raise {
  tay_err(Str("encountered an essential singularity in:"))
}

///|
fn unfam_sing_err() -> Value raise {
  tay_err(Str("encountered an unfamiliar singularity in:"))
}

///|
fn infin_ord_err() -> Value raise {
  tay_err(Str("expansion to infinite order?"))
}

///|
fn tay_depth_err() -> Value raise {
  tay_err(Str("'taylordepth' exceeded while expanding:"))
}

// Subtitle TAYLORINFO

///|
fn taylor_trunc(q : Value) -> Value raise {
  let q = current_trunc(q)
  if q is Nil {
    q_d_inf
  } else if equal(cdr(q), Fix(1L)) {
    car(q)
  } else {
    list3(list1(q_rat), car(q), cdr(q))
  }
}

///|
fn hayat__fourth_head_is(qk : Value, s : Value) -> Bool {
  let f = fourth(qk)
  f.truthy() && consp(f) && eq(caar(f), s)
}

///|
fn taylor_info(q : Value) -> Value raise {
  let mut q = q
  let mut acc_var : Value = Nil
  let mut acc_pt : Value = Nil
  let mut acc_ord : Value = Nil
  if q is Nil {
    return Nil
  }
  let mut qk = car(q)
  q = cdr(q)
  if hayat__fourth_head_is(qk, q_multivar) {
    Nil
  } else if hayat__fourth_head_is(qk, q_multi) {
    while hayat__fourth_head_is(qk, q_multi) {
      acc_ord = cons(taylor_trunc(qk), acc_ord)
      acc_pt = cons(exp_pt(qk), acc_pt)
      acc_var = cons(datum_var(qk), acc_var)
      qk = car(q)
      q = cdr(q)
    }
    acc_ord = cons(list1(q_mlist), acc_ord)
    acc_pt = cons(list1(q_mlist), acc_pt)
    acc_var = cons(list1(q_mlist), acc_var)
    q = taylor_info(q)
    if q is Nil {
      list3(acc_var, acc_pt, acc_ord)
    } else {
      append(q, list3(acc_var, acc_pt, acc_ord))
    }
  } else {
    let mut acc = if hayat__fourth_head_is(qk, q_d_asymp) {
      list1(q_d_asymp)
    } else {
      Nil
    }
    acc = cons(taylor_trunc(qk), acc)
    acc = cons(exp_pt(qk), acc)
    acc = cons(datum_var(qk), acc)
    acc = cons(list1(q_mlist), acc)
    q = taylor_info(q)
    if q is Nil {
      list1(acc)
    } else {
      append(q, list1(acc))
    }
  }
}

///|
fn d_taylorinfo(x : Value) -> Value raise {
  if consp(x) && memq(q_trunc, first(x)).truthy() {
    cons(list1(q_mlist), taylor_info(mrat_tlist(x)))
  } else {
    Nil
  }
}

///|
fn init_hayat() -> Unit raise {
  defvar_init(q_tlist, Nil)
  defvar_init(q_d_psexpand, Nil)
  defvar_init(q_tvar_limits, Nil)
  hayat__init_exp_forms()
  set(
    q_n_starpscirc,
    list([
      q_p_cot, q_p_tan, q_p_csc, q_p_sin, q_p_sec, q_p_cos, q_p_coth, q_p_tanh,
      q_p_csch, q_p_sinh, q_p_sech, q_p_cosh,
    ]),
  )
  |> ignore
  set(
    q_n_starpsacirc,
    list([
      q_p_acot, q_p_atan, q_p_acsc, q_p_asin, q_p_asec, q_p_acos, q_p_acoth,
      q_p_atanh, q_p_acsch, q_p_asinh, q_p_asech, q_p_acosh,
    ]),
  )
  |> ignore
  set(
    q_const_exp_funs,
    list_star([
      cons(q_p_gamma, q_gam_const),
      cons(q_d_psi, q_plygam_const),
      mapcar(q => cons(q, q_trig_const), symval(q_n_starpscirc)),
    ]),
  )
  |> ignore
  set(
    q_trigdisp,
    list([
      cons(q_p_sin, q_psina_plusb),
      cons(q_p_cos, q_pscosa_plusb),
      cons(q_p_tan, q_pstana_plusb),
      cons(q_p_sinh, q_psinha_plusb),
      cons(q_p_cosh, q_pscosha_plusb),
      cons(q_p_tanh, q_pstanha_plusb),
    ]),
  )
  |> ignore
  set(
    q_tay_pole_expand,
    list([cons(q_p_gamma, q_plygam_pole), cons(q_d_psi, q_plygam_pole)]),
  )
  |> ignore
  // These should be handled by symbolic-expand; be sure to change this
  // with tay-exponentialize!
  set(
    q_tay_const_expand,
    append(
      mapcar(q => cons(q, q_tay_exponentialize), symval(q_n_starpscirc)),
      mapcar(q => cons(q, q_tay_exponentialize), symval(q_n_starpsacirc)),
    ),
  )
  |> ignore
  for f in [
    q_p_acos, q_p_acot, q_p_asec, q_p_acsc, q_p_acosh, q_p_acoth, q_p_asech,
    q_p_acsch,
  ] {
    putprop(f, q_atrig_trans, q_tay_trans) |> ignore
  }
  putprop(q_p_atan2, q_atan2_trans, q_tay_trans) |> ignore
  putprop(q_mfactorial, q_factorial_trans, q_tay_trans) |> ignore
  putprop(q_p_signum, q_signum_trans, q_tay_trans) |> ignore
  putprop(q_p_gamma_incomplete, q_gamma_upper_trans, q_tay_trans) |> ignore
  putprop(q_d_gamma_incomplete, q_gamma_upper_trans, q_tay_trans) |> ignore
  putprop(q_p_gamma_incomplete_lower, q_gamma_lower_trans, q_tay_trans)
  |> ignore
  putprop(q_d_gamma_incomplete_lower, q_gamma_lower_trans, q_tay_trans)
  |> ignore
}

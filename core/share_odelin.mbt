// Port of share/contrib/diffequations/odelin.lisp (Barton Willis, 2004,
// 2009): Maxima code for linear homogeneous second order differential
// equations.
//
// odelin.lisp loads sqfr, spherodialwave, kummer, extrabessel, lazysolver,
// gauss, functs and odeutils. Of these, spherodialwave, kummer and
// extrabessel are plain property definitions and functs is a .mac file,
// so they are loaded as Maxima does. The Lisp files sqfr.lisp,
// odeutils.lisp, lazysolver.lisp and gauss.lisp define functions (or use
// backquote) that the port cannot load from source and that have no
// generated declarations; they are ported below as private helpers and
// installed in their symbols' function cells when odelin is loaded.

// ---------------------------------------------------------------------------
// odeutils.lisp

///|
let share_odelin__q_number_of_unks : Value = sym("number-of-unks")

///|
let share_odelin__q_mbag_map : Value = sym("mbag-map")

///|
fn share_odelin__mbag_map(
  f : (Value) -> Value raise,
  bag : Value,
) -> Value raise {
  simplify(cons(list1(mop(bag)), mapcar(f, margs(bag))))
}

///|
fn share_odelin__number_of_unks(p : Value, unks : Value) -> Value raise {
  with_special(q_d_listconstvars, Nil, () => d_cardinality(
    d_intersection(d_setify(d_listofvars(p)), list1(unks)),
  ))
}

///|
fn share_odelin__load_odeutils() -> Unit raise {
  d_put(sym("$odeutils"), Fix(1L), q_d_version) |> ignore
  defun(share_odelin__q_mbag_map, args => share_odelin__mbag_map(
    x => funcall(args[0], [x]),
    args[1],
  ))
  defun(share_odelin__q_number_of_unks, args => share_odelin__number_of_unks(
    args[0],
    args[1],
  ))
}

// ---------------------------------------------------------------------------
// sqfr.lisp

///|
let share_odelin__q_require_symbol : Value = sym("require-symbol")

///|
let share_odelin__q_strictmysqfr : Value = sym("$strictmysqfr")

///|
/// If x is a symbol or a subvarp, return its general representation.
/// Otherwise signal an error---the argument f is the string name of a
/// function that requires the symbol.
fn share_odelin__require_symbol(x : Value, f : Value) -> Value raise {
  let x = d_ratdisrep(x)
  if symbolp(x) || d_subvarp(x).truthy() {
    x
  } else {
    merr("Function ~:M requires a symbol; instead found ~:M", [f, x])
  }
}

///|
fn share_odelin__strictmysqfr(p : Value, x : Value) -> (Value, Value) raise {
  let mut p = d_expand(d_ratdisrep(p))
  let x = share_odelin__require_symbol(x, Str("$mysqfr"))
  with_specials(
    [
      (q_d_gcd, q_d_spmod),
      (q_d_algebraic, t),
      (q_d_resultant, q_d_red),
      (q_d_ratfac, Nil),
      (q_d_ratprint, Nil),
    ],
    () => {
      let lc = d_coeff(p, x, n=d_hipow(p, x))
      p = d_expand(div(p, lc))
      let mut acc : Value = Nil
      while !d_freeof(list2(x, p)).truthy() {
        let r = d_gcd(p, d_diff(list2(p, x)), list1(x))
        let q = d_first(d_divide(p, r, Nil))
        let mut ai = d_first(d_divide(q, d_gcd(q, r, list1(x)), list1(x)))
        ai = div(ai, d_coeff(ai, x, n=d_hipow(ai, x)))
        acc = cons(ai, acc)
        p = r
      }
      acc = reverse(acc)
      let mut r = lc
      let mut i = 0L
      let mut w : Value = Nil
      let mut bad : Value = Nil
      while acc.truthy() {
        let ai = car(acc)
        acc = cdr(acc)
        i += 1L
        r = mul2(r, power(ai, Fix(i)))
        let s = d_resultant(ai, d_diff(list2(ai, x)), x)
        if !d_constantp(s).truthy() {
          bad = cons(d_factor(s), bad)
        }
        for wi in w.iter() {
          let s = d_resultant(ai, wi, x)
          if !d_constantp(s).truthy() {
            bad = cons(d_factor(s), bad)
          }
        }
        w = cons(ai, w)
      }
      bad = cons(list1(q_d_set), bad)
      bad = share_odelin__mbag_map(
        w => list3(list1(q_mnotequal), w, Fix(0L)),
        bad,
      )
      if !d_emptyp(bad).truthy() {
        mtell(list2(Str("Proviso: assuming ~:M~%"), bad)) |> ignore
      }
      (r, bad)
    },
  )
}

///|
fn share_odelin__mysqfr(p : Value, x : Value) -> Value raise {
  let mut p = d_expand(d_ratdisrep(p))
  let x = share_odelin__require_symbol(x, Str("$mysqfr"))
  with_specials([(q_d_gcd, q_d_spmod), (q_d_algebraic, t)], () => {
    if like(Fix(0L), p).truthy() {
      Fix(0L)
    } else {
      p = d_expand(p)
      let mut acc = d_coeff(p, x, n=d_hipow(p, x))
      p = div(p, acc)
      let mut i = 0L
      while !d_freeof(list2(x, p)).truthy() {
        let r = d_gcd(p, d_diff(list2(p, x)), list1(x))
        let q = d_first(d_divide(p, r, list1(x)))
        let mut ai = d_first(d_divide(q, d_gcd(q, r, list1(x)), list1(x)))
        ai = div(ai, d_coeff(ai, x, n=d_hipow(ai, x)))
        i += 1L
        acc = mul2(acc, power(ai, Fix(i)))
        p = r
      }
      acc
    }
  })
}

///|
fn share_odelin__load_sqfr() -> Unit raise {
  d_put(q_d_sqfr, Fix(1L), q_d_version) |> ignore
  share_odelin__load_odeutils()
  defun(share_odelin__q_require_symbol, args => share_odelin__require_symbol(
    args[0],
    args[1],
  ))
  defun(share_odelin__q_strictmysqfr, args => {
    check_arity("$strictmysqfr", args, 2)
    share_odelin__strictmysqfr(args[0], args[1]).0
  })
  defun(q_d_mysqfr, args => {
    check_arity("$mysqfr", args, 2)
    share_odelin__mysqfr(args[0], args[1])
  })
}

// ---------------------------------------------------------------------------
// lazysolver.lisp

///|
let share_odelin__q_aalgsys_is_loquacious : Value = sym("$aalgsys_is_loquacious")

///|
let share_odelin__q_checksolution : Value = sym("$checksolution")

///|
fn share_odelin__variablep(e : Value) -> Bool raise {
  d_symbolp(e).truthy() || d_subvarp(e).truthy()
}

///|
fn share_odelin__checksolution(
  sol : Value,
  eqs : Value,
  nz : Value,
) -> Value raise {
  with_specials(
    [
      (q_d_gcd, q_d_spmod),
      (q_d_algebraic, t),
      (q_d_ratfac, Nil),
      (q_d_ratprint, Nil),
    ],
    () => {
      let sol = if !d_listp(sol).truthy() {
        list2(list1(q_mlist), sol)
      } else {
        sol
      }
      let mut eqs = if !d_listp(eqs).truthy() {
        list2(list1(q_mlist), eqs)
      } else {
        eqs
      }
      let nz = if !d_listp(nz).truthy() { list2(list1(q_mlist), nz) } else { nz }
      eqs = mapcar(e => meqhk(e), cdr(eqs))
      eqs = cons(list1(q_mlist), eqs)
      lbool(
        every(s => mequalp(s).truthy(), cdr(sol)) &&
        every(s => share_odelin__variablep(d_lhs(s)), cdr(sol)) &&
        every(s => like(Fix(0L), s).truthy(), cdr(sratsimp(d_substitute(sol, eqs)))) &&
        every(s => !like(Fix(0L), s).truthy(), cdr(sratsimp(d_substitute(sol, nz)))),
      )
    },
  )
}

///|
fn share_odelin__my_expr_size(e : Value) -> Int raise {
  share_odelin__xmy_expr_size(d_totaldisrep(e))
}

///|
fn share_odelin__xmy_expr_size(e : Value) -> Int raise {
  if consp(e) {
    let mut n = 0
    for x in margs(e).iter() {
      n += share_odelin__my_expr_size(x)
    }
    n
  } else {
    1
  }
}

///|
fn share_odelin__my_freeof(unks : Value, q : Value) -> Bool raise {
  every(x => d_freeof(list2(x, q)).truthy(), cdr(unks))
}

///|
fn share_odelin__checkedalgsys(
  eqs : Value,
  vars : Value,
  nz : Value,
) -> Value raise {
  with_specials(
    [
      (q_d_ratfac, Nil),
      (q_d_ratprint, Nil),
      (q_d_realonly, Nil),
      (q_d_algexact, t),
      (q_d_gcd, q_d_spmod),
      (q_d_algebraic, t),
      (q_d_programmode, t),
      (q_d_globalsolve, Nil),
      (q_d_solveexplicit, t),
      (q_d_listconstvars, t),
      (q_d_solveradcan, Nil),
      (q_d_ratvars, Nil),
    ],
    () => {
      if symval(share_odelin__q_aalgsys_is_loquacious).truthy() {
        mtell(
          list3(
            Str("...solving ~:M equations in ~:M variables~%"),
            d_length(eqs),
            d_length(vars),
          ),
        )
        |> ignore
      }
      let sol = list_to_array(cdr(d_algsys(eqs, vars)))
      // (stable-sort sol #'(lambda (a b) (< (my-expr-size a) (my-expr-size b))))
      let sized = sol.map(s => (share_odelin__my_expr_size(s), s))
      for i in 1..<sized.length() {
        let cur = sized[i]
        let mut j = i - 1
        while j >= 0 && sized[j].0 > cur.0 {
          sized[j + 1] = sized[j]
          j -= 1
        }
        sized[j + 1] = cur
      }
      for e in sized {
        if share_odelin__checksolution(e.1, eqs, nz).truthy() {
          return e.1
        }
      }
      Nil
    },
  )
}

///|
fn share_odelin__unks_in_eq(eq_ : Value, unks : Value) -> Value raise {
  with_special(q_d_listconstvars, Nil, () => d_intersection(
    d_setify(d_listofvars(eq_)),
    list1(unks),
  ))
}

///|
fn share_odelin__aalgsys(
  e_eqs : Value,
  eqs : Value,
  unks : Value,
  nz : Value,
) -> Value raise {
  with_specials(
    [
      (q_d_gcd, q_d_spmod),
      (q_d_algebraic, t),
      (q_d_ratvars, Nil),
      (q_d_radexpand, Nil),
      (q_d_ratfac, Nil),
      (q_d_ratprint, Nil),
    ],
    () => {
      let mut unks = d_setify(unks)
      unks = share_odelin__mbag_map(x => d_ratdisrep(x), unks)
      let mut eqs = d_setify(eqs)
      eqs = share_odelin__mbag_map(x => d_ratdisrep(x), eqs)
      let mut e_eqs = d_setify(e_eqs)
      e_eqs = share_odelin__mbag_map(x => d_ratdisrep(x), e_eqs)
      e_eqs = share_odelin__mbag_map(x => d_factor(x), e_eqs)
      let unks0 = unks
      e_eqs = d_union(
        list2(
          e_eqs,
          d_subset(
            eqs,
            lfunc("aalgsys-one-unk", a => lbool(
              num_eq(Fix(1L), share_odelin__number_of_unks(a[0], unks0)),
            )),
          ),
        ),
      )
      let mut e_vars = share_odelin__unks_in_eq(e_eqs, unks)
      let e_vars0 = e_vars
      e_eqs = d_union(
        list2(
          e_eqs,
          d_subset(
            eqs,
            lfunc("aalgsys-same-unks", a => like(
              share_odelin__unks_in_eq(a[0], unks0),
              e_vars0,
            )),
          ),
        ),
      )
      e_eqs = share_odelin__mbag_map(x => d_ratdisrep(x), e_eqs)
      e_eqs = share_odelin__mbag_map(x => d_factor(x), e_eqs)
      e_eqs = d_disjoin(Fix(0L), e_eqs)
      e_eqs = d_listify(e_eqs)
      e_vars = d_listify(e_vars)
      eqs = d_listify(eqs)
      unks = d_listify(unks)
      if !d_emptyp(e_vars).truthy() {
        let mut e_sol = d_algsys(e_eqs, e_vars)
        e_sol = d_setify(e_sol)
        let e_eqs0 = e_eqs
        e_sol = d_subset(
          e_sol,
          lfunc("aalgsys-checksolution", a => share_odelin__checksolution(
            a[0], e_eqs0, nz,
          )),
        )
        e_sol = d_subset(
          e_sol,
          lfunc("aalgsys-rnum-freeof", a => lbool(
            share_odelin__my_freeof(symval(q_d__pctrnum_list), a[0]),
          )),
        )
        e_sol = d_listify(e_sol)
        if !d_emptyp(e_sol).truthy() {
          for ei in margs(e_sol).iter() {
            let sol = share_odelin__checkedalgsys(
              d_append(list2(ei, d_substitute(ei, eqs))),
              unks,
              nz,
            )
            if d_listp(sol).truthy() {
              return sol
            }
          }
          Nil
        } else {
          share_odelin__checkedalgsys(d_append(list2(e_eqs, eqs)), unks, nz)
        }
      } else {
        share_odelin__checkedalgsys(eqs, unks, nz)
      }
    },
  )
}

///|
fn share_odelin__nonconstant_factors(e : Value, vars : Value) -> Value raise {
  let mut acc : Value = Nil
  let e = d_factor(e)
  let es = if mtimesp(e).truthy() { margs(e) } else { list1(e) }
  for ei in es.iter() {
    let ei = if mexptp(ei).truthy() { car(margs(ei)) } else { ei }
    if !share_odelin__my_freeof(vars, ei) {
      acc = cons(ei, acc)
    }
  }
  cons(list1(q_d_set), acc)
}

///|
fn share_odelin__load_lazysolver() -> Unit raise {
  d_put(sym("$lazysolver"), Fix(1L), q_d_version) |> ignore
  share_odelin__load_odeutils()
  if !boundp(share_odelin__q_aalgsys_is_loquacious) {
    set(share_odelin__q_aalgsys_is_loquacious, Nil) |> ignore
  }
  defun(sym("variablep"), args => lbool(share_odelin__variablep(args[0])))
  defun(share_odelin__q_checksolution, args => {
    check_arity_range("$checksolution", args, 2, 3)
    share_odelin__checksolution(
      args[0],
      args[1],
      args.get(2).unwrap_or(list1(list1(q_mlist))),
    )
  })
  defun(sym("my-expr-size"), args => int(share_odelin__my_expr_size(args[0])))
  defun(sym("xmy-expr-size"), args => int(share_odelin__xmy_expr_size(args[0])))
  defun(sym("my-freeof"), args => lbool(
    share_odelin__my_freeof(args[0], args[1]),
  ))
  defun(q_d_checkedalgsys, args => {
    check_arity_range("$checkedalgsys", args, 2, 3)
    share_odelin__checkedalgsys(
      args[0],
      args[1],
      args.get(2).unwrap_or(list1(list1(q_mlist))),
    )
  })
  defun(sym("nonconstant-factors"), args => share_odelin__nonconstant_factors(
    args[0],
    args[1],
  ))
  defun(sym("unks-in-eq"), args => share_odelin__unks_in_eq(args[0], args[1]))
  defun(q_d_aalgsys, args => {
    check_arity_range("$aalgsys", args, 3, 4)
    share_odelin__aalgsys(
      args[0],
      args[1],
      args[2],
      args.get(3).unwrap_or(list1(list1(q_mlist))),
    )
  })
}

// ---------------------------------------------------------------------------
// gauss.lisp: derivatives of the hypergeometric functions gauss_a, gauss_b.

///|
fn share_odelin__load_gauss() -> Unit raise {
  d_put(sym("$gauss"), Fix(1L), q_d_version) |> ignore
  let unks = "((unk) \"$first\" \"~A\") ((unk) \"$second\" \"~A\") ((unk) \"$third\" \"~A\")"
  for f in ["gauss_a", "gauss_b"] {
    let u = unks.replace_all(old="~A", new="$" + f)
    let du = unks.replace_all(old="~A", new="$d" + f)
    putprop(
      sym("$" + f),
      lread("((a b c x) " + u + " (($d" + f + ") a b c x))"),
      q_grad,
    )
    |> ignore
    putprop(
      sym("$d" + f),
      lread(
        "((a b c x) " +
        du +
        " ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) -1 x)) -1) ((mexpt) x -1) ((mplus) ((mtimes) a (($" +
        f +
        ") a b c x) b) ((mtimes) (($d" +
        f +
        ") a b c x) ((mplus) ((mtimes) -1 c) ((mtimes) ((mplus) 1 a b) x))))))",
      ),
      q_grad,
    )
    |> ignore
  }
}

// ---------------------------------------------------------------------------
// odelin.lisp

///|
fn ode_polynomialp(p : Value, x : Value) -> Value raise {
  d_polynomialp(
    p,
    list2(list1(q_mlist), x),
    coeffp=list3(
      list1(q_lambda),
      list2(list1(q_mlist), q_d_s),
      list3(q_d_freeof, x, q_d_s),
    ),
  )
}

///|
fn require_linear_homogeneous_de(de : Value, y : Value, x : Value) -> Value raise {
  let y = share_odelin__require_symbol(y, Str("$odelin"))
  let x = share_odelin__require_symbol(x, Str("$odelin"))
  let mut de = de
  if d_listp(de).truthy() || d_setp(de).truthy() {
    if num_eq(Fix(1L), d_cardinality(de)) {
      de = nth(1, de)
    } else {
      merr("'odelin' doesn't handle systems of DEs.~%", []) |> ignore
    }
  }
  de = d_ratdisrep(de)
  de = meqhk(de)
  let mut acc : Value = Nil
  let mut f = de
  let mut n = d_derivdegree(de, y, x)
  if !(integerp(n) && num_gt(n, Fix(0L))) {
    merr("'odelin' doesn't handle order ~:M DEs.~%", [n]) |> ignore
  }
  de = d_rat(de, Nil)
  while num_gt(n, Fix(-1L)) {
    let cf = if num_eq(n, Fix(0L)) {
      d_ratcoef(de, y, n=Fix(1L))
    } else {
      d_ratcoef(de, list4(list1(q_p_derivative), y, x, n))
    }
    if d_freeof(list2(y, cf)).truthy() {
      acc = cons(cf, acc)
    } else {
      merr("DE must be linear", []) |> ignore
    }
    f = sub(f, mul2(cf, list4(list1(q_p_derivative), y, x, n)))
    n = num_sub(n, Fix(1L))
  }
  f = sratsimp(f)
  if !like(Fix(0L), f).truthy() {
    merr("DE must be linear and homogeneous.~%", []) |> ignore
  }
  acc
}

///|
fn d_odelin(de : Value, y : Value, x : Value) -> Value raise {
  let cfs = require_linear_homogeneous_de(de, y, x)
  let n = length(cfs)
  if n == 2 {
    odelin_order_one(cfs, x)
  } else if n == 3 {
    odelin_order_two(cfs, x)
  } else {
    merr("'odelin' doesn't handle DEs with order ~:M", [int(n - 1)])
  }
}

///|
fn odelin_order_one(cfs : Value, x : Value) -> Value raise {
  fss_cleanup(
    take(list1(q_d_set), [
      d_exp(d_integrate(mul2(Fix(-1L), div(car(cfs), cadr(cfs))), x)),
    ]),
    x,
  )
}

///|
fn expunge_const_factors(e : Value, x : Value) -> Value raise {
  let mut acc : Value = Fix(1L)
  if like(Fix(0L), e).truthy() {
    Fix(0L)
  } else {
    let e = d_factor(e)
    let es = if mtimesp(e).truthy() { margs(e) } else { list1(e) }
    for ei in es.iter() {
      if !d_freeof(list2(x, ei)).truthy() {
        acc = mul2(ei, acc)
      }
    }
    acc
  }
}

///|
/// Cleanup a fundamental solution set (FSS).
fn fss_cleanup(fss : Value, x : Value) -> Value raise {
  let nfss = share_odelin__mbag_map(
    s => expunge_const_factors(d_radcan(s), x),
    fss,
  )
  if like(nfss, fss).truthy() {
    fss
  } else {
    fss_cleanup(nfss, x)
  }
}

///|
fn post_check_cleanup(fss : Value) -> Value raise {
  let fss = d_substitute(q_p_bessel_j, q_d_fbessel_j, expr=fss)
  d_substitute(q_p_bessel_y, q_d_fbessel_y, expr=fss)
}

///|
fn odelin_order_two(cfs : Value, x : Value) -> Value raise {
  let mut p0 = nth(0, cfs)
  let mut p1 = nth(1, cfs)
  let p2 = nth(2, cfs)
  let mut sol : Value = Nil
  let mut ode_methods : Array[(Value, Value) -> Value raise] = [
    ode_solve_by_factoring, bessel_de_solver, hypergeo01_de_solver, spherodialwave_de_solver,
    bessel_sqrt_de_solver, hypergeo21_de_solver,
  ]
  p1 = div(p1, p2)
  p0 = div(p0, p2)
  if !(
      ode_polynomialp(d_ratnumer(p1), x).truthy() &&
      ode_polynomialp(d_ratdenom(p1), x).truthy() &&
      ode_polynomialp(d_ratnumer(p0), x).truthy() &&
      ode_polynomialp(d_ratdenom(p0), x).truthy()
    ) {
    ode_methods = []
  }
  let p = addn_([
    p0,
    div(d_diff(list2(p1, x)), Fix(-2L)),
    muln_([p1, p1, div(Fix(-1L), Fix(4L))]),
  ])
  let m = d_exp(d_integrate(div(p1, Fix(-2L)), x))
  let mut k = 0
  while !sol.truthy() && k < ode_methods.length() {
    sol = ode_methods[k](p, x)
    k += 1
    if d_setp(sol).truthy() {
      sol = fss_cleanup(share_odelin__mbag_map(s => mul2(m, s), sol), x)
      sol = if check_fss(cfs, sol, x).truthy() {
        post_check_cleanup(sol)
      } else {
        Nil
      }
    }
  }
  sol
}

///|
fn share_odelin__simp_unk(x : Value, y : Value, z : Value) -> Value raise {
  ignore((y, z))
  merr("Maxima doesn't know the derivative of ~:M with respect the ~:M argument", [
    nth(2, x),
    nth(1, x),
  ])
}

///|
fn check_de_sol(cfs : Value, sol : Value, x : Value) -> Value raise {
  let mut zip : Value = Fix(0L)
  let mut sol = sol
  for cf in cfs.iter() {
    zip = add(list2(zip, mul2(cf, sol)))
    sol = d_diff(list2(sol, x))
  }
  zip = sratsimp(zip)
  if like(Fix(0L), zip).truthy() ||
    like(Fix(0L), d_radcan(zip)).truthy() ||
    like(Fix(0L), d_radcan(d_expand(zip))).truthy() ||
    like(Fix(0L), mfuncall(q_d_expintegral_e_simplify, list1(zip))).truthy() {
    t
  } else {
    mtell(list2(Str("should vanish, but it does not ~:M~%"), zip))
  }
}

///|
fn check_fss(cfs : Value, fss : Value, x : Value) -> Value raise {
  lbool(
    d_setp(fss).truthy() &&
    length(cfs) == length(fss) &&
    every(s => check_de_sol(cfs, s, x).truthy(), cdr(fss)) &&
    !like(
      Fix(0L),
      d_radcan(d_determinant(mfuncall(q_d_wronskian, list2(d_listify(fss), x)))),
    ).truthy(),
  )
}

///|
/// Return a polynomial in x with degree deg and a list of its coefficients.
/// Each coefficient of the polynomial is a gensym.
fn make_unk_poly(x : Value, deg : Value) -> (Value, Value) raise {
  let x = d_ratdisrep(x)
  let mut p : Value = Fix(0L)
  let mut z : Value = Fix(1L)
  let mut cfs : Value = Nil
  let deg = to_int(deg) + 1
  for _ in 0..<deg {
    let cf = gensym()
    cfs = cons(cf, cfs)
    p = add(list2(p, mul2(cf, z)))
    z = mul2(z, x)
  }
  (p, reverse(cfs))
}

///|
fn polycfs_to_eqs(p : Value, x : Value) -> Value raise {
  with_specials([(q_d_ratfac, Nil), (q_d_ratprint, Nil)], () => {
    let p = d_rat(p, list1(x))
    let n = 1 + to_int(d_hipow(p, x))
    let mut eqs : Value = Nil
    for i in 0..<n {
      eqs = cons(d_ratcoef(p, x, n=int(i)), eqs)
    }
    eqs
  })
}

///|
/// Solve y'' - r y by factoring the differential operator (D^2 - r) as
/// (D+a)(D-a), where r and a are rational functions: a' + a^2 = r.
/// Solutions to (D+a)(D-a) f = 0 are f = mu, where mu = exp
/// (integrate(a,x)) and f = mu * integrate(1/mu^2,x).
fn ode_solve_by_factoring(r : Value, x : Value) -> Value raise {
  with_special(q_d_radexpand, Nil, () => {
    let a = factor_differential_op(r, x)
    if a.truthy() {
      let a = d_radcan(a)
      let mu = d_radcan(d_exp(d_integrate(a, x)))
      list3(
        list1(q_d_set),
        mu,
        mul2(mu, d_integrate(div(Fix(1L), mul2(mu, mu)), x)),
      )
    } else {
      Nil
    }
  })
}

///|
/// Let r = p/q be rational. We either find a rational function a such that
/// a' + a^2 = p/q = p q / q^2, or we return nil. We do this by setting
/// a = w / q. Then q w' - q' w + w^2 = pq.
fn factor_differential_op(r : Value, x : Value) -> Value raise {
  let r = d_rat(r, list1(x))
  let p = d_ratnumer(r)
  let q = d_ratdenom(r)
  let m = d_hipow(q, x)
  let l = d_hipow(p, x)
  with_special(q_d_ratfac, Nil, () => {
    let m = to_int(d_totaldisrep(m))
    let l = to_int(d_totaldisrep(l))
    let n = if 2 + l < m {
      (m - 1).max(l + 1)
    } else if (m + l) % 2 == 0 {
      (m + l) / 2
    } else {
      -1
    }
    if n > -1 {
      let (w0, vars) = make_unk_poly(x, int(n))
      let mut w = w0
      let vars = cons(list1(q_mlist), reverse(vars))
      let mut zip = addn_([
        mul2(q, d_diff(list2(w, x))),
        muln_([Fix(-1L), w, d_diff(list2(q, x))]),
        mul2(w, w),
        mul2(p, q),
      ])
      zip = d_rat(zip, list1(x))
      zip = polycfs_to_eqs(zip, x)
      zip = cons(list1(q_mlist), zip)
      let sol = share_odelin__checkedalgsys(zip, vars, list1(list1(q_mlist)))
      if !sol.truthy() {
        Nil
      } else {
        w = div(w, q)
        d_substitute(sol, w)
      }
    } else {
      Nil
    }
  })
}

///|
fn polynomial_filter(p : Value, x : Value, f : Value) -> Value raise {
  with_specials([(q_d_ratfac, Nil), (q_d_ratprint, Nil)], () => {
    // Get rid of terms like sqr(5)^2, %i^2...
    let p = sratsimp(p)
    let p = share_odelin__mysqfr(p, x)
    let ps = if mtimesp(p).truthy() { margs(p) } else { list1(p) }
    let mut q : Value = Fix(1L)
    for pj in ps.iter() {
      let mut pj = pj
      let mut n : Value = Fix(0L)
      if mexptp(pj).truthy() {
        n = nth(2, pj)
        pj = nth(1, pj)
      } else if d_freeof(list2(x, pj)).truthy() {
        n = Fix(0L)
      } else {
        n = Fix(1L)
      }
      n = funcall(f, [n])
      q = mult(q, power(pj, n))
    }
    q
  })
}

///|
fn ratfun_degree(q : Value, x : Value) -> Value raise {
  with_special(q_d_ratfac, Nil, () => {
    let q = d_rat(q, list1(x))
    num_sub(d_hipow(d_ratnumer(q), x), d_hipow(d_ratdenom(q), x))
  })
}

///|
/// (lambda (n) (min 1 n))
fn share_odelin__min1() -> Value {
  lfunc("odelin-min1", a => if num_lt(a[0], Fix(1L)) { a[0] } else { Fix(1L) })
}

///|
fn xeasy_eqs(p : Value, s : Value, x : Value) -> Value raise {
  let mut acc = list1(list1(q_d_set))
  let s = polynomial_filter(s, x, share_odelin__min1())
  let s = cdr(d_solve(s, varl=x))
  for si in s.iter() {
    acc = d_adjoin(d_substitute(si, p), acc)
  }
  require_set(acc, Str("easy-eqs"))
}

///|
/// Find conditions that make the polynomial 'cnd' vanish at each zero of
/// the polynomial 's.' When the zero of 's' isn't messy, we simply evaluate
/// 'cnd' at the zero. When the zero of 's' is messy, we use a different
/// method.
fn easy_eqs(cnd : Value, s : Value, x : Value) -> Value raise {
  with_specials(
    [
      (q_d_programmode, t),
      (q_d_globalsolve, Nil),
      (q_d_solveexplicit, t),
      (q_d_solveradcan, Nil),
    ],
    () => {
      let mut acc : Value = Nil
      let s = polynomial_filter(s, x, share_odelin__min1())
      let s = d_factor(s)
      let ss = if mtimesp(s).truthy() { margs(s) } else { list1(s) }
      for si in ss.iter() {
        let si = d_expand(si)
        let n = d_hipow(si, x)
        // Check for a non-messy zero.
        if num_lt(n, Fix(3L)) {
          let sis = margs(d_solve(si, varl=x))
          for sij in sis.iter() {
            acc = cons(d_substitute(sij, cnd), acc)
          }
        } else {
          acc = append(
            acc,
            polycfs_to_eqs(
              funcall(q_d_second, [d_divide(cnd, si, list1(x))]),
              x,
            ),
          )
        }
      }
      acc
    },
  )
}

///|
/// Expunge multiple zeros.
fn clean_equation(p : Value) -> Value raise {
  let mut acc : Value = Fix(1L)
  let p = d_sqfr(p)
  let ps = if mtimesp(p).truthy() {
    margs(p)
  } else if mexptp(p).truthy() {
    list1(car(margs(p)))
  } else {
    list1(p)
  }
  for pj in ps.iter() {
    acc = mul2(acc, if mexptp(pj).truthy() { car(margs(pj)) } else { pj })
  }
  acc
}

///|
/// generic-de-solver uses a method described by Bronstein and Lafaille to
/// compute special function solutions of non-Liouvillian 2nd order linear
/// homogeneous ODES (M Bronstein, S Lafaille, Solutions of linear ordinary
/// differential equations in terms of special functions, ISSAC 2002).
///
/// Given an ode y'' = v y and a target 2nd order linear ODE L y = 0, with
/// L = D^2 + a1 D + a0 and {F1,F2} a known fundamental solution set, we
/// seek m(x) and xi(x) st { m(x) F1(xi(x)), m(x) F2{xi(x)) } is a
/// fundamental solution set of y'' = v y. xi(x) = P(x)/Q(x) satisfies a
/// non-linear third-order ODE (get-de-cnd); Q(x) is given by certain terms
/// in the square-free factorization of the denominator of v(x)
/// (denom-filter) and an upper bound to the degree of P(x) is known
/// (degree-bound), so P(x) is found by undetermined coefficients. params
/// are the additional parameters in the operator; de-cnd is -Delta/4,
/// Delta = (a1)^2 + 2 a1' - 4 a0.
fn generic_de_solver(
  v : Value,
  x : Value,
  params : Value,
  denom_filter : Value,
  degree_bound : Value,
  de_cnd : Value,
) -> Value raise {
  let v = d_rat(v, list1(x))
  with_special(q_d_ratfac, Nil, () => {
    let s = d_ratdenom(v)
    let q = polynomial_filter(s, x, denom_filter)
    let n = funcall(degree_bound, [q, v, x])
    let (p0, unks) = make_unk_poly(x, n)
    let mut p = p0
    let nz = list3(
      list1(q_mlist),
      p,
      sub(mul2(p, d_diff(list2(q, x))), mul2(q, d_diff(list2(p, x)))),
    )
    let mut unks = append(params, unks)
    unks = cons(list1(q_mlist), unks)
    let cnd = get_de_cnd(div(p, q), v, de_cnd, x)
    let mut xeqs = easy_eqs(cnd, s, x)
    let mut eqs = polycfs_to_eqs(cnd, x)
    unks = d_listify(unks)
    eqs = mapcar(e => clean_equation(e), eqs)
    xeqs = mapcar(e => clean_equation(e), xeqs)
    eqs = cons(list1(q_mlist), eqs)
    xeqs = cons(list1(q_mlist), xeqs)
    let sol = share_odelin__aalgsys(xeqs, eqs, unks, nz)
    if d_listp(sol).truthy() {
      p = d_substitute(sol, p)
      let params = mapcar(s => d_substitute(sol, s), params)
      list2(div(p, q), params)
    } else {
      Nil
    }
  })
}

///|
/// Returns the differential equation satisfied by xi(x) [Eq 7 in paper]
///   3*xi''^2 - 2*xi'*xi''' + (a1(xi)^2 + 2*a1'(xi) - 4*a0(xi))*xi'^4
///     - 4*v*xi'^2 = 0,
/// times -1. vh is v(x) in the DE to be solved (D^2-v)y=0; v is
/// -(a1(x)^2 + 2*a1'(x) - 4*a0(x))/4.
fn get_de_cnd(xi : Value, vh : Value, v : Value, x : Value) -> Value raise {
  with_specials([(q_d_ratfac, Nil), (q_d_ratprint, Nil)], () => {
    let xi = d_ratdisrep(xi)
    let dxi = d_diff(list2(xi, x))
    let dxi_2 = mul2(dxi, dxi)
    let ddxi = d_diff(list2(dxi, x))
    let dddxi = d_diff(list2(ddxi, x))
    // 4*dxi^4*v(xi)-4*dxi^2*vh(x)+2*dddxi*dxi-3*ddxi^2
    d_ratdisrep(
      d_ratnumer(
        addn_([
          muln_([Fix(4L), d_substitute(xi, x, expr=v), dxi_2, dxi_2]),
          muln_([Fix(-4L), vh, dxi_2]),
          muln_([Fix(2L), dxi, dddxi]),
          muln_([Fix(-3L), ddxi, ddxi]),
        ]),
      ),
    )
  })
}

///|
/// (if (and (evenp n) (> n 3)) (/ (- n 2) 2) 0)
fn share_odelin__even_filter(n : Value) -> Value raise {
  if evenp(n) && num_gt(n, Fix(3L)) {
    num_div(num_sub(n, Fix(2L)), Fix(2L))
  } else {
    Fix(0L)
  }
}

///|
/// (ceiling (+ 1 ($hipow q x) (/ (max (ratfun-degree v x) -2) 2)))
fn share_odelin__half_degree_bound(q : Value, v : Value, x : Value) -> Value raise {
  let rd = ratfun_degree(v, x)
  let mx : Value = if num_gt(rd, Fix(-2L)) { rd } else { Fix(-2L) }
  ceiling1(num_add(num_add(Fix(1L), d_hipow(q, x)), num_div(mx, Fix(2L))))
}

///|
/// The differential operator with the FSS {bessel_j(mu,x),bessel_y(mu,x)}
/// is L = D^2 + a1*D + a0, with a1 = 1/x and a0 = (1-mu^2/x^2); Delta =
/// (4*mu^2-1)/x^2-4 (order at infinity is 0); de-cnd = -Delta/4 =
/// (4*x^2+1-4*mu^2)/(4*x^2). Additional parameter [mu].
fn bessel_xi_denom_filter(n : Value) -> Value raise {
  share_odelin__even_filter(n)
}

///|
fn bessel_xi_degree_bound(q : Value, v : Value, x : Value) -> Value raise {
  share_odelin__half_degree_bound(q, v, x)
}

///|
fn bessel_de_solver(v : Value, x : Value) -> Value raise {
  let mu = gensym()
  with_special(q_d_radexpand, Nil, () => {
    let xi = generic_de_solver(
      v,
      x,
      list1(mu),
      q_bessel_xi_denom_filter,
      q_bessel_xi_degree_bound,
      div(
        addn_([muln_([Fix(4L), x, x]), Fix(1L), muln_([Fix(-4L), mu, mu])]),
        muln_([Fix(4L), x, x]),
      ),
    )
    if xi.truthy() {
      let z = sratsimp(nth(0, xi))
      let mu = sratsimp(car(nth(1, xi)))
      let m = mul2(
        power(z, div(Fix(1L), Fix(2L))),
        power(d_diff(list2(z, x)), div(Fix(-1L), Fix(2L))),
      )
      share_odelin__mbag_map(
        s => mul2(m, s),
        list3(
          list1(q_d_set),
          list3(list1(q_d_fbessel_j), mu, z),
          list3(list1(q_d_fbessel_y), mu, z),
        ),
      )
    } else {
      Nil
    }
  })
}

///|
/// The differential operator with the FSS {bessel_j(mu,sqrt(x)),
/// bessel_y(mu,sqrt(x))} is L = D^2 + a1 D + a0, with a1 = 1/x and a0 =
/// (1/x-mu^2/x^2)/4; Delta -> 1/x as x-> infinity (order at infinity is 1);
/// de-cnd = (1 + x - mu^2)/(4*x^2). Additional parameter [mu].
fn bessel_sqrt_xi_denom_filter(n : Value) -> Value raise {
  if num_gt(n, Fix(2L)) {
    num_sub(n, Fix(2L))
  } else {
    Fix(0L)
  }
}

///|
fn bessel_sqrt_xi_degree_bound(q : Value, v : Value, x : Value) -> Value raise {
  let rd = ratfun_degree(v, x)
  let mx : Value = if num_gt(Fix(-2L), rd) { Fix(-2L) } else { rd }
  num_add(num_add(Fix(2L), d_hipow(q, x)), mx)
}

///|
fn bessel_sqrt_de_solver(v : Value, x : Value) -> Value raise {
  let mu = gensym()
  with_special(q_d_radexpand, Nil, () => {
    let xi = generic_de_solver(
      v,
      x,
      list1(mu),
      q_bessel_sqrt_xi_denom_filter,
      q_bessel_sqrt_xi_degree_bound,
      div(
        addn_([Fix(1L), x, muln_([Fix(-1L), mu, mu])]),
        muln_([Fix(4L), x, x]),
      ),
    )
    if xi.truthy() {
      let mut z = sratsimp(nth(0, xi))
      let mu = sratsimp(car(nth(1, xi)))
      let m = mul2(
        power(z, div(Fix(1L), Fix(2L))),
        power(d_diff(list2(z, x)), div(Fix(-1L), Fix(2L))),
      )
      z = power(z, div(Fix(1L), Fix(2L)))
      share_odelin__mbag_map(
        s => mul2(m, s),
        list3(
          list1(q_d_set),
          list3(list1(q_d_fbessel_j), mu, z),
          list3(list1(q_d_fbessel_y), mu, z),
        ),
      )
    } else {
      Nil
    }
  })
}

///|
/// The differential operator with the FSS {kummer_m(a,b,x),kummer_u(a,b,x)}
/// is L = D^2 + a1*D + a0, with a1 = b/x - 1 and a0 = -a/x; Delta -> 1 as
/// x-> infinity (order at infinity is 0); de-cnd =
/// (-x^2+(2*b-4*a)*x-b^2+2*b)/(4*x^2). Additional parameters [a,b].
fn hypergeo01_xi_denom_filter(n : Value) -> Value raise {
  share_odelin__even_filter(n)
}

///|
fn hypergeo01_xi_degree_bound(q : Value, v : Value, x : Value) -> Value raise {
  share_odelin__half_degree_bound(q, v, x)
}

///|
fn hypergeo01_de_solver(v : Value, x : Value) -> Value raise {
  let a = gensym()
  let b = gensym()
  with_special(q_d_radexpand, Nil, () => {
    let xi = generic_de_solver(
      v,
      x,
      list2(a, b),
      q_hypergeo01_xi_denom_filter,
      q_hypergeo01_xi_degree_bound,
      // (-x^2+(2*b-4*a)*x-b^2+2*b)/(4*x^2)
      div(
        addn_([
          mul2(x, x),
          mul2(sub(mul2(Fix(4L), a), mul2(Fix(2L), b)), x),
          mul2(b, b),
          mul2(Fix(-2L), b),
        ]),
        muln_([Fix(-4L), x, x]),
      ),
    )
    if xi.truthy() {
      let z = sratsimp(car(xi))
      let a = caadr(xi)
      let b = cadadr(xi)
      let m = muln_([
        power(q_d__pcte, div(z, Fix(-2L))),
        power(z, div(b, Fix(2L))),
        power(d_diff(list2(z, x)), div(Fix(-1L), Fix(2L))),
      ])
      share_odelin__mbag_map(
        s => mul2(s, m),
        list3(
          list1(q_d_set),
          list4(list1(q_d_kummer_m), a, b, z),
          list4(list1(q_d_kummer_u), a, b, z),
        ),
      )
    } else {
      Nil
    }
  })
}

///|
/// The differential operator with the FSS {spherodialwave_a(b,c,q,x),
/// spherodialwave_b(b,c,q,x)} is L = D^2 + a1*D + a0, with a1 =
/// -2*(b+1)*x/(1-x^2) and a0 = (c-4*q*x^2)/(1-x^2); Delta -> constant as
/// x-> infinity (order at infinity is 0); de-cnd = (q*x^4 -
/// (4q+b^2+b+c)*x^2 + (b+c+1)) / (1-x^2)^2. Additional parameters [b,c,q].
fn spherodialwave_xi_denom_filter(n : Value) -> Value raise {
  share_odelin__even_filter(n)
}

///|
fn spherodialwave_xi_degree_bound(q : Value, v : Value, x : Value) -> Value raise {
  share_odelin__half_degree_bound(q, v, x)
}

///|
fn spherodialwave_de_solver(v : Value, x : Value) -> Value raise {
  let b = gensym()
  let c = gensym()
  let q = gensym()
  let x2 = mul2(x, x)
  with_special(q_d_radexpand, Nil, () => {
    let xi = generic_de_solver(
      v,
      x,
      list3(b, c, q),
      q_spherodialwave_xi_denom_filter,
      q_spherodialwave_xi_degree_bound,
      mul2(
        power(add(list2(Fix(1L), mul2(add(list2(Fix(-2L), x2)), x2))), Fix(-1L)),
        addn_([
          Fix(1L),
          b,
          c,
          mul2(
            x2,
            addn_([
              mul2(add(list2(Fix(-1L), mul2(Fix(-1L), b))), b),
              mul2(Fix(-1L), c),
              mul2(Fix(-4L), q),
              muln_([Fix(4L), q, x2]),
            ]),
          ),
        ]),
      ),
    )
    // (x2*(4*q*x2-4*q-c+(-b-1)*b)+c+b+1)/((x2-2)*x2+1), x2 = x^2.
    if xi.truthy() {
      let z = sratsimp(nth(0, xi))
      let b = nth(0, nth(1, xi))
      let c = nth(1, nth(1, xi))
      let q = nth(2, nth(1, xi))
      let m = mul2(
        power(sub(mul2(z, z), Fix(1L)), div(add(list2(b, Fix(1L))), Fix(2L))),
        power(d_diff(list2(z, x)), div(Fix(-1L), Fix(2L))),
      )
      share_odelin__mbag_map(
        s => mul2(m, s),
        list3(
          list1(q_d_set),
          list([list1(q_d_spherodialwave_a), b, c, q, z]),
          list([list1(q_d_spherodialwave_b), b, c, q, z]),
        ),
      )
    } else {
      Nil
    }
  })
}

///|
/// The differential operator for the hypergeometric differential equation
/// (A&S 15.5.1) with the FSS {gauss_a(a,b,c,x),gauss_b(a,b,c,x)} is L = D^2
/// + a1 D + a0, with a1=(c-(a+b+1)*x)/(x*(1-x)) and a0=-a*b/(x*(1-x));
/// Delta -> constant/x^2 as x-> infinity (order at infinity is 2); de-cnd
/// = -((b^2-2*a*b+a^2-1)*x^2+((-2*b-2*a+2)*c+4*a*b)*x+c^2-2*c)/
/// (4*x^2*(x-1)^2). Additional parameters [a,b,c].
fn hypergeo21_xi_denom_filter(n : Value) -> Value raise {
  ignore(n)
  Fix(0L)
}

///|
fn hypergeo21_xi_degree_bound(q : Value, v : Value, x : Value) -> Value raise {
  ignore((q, v, x))
  Fix(1L)
}

///|
fn hypergeo21_de_solver(v : Value, x : Value) -> Value raise {
  let a = gensym()
  let b = gensym()
  let c = gensym()
  with_special(q_d_radexpand, Nil, () => {
    let xi = generic_de_solver(
      v,
      x,
      list3(a, b, c),
      q_hypergeo21_xi_denom_filter,
      q_hypergeo21_xi_degree_bound,
      div(
        add(
          list2(
            mul2(
              x,
              addn_([
                mul2(
                  addn_([
                    mul2(add(list2(mul2(Fix(2L), a), n_starmminus(b))), b),
                    n_starmminus(power(a, Fix(2L))),
                    Fix(1L),
                  ]),
                  x,
                ),
                mul2(addn_([mul2(Fix(2L), b), mul2(Fix(2L), a), Fix(-2L)]), c),
                muln_([Fix(-4L), a, b]),
              ]),
            ),
            mul2(add(list2(Fix(2L), n_starmminus(c))), c),
          ),
        ),
        mul2(
          power(x, Fix(2L)),
          add(list2(mul2(x, add(list2(mul2(Fix(4L), x), Fix(-8L)))), Fix(4L))),
        ),
      ),
    )
    if xi.truthy() {
      let z = sratsimp(nth(0, xi))
      let a = nth(0, nth(1, xi))
      let b = nth(1, nth(1, xi))
      let c = nth(2, nth(1, xi))
      // (xi(x))^(c/2) * (xi(x)-1)^((-c+b+a+1)/2) * f(xi(x)) /
      // sqrt(diff(xi(x),x))
      let m = muln_([
        power(z, div(c, Fix(2L))),
        power(
          sub(z, Fix(1L)),
          div(addn_([Fix(1L), a, b, mul2(Fix(-1L), c)]), Fix(2L)),
        ),
        power(d_diff(list2(z, x)), div(Fix(-1L), Fix(2L))),
      ])
      share_odelin__mbag_map(
        s => mul2(m, s),
        list3(
          list1(q_d_set),
          list([list1(q_d_gauss_a), a, b, c, z]),
          list([list1(q_d_gauss_b), a, b, c, z]),
        ),
      )
    } else {
      Nil
    }
  })
}

///|
fn init_share_odelin() -> Unit raise {
  d_put(q_d_odelin, Fix(20L), q_d_version) |> ignore
  // ($load "sqfr") ... ($load "odeutils"); see the comment at the top.
  share_odelin__load_sqfr()
  d_load(Str("spherodialwave")) |> ignore
  d_load(Str("kummer")) |> ignore
  d_load(Str("extrabessel")) |> ignore
  share_odelin__load_lazysolver()
  share_odelin__load_gauss()
  d_load(Str("functs")) |> ignore
  share_odelin__load_odeutils()
  putprop(q_unk, q_simp_unk, q_operators) |> ignore
  defun(
    q_simp_unk,
    args => share_odelin__simp_unk(args[0], args[1], args[2]),
    name="simp-unk",
  )
}

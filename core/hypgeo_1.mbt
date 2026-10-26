// Port of src/hypgeo.lisp (part 1): helpers, test functions for the pattern
// matcher, shortcuts for special functions and the M2 patterns.
//
// These are the main routines for finding the Laplace Transform of special
// functions --- written by Yannis Avgoustis, modified by Edward Lafferty.
//
// References:
//   Definite integration using the generalized hypergeometric functions,
//   Avgoustis, Ioannis Dimitrios, Thesis 1977, M.S. MIT.
//   Avgoustis, I. D., Symbolic Laplace Transforms of Special Functions,
//   Proceedings of the 1977 MACSYMA Users' Conference, pp 21-41.
//
// The specials *hypgeo-var* (variable of integration) and *hypgeo-par*
// (parameter of the Laplace transform, typically s) are bound in DEFEXEC.

///|
/// Placeholder symbols in the pattern templates: the backquoted `,var2`
/// and `,par` of the Lisp patterns.
let hypgeo__ph_var2 : Value = sym("hypgeo-var2")

///|
let hypgeo__ph_par : Value = sym("hypgeo-par")

///|
/// `((rat simp) n d)`
fn hypgeo__r(n : Int, d : Int) -> Value {
  mk_simp(q_rat, [int(n), int(d)])
}

///|
fn hypgeo__var() -> Value {
  symval(q_ear_hypgeo_var)
}

///|
fn hypgeo__par() -> Value {
  symval(q_ear_hypgeo_par)
}

///|
/// `(setq *hyp-return-noun-flag* flag)`
fn hypgeo__flag(flag : Value) -> Value {
  set(q_ear_hyp_return_noun_flag, flag)
}

///|
/// `(unwind-protect body cleanup)`
fn hypgeo__unwind(
  body : () -> Value raise,
  cleanup : () -> Unit raise,
) -> Value raise {
  body() catch {
    e => {
      cleanup()
      raise e
    }
  } noraise {
    v => {
      cleanup()
      v
    }
  }
}

///|
/// `(with-new-context (context) body)` from maxmac.lisp.
fn hypgeo__with_new_context(f : () -> Value raise) -> Value raise {
  let my_context = gensym(prefix="$ctxt")
  d_supcontext(list2(my_context, symval(q_context))) |> ignore
  hypgeo__unwind(f, () => d_killcontext(list1(my_context)) |> ignore)
}

///|
/// `(take '(op) args...)` for a one-symbol operator header.
fn hypgeo__take(op : Value, args : Array[Value]) -> Value raise {
  take(list1(op), args)
}

///|
/// The three values of `(complex-number-p u 'mnump)` (numerical-utils.lisp),
/// whose declaration returns only the primary value.
fn hypgeo__complex_number_p_mv(u : Value) -> (Bool, Value, Value) raise {
  fn n(x : Value) -> Bool raise {
    mnump(x).truthy()
  }

  fn is_i(x : Value) -> Bool raise {
    eq(x, q_d__pcti) && n(int(1))
  }

  if n(u) {
    return (true, u, int(0))
  }
  if atom(u) {
    if is_i(u) {
      return (true, int(0), int(1))
    }
    return (false, Nil, Nil)
  }
  if mplusp(u).truthy() {
    if cdddr(u) is Nil && n(cadr(u)) {
      let re = cadr(u)
      let a2 = caddr(u)
      if is_i(a2) {
        return (true, re, int(1))
      }
      if mtimesp(a2).truthy() &&
        cdddr(a2) is Nil &&
        n(cadr(a2)) &&
        eq(caddr(a2), q_d__pcti) {
        return (true, re, cadr(a2))
      }
    }
    return (false, Nil, Nil)
  }
  if mtimesp(u).truthy() {
    if cdddr(u) is Nil && n(cadr(u)) && eq(caddr(u), q_d__pcti) {
      return (true, int(0), cadr(u))
    }
    return (false, Nil, Nil)
  }
  (false, Nil, Nil)
}

// ---------------------------------------------------------------------------
// Helper function for this file

///|
fn substl(p1 : Value, p2 : Value, p3 : Value) -> Value raise {
  if eq(p1, p2) {
    p3
  } else {
    maxima_substitute(p1, p2, p3)
  }
}

// Test functions for pattern match

///|
/// Not used here.  This is only used in defint.lisp.
fn freevar0(m : Value) -> Value raise {
  if equal(m, int(0)) {
    Nil
  } else {
    freevar(m)
  }
}

///|
/// Test if EXPR is 1 or %e.
fn expor1p(expr : Value) -> Value raise {
  lbool(equal(expr, int(1)) || eq(expr, q_d__pcte))
}

///|
fn has(expr : Value, x : Value) -> Value raise {
  lbool(!free(expr, x).truthy())
}

///|
fn free_not_zero_p(expr : Value, x : Value) -> Value raise {
  if !equal(expr, int(0)) {
    free(expr, x)
  } else {
    Nil
  }
}

///|
fn free2(expr : Value, x : Value, y : Value) -> Value raise {
  if free(expr, x).truthy() {
    free(expr, y)
  } else {
    Nil
  }
}

///|
fn has_not_alike1_p(expr : Value, x : Value) -> Value raise {
  if !alike1(expr, x).truthy() {
    has(expr, x)
  } else {
    Nil
  }
}

// Some shortcuts for special functions.

///|
/// Lommel's little s[u,v](z) function.
fn littleslommel(m : Value, n : Value, z : Value) -> Value raise {
  list3(list2(q_mqapply, q_simp), list([list3(q_d__pcts, q_simp, q_array), m, n]), z)
}

///|
/// Whittaker's M function
fn mwhit(a : Value, i1 : Value, i2 : Value) -> Value raise {
  list3(list2(q_mqapply, q_simp), list([list3(q_d__pctm, q_simp, q_array), i1, i2]), a)
}

///|
/// Whittaker's W function
fn wwhit(a : Value, i1 : Value, i2 : Value) -> Value raise {
  list3(list2(q_mqapply, q_simp), list([list3(q_d__pctw, q_simp, q_array), i1, i2]), a)
}

///|
/// Jacobi P
fn pjac(x : Value, n : Value, a : Value, b : Value) -> Value raise {
  list3(
    list2(q_mqapply, q_simp),
    list([list3(q_d__pctp, q_simp, q_array), n, a, b]),
    x,
  )
}

// ---------------------------------------------------------------------------
// The M2 patterns.  Each template is read once; the placeholder symbols
// stand for the backquoted variable of integration and parameter.

///|
/// Inline pattern of LT-UNITSTEP-EXP: v*unit_step(w)+d.
let hypgeo__p_unitstep_exp : Value = try! lread(
  "((mplus) ((coeffpt) (v nonzerp) (($unit_step) (w has hypgeo-var2))) ((coeffpp) (d zerp)))",
)

///|
let hypgeo__p_m2_arbpow1 : Value = try! lread(
  "((mplus) ((coeffpt) (c free hypgeo-var2) ((mexpt) (u has hypgeo-var2) (v free hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_arbpow1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_arbpow1))
}

///|
let hypgeo__p_m2_arbpow2 : Value = try! lread(
  "((mplus) ((mtimes) ((coefftt) (c free hypgeo-var2)) ((mexpt) (u equal hypgeo-var2) (v free hypgeo-var2)) ((mexpt) ((mplus) (a free hypgeo-var2) ((coefft) (b free hypgeo-var2) (u equal hypgeo-var2))) (w free-not-zero-p hypgeo-var2))) ((coeffpp) (d zerp)))",
)

///|
fn m2_arbpow2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_arbpow2))
}

///|
let hypgeo__p_m2_asin : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%asin) (w has hypgeo-var2))) ((coeffpp) (a equal 0)))",
)

///|
fn m2_asin(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_asin))
}

///|
let hypgeo__p_m2_atan : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%atan) (w has hypgeo-var2))) ((coeffpp) (a equal 0)))",
)

///|
fn m2_atan(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_atan))
}

///|
let hypgeo__p_m2_atanh : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%atanh) (w has hypgeo-var2))) ((coeffpp) (a equal 0)))",
)

///|
fn m2_atanh(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_atanh))
}

///|
let hypgeo__p_m2_onej : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_j) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onej(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onej))
}

///|
let hypgeo__p_m2_twoj : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_j) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_j) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_twoj(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_twoj))
}

///|
let hypgeo__p_m2_twoy : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_y) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_y) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_twoy(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_twoy))
}

///|
let hypgeo__p_m2_twok : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_k) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_k) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_twok(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_twok))
}

///|
let hypgeo__p_m2_onekoney : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_k) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_y) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onekoney(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onekoney))
}

///|
let hypgeo__p_m2_onej_hat2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) ((%bessel_j) (v free hypgeo-var2) (w has hypgeo-var2)) 2)) ((coeffpp) (a zerp)))",
)

///|
fn m2_onej_hat2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onej_hat2))
}

///|
let hypgeo__p_m2_oney_hat2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) ((%bessel_y) (v free hypgeo-var2) (w has hypgeo-var2)) 2)) ((coeffpp) (a zerp)))",
)

///|
fn m2_oney_hat2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oney_hat2))
}

///|
let hypgeo__p_m2_onek_hat2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) ((%bessel_k) (v free hypgeo-var2) (w has hypgeo-var2)) 2)) ((coeffpp) (a zerp)))",
)

///|
fn m2_onek_hat2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onek_hat2))
}

///|
let hypgeo__p_m2_onei : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_i) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onei(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onei))
}

///|
let hypgeo__p_m2_twoi : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_i) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_i) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_twoi(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_twoi))
}

///|
let hypgeo__p_m2_two_hankel_1 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hankel_1) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_1) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_two_hankel_1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_two_hankel_1))
}

///|
let hypgeo__p_m2_two_hankel_2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hankel_2) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_2) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_two_hankel_2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_two_hankel_2))
}

///|
let hypgeo__p_m2_hankel_1_starhankel_2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hankel_1) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_2) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_hankel_1_starhankel_2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hankel_1_starhankel_2))
}

///|
let hypgeo__p_m2_oneyonej : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_y) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_j) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneyonej(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneyonej))
}

///|
let hypgeo__p_m2_onekonej : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_k) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_j) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onekonej(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onekonej))
}

///|
let hypgeo__p_m2_bessel_y_starhankel_1 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_y) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_1) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_bessel_y_starhankel_1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_bessel_y_starhankel_1))
}

///|
let hypgeo__p_m2_bessel_y_starhankel_2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_y) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_2) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_bessel_y_starhankel_2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_bessel_y_starhankel_2))
}

///|
let hypgeo__p_m2_bessel_k_starhankel_1 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_k) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_1) (v1 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_bessel_k_starhankel_1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_bessel_k_starhankel_1))
}

///|
let hypgeo__p_m2_bessel_k_starhankel_2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_k) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_2) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_bessel_k_starhankel_2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_bessel_k_starhankel_2))
}

///|
let hypgeo__p_m2_oneionej : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_i) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_j) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneionej(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneionej))
}

///|
let hypgeo__p_m2_bessel_i_starhankel_1 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_i) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_1) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_bessel_i_starhankel_1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_bessel_i_starhankel_1))
}

///|
let hypgeo__p_m2_bessel_i_starhankel_2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_i) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%hankel_2) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_bessel_i_starhankel_2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_bessel_i_starhankel_2))
}

///|
let hypgeo__p_m2_hankel_1_starbessel_j : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hankel_1) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_j) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_hankel_1_starbessel_j(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hankel_1_starbessel_j))
}

///|
let hypgeo__p_m2_hankel_2_starbessel_j : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hankel_2) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_j) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_hankel_2_starbessel_j(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hankel_2_starbessel_j))
}

///|
let hypgeo__p_m2_oneioney : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_i) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_y) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneioney(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneioney))
}

///|
let hypgeo__p_m2_oneionek : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_i) (v1 free hypgeo-var2) (w1 has hypgeo-var2)) ((%bessel_k) (v2 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneionek(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneionek))
}

///|
let hypgeo__p_m2_onei_hat2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) ((%bessel_i) (v free hypgeo-var2) (w has hypgeo-var2)) 2)) ((coeffpp) (a zerp)))",
)

///|
fn m2_onei_hat2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onei_hat2))
}

///|
let hypgeo__p_m2_hankel_1_hat2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) ((%hankel_1) (v free hypgeo-var2) (w has hypgeo-var2)) 2)) ((coeffpp) (a zerp)))",
)

///|
fn m2_hankel_1_hat2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hankel_1_hat2))
}

///|
let hypgeo__p_m2_hankel_2_hat2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) ((%hankel_2) (v free hypgeo-var2) (w has hypgeo-var2)) 2)) ((coeffpp) (a zerp)))",
)

///|
fn m2_hankel_2_hat2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hankel_2_hat2))
}

///|
let hypgeo__p_m2_oney : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_y) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oney(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oney))
}

///|
let hypgeo__p_m2_onek : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%bessel_k) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onek(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onek))
}

///|
let hypgeo__p_m2_hankel_1 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hankel_1) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_hankel_1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hankel_1))
}

///|
let hypgeo__p_m2_hankel_2 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hankel_2) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_hankel_2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hankel_2))
}

///|
let hypgeo__p_m2_onelog : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%log) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onelog(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onelog))
}

///|
let hypgeo__p_m2_onerf : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%erf) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onerf(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onerf))
}

///|
let hypgeo__p_m2_onerfc : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%erfc) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onerfc(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onerfc))
}

///|
let hypgeo__p_m2_onefresnel_s : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%fresnel_s) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onefresnel_s(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onefresnel_s))
}

///|
let hypgeo__p_m2_onefresnel_c : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%fresnel_c) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onefresnel_c(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onefresnel_c))
}

///|
let hypgeo__p_m2_oneexpintegral_e : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%expintegral_e) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneexpintegral_e(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneexpintegral_e))
}

///|
let hypgeo__p_m2_oneexpintegral_ei : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%expintegral_ei) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneexpintegral_ei(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneexpintegral_ei))
}

///|
let hypgeo__p_m2_oneexpintegral_e1 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%expintegral_e1) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneexpintegral_e1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneexpintegral_e1))
}

///|
let hypgeo__p_m2_oneexpintegral_si : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%expintegral_si) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneexpintegral_si(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneexpintegral_si))
}

///|
let hypgeo__p_m2_oneexpintegral_shi : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%expintegral_shi) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneexpintegral_shi(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneexpintegral_shi))
}

///|
let hypgeo__p_m2_oneexpintegral_ci : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%expintegral_ci) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneexpintegral_ci(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneexpintegral_ci))
}

///|
let hypgeo__p_m2_oneexpintegral_chi : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%expintegral_chi) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneexpintegral_chi(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneexpintegral_chi))
}

///|
let hypgeo__p_m2_onekelliptic : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($kelliptic) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onekelliptic(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onekelliptic))
}

///|
let hypgeo__p_m2_elliptic_kc : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%elliptic_kc) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_elliptic_kc(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_elliptic_kc))
}

///|
let hypgeo__p_m2_onee : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($%e) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onee(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onee))
}

///|
let hypgeo__p_m2_elliptic_ec : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%elliptic_ec) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_elliptic_ec(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_elliptic_ec))
}

///|
let hypgeo__p_m2_onegammaincomplete : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%gamma_h_incomplete) (w1 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onegammaincomplete(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onegammaincomplete))
}

///|
let hypgeo__p_m2_onegamma_incomplete_lower : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%gamma_incomplete_lower) (w1 free hypgeo-var2) (w2 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onegamma_incomplete_lower(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onegamma_incomplete_lower))
}

///|
let hypgeo__p_m2_struve_h : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%struve_h) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp)(a zerp)))",
)

///|
fn m2_struve_h(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_struve_h))
}

///|
let hypgeo__p_m2_struve_l : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%struve_l) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_struve_l(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_struve_l))
}

///|
let hypgeo__p_m2_ones : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%s array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_ones(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_ones))
}

///|
let hypgeo__p_m2_oneslommel : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($slommel array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneslommel(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneslommel))
}

///|
let hypgeo__p_m2_parabolic_cylinder_d : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($parabolic_cylinder_d) (v free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_parabolic_cylinder_d(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_parabolic_cylinder_d))
}

///|
let hypgeo__p_m2_onekbateman : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($kbateman array) (v free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onekbateman(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onekbateman))
}

///|
let hypgeo__p_m2_onel : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%l array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onel(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onel))
}

///|
let hypgeo__p_m2_one_gen_laguerre : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%gen_laguerre) (v1 free hypgeo-var2) (v2 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_one_gen_laguerre(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_one_gen_laguerre))
}

///|
let hypgeo__p_m2_one_laguerre : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%laguerre) (v1 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_one_laguerre(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_one_laguerre))
}

///|
let hypgeo__p_m2_onec : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%c array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onec(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onec))
}

///|
let hypgeo__p_m2_onet : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%t array) (v1 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onet(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onet))
}

///|
let hypgeo__p_m2_oneu : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%u array) (v1 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneu(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneu))
}

///|
let hypgeo__p_m2_onepjac : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%p array) (v1 free hypgeo-var2) (v2 free hypgeo-var2) (v3 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onepjac(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onepjac))
}

///|
let hypgeo__p_m2_jacobi_p : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($jacobi_p) (v1 free hypgeo-var2) (v2 free hypgeo-var2) (v3 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_jacobi_p(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_jacobi_p))
}

///|
let hypgeo__p_m2_hyp_onep : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%p array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_hyp_onep(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hyp_onep))
}

///|
let hypgeo__p_m2_assoc_legendre_p : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($assoc_legendre_p) (v1 free hypgeo-var2) (v2 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_assoc_legendre_p(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_assoc_legendre_p))
}

///|
let hypgeo__p_m2_onep0 : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply)(($%p array) (v1 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onep0(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onep0))
}

///|
let hypgeo__p_m2_legendre_p : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($legendre_p) (v free hypgeo-var2)) (w has hypgeo-var2)) ((coeffpp) (a zerp)))",
)

///|
fn m2_legendre_p(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_legendre_p))
}

///|
let hypgeo__p_m2_one_hermite : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hermite) (v1 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_one_hermite(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_one_hermite))
}

///|
let hypgeo__p_m2_oneq : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%q array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_oneq(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_oneq))
}

///|
let hypgeo__p_m2_assoc_legendre_q : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($assoc_legendre_q) (v1 free hypgeo-var2) (v2 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_assoc_legendre_q(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_assoc_legendre_q))
}

///|
let hypgeo__p_m2_onew : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%w array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onew(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onew))
}

///|
let hypgeo__p_m2_whittaker_w : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($whittaker_w) (v1 free hypgeo-var2) (v2 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_whittaker_w(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_whittaker_w))
}

///|
let hypgeo__p_m2_onem : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%m array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onem(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onem))
}

///|
let hypgeo__p_m2_whittaker_m : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($whittaker_m) (v1 free hypgeo-var2) (v2 free hypgeo-var2) (w has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_whittaker_m(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_whittaker_m))
}

///|
let hypgeo__p_m2_onef : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mqapply) (($%f array) (v1 free hypgeo-var2) (v2 free hypgeo-var2)) (w1 free hypgeo-var2) (w2 free hypgeo-var2) (w3 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_onef(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_onef))
}

///|
let hypgeo__p_m2_hypergeometric : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((%hypergeometric) (w1 free hypgeo-var2) (w2 free hypgeo-var2) (w3 has hypgeo-var2))) ((coeffpp) (a zerp)))",
)

///|
fn m2_hypergeometric(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_hypergeometric))
}

///|
let hypgeo__p_m2_ltep : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) $%e ((mplus) ((coeffpt) (a free2 hypgeo-var2 hypgeo-par) (x alike1 hypgeo-var2)) ((coeffpt) (e free2 hypgeo-var2 hypgeo-par) (f has hypgeo-var2)) ((mtimes) -1 (p alike1 hypgeo-par) (x alike1 hypgeo-var2)) ((coeffpp) (c free2 hypgeo-var2 hypgeo-par))))) ((coeffpp) (d equal 0)))",
)

///|
fn m2_ltep(expr : Value, var2 : Value, par : Value) -> Value raise {
  m2(expr, subst(par, hypgeo__ph_par, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_ltep)))
}

///|
let hypgeo__p_m2_defltep : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) ((mexpt) $%e ((mplus) ((coeffpt) (a free hypgeo-var2) (x alike1 hypgeo-var2)) ((coeffpt) (e free hypgeo-var2) (f has-not-alike1-p hypgeo-var2)) ((coeffpp) (c free hypgeo-var2))))) ((coeffpp) (d equal 0)))",
)

///|
fn m2_defltep(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_defltep))
}

///|
let hypgeo__p_m2_sum_with_exp_case1 : Value = try! lread(
  "((mplus) ((coefft) (c free hypgeo-var2) ((mexpt) (u alike1 hypgeo-var2) -1) ((mexpt) $%e ((mplus) ((coeffpt) (a nonzerp) (u alike1 hypgeo-var2)) ((coeffpp) (z1 zerp))))) ((coefft) (c2 equal-times-minus-one c) ((mexpt) (u alike1 hypgeo-var2) -1) ((mexpt) $%e ((mplus) ((coeffpt) (b nonzerp) (u alike1 hypgeo-var2)) ((coeffpp) (z2 zerp))))) ((coeffpp) (d true)))",
)

///|
fn m2_sum_with_exp_case1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_sum_with_exp_case1))
}

///|
let hypgeo__p_m2_sum_with_exp_case2 : Value = try! lread(
  "((mplus) ((coefft) (c free hypgeo-var2) ((mexpt) (u alike1 hypgeo-var2) ((rat) -3 2)) ((mexpt) $%e ((mplus) ((coeffpt) (a nonzerp) (u alike1 hypgeo-var2)) ((coeffpp) (z1 zerp))))) ((coefft) (c2 equal-times-minus-one c) ((mexpt) (u alike1 hypgeo-var2) ((rat) -3 2)) ((mexpt) $%e ((mplus) ((coeffpt) (b nonzerp) (u alike1 hypgeo-var2)) ((coeffpp) (z2 zerp))))) ((coeffpp) (d true)))",
)

///|
fn m2_sum_with_exp_case2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_sum_with_exp_case2))
}

///|
let hypgeo__p_m2_sum_with_exp_case3 : Value = try! lread(
  "((mplus) ((coefft) (c free hypgeo-var2) ((mexpt) (u alike1 hypgeo-var2) -2)) ((coefft) (c2 equal c) ((mexpt) (u alike1 hypgeo-var2) -2) ((mexpt) $%e ((mplus) ((coeffpt) (a nonzerp) (u alike1 hypgeo-var2)) ((coeffpp) (z1 zerp))))) ((coefft) (c3 equal-times-minus-two c) ((mexpt) (u alike1 hypgeo-var2) -2) ((mexpt) $%e ((mplus) ((coeffpt) (b equal-div-two a) (u alike1 hypgeo-var2)) ((coeffpp) (z2 zerp))))) ((coeffpp) (d true)))",
)

///|
fn m2_sum_with_exp_case3(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_sum_with_exp_case3))
}

///|
let hypgeo__p_m2_sum_with_exp_case4 : Value = try! lread(
  "((mplus) ((coefft) (c free hypgeo-var2) ((mexpt) (u alike1 hypgeo-var2) -1)) ((coefft) (c2 equal c) ((mexpt) (u alike1 hypgeo-var2) -1) ((mexpt) $%e ((mplus) ((coeffpt) (a nonzerp) (u alike1 hypgeo-var2)) ((coeffpp) (z1 zerp))))) ((coefft) (c3 equal-times-minus-two c) ((mexpt) (u alike1 hypgeo-var2) -1) ((mexpt) $%e ((mplus) ((coeffpt) (b equal-div-two a) (u alike1 hypgeo-var2)) ((coeffpp) (z2 zerp))))) ((coeffpp) (d true)))",
)

///|
fn m2_sum_with_exp_case4(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_sum_with_exp_case4))
}

///|
let hypgeo__p_m2_sum_with_exp_case5 : Value = try! lread(
  "((mplus) ((coefft) (c free hypgeo-var2) ((mexpt) (u alike1 hypgeo-var2) -1)) ((coefft) (c2 equal-times-minus-one c) ((mexpt) (u alike1 hypgeo-var2) -1) ((mexpt) $%e ((mplus) ((coeffpt) (a nonzerp) (u alike1 hypgeo-var2)) ((coeffpp) (z1 zerp))))) ((coeffpp) (d true)))",
)

///|
fn m2_sum_with_exp_case5(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_sum_with_exp_case5))
}

///|
let hypgeo__p_m2_sum : Value = try! lread(
  "((mplus) ((coeffpt) (c free hypgeo-var2) ((%sum) (u true) (i true) (l true) (h true))) ((coeffpp) (d zerp)))",
)

///|
fn m2_sum(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_sum))
}

///|
let hypgeo__p_m2_unit_step : Value = try! lread(
  "((mplus) ((coeffpt) (u nonzerp) (($unit_step) ((mplus) (x alike1 hypgeo-var2) ((coeffpp) (a true))))) ((coeffpp) (d zerp)))",
)

///|
fn m2_unit_step(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_unit_step))
}

///|
let hypgeo__p_m2_c_start_hatv : Value = try! lread(
  "((mtimes) ((coefftt) (c free hypgeo-var2)) ((mexpt) (u alike1 hypgeo-var2) (v free hypgeo-var2)))",
)

///|
fn m2_c_start_hatv(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_c_start_hatv))
}

///|
let hypgeo__p_m2_t_hat2 : Value = try! lread(
  "((mexpt) (u alike1 hypgeo-var2) 2)",
)

///|
fn m2_t_hat2(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_t_hat2))
}

///|
let hypgeo__p_m2_sqroott : Value = try! lread(
  "((mexpt) (u alike1 hypgeo-var2) ((rat) 1 2))",
)

///|
fn m2_sqroott(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_sqroott))
}

///|
let hypgeo__p_m2_t_hat_1 : Value = try! lread(
  "((mexpt) (u alike1 hypgeo-var2) -1)",
)

///|
fn m2_t_hat_1(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_t_hat_1))
}

///|
let hypgeo__p_m2_e_hat_t : Value = try! lread(
  "((mexpt) $%e ((mtimes) -1 (u alike1 hypgeo-var2)))",
)

///|
fn m2_e_hat_t(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_e_hat_t))
}

///|
let hypgeo__p_m2_e_hatt : Value = try! lread(
  "((mexpt) $%e (u alike1 hypgeo-var2))",
)

///|
fn m2_e_hatt(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_e_hatt))
}

///|
let hypgeo__p_m2_a_start : Value = try! lread(
  "((mplus) ((mtimes) (u alike1 hypgeo-var2) (a free hypgeo-var2)) ((coeffpp) (c equal 0)))",
)

///|
fn m2_a_start(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_a_start))
}

///|
let hypgeo__p_m2_atb : Value = try! lread(
  "((mplus) ((coeffpt) (a free hypgeo-var2) (u alike1 hypgeo-var2)) ((coeffpp) (b free hypgeo-var2)))",
)

///|
fn m2_atb(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_atb))
}

///|
let hypgeo__p_m2_d_starx_hatm_star_pcte_hata_starx : Value = try! lread(
  "((mtimes) ((coefftt) (d free2 hypgeo-var2 hypgeo-par)) ((mexpt) (x alike1 hypgeo-var2) (m free2 hypgeo-var2 hypgeo-par)) ((mexpt) (q expor1p) ((mtimes) ((coefftt) (a free2 hypgeo-var2 hypgeo-par)) (x alike1 hypgeo-var2))))",
)

///|
fn m2_d_starx_hatm_star_pcte_hata_starx(expr : Value, var2 : Value, par : Value) -> Value raise {
  m2(expr, subst(par, hypgeo__ph_par, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_d_starx_hatm_star_pcte_hata_starx)))
}

///|
let hypgeo__p_m2_f_plusc : Value = try! lread(
  "((mplus) ((coeffpt) (f has hypgeo-var2)) ((coeffpp) (c free hypgeo-var2)))",
)

///|
fn m2_f_plusc(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_f_plusc))
}

///|
let hypgeo__p_m2_a_starx_hatm_plusc : Value = try! lread(
  "((mplus) ((coefft) (a free hypgeo-var2) ((mexpt) (x alike1 hypgeo-var2) (m free-not-zero-p hypgeo-var2))) ((coeffpp) (c free hypgeo-var2)))",
)

///|
fn m2_a_starx_hatm_plusc(expr : Value, var2 : Value) -> Value raise {
  m2(expr, subst(var2, hypgeo__ph_var2, hypgeo__p_m2_a_starx_hatm_plusc))
}


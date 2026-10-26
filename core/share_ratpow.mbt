// Port of share/contrib/ratpow.lisp (Stavros Macrakis, 2013-2015, v0.3).
//
// These functions operate on the *numerator* of a CRE; to find the
// exponents in the denominator, use ratXXpow(ratdenom(...)).
//
// ratp_hipow -- highest power of the main variable in a CRE polynomial
// ratp_lopow -- lowest power of the main variable in a CRE polynomial
// ratp_coeffs -- list of powers and coefficients of the main variable
// ratp_dense_coeffs -- list of coefficients of the main variable, highest first
// ratp_dense_coeffs_lo -- list of coefficients of the main variable, lowest first

///|
/// ratp_hipow( expr, var ) => highest power of var in ratnumer(expr)
///  ratp_hipow( x^(5/2) + x^2 , x) => 2
///  ratp_hipow( x^(5/2) + x^2 , sqrt(x)) => 5
fn d_ratp_hipow(e : Value, v : Value) -> Value raise {
  ratp_pow(e, v, q_hipow)
}

///|
/// ratp_lopow( expr, var ) => lowest power of var in ratnumer(expr)
///  ratp_lopow( x^(5/2) + x^3 , x) => 0
///  CRE is {x}^3 + {x^(1/2)}^5 * {x}^0, where {} denotes kernels
fn d_ratp_lopow(e : Value, v : Value) -> Value raise {
  ratp_pow(e, v, q_lopow)
}

///|
/// ratp_coeffs( expr, var ) => list of powers/coefficients in ratnumer(expr)
/// returned coefficients are in CRE form except for numbers
///  ratp_coeffs( 4*x^3 + x + sqrt(x), x) => [[3,4],[1,1],[0,sqrt(x)]]
fn d_ratp_coeffs(e : Value, v : Value) -> Value raise {
  ratp_pow(e, v, q_sparse_coeffs)
}

///|
/// ratp_dense_coeffs( expr, var ) => list of coefficients in ratnumer(expr),
/// highest first
///  ratp_dense_coeffs( 4*x^3 + x + sqrt(x), x) => [4,0,1,sqrt(x)]
fn d_ratp_dense_coeffs(e : Value, v : Value) -> Value raise {
  ratp_pow(e, v, q_dense_coeffs)
}

///|
/// ratp_dense_coeffs_lo( expr, var ) => list of coefficients in
/// ratnumer(expr), lowest first
///  ratp_dense_coeffs_lo( 4*x^3 + x + sqrt(x), x) => [sqrt(x),1,0,4]
fn d_ratp_dense_coeffs_lo(e : Value, v : Value) -> Value raise {
  ratp_pow(e, v, q_dense_coeffs_low)
}

///|
fn ratp_pow(e : Value, v : Value, func : Value) -> Value raise {
  if mbagp(e).truthy() {
    return simplify(
      cons(list1(caar(e)), mapcar(i => ratp_pow(i, v, func), cdr(e))),
    )
  }
  // change main variable if necessary
  let e = d_rat(
    if d_taylorp(e).truthy() {
      d_ratdisrep(e)
    } else {
      e
    },
    list1(v),
  )
  let mrat = car(e)
  let mut kernels = caddr(mrat)
  let gensyms = cadddr(mrat)
  let mainvar_gensym = nth(length(kernels) - 1, gensyms)
  let numerat = cadr(e)
  let mut res : Value = Nil
  let lis = if pcoefp(numerat).truthy() || !eq(car(numerat), mainvar_gensym) {
    list2(int(0), numerat)
  } else {
    cdr(numerat)
  }
  if eq(func, q_hipow) {
    car(lis)
  } else if eq(func, q_lopow) {
    car(nthcdr(length(lis) - 2, lis))
  } else {
    kernels = butlast(kernels, n=1)
    let mrat = list([q_mrat, q_simp, kernels, gensyms])
    // Putprop needed for pdisrep, but not part-rat
    if eq(func, q_sparse_coeffs) {
      let mut lis = lis
      while lis.truthy() {
        res = cons(
          list([list2(q_mlist, q_simp), car(lis), part_rat(mrat, cadr(lis))]),
          res,
        )
        lis = cddr(lis)
      }
      cons(list2(q_mlist, q_simp), nreverse(res))
    } else if memq(func, list2(q_dense_coeffs, q_dense_coeffs_low)).truthy() {
      let mut lis = lis
      let mut pow = car(lis)
      while lis.truthy() {
        while num_gt(pow, car(lis)) {
          res = cons(int(0), res)
          pow = num_sub(pow, int(1))
        }
        res = cons(part_rat(mrat, cadr(lis)), res)
        lis = cddr(lis)
        pow = num_sub(pow, int(1))
      }
      cons(list2(q_mlist, q_simp), if eq(func, q_dense_coeffs_low) {
        res
      } else {
        nreverse(res)
      })
    } else {
      Nil
    }
  }
}

///|
fn part_rat(mrat : Value, expr : Value) -> Value raise {
  if pcoefp(expr).truthy() {
    expr
  } else {
    list_star([mrat, expr, int(1)])
  }
}

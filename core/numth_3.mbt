// Port of src/numth.lisp, part 3: GALOIS FIELDS -- irreducibility,
// primitive elements and polynomials, random elements, factoring, gcd,
// order, degree, minimal polynomial, trace, norm, normal bases, matrices,
// discrete logarithm, nth roots and tables of small fields; and the
// top-level forms of numth.lisp (init_numth).

///|
fn numth__gf_coeff_limit() -> Value {
  symval(q_d_gf_coeff_limit)
}

// irreducibility (Ben-Or algorithm) -------------------------------------------

///|
fn d_gf_irreducible_p(a : Value, p? : Value = Nil) -> Value raise {
  let mut p = p
  if p.truthy() {
    if !(integerp(p) && primep(p).truthy()) {
      numth__err(
        "`gf_irreducible_p': Second argument must be a prime number.",
        [],
      )
      |> ignore
    }
  } else {
    gf_char_q(Str("gf_irreducible_p")) |> ignore
    p = numth__gf_char()
  }
  numth__ef(Nil, fn() {
    numth__with_char(p, fn() {
      let x = gf_p2x(a) // gf-p2x depends on *gf-char*
      if x is Nil {
        Nil
      } else {
        let n = car(x)
        if numth__eqi(n, 0) {
          Nil
        } else if numth__eqi(n, 1) {
          t
        } else {
          gf_irr_p(x, p, car(x))
        }
      }
    })
  })
}

///|
fn d_ef_irreducible_p(a : Value) -> Value raise {
  ef_gf_field_q(Str("ef_irreducible_p")) |> ignore
  numth__ef(t, fn() {
    let a = gf_p2x(a)
    gf_irr_p(a, numth__gf_card(), car(a))
  })
}

///|
/// is y irreducible of degree n over Fq[x] ?
///
///                 q,n > 1 !
/// gf-irr-p is independent from any settings
fn gf_irr_p(y : Value, q : Value, n : Value) -> Value raise {
  numth__with_char(car(cfactorw(q)), fn() {
    let x = list2(Fix(1L), Fix(1L))
    let mx = gf_minus(x) // gf-minus needs *gf-char*
    let lc = cadr(y)
    let mut y = y
    if !numth__eqi(lc, 1) {
      y = gf_xctimes(y, gf_cinv(lc)) // monicize y
    }
    let mut i : Value = Fix(1L)
    let mut xq = x
    let n2 = ash(n, -1)
    while !num_gt(i, n2) {
      xq = gf_pow(xq, q, y)
      if !numth__eqi(car(gf_gcd(y, gf_plus(xq, mx))), 0) {
        return Nil
      }
      i = one_plus(i)
    }
    t
  })
}

///|
/// find an irreducible element
///
/// gf_irreducible is independent from any settings
/// p,n : desired characteristic and degree
fn d_gf_irreducible(p : Value, n : Value) -> Value raise {
  if !(integerp(p) && primep(p).truthy() && integerp(n)) {
    numth__err("`gf_irreducible' needs a prime number and an integer.", [])
    |> ignore
  }
  gf_set_rat_header() |> ignore
  numth__with_char(p, fn() {
    numth__ef(Nil, fn() {
      let irr = gf_irr(p, n)
      if irr.truthy() {
        gf_x2p(irr)
      } else {
        Nil
      }
    })
  })
}

///|
/// n : desired degree
fn d_ef_irreducible(n : Value) -> Value raise {
  ef_gf_field_q(Str("ef_irreducible")) |> ignore
  if !integerp(n) {
    numth__err("`ef_irreducible' needs an integer.", []) |> ignore
  }
  numth__ef(t, fn() {
    let irr = ef_irr(n)
    if irr.truthy() {
      gf_x2p(irr)
    } else {
      Nil
    }
  })
}

///|
fn gf_irr(p : Value, n : Value) -> Value raise {
  n_starf_irr(p, n)
}

///|
fn ef_irr(n : Value) -> Value raise {
  n_starf_irr(numth__gf_card(), n)
}

///|
fn n_starf_irr(q : Value, n : Value) -> Value raise {
  if numth__eqi(n, 1) {
    return list2(Fix(1L), Fix(1L))
  }
  let inc = num_min(numth__gf_coeff_limit(), q)
  let i_lim = expt(inc, n)
  let mut i : Value = Fix(1L)
  while true {
    if num_ge(i, i_lim) {
      return numth__err(
        "No irreducible polynomial found.~%~\n                                    `gf_coeff_limit' might be too small.~%",
        [],
      )
    }
    let mut x = numth__with_char(inc, fn() { gf_n2x(i) })
    if numth__eqi(car(numth__last2(x)), 0) {
      x = cons(n, cons(Fix(1L), x))
      if gf_irr_p(x, q, n).truthy() {
        return x
      }
    }
    i = one_plus(i)
  }
  Nil
}

// Primitive elements ----------------------------------------------------------

///|
/// Tests if an element is primitive in the field
fn d_gf_primitive_p(a : Value) -> Value raise {
  gf_data_q(Str("gf_primitive_p")) |> ignore // --> precomputations are performed
  numth__ef(Nil, fn() {
    let x = gf_p2x(a)
    let n = gf_x2n(x)
    if numth__eqi(n, 0) || num_ge(n, numth__gf_card()) {
      Nil
    } else if numth__eqi(symval(q_ear_gf_exp), 1) {
      zn_primroot_p(
        n,
        numth__gf_char(),
        numth__gf_ord(),
        mapcar(f => car(f), symval(q_ear_gf_fs_ord)),
      )
    } else {
      gf_prim_p(x)
    }
  })
}

///|
fn d_ef_primitive_p(a : Value) -> Value raise {
  ef_data_q(Str("ef_primitive_p")) |> ignore // --> precomputations are performed
  numth__ef(t, fn() {
    let a = gf_p2x(a)
    if a is Nil {
      Nil
    } else if num_ge(car(a), symval(q_ear_ef_exp)) {
      Nil
    } else if numth__eqi(car(a), 0) {
      if numth__eqi(symval(q_ear_ef_exp), 1) {
        numth__ef(Nil, fn() { gf_prim_p(gf_n2x(cadr(a))) })
      } else {
        Nil
      }
    } else {
      ef_prim_p(a)
    }
  })
}

// Testing primitivity in (Fq^n)*:
//
// We check f(x)^ei # 1 (ei = ord/pi) for all prime factors pi of ord.
//
// With ei = sum(aij*q^j, j,0,m) in base q and using f(x)^q = f(x^q) we get
//
// f(x)^ei = f(x)^sum(aij*q^j, j,0,m) = prod(f(x^q^j)^aij, j,0,m).
//
// Special case: red is irreducible, f(x) = x+c and pi|ord and pi|q-1.
//
// Then ei = (q^n-1)/(q-1) * (q-1)/pi = sum(q^j, j,0,n-1) * (q-1)/pi.
//
// With ai = (q-1)/pi and using red(z) = prod(z - x^q^j, j,0,n-1) we get
//
// f(x)^ei = f(x)^sum(ai*q^j, j,0,n-1) = (prod(f(x)^q^j, j,0,n-1))^ai
//
//         = (prod(x^q^j + c, j,0,n-1))^ai
//         = ((-1)^n * prod(-c - x^q^j, j,0,n-1))^ai
//
//         = ((-1)^n * red(-c))^ai

///|
fn gf_prim_p(x : Value) -> Value raise {
  if symval(q_ear_gf_irred_q).truthy() {
    n_starf_prim_p_2(
      x,
      numth__gf_char(),
      numth__gf_red(),
      symval(q_ear_gf_fsx),
      symval(q_ear_gf_fsx_base_p),
      symval(q_ear_gf_x_hatp_powers),
    )
  } else if gf_unit_p(x, numth__gf_red()).truthy() {
    n_starf_prim_p_1(
      x,
      numth__gf_red(),
      numth__gf_ord(),
      symval(q_ear_gf_fs_ord),
    )
  } else {
    Nil
  }
}

///|
fn ef_prim_p(x : Value) -> Value raise {
  if symval(q_ear_ef_irred_q).truthy() {
    n_starf_prim_p_2(
      x,
      numth__gf_card(),
      numth__ef_red(),
      symval(q_ear_ef_fsx),
      symval(q_ear_ef_fsx_base_q),
      symval(q_ear_ef_x_hatq_powers),
    )
  } else if gf_unit_p(x, numth__ef_red()).truthy() {
    n_starf_prim_p_1(
      x,
      numth__ef_red(),
      symval(q_ear_ef_ord),
      symval(q_ear_ef_fs_ord),
    )
  } else {
    Nil
  }
}

///|
fn n_starf_prim_p_1(x : Value, red : Value, ord : Value, fs_ord : Value) -> Value raise {
  for pe in fs_ord.iter() {
    if numth__is_one(gf_pow(x, numth__trunc(ord, car(pe)), red)) {
      return Nil
    }
  }
  t
}

///|
/// *f-prim-p-2 uses precomputations and exponentiation by composition
fn n_starf_prim_p_2(
  x : Value,
  q : Value,
  red : Value,
  fs : Value,
  fs_base_q : Value,
  x_hatq_powers : Value,
) -> Value raise {
  if !(numth__eqi(numth__gf_char(), 2) ||
    numth__eqi(gf_jacobi(x, red, q), -1)) {
    // red is assumed to be irreducible
    return Nil
  }
  let exponent = car(red)
  let x_c = numth__eqi(car(x), 1) && numth__eqi(cadr(x), 1)
  let lf = array_dimension(fs, 0)
  for i in 0..<lf {
    let mut j = 0
    let fsi = aref1(fs, i)
    if x_c && cadr(fsi).truthy() {
      // linear and pi|ord and pi|p-1
      let neg_c : Value = if length(x) == 2 {
        Fix(0L)
      } else {
        gf_cminus_b(car(last(x)))
      }
      let mut z = list2(Fix(0L), gf_at(red, neg_c))
      if oddp(exponent) {
        z = gf_minus(z) //  (-1)^n * red(-c)
      }
      z = gf_pow(z, caddr(fsi), red) // ((-1)^n * red(-c))^ai
      if z is Nil || numth__is_one(z) {
        return Nil
      }
    } else {
      let mut prod = list2(Fix(0L), Fix(1L))
      for aij in aref1(fs_base_q, i).iter() {
        let y = gf_compose(aref1(x_hatq_powers, j), x, red) //      f(x^q^j)
        let y = gf_pow(y, aij, red) //      f(x^q^j)^aij
        prod = gf_times(prod, y, red)
        j += 1
      }
      if prod is Nil || numth__is_one(prod) {
        // prod(f(x^q^j)^aij, j,0,m)
        return Nil
      }
    }
  }
  t
}

///|
/// generalized Jacobi-symbol (Bach-Shallit, Theorem 6.7.1)
fn d_gf_jacobi(a : Value, b : Value) -> Value raise {
  gf_char_q(Str("gf_jacobi")) |> ignore
  numth__ef(Nil, fn() {
    let x = gf_p2x(a)
    let y = gf_p2x(b)
    if numth__eqi(numth__gf_char(), 2) {
      if gf_rem(x, y) is Nil {
        Fix(0L)
      } else {
        Fix(1L)
      }
    } else {
      gf_jacobi(x, y, numth__gf_char())
    }
  })
}

///|
fn d_ef_jacobi(a : Value, b : Value) -> Value raise {
  ef_gf_field_q(Str("ef_jacobi")) |> ignore
  numth__ef(t, fn() {
    let x = gf_p2x(a)
    let y = gf_p2x(b)
    if numth__eqi(car(cfactorw(numth__gf_card())), 2) {
      if gf_rem(x, y) is Nil {
        Fix(0L)
      } else {
        Fix(1L)
      }
    } else {
      gf_jacobi(x, y, numth__gf_card())
    }
  })
}

///|
fn gf_jacobi(u : Value, v : Value, q : Value) -> Value raise {
  let u = gf_rem(u, v)
  if u is Nil {
    return Fix(0L)
  }
  let c = cadr(u)
  let mut s : Value = if evenp(car(v)) { Fix(1L) } else { gf_cjacobi(c) }
  if numth__eqi(car(u), 0) {
    s
  } else {
    let u = gf_xctimes(u, gf_cinv(c))
    if oddp(ash(one_minus(q), -1)) && oddp(car(u)) && oddp(car(v)) {
      s = neg(s)
    }
    num_mul(s, gf_jacobi(v, u, q))
  }
}

///|
fn gf_cjacobi(c : Value) -> Value raise {
  if numth__efp() {
    numth__ef(Nil, fn() {
      gf_jacobi(gf_n2x(c), numth__gf_red(), numth__gf_char())
    })
  } else {
    d_jacobi(c, numth__gf_char())
  }
}

///|
/// modular composition (uses Horner and square and multiply)
/// y(x) mod red
fn d_gf_compose(a : Value, b : Value) -> Value raise {
  gf_red_q(Str("gf_compose")) |> ignore
  numth__ef(Nil, fn() {
    gf_x2p(gf_compose(gf_p2x(a), gf_p2x(b), numth__gf_red()))
  })
}

///|
fn d_ef_compose(a : Value, b : Value) -> Value raise {
  ef_red_q(Str("ef_compose")) |> ignore
  numth__ef(t, fn() {
    gf_x2p(gf_compose(gf_p2x(a), gf_p2x(b), numth__ef_red()))
  })
}

///|
fn gf_compose(x : Value, y : Value, red : Value) -> Value raise {
  if x is Nil || y is Nil {
    Nil
  } else if numth__eqi(car(y), 0) {
    y
  } else if numth__eqi(car(x), 0) {
    let n = gf_at(y, cadr(x))
    if numth__eqi(n, 0) {
      Nil
    } else {
      list2(Fix(0L), n)
    }
  } else {
    let mut y = y
    let mut res : Value = Nil
    while true {
      res = gf_nplus(res, list2(Fix(0L), cadr(y)))
      if cddr(y) is Nil {
        return gf_times(res, gf_pow(x, car(y), red), red)
      }
      res = gf_times(res, gf_pow(x, num_sub(car(y), caddr(y)), red), red)
      y = cddr(y)
    }
    Nil
  }
}

///|
/// a(n) with poly a and integer n
fn gf_at_errchk(n : Value, fun : Value) -> Value raise {
  if !integerp(n) {
    numth__err("`~m': Second argument must be an integer.", [fun])
  } else {
    Nil
  }
}

///|
/// integer n
fn d_gf_at(a : Value, n : Value) -> Value raise {
  gf_char_q(Str("gf_at")) |> ignore
  gf_at_errchk(n, Str("gf_at")) |> ignore
  numth__ef(Nil, fn() { gf_at(gf_p2x(a), n) })
}

///|
/// poly a, integer n
fn d_ef_at(a : Value, n : Value) -> Value raise {
  ef_gf_field_q(Str("ef_at")) |> ignore
  gf_at_errchk(n, Str("ef_at")) |> ignore
  numth__ef(t, fn() { gf_at(gf_p2x(a), n) })
}

///|
/// Horner and square and multiply
fn gf_at(x : Value, n : Value) -> Value raise {
  if x is Nil || integerp(x) {
    return x
  }
  let mut x = x
  let mut i : Value = Fix(0L)
  while true {
    i = gf_cplus_b(i, cadr(x))
    if cddr(x) is Nil {
      let i1 = gf_cpow(n, car(x))
      return gf_ctimes(i, i1)
    }
    let i1 = gf_cpow(n, num_sub(car(x), caddr(x)))
    i = gf_ctimes(i, i1)
    x = cddr(x)
  }
  Nil
}

///|
/// find a primitive element:
fn d_gf_primitive() -> Value raise {
  gf_data_q(Str("gf_primitive")) |> ignore
  numth__ef(Nil, fn() {
    let prim = symval(q_ear_gf_prim)
    if prim is Nil {
      Nil
    } else if equal(prim, q_d_unknown) {
      set(q_ear_gf_prim, gf_prim()) |> ignore
      if symval(q_ear_gf_prim) is Nil {
        Nil
      } else {
        gf_x2p(symval(q_ear_gf_prim))
      }
    } else {
      gf_x2p(prim)
    }
  })
}

///|
fn d_ef_primitive() -> Value raise {
  ef_data_q(Str("ef_primitive")) |> ignore
  numth__ef(t, fn() {
    let prim = symval(q_ear_ef_prim)
    if prim is Nil {
      Nil
    } else if equal(prim, q_d_unknown) {
      if numth__eqi(symval(q_ear_ef_exp), 1) {
        set(
          q_ear_ef_prim,
          numth__ef(Nil, fn() { gf_x2n(symval(q_ear_gf_prim)) }),
        )
      } else {
        set(q_ear_ef_prim, ef_prim()) |> ignore
        if symval(q_ear_ef_prim) is Nil {
          Nil
        } else {
          gf_x2p(symval(q_ear_ef_prim))
        }
      }
    } else {
      gf_x2p(prim)
    }
  })
}

///|
fn gf_prim() -> Value raise {
  n_starf_prim(numth__gf_char(), symval(q_ear_gf_exp), q_gf_prim_p)
}

///|
fn ef_prim() -> Value raise {
  n_starf_prim(numth__gf_card(), symval(q_ear_ef_exp), q_ef_prim_p)
}

///|
fn n_starf_prim(inc : Value, e : Value, prim_p_fn : Value) -> Value raise {
  let inc = num_min(numth__gf_coeff_limit(), inc)
  let mut n = inc
  let n_lim = expt(inc, e)
  while true {
    if num_ge(n, n_lim) {
      return if num_eq(numth__gf_coeff_limit(), inc) {
        q_d_unknown
      } else {
        Nil
      }
    }
    let x = numth__with_char(inc, fn() { gf_n2x(n) })
    if numth__eqi(cadr(x), 2) {
      n = one_minus(num_mul(ash(n, -1), inc)) // go to next monic poly
    } else if funcall(prim_p_fn, [x]).truthy() {
      return x
    }
    n = one_plus(n)
  }
  Nil
}

///|
/// precomputation for *f-prim-p:
fn gf_precomp() -> Value raise {
  n_starf_precomp(
    one_minus(numth__gf_char()),
    numth__gf_ord(),
    symval(q_ear_gf_fs_ord),
  )
}

///|
fn ef_precomp() -> Value raise {
  n_starf_precomp(
    one_minus(numth__gf_card()),
    symval(q_ear_ef_ord),
    symval(q_ear_ef_fs_ord),
  )
}

///|
fn n_starf_precomp(q__1_ : Value, ord : Value, fs_ord : Value) -> Value raise {
  let q_1 = q__1_
  numth__nofaclim(fn() {
    let mut fs_ord = fs_ord
    let mut fs_q_1 = numth__sort_car(get_factor_list(q_1)) // .. [pi, ei] ..
    for fj in fs_q_1.iter() {
      fs_ord = numth__remove_first(fs_ord, sj => num_eq(car(fj), car(sj)))
    }
    fs_q_1 = mapcar(pe => list3(car(pe), t, numth__trunc(q_1, car(pe))), fs_q_1) // .. [pi, true, (p-1)/pi] ..
    fs_ord = mapcar(pe => list2(car(pe), Nil), fs_ord) // .. [pi, false] ..
    let fs_list = numth__merge(fs_q_1, fs_ord, (a, b) => num_lt(car(a), car(b)))
    // qi = ord/pi = sum(aij*p^j, j,0,m)
    if numth__efp() {
      set(q_ear_ef_fsx, vector(list_to_array(fs_list))) |> ignore
      set(
        q_ear_ef_fsx_base_q,
        vector(
          list_to_array(
            mapcar(pe => nreverse(gf_n2l(numth__trunc(ord, car(pe)))), fs_list),
          ),
        ),
      )
      |> ignore
      set(
        q_ear_ef_x_hatq_powers,
        gf_x_hatp_powers(numth__gf_card(), symval(q_ear_ef_exp), numth__ef_red()),
      ) // x^p^j
    } else {
      set(q_ear_gf_fsx, vector(list_to_array(fs_list))) |> ignore
      set(
        q_ear_gf_fsx_base_p,
        vector(
          list_to_array(
            mapcar(pe => nreverse(gf_n2l(numth__trunc(ord, car(pe)))), fs_list),
          ),
        ),
      )
      |> ignore
      set(
        q_ear_gf_x_hatp_powers,
        gf_x_hatp_powers(numth__gf_char(), symval(q_ear_gf_exp), numth__gf_red()),
      ) // x^p^j
    }
  })
}

///|
/// returns an array of polynomials x^p^j, j = 0, 1, .. , (n-1), where
/// n = *gf-exp*
fn gf_x_hatp_powers(q : Value, n : Value, red : Value) -> Value raise {
  let n = to_int(n)
  let a = make_array([n], initial=Nil, elt="list")
  aset1(a, 0, list2(Fix(1L), Fix(1L))) |> ignore // x
  for j in 1..<n {
    aset1(a, j, gf_pow(aref1(a, j - 1), q, red)) |> ignore
  }
  a
}

// Primitive polynomials -------------------------------------------------------

///|
/// test if a is a primitive polynomial over Fq
fn d_gf_primitive_poly_p(a : Value, p? : Value = Nil) -> Value raise {
  let mut p = p
  if p.truthy() {
    if !(integerp(p) && primep(p).truthy()) {
      numth__err("`gf_primitive_poly_p': ~m is not a prime number.", [p])
      |> ignore
    }
  } else {
    gf_char_q(Str("gf_primitive_poly_p")) |> ignore
    p = numth__gf_char()
  }
  numth__ef(Nil, fn() {
    numth__with_char(p, fn() {
      let y = gf_p2x(a) // gf-p2x depends on *gf-char*
      let n = car(y)
      gf_primpoly_p(y, p, n)
    })
  })
}

///|
fn d_ef_primitive_poly_p(y : Value) -> Value raise {
  ef_gf_field_q(Str("ef_primitive_poly_p")) |> ignore
  numth__ef(t, fn() {
    let y = gf_p2x(y)
    gf_primpoly_p(y, numth__gf_card(), car(y))
  })
}

///|
/// `(apply #'vector (mapcar #'(lambda (f) (nreverse (gf-n2l (truncate r f))))
/// fs-r))` with *gf-char* bound to q
fn numth__fs_r_base_q(q : Value, r : Value, fs_r : Value) -> Value raise {
  numth__with_char(q, fn() {
    vector(
      list_to_array(
        mapcar(f => nreverse(gf_n2l(numth__trunc(r, f))), fs_r),
      ),
    )
  })
}

///|
/// based on
/// TOM HANSEN AND GARY L. MULLEN
/// PRIMITIVE POLYNOMIALS OVER FINITE FIELDS
/// (gf-primpoly-p performs a full irreducibility check
///  and therefore doesn't check whether x^((q^n-1)/(q-1)) = (-1)^n * y(0)
///  mod y)
fn gf_primpoly_p(y : Value, q : Value, n : Value) -> Value raise {
  if !numth__eqi(cadr(y), 1) {
    // monic poly assumed
    return Nil
  }
  let fs_q = cfactorw(q)
  with_specials(
    [
      (q_ear_gf_char, car(fs_q)),
      (q_ear_gf_exp, if numth__efp() { cadr(fs_q) } else { n }),
      (q_d_intfaclim, Nil),
    ],
    fn() {
      let q_1 = one_minus(q)
      let mut fs_q_1 : Value = Nil
      let mut const_ = numth__last2(y)
      // the constant part ...
      if !numth__eqi(car(const_), 0) {
        return Nil
      }
      const_ = cadr(const_)
      if oddp(n) {
        const_ = gf_cminus_b(const_) // (-1)^n*const
      }
      // ... must be primitive in Fq:
      let ok = if numth__efp() && num_gt(symval(q_ear_gf_exp), Fix(1L)) {
        let c = const_
        numth__ef(Nil, fn() { gf_prim_p(gf_n2x(c)) })
      } else {
        fs_q_1 = numth__sort_num(mapcar(x => car(x), get_factor_list(q_1)))
        zn_primroot_p(const_, q, q_1, fs_q_1)
      }
      if !ok.truthy() {
        return Nil
      }
      // the linear case:
      if numth__eqi(n, 1) {
        return t
      }
      // y must be irreducible:
      if !gf_irr_p(y, q, n).truthy() {
        return Nil
      }
      // check for all prime factors fi of r = (q^n-1)/(q-1) which do not
      // divide q-1 that x^(r/fi) mod y is not an integer:
      // pre-computation:
      let x_hatq_powers = gf_x_hatp_powers(q, n, y)
      let r = numth__trunc(one_minus(expt(q, n)), q_1)
      let mut fs_r = numth__sort_num(mapcar(x => car(x), get_factor_list(r)))
      if fs_q_1 is Nil {
        fs_q_1 = numth__sort_num(mapcar(x => car(x), get_factor_list(q_1)))
      }
      for fj in fs_q_1.iter() {
        fs_r = numth__remove_first(fs_r, sj => num_eq(fj, sj))
      }
      let fs_r_base_q = numth__fs_r_base_q(q, r, fs_r)
      // check:
      gf_primpoly_p_exit(y, fs_r_base_q, x_hatq_powers)
    },
  )
}

///|
/// uses exponentiation by pre-computation
fn gf_primpoly_p_exit(
  y : Value,
  fs_r_base_q : Value,
  x_hatq_powers : Value,
) -> Value raise {
  let dim = array_dimension(fs_r_base_q, 0)
  for i in 0..<dim {
    let mut j = 0
    let mut zz = list2(Fix(0L), Fix(1L))
    for aij in aref1(fs_r_base_q, i).iter() {
      // fi = sum(aij*q^j, j,0,n-1)
      let z = gf_pow(aref1(x_hatq_powers, j), aij, y)
      zz = gf_times(zz, z, y)
      j += 1
    }
    if numth__eqi(car(zz), 0) {
      return Nil
    }
  }
  t
}

///|
/// find a primitive polynomial
fn d_gf_primitive_poly(p : Value, n : Value) -> Value raise {
  if !(integerp(p) && primep(p).truthy() && integerp(n)) {
    numth__err("`gf_primitive_poly' needs a prime number and an integer.", [])
    |> ignore
  }
  gf_set_rat_header() |> ignore
  numth__ef(Nil, fn() {
    numth__with_char(p, fn() { gf_x2p(gf_primpoly(p, n)) }) // gf-x2p needs *gf-char*
  })
}

///|
fn d_ef_primitive_poly(n : Value) -> Value raise {
  ef_gf_field_q(Str("ef_primitive_poly")) |> ignore
  numth__ef(t, fn() { gf_x2p(gf_primpoly(numth__gf_card(), n)) })
}

///|
fn gf_primpoly(q : Value, n : Value) -> Value raise {
  let fs_q = cfactorw(q)
  with_specials(
    [
      (q_ear_gf_char, car(fs_q)),
      (q_ear_gf_exp, if numth__efp() { cadr(fs_q) } else { n }),
      (q_d_intfaclim, Nil),
    ],
    fn() {
      let q_1 = one_minus(q)
      let fs_q_1 = numth__sort_num(mapcar(x => car(x), get_factor_list(q_1)))
      // the linear case:
      if numth__eqi(n, 1) {
        let prt : Value = if numth__eqi(q, 2) {
          Fix(1L)
        } else {
          zn_primroot(q, q_1, fs_q_1)
        }
        return list([Fix(1L), Fix(1L), Fix(0L), gf_cminus_b(prt)])
      }
      // pre-computation part 1:
      let r = numth__trunc(one_minus(expt(q, n)), q_1)
      let mut fs_r = numth__sort_num(mapcar(x => car(x), get_factor_list(r)))
      for fj in fs_q_1.iter() {
        fs_r = numth__remove_first(fs_r, sj => num_eq(fj, sj))
      }
      let fs_r_base_q = numth__fs_r_base_q(q, r, fs_r)
      // search:
      let inc = num_min(numth__gf_coeff_limit(), q)
      let i_lim = expt(inc, n)
      let mut i = one_plus(inc)
      while true {
        if num_ge(i, i_lim) {
          return numth__err(
            "No primitive polynomial found.~%~\n                                      `gf_coeff_limit' might be too small.~%",
            [],
          )
        }
        let i0 = i
        let x = numth__with_char(inc, fn() { gf_n2x(i0) })
        let x = cons(n, cons(Fix(1L), x))
        if gf_primpoly_p2(
            x,
            numth__gf_char(),
            symval(q_ear_gf_exp),
            q,
            n,
            fs_q_1,
            fs_r_base_q,
          ).truthy() {
          return x
        }
        i = one_plus(i)
      }
      Nil
    },
  )
}

///|
fn gf_primpoly_p2(
  y : Value,
  p : Value,
  e : Value,
  q : Value,
  n : Value,
  fs_q_1 : Value,
  fs_r_base_q : Value,
) -> Value raise {
  if !numth__eqi(cadr(y), 1) {
    // monic poly assumed
    return Nil
  }
  with_specials([(q_ear_gf_char, p), (q_ear_gf_exp, e)], fn() {
    let q_1 = one_minus(q)
    let mut const_ = numth__last2(y)
    // the constant part ...
    if !numth__eqi(car(const_), 0) {
      return Nil
    }
    const_ = cadr(const_)
    if oddp(n) {
      const_ = gf_cminus_b(const_) // (-1)^n*const
    }
    // ... must be primitive in Fq:
    let ok = if numth__efp() && num_gt(symval(q_ear_gf_exp), Fix(1L)) {
      let c = const_
      numth__ef(Nil, fn() { gf_prim_p(gf_n2x(c)) })
    } else {
      zn_primroot_p(const_, q, q_1, fs_q_1)
    }
    if !ok.truthy() {
      return Nil
    }
    // y must be irreducible:
    if !gf_irr_p(y, q, n).truthy() {
      return Nil
    }
    // y dependent pre-computation and final check:
    gf_primpoly_p_exit(y, fs_r_base_q, gf_x_hatp_powers(q, n, y))
  })
}

// random elements -------------------------------------------------------------

///|
/// Produces a random element within the given environment
fn d_gf_random(p? : Value = Nil, n? : Value = Nil) -> Value raise {
  numth__ef(t, fn() {
    if n.truthy() {
      numth__with_char(p, fn() {
        if !symval(q_ear_gf_red_q).truthy() {
          gf_set_rat_header() |> ignore
        }
        gf_x2p(gf_random(p, n))
      })
    } else {
      gf_data_q(Str("gf_random")) |> ignore
      gf_x2p(gf_random(numth__gf_char(), symval(q_ear_gf_exp)))
    }
  })
}

///|
fn d_ef_random(q? : Value = Nil, n? : Value = Nil) -> Value raise {
  numth__ef(t, fn() {
    if n.truthy() {
      numth__with_char(q, fn() { gf_x2p(gf_random(q, n)) })
    } else {
      ef_data_q(Str("ef_random")) |> ignore
      gf_x2p(gf_random(numth__gf_card(), symval(q_ear_ef_exp)))
    }
  })
}

///|
/// (CL `random` is implemented by the MT19937 generator of the port.)
fn gf_random(q : Value, n : Value) -> Value raise {
  let mut e : Value = Fix(0L)
  let mut x : Value = Nil
  while !num_eq(e, n) {
    let c = mt_random(q)
    if !numth__eqi(c, 0) {
      x = cons(e, cons(c, x))
    }
    e = one_plus(e)
  }
  x
}

// factoring -------------------------------------------------------------------

///|
/// set p to switch to another modulus
fn d_gf_factor(a : Value, p? : Value = Nil) -> Value raise {
  let mut p = p
  if p.truthy() {
    if !(integerp(p) && primep(p).truthy()) {
      numth__err("`gf_factor': Second argument must be a prime number.", [])
      |> ignore
    }
    gf_set_rat_header() |> ignore
  } else {
    gf_char_q(Str("gf_factor")) |> ignore
    p = numth__gf_char()
  }
  with_specials([(q_ear_gf_char, p), (q_modulus, p)], fn() {
    let a = d_rat(a, Nil)
    numth__ef(Nil, fn() {
      if length(caddar(a)) > 1 {
        numth__err("`gf_factor': Polynomial must be univariate.", []) |> ignore
      }
      let a = cadr(a)
      if integerp(a) {
        num_mod(a, numth__gf_char())
      } else {
        let a = if symval(q_d_gf_cantor_zassenhaus).truthy() {
          gf_factor(gf_mod(cdr(a)), p)
        } else {
          gf_ns2pmod_factors(pfactor(a))
        }
        let mut a = gf_disrep_factors(a)
        if consp(a) && consp(car(a)) && equal(caar(a), q_mtimes) {
          a = simplifya(cons(list1(q_mtimes), cdr(a)), Nil)
        }
        a
      }
    })
  })
}

///|
/// adjust results from rat3d/pfactor to a positive modulus if $gf_balanced =
/// false (modifies fs)
fn gf_ns2pmod_factors(fs : Value) -> Value raise {
  if symval(q_d_gf_balanced).truthy() {
    return fs
  }
  let m = numth__gf_char()
  let mut r = fs
  while r is Cons(_) {
    if integerp(car(r)) {
      if minusp(car(r)) {
        rplaca(r, num_add(car(r), m)) |> ignore // only in the case *ef-arith?* = false
      }
    } else {
      rplaca(r, gf_ns2pmod_factor(cdar(r), m)) |> ignore
    }
    r = cddr(r)
  }
  fs
}

///|
fn gf_ns2pmod_factor(fac : Value, m : Value) -> Value raise {
  let mut r = cdr(fac)
  while true {
    if minusp(car(r)) {
      rplaca(r, num_add(car(r), m)) |> ignore
    }
    if cdr(r) is Nil {
      return fac
    }
    r = cddr(r)
  }
  fac
}

///|
fn gf_disrep_factors(fs : Value) -> Value raise {
  if integerp(fs) {
    return gf_cp2smod(fs)
  }
  let mut fs = nreverse(fs)
  let mut p : Value = Nil
  while fs is Cons(_) {
    let e = car(fs)
    let fac = cadr(fs)
    fs = cddr(fs)
    p = if integerp(fac) {
      cons(gf_cp2smod(fac), p)
    } else if numth__eqi(e, 1) {
      cons(gf_disrep(gf_np2smod(fac)), p)
    } else {
      cons(
        list3(list2(q_mexpt, q_simp), gf_disrep(gf_np2smod(fac)), e),
        p,
      )
    }
  }
  cons(list3(q_mtimes, q_simp, q_factored), p)
}

///|
fn d_ef_factor(a : Value) -> Value raise {
  ef_gf_field_q(Str("ef_factor")) |> ignore
  numth__ef(t, fn() {
    let a = numth__with_modulus(Nil, fn() { d_rat(a, Nil) })
    if length(caddar(a)) > 1 {
      numth__err("`ef_factor': Polynomial must be univariate.", []) |> ignore
    }
    let a = cadr(a)
    if integerp(a) {
      ef_cmod(a)
    } else {
      let mut a = gf_disrep_factors(
        gf_factor(gf_mod(cdr(a)), numth__gf_card()),
      )
      if consp(a) && consp(car(a)) && equal(caar(a), q_mtimes) {
        a = simplifya(cons(list1(q_mtimes), cdr(a)), Nil)
      }
      a
    }
  })
}

///|
/// non-integer x
fn gf_factor(x : Value, q : Value) -> Value raise {
  let lc = cadr(x)
  let mut x = x
  let mut z : Value = Nil
  if !numth__eqi(lc, 1) {
    x = gf_xctimes(x, gf_cinv(lc)) // monicize x
  }
  if gf_irr_p(x, q, car(x)).truthy() {
    z = list2(x, Fix(1L))
  } else {
    let sqfr = gf_square_free(x)
    for v in sqfr.iter() {
      let e = car(v)
      let y = cadr(v)
      let y = gf_distinct_degree_factors(y, q)
      for w in y.iter() {
        z = nconc(gf_equal_degree_factors(w, q, e), z)
      }
    }
  }
  if numth__eqi(lc, 1) {
    z
  } else {
    cons(lc, cons(Fix(1L), z))
  }
}

///|
fn gf_diff(x : Value) -> Value raise {
  if x is Nil {
    return Nil
  }
  let m = numth__gf_char()
  let mut rx = x
  let mut res : Value = Nil
  while !(rx is Nil || numth__eqi(car(rx), 0)) {
    let c = gf_ctimes(num_mod(car(rx), m), cadr(rx))
    if !numth__eqi(c, 0) {
      res = cons(one_minus(car(rx)), res)
      res = cons(c, res)
    }
    rx = cddr(rx)
  }
  nreverse(res)
}

///|
/// c -> c^p^(n-1)
fn ef_pth_croot(c : Value) -> Value raise {
  let p = numth__gf_char()
  numth__ef(t, fn() {
    let mut c = c
    let mut i : Value = Fix(0L)
    let n = one_minus(symval(q_ear_gf_exp))
    while num_lt(i, n) {
      c = gf_cpow(c, p)
      i = one_plus(i)
    }
    c
  })
}

///|
fn gf_pth_root(x : Value) -> Value raise {
  let p = numth__gf_char()
  if x is Nil {
    return Nil
  }
  let mut rx = x
  let mut res : Value = Nil
  while rx is Cons(_) {
    res = cons(numth__trunc(car(rx), p), res)
    let mut c = cadr(rx)
    if numth__efp() {
      // p # q
      c = ef_pth_croot(c)
    }
    res = cons(c, res)
    rx = cddr(rx)
  }
  nreverse(res)
}

///|
fn gf_gcd_cofactors(x : Value, dx : Value) -> (Value, Value, Value) raise {
  let g = gf_gcd(x, dx)
  let a = gf_divide(x, g).0
  let b = gf_divide(dx, g).0
  (g, a, b)
}

///|
/// monic x
fn gf_square_free(x : Value) -> Value raise {
  let mut x = x
  let mut fs : Value = Nil
  let mut r = gf_diff(x)
  let g = gf_gcd(x, r)
  if numth__is_one(g) {
    return list1(list2(Fix(1L), x))
  }
  if r.truthy() {
    // # 0
    r = gf_divide(x, g).0
    x = g // d.h. x # 1
    let mut m = 1
    while !numth__is_one(r) {
      let (r1, f, x1) = gf_gcd_cofactors(r, x)
      r = r1
      x = x1
      if !numth__is_one(f) {
        fs = cons(list2(numth__i(m), f), fs)
      }
      m += 1
    }
  }
  if !numth__is_one(x) {
    fs = append(
      mapcar(
        v => rplaca(v, num_mul(car(v), numth__gf_char())),
        gf_square_free(gf_pth_root(x)),
      ),
      fs,
    )
  }
  nreverse(fs)
}

///|
fn gf_distinct_degree_factors(x : Value, q : Value) -> Value raise {
  let mut w = list2(Fix(1L), Fix(1L))
  let mut fs : Value = Nil
  let mut x = x
  numth__with_char(car(cfactorw(q)), fn() {
    let mut n = 1
    while !numth__is_one(x) {
      if num_gt(numth__i(n << 1), car(x)) {
        fs = cons(list2(x, car(x)), fs)
        break
      }
      w = gf_nred(w, x)
      w = gf_pow(w, q, x)
      let f = gf_gcd(gf_plus(w, gf_nminus(list2(Fix(1L), Fix(1L)))), x)
      if !numth__is_one(f) {
        fs = cons(list2(f, numth__i(n)), fs)
        x = gf_divide(x, f).0
      }
      n += 1
    }
    nreverse(fs)
  })
}

///|
fn gf_nonconst_random(q : Value, q_hatn_ : Value) -> Value raise {
  while true {
    let r = mt_random(q_hatn_)
    if num_ge(r, q) {
      return numth__with_char(q, fn() { gf_n2x(r) })
    }
  }
  Nil
}

///|
/// computes Tm(x) = x^2^(m-1) + x^2^(m-2) + .. + x^4 + x^2 + x in F2[x]
/// m > 0
fn gf_trace_poly_f2(x : Value, m : Value, red : Value) -> Value raise {
  let mut x = x
  let mut tm = gf_nred(x, red)
  let mut i : Value = Fix(1L)
  while !num_eq(i, m) {
    x = gf_sq(x, red)
    tm = gf_plus(tm, x)
    i = one_plus(i)
  }
  tm
}

///|
/// Cantor and Zassenhaus' algorithm
fn gf_equal_degree_factors(x_and_d : Value, q : Value, mult : Value) -> Value raise {
  let x = car(x_and_d)
  let d = cadr(x_and_d)
  let n = car(x)
  if num_eq(n, d) {
    return list2(x, mult)
  }
  let p_k = cfactorw(q)
  let p = car(p_k)
  let k = cadr(p_k)
  numth__with_char(p, fn() {
    let mut f = list2(Fix(0L), Fix(1L))
    let q_n = expt(q, n)
    let mut m : Value = Nil
    let mut e : Value = Nil
    if numth__eqi(p, 2) {
      m = num_mul(k, d) // q = 2^k
    } else {
      e = ash(one_minus(expt(q, d)), -1)
    }
    while !(!numth__is_one(f) && !equal(x, f)) {
      let r = gf_nonconst_random(q, q_n)
      f = gf_gcd(x, r)
      if numth__is_one(f) {
        let r_e = if numth__eqi(p, 2) {
          gf_trace_poly_f2(r, m, x) // q = 2^k
        } else {
          gf_pow(r, e, x)
        } // q is odd prime power
        f = gf_gcd(x, gf_nplus(r_e, gf_nminus(list2(Fix(0L), Fix(1L)))))
      }
    }
    append(
      gf_equal_degree_factors(list2(gf_divide(x, f).0, d), q, mult),
      gf_equal_degree_factors(list2(f, d), q, mult),
    )
  })
}

// gcd, gcdex and test of invertibility ----------------------------------------

///|
fn d_ef_gcd(a : Value, b : Value) -> Value raise {
  ef_gf_field_q(Str("ef_gcd")) |> ignore
  numth__ef(t, fn() { gf_x2p(gf_gcd(gf_p2x(a), gf_p2x(b))) })
}

///|
fn d_gf_gcd(a : Value, b : Value, p? : Value = Nil) -> Value raise {
  numth__ef(Nil, fn() {
    if p.truthy() {
      if !(integerp(p) && primep(p).truthy()) {
        numth__err("`gf_gcd': ~m is not a prime number.", [p]) |> ignore
      }
      gf_set_rat_header() |> ignore
      with_specials([(q_ear_gf_char, p), (q_modulus, p)], fn() {
        let vars = caddar(d_rat(a, Nil))
        if length(vars) > 1 {
          numth__err("`gf_gcd': Polynomials must be univariate.", []) |> ignore
        }
        gf_x2p(gf_gcd(gf_p2x(a), gf_p2x(b)))
      })
    } else {
      gf_char_q(Str("gf_gcd")) |> ignore
      gf_x2p(gf_gcd(gf_p2x(a), gf_p2x(b)))
    }
  })
}

///|
fn d_gf_gcdex(a : Value, b : Value) -> Value raise {
  gf_red_q(Str("gf_gcdex")) |> ignore
  numth__ef(Nil, fn() {
    cons(
      numth__mlist(),
      mapcar(x => gf_x2p(x), gf_gcdex(gf_p2x(a), gf_p2x(b), numth__gf_red())),
    )
  })
}

///|
fn d_ef_gcdex(a : Value, b : Value) -> Value raise {
  ef_red_q(Str("ef_gcdex")) |> ignore
  numth__ef(t, fn() {
    cons(
      numth__mlist(),
      mapcar(x => gf_x2p(x), gf_gcdex(gf_p2x(a), gf_p2x(b), numth__gf_red())),
    )
  })
}

///|
fn d_gf_unit_p(a : Value) -> Value raise {
  gf_red_q(Str("gf_unit_p")) |> ignore
  numth__ef(Nil, fn() { gf_unit_p(gf_p2x(a), numth__gf_red()) })
}

///|
fn d_ef_unit_p(a : Value) -> Value raise {
  ef_red_q(Str("ef_unit_p")) |> ignore
  numth__ef(t, fn() { gf_unit_p(gf_p2x(a), numth__ef_red()) })
}

///|
fn gf_unit_p(x : Value, red : Value) -> Value raise {
  lbool(num_eq(Fix(0L), car(gf_gcd(x, red))))
}

// order -----------------------------------------------------------------------

///|
/// group/element order
fn d_gf_order(a? : Value = Nil) -> Value raise {
  gf_data_q(Str("gf_order")) |> ignore
  if a.truthy() {
    numth__ef(Nil, fn() {
      let a = gf_p2x(a)
      if a.truthy() &&
        (symval(q_ear_gf_irred_q).truthy() ||
        gf_unit_p(a, numth__gf_red()).truthy()) {
        gf_ord(a, numth__gf_ord(), symval(q_ear_gf_fs_ord), numth__gf_red())
      } else {
        Nil
      }
    })
  } else {
    numth__gf_ord()
  }
}

///|
fn d_ef_order(a? : Value = Nil) -> Value raise {
  ef_data_q(Str("ef_order")) |> ignore
  if a.truthy() {
    numth__ef(t, fn() {
      let a = gf_p2x(a)
      if a.truthy() &&
        (symval(q_ear_ef_irred_q).truthy() ||
        gf_unit_p(a, numth__ef_red()).truthy()) {
        gf_ord(
          a,
          symval(q_ear_ef_ord),
          symval(q_ear_ef_fs_ord),
          numth__ef_red(),
        )
      } else {
        Nil
      }
    })
  } else {
    symval(q_ear_ef_ord)
  }
}

///|
/// find the lowest value k for which a^k = 1 (assume x # 0)
fn gf_ord(x : Value, ord : Value, fs_ord : Value, red : Value) -> Value raise {
  let mut ord = ord
  for pe in fs_ord.iter() {
    let p = car(pe)
    let mut e = cadr(pe)
    ord = numth__trunc(ord, expt(p, e))
    let mut z = gf_pow_dol(x, ord, red) // use exponentiation by precomputation
    while !numth__is_one(z) {
      ord = num_mul(ord, p)
      if numth__eqi(e, 1) {
        break
      }
      e = one_minus(e)
      z = gf_pow_dol(z, p, red)
    }
  }
  ord
}

///|
fn gf_ord_by_table(x : Value) -> Value raise {
  let index = numth__svref(symval(q_d_gf_logs), gf_x2n(x))
  numth__trunc(numth__gf_ord(), num_gcd(numth__gf_ord(), index))
}

///|
/// Fq^n = F[x]/(f) is no field <=> f splits into factors
///
///   f = f1^e1 * ... * fk^ek where fi are irreducible of degree ni.
///
/// We compute the order of the group (F[x]/(fi^ei))* by
///
///   ((q^ni)^ei - (q^ni)^(ei-1)) = ((q^ni) - 1) * (q^ni)^(ei-1)
///
/// and ord((Fq^n)*) with help of the Chinese Remainder Theorem.
fn gf_group_order(q : Value, red : Value) -> Value raise {
  let mut ne_list : Value = Nil
  let mut ord : Value = Fix(1L)
  let mut x = gf_factor(red, q) // red is assumed to be a monic poly
  while x is Cons(_) {
    ne_list = cons(list2(caar(x), cadr(x)), ne_list) // (list ni ei), f = prod(fi^ei) with fi of degree ni
    x = cddr(x)
  }
  for a in ne_list.iter() {
    let q_n = expt(q, car(a))
    let e = cadr(a)
    ord = num_mul(ord, num_mul(one_minus(q_n), expt(q_n, one_minus(e))))
  }
  ord
}

// degree, minimal polynomial, trace and norm ----------------------------------

///|
/// degree: Find the lowest value d for which x^(q^d) = x
fn gf_degree_errchk(a : Value, n : Value, fun : Value) -> Value raise {
  if a.truthy() && num_ge(car(a), n) {
    numth__err("`~m': Leading exponent must be smaller than ~m.", [fun, n])
  } else {
    Nil
  }
}

///|
fn d_gf_degree(a : Value) -> Value raise {
  gf_field_q(Str("gf_degree")) |> ignore
  numth__ef(Nil, fn() {
    let a = gf_p2x(a)
    gf_degree_errchk(a, symval(q_ear_gf_exp), Str("gf_degree")) |> ignore
    n_starf_deg(
      a,
      symval(q_ear_gf_exp),
      numth__gf_red(),
      symval(q_ear_gf_x_hatp_powers),
    )
  })
}

///|
fn d_ef_degree(a : Value) -> Value raise {
  ef_field_q(Str("ef_degree")) |> ignore
  numth__ef(t, fn() {
    let a = gf_p2x(a)
    gf_degree_errchk(a, symval(q_ear_ef_exp), Str("ef_degree")) |> ignore
    n_starf_deg(
      a,
      symval(q_ear_ef_exp),
      numth__ef_red(),
      symval(q_ear_ef_x_hatq_powers),
    )
  })
}

///|
fn n_starf_deg(x : Value, n : Value, red : Value, x_hatq_powers : Value) -> Value raise {
  let mut d = 1
  while !numth__eqi(n, d) {
    if equal(x, gf_compose(aref1(x_hatq_powers, d), x, red)) {
      // f(x)^q = f(x^q)
      return numth__i(d)
    }
    d += 1
  }
  numth__i(d)
}

///|
/// produce the minimal polynomial
fn d_gf_minimal_poly(a : Value) -> Value raise {
  gf_field_q(Str("gf_minimal_poly")) |> ignore
  numth__ef(Nil, fn() {
    let a = gf_p2x(a)
    gf_degree_errchk(a, symval(q_ear_gf_exp), Str("gf_minimal_poly")) |> ignore
    gf_minpoly(a, numth__gf_red(), symval(q_ear_gf_x_hatp_powers))
  })
}

///|
fn d_ef_minimal_poly(a : Value) -> Value raise {
  ef_field_q(Str("ef_minimal_poly")) |> ignore
  numth__ef(t, fn() {
    let a = gf_p2x(a)
    gf_degree_errchk(a, symval(q_ear_ef_exp), Str("ef_minimal_poly")) |> ignore
    gf_minpoly(a, numth__ef_red(), symval(q_ear_ef_x_hatq_powers))
  })
}

///|
///                                  2             (d-1)
///                        q        q             q
///   f(z) = (z - x) (z - x ) (z - x  ) ... (z - x  )   , where d = degree(x)
fn gf_minpoly(x : Value, red : Value, x_hatq_powers : Value) -> Value raise {
  if x is Nil {
    return q_d_z
  }
  let n = to_int(car(red))
  let mut powers = list1(gf_minus(x))
  let mut prod = list2(Fix(0L), list2(Fix(0L), Fix(1L)))
  for i in 1..<n {
    let xqi = gf_compose(aref1(x_hatq_powers, i), x, red)
    if equal(x, xqi) {
      break
    }
    powers = cons(gf_nminus(xqi), powers)
  }
  for pow in powers.iter() {
    let zx = gf_zx(prod)
    let cx = gf_ncx(pow, prod, red)
    prod = gf_nzx_pluscx(zx, cx)
  }
  d_substitute(q_d_z, q_d_x, expr=gf_x2p(gf_nxx2x(prod)))
}

///|
/// (gf-zx '(3 (5 1 3 1) 2 (4 1))) -> (4 (5 1 3 1) 3 (4 1))
///          3  5   3     2  4         4  5   3     3  4
///         z (x + x ) + z  x      -> z (x + x ) + z  x
fn gf_zx(x : Value) -> Value raise {
  let res = list2(one_plus(car(x)), cadr(x))
  let mut r = cdr(res)
  let mut rx = cddr(x)
  while rx is Cons(_) {
    rplacd(r, list2(one_plus(car(rx)), cadr(rx))) |> ignore
    r = cddr(r)
    rx = cddr(rx)
  }
  res
}

///|
/// modifies x
/// (gf-ncx '(1 1) '(3 (4 1 3 1) 2 (2 1)) '(6 1))
///    -> (3 (5 1 4 1) 2 (3 1))
fn gf_ncx(c : Value, x : Value, red : Value) -> Value raise {
  if c is Nil {
    return c
  }
  let mut r = cdr(x)
  while r is Cons(_) {
    rplaca(r, gf_times(c, car(r), red)) |> ignore
    r = cddr(r)
  }
  x
}

///|
/// modifies zx
fn gf_nzx_pluscx(zx : Value, cx : Value) -> Value raise {
  let mut r = cdr(zx)
  let mut s = cdr(cx)
  while cdr(r).truthy() {
    let r_s = gf_plus(caddr(r), car(s))
    if r_s.truthy() {
      r = cddr(r)
      rplaca(r, r_s) |> ignore
    } else {
      rplacd(r, cdddr(r)) |> ignore
    }
    s = cddr(s)
  }
  nconc(zx, list2(Fix(0L), car(s)))
}

///|
/// modifies xx
/// (gf-nxx2x '(4 (0 3) 2 (0 1))) -> (4 3 2 1)
fn gf_nxx2x(xx : Value) -> Value raise {
  let mut r = cdr(xx)
  while r is Cons(_) {
    rplaca(r, cadar(r)) |> ignore
    r = cddr(r)
  }
  xx
}

///|
///                      2         (n-1)
///                 q   q         q
/// trace(a) = a + a + a  + .. + a
fn d_gf_trace(a : Value) -> Value raise {
  gf_field_q(Str("gf_trace")) |> ignore
  numth__ef(Nil, fn() {
    gf_trace(gf_p2x(a), numth__gf_red(), symval(q_ear_gf_x_hatp_powers))
  })
}

///|
fn d_ef_trace(a : Value) -> Value raise {
  ef_field_q(Str("ef_trace")) |> ignore
  numth__ef(t, fn() {
    gf_trace(gf_p2x(a), numth__ef_red(), symval(q_ear_ef_x_hatq_powers))
  })
}

///|
fn gf_trace(x : Value, red : Value, x_hatq_powers : Value) -> Value raise {
  let n = to_int(car(red))
  let mut su = x
  for i in 1..<n {
    su = gf_plus(su, gf_compose(aref1(x_hatq_powers, i), x, red))
  }
  gf_x2p(su)
}

///|
///                     2        (n-1)      n                         2         (n-1)
///            1 + q + q + .. + q         (q - 1)/(q - 1)        q   q         q
/// norm(a) = a                        = a                = a * a * a  * .. * a
fn d_gf_norm(a : Value) -> Value raise {
  gf_field_q(Str("gf_norm")) |> ignore
  numth__ef(Nil, fn() {
    gf_norm(gf_p2x(a), numth__gf_red(), symval(q_ear_gf_x_hatp_powers))
  })
}

///|
fn d_ef_norm(a : Value) -> Value raise {
  ef_field_q(Str("ef_norm")) |> ignore
  numth__ef(t, fn() {
    gf_norm(gf_p2x(a), numth__ef_red(), symval(q_ear_ef_x_hatq_powers))
  })
}

///|
fn gf_norm(x : Value, red : Value, x_hatq_powers : Value) -> Value raise {
  let n = to_int(car(red))
  let mut prod = x
  for i in 1..<n {
    prod = gf_times(prod, gf_compose(aref1(x_hatq_powers, i), x, red), red)
  }
  gf_x2p(prod)
}

// normal elements and normal basis --------------------------------------------

///|
/// Tests if an element is normal
fn d_gf_normal_p(a : Value) -> Value raise {
  gf_field_q(Str("gf_normal_p")) |> ignore
  numth__ef(Nil, fn() { gf_normal_p(gf_p2x(a)) })
}

///|
fn gf_normal_p(x : Value) -> Value raise {
  if x is Nil {
    return Nil
  }
  let mat = gf_maybe_normal_basis(x)
  numth__with_modulus(numth__gf_char(), fn() {
    lbool(equal(d_rank(mat), symval(q_ear_gf_exp)))
  })
}

///|
fn d_ef_normal_p(a : Value) -> Value raise {
  ef_field_q(Str("ef_normal_p")) |> ignore
  numth__ef(t, fn() { ef_normal_p(gf_p2x(a)) })
}

///|
fn ef_normal_p(x : Value) -> Value raise {
  if x is Nil {
    return Nil
  }
  let mat = ef_maybe_normal_basis(x)
  lbool(!num_eq(Fix(0L), d_ef_determinant(mat)))
}

///|
/// Finds a normal element e in the field; that is,
/// an element for which the list [e, e^q, e^(q^2), ... , e^(q^(n-1))] is a
/// basis
fn d_gf_normal() -> Value raise {
  gf_field_q(Str("gf_normal")) |> ignore
  numth__ef(Nil, fn() {
    gf_x2p(gf_normal(numth__gf_char(), symval(q_ear_gf_exp), q_gf_normal_p))
  })
}

///|
fn d_ef_normal() -> Value raise {
  ef_field_q(Str("ef_normal")) |> ignore
  numth__ef(t, fn() {
    gf_x2p(gf_normal(numth__gf_card(), symval(q_ear_ef_exp), q_ef_normal_p))
  })
}

///|
fn gf_normal(q : Value, n : Value, normal_p_fn : Value) -> Value raise {
  let inc = num_min(numth__gf_coeff_limit(), q)
  let i_lim = expt(inc, n)
  let mut i = inc
  while true {
    if num_ge(i, i_lim) {
      return numth__err(
        "No normal element found.~%~\n                                    `gf_coeff_limit' might be too small.~%",
        [],
      )
    }
    let i0 = i
    let x = numth__with_char(inc, fn() { gf_n2x(i0) })
    if funcall(normal_p_fn, [x]).truthy() {
      return x
    }
    i = one_plus(i)
  }
  Nil
}

///|
/// Finds a normal element in the field by producing random elements and
/// checking if each one is normal
fn d_gf_random_normal() -> Value raise {
  gf_field_q(Str("gf_random_normal")) |> ignore
  numth__ef(Nil, fn() { gf_x2p(gf_random_normal()) })
}

///|
fn gf_random_normal() -> Value raise {
  let mut x = gf_random(numth__gf_char(), symval(q_ear_gf_exp))
  while !gf_normal_p(x).truthy() {
    x = gf_random(numth__gf_char(), symval(q_ear_gf_exp))
  }
  x
}

///|
fn d_ef_random_normal() -> Value raise {
  ef_field_q(Str("ef_random_normal")) |> ignore
  numth__ef(t, fn() { gf_x2p(ef_random_normal()) })
}

///|
fn ef_random_normal() -> Value raise {
  let mut x = gf_random(numth__gf_card(), symval(q_ear_ef_exp))
  while !ef_normal_p(x).truthy() {
    x = gf_random(numth__gf_card(), symval(q_ear_ef_exp))
  }
  x
}

///|
/// Produces a normal basis as a matrix;
/// the columns are the coefficients of the powers e^(q^i) of the normal
/// element
fn d_gf_normal_basis(a : Value) -> Value raise {
  gf_field_q(Str("gf_normal_basis")) |> ignore
  numth__ef(Nil, fn() {
    let x = gf_p2x(a)
    numth__with_modulus(numth__gf_char(), fn() {
      let mat = gf_maybe_normal_basis(x)
      if !equal(d_rank(mat), symval(q_ear_gf_exp)) {
        numth__err(
          "Argument to `gf_normal_basis' must be a normal element.",
          [],
        )
        |> ignore
      }
      mat
    })
  })
}

///|
fn d_ef_normal_basis(a : Value) -> Value raise {
  ef_field_q(Str("ef_normal_basis")) |> ignore
  numth__ef(t, fn() {
    let mat = ef_maybe_normal_basis(gf_p2x(a))
    if !!num_eq(Fix(0L), d_ef_determinant(mat)) {
      merr("Argument to `ef_normal_basis' must be a normal element.", [])
      |> ignore
    }
    mat
  })
}

///|
fn gf_maybe_normal_basis(x : Value) -> Value raise {
  n_starf_maybe_normal_basis(
    x,
    symval(q_ear_gf_x_hatp_powers),
    symval(q_ear_gf_exp),
    numth__gf_red(),
  )
}

///|
fn ef_maybe_normal_basis(x : Value) -> Value raise {
  n_starf_maybe_normal_basis(
    x,
    symval(q_ear_ef_x_hatq_powers),
    symval(q_ear_ef_exp),
    numth__ef_red(),
  )
}

///|
fn n_starf_maybe_normal_basis(
  x : Value,
  x_hatq_powers : Value,
  e : Value,
  red : Value,
) -> Value raise {
  let e_1 = one_minus(e)
  d_transpose(
    d_genmatrix(
      lfunc("*f-maybe-normal-basis", args => {
        let i = to_int(args[0])
        let j = to_int(args[1])
        aref1(
          gf_x2array(gf_compose(aref1(x_hatq_powers, i - 1), x, red), e_1),
          j - 1,
        )
      }),
      e,
      j2=e,
    ),
  )
}

///|
/// coefficients as an array of designated length
fn gf_x2array(x : Value, len : Value) -> Value raise {
  let len = to_int(len)
  let cs = make_array([len + 1], initial=Fix(0L))
  let mut k = len
  let mut x = x
  while x is Cons(_) {
    let ex = to_int(car(x))
    if k > ex {
      k -= 1
    } else if k == ex {
      aset1(cs, len - k, cadr(x)) |> ignore
      x = cddr(x)
      k -= 1
    } else {
      x = cddr(x)
    }
  }
  cs
}

///|
/// Produces the normal representation of an element as a list of
/// coefficients.  Needs the inverted normal basis as the second argument
/// (the inversion might be time consuming)
fn d_gf_normal_basis_rep(a : Value, m_inv : Value) -> Value raise {
  gf_field_q(Str("gf_normal_basis_rep")) |> ignore
  numth__ef(Nil, fn() {
    gf_normal_basis_rep(gf_p2x(a), m_inv, symval(q_ear_gf_exp), q_d_gf_matmult)
  })
}

///|
fn d_ef_normal_basis_rep(a : Value, m_inv : Value) -> Value raise {
  ef_field_q(Str("ef_normal_basis_rep")) |> ignore
  numth__ef(t, fn() {
    gf_normal_basis_rep(gf_p2x(a), m_inv, symval(q_ear_ef_exp), q_d_ef_matmult)
  })
}

///|
fn gf_normal_basis_rep(
  x : Value,
  m_inv : Value,
  e : Value,
  matmult_fn : Value,
) -> Value raise {
  let cs = cons(numth__mlist(), gf_x2l(x, e))
  let nbrep = mfuncall(matmult_fn, list2(m_inv, cs))
  cons(numth__mlist(), mapcar(x => cadr(x), cdr(nbrep)))
}

// functions for matrices ------------------------------------------------------

///|
fn d_gf_matneg(m : Value) -> Value raise {
  gf_char_q(Str("gf_matneg")) |> ignore
  mfuncall(q_d_matrixmap, list2(q_d_gf_neg, m))
}

///|
fn d_ef_matneg(m : Value) -> Value raise {
  ef_gf_field_q(Str("ef_matneg")) |> ignore
  mfuncall(q_d_matrixmap, list2(q_d_ef_neg, m))
}

///|
/// matrix addition (convenience: mat, list or poly possible as argument)
fn d_gf_matadd(args : Value) -> Value raise {
  numth__ef(Nil, fn() {
    reduce((m1, m2) => gf_matadd(m1, m2, q_d_gf_add), args)
  })
}

///|
fn d_ef_matadd(args : Value) -> Value raise {
  gf_data_q(Str("ef_matadd")) |> ignore
  numth__ef(t, fn() {
    reduce((m1, m2) => gf_matadd(m1, m2, q_d_ef_add), args)
  })
}

///|
fn gf_matadd(m1 : Value, m2 : Value, add_fn : Value) -> Value raise {
  let mut m1 = m1
  let mut m2 = m2
  if d_listp(m1).truthy() {
    m1 = d_transpose(m1)
  }
  if d_listp(m2).truthy() {
    m2 = d_transpose(m2)
  }
  if d_matrixp(m1).truthy() && d_matrixp(m2).truthy() {
    gf_matadd2(m1, m2, add_fn)
  } else if d_matrixp(m1).truthy() {
    gf_matadd1(m1, m2, add_fn) // assumed without checking: m2 is poly
  } else if d_matrixp(m2).truthy() {
    gf_matadd1(m2, m1, add_fn)
  } else {
    mfuncall(add_fn, list2(m1, m2))
  }
}

///|
fn gf_matadd1(m : Value, poly : Value, add_fn : Value) -> Value raise {
  let mut new_ : Value = Nil
  for row in cdr(m).iter() {
    new_ = cons(
      cons(numth__mlist(), mapcar(p => mfuncall(add_fn, list2(p, poly)), cdr(row))),
      new_,
    )
  }
  cons(numth__matrix(), nreverse(new_))
}

///|
fn gf_matadd2_error() -> Value raise {
  numth__err("Arguments to `~m' must have same formal structure.", [
    Str(if numth__efp() { "ef_matadd" } else { "gf_matadd" }),
  ])
}

///|
fn gf_matadd2(m1 : Value, m2 : Value, add_fn : Value) -> Value raise {
  let m1 = cdr(m1)
  let m2 = cdr(m2)
  if length(car(m1)) != length(car(m2)) {
    gf_matadd2_error() |> ignore
  }
  let mut r1 = m1
  let mut r2 = m2
  let mut new_ : Value = Nil
  while !(r1 is Nil || r2 is Nil) {
    new_ = cons(
      cons(
        numth__mlist(),
        mapcar2((a, b) => funcall(add_fn, [a, b]), cdar(r1), cdar(r2)),
      ),
      new_,
    )
    r1 = cdr(r1)
    r2 = cdr(r2)
  }
  if !(r1 is Nil && r2 is Nil) {
    gf_matadd2_error() |> ignore
  }
  cons(numth__matrix(), nreverse(new_))
}

///|
/// matrix multiplication (convenience: mat, list or poly possible as
/// argument)
fn d_gf_matmult(args : Value) -> Value raise {
  gf_red_q(Str("gf_matmult")) |> ignore
  numth__ef(Nil, fn() { n_starf_matmult(q_d_gf_mult, args) })
}

///|
fn d_ef_matmult(args : Value) -> Value raise {
  ef_red_q(Str("ef_matmult")) |> ignore
  numth__ef(t, fn() { n_starf_matmult(q_d_ef_mult, args) })
}

///|
fn n_starf_matmult(mult_fn : Value, args : Value) -> Value raise {
  d_rreduce(
    lfunc("*f-matmult", a => gf_matmult(a[0], a[1], mult_fn)),
    cons(numth__mlist(), args),
  )
}

///|
fn gf_matmult(m1 : Value, m2 : Value, mult_fn : Value) -> Value raise {
  let mut m1 = m1
  let mut m2 = m2
  if d_listp(m1).truthy() {
    m1 = list2(numth__matrix(), m1)
  }
  if d_listp(m2).truthy() {
    m2 = d_transpose(m2)
  }
  if d_matrixp(m1).truthy() && d_matrixp(m2).truthy() {
    gf_matmult2(m1, m2)
  } else if d_matrixp(m1).truthy() {
    gf_matmult1(m1, m2, mult_fn) // assumed without checking: m2 is poly
  } else if d_matrixp(m2).truthy() {
    gf_matmult1(m2, m1, mult_fn)
  } else {
    mfuncall(mult_fn, list2(m1, m2))
  }
}

///|
fn gf_matmult1(m : Value, poly : Value, mult_fn : Value) -> Value raise {
  let mut new_ : Value = Nil
  for row in cdr(m).iter() {
    new_ = cons(
      cons(
        numth__mlist(),
        mapcar(p => mfuncall(mult_fn, list2(p, poly)), cdr(row)),
      ),
      new_,
    )
  }
  cons(numth__matrix(), nreverse(new_))
}

///|
fn gf_matmult2(m1 : Value, m2 : Value) -> Value raise {
  let m1 = cdr(m1)
  let m2 = cdr(d_transpose(m2))
  if length(car(m1)) != length(car(m2)) {
    numth__err("`~m': attempt to multiply non conformable matrices.", [
      Str(if numth__efp() { "ef_matmult" } else { "gf_matmult" }),
    ])
    |> ignore
  }
  let red = if numth__efp() { numth__ef_red() } else { numth__gf_red() }
  let mut new_mat : Value = Nil
  for row1 in m1.iter() {
    let mut new_row : Value = Nil
    for row2 in m2.iter() {
      new_row = cons(
        gf_x2p(
          reduce(
            (x, y) => gf_nplus(x, y),
            mapcar2(
              (a, b) => gf_times(gf_p2x(a), gf_p2x(b), red),
              cdr(row1),
              cdr(row2),
            ),
          ),
        ),
        new_row,
      )
    }
    new_mat = cons(cons(numth__mlist(), nreverse(new_row)), new_mat)
  }
  if !eq(Nil, symval(q_d_scalarmatrixp)) &&
    length(new_mat) == 1 &&
    length(cdar(new_mat)) == 1 {
    cadar(new_mat)
  } else {
    cons(numth__matrix(), nreverse(new_mat))
  }
}

// invert and determinant by lu ------------------------------------------------

///|
fn zn_p_errchk(p : Value, fun : Value, pos : Value) -> Value raise {
  if !(p.truthy() && integerp(p) && primep(p).truthy()) {
    numth__err("`~m': ~m argument must be prime number.", [fun, pos])
  } else {
    Nil
  }
}

///|
/// returns nil when LU-decomposition fails
fn try_lu_and_call(fun : Value, m : Value, ring : Value) -> Value raise {
  let redirect = make_string_output_stream()
  // protect against lu failure; discard error messages from lu-factor.
  // The RETURN-FROM in the cleanup form of the UNWIND-PROTECT aborts any
  // non-local exit, so every error yields nil.
  with_special(standard_output, redirect, fn() {
    mfuncall(fun, list2(m, ring))
  }) catch {
    _ => Nil
  }
}

///|
fn d_zn_invert_by_lu(m : Value, p : Value) -> Value raise {
  zn_p_errchk(p, Str("zn_invert_by_lu"), Str("Second")) |> ignore
  numth__ef(Nil, fn() {
    numth__with_char(p, fn() {
      try_lu_and_call(q_d_invert_by_lu, m, q_gf_coeff_ring)
    })
  })
}

///|
fn d_gf_matinv(m : Value) -> Value raise {
  format(
    t,
    "`gf_matinv' is deprecated. ~%~\n             The user is asked to use `gf_invert_by_lu' instead.~%",
    [],
  )
  |> ignore
  d_gf_invert_by_lu(m)
}

///|
fn d_gf_invert_by_lu(m : Value) -> Value raise {
  gf_field_q(Str("gf_invert_by_lu")) |> ignore
  numth__ef(Nil, fn() { try_lu_and_call(q_d_invert_by_lu, m, q_gf_ring) })
}

///|
fn d_ef_invert_by_lu(m : Value) -> Value raise {
  ef_field_q(Str("ef_invert_by_lu")) |> ignore
  numth__ef(t, fn() { try_lu_and_call(q_d_invert_by_lu, m, q_ef_ring) })
}

///|
/// determinant
fn d_zn_determinant(m : Value, p : Value) -> Value raise {
  zn_p_errchk(p, Str("zn_determinant"), Str("Second")) |> ignore
  numth__ef(Nil, fn() {
    numth__with_char(p, fn() {
      let det = try_lu_and_call(q_d_determinant_by_lu, m, q_gf_coeff_ring)
      if det.truthy() {
        det
      } else {
        num_mod(mfuncall(q_d_determinant, list1(m)), p)
      }
    })
  })
}

///|
fn d_gf_determinant(m : Value) -> Value raise {
  gf_field_q(Str("gf_determinant")) |> ignore
  numth__ef(Nil, fn() {
    let det = try_lu_and_call(q_d_determinant_by_lu, m, q_gf_ring)
    if det.truthy() {
      det
    } else {
      with_specials(
        [
          (q_d_matrix_element_mult, q_d_gf_mult),
          (q_d_matrix_element_add, q_d_gf_add),
        ],
        fn() { mfuncall(q_d_determinant, list1(m)) },
      )
    }
  })
}

///|
fn d_ef_determinant(m : Value) -> Value raise {
  ef_field_q(Str("ef_determinant")) |> ignore
  numth__ef(t, fn() {
    let det = try_lu_and_call(q_d_determinant_by_lu, m, q_ef_ring)
    if det.truthy() {
      det
    } else {
      with_specials(
        [
          (q_d_matrix_element_mult, q_d_ef_mult),
          (q_d_matrix_element_add, q_d_ef_add),
        ],
        fn() { mfuncall(q_d_determinant, list1(m)) },
      )
    }
  })
}

// discrete logarithm ----------------------------------------------------------

///|
/// solve g^x = a in Fq^n, where g a generator of (Fq^n)*
fn d_gf_index(a : Value) -> Value raise {
  gf_data_q(Str("gf_index")) |> ignore
  gf_log_errchk1(symval(q_ear_gf_prim), Str("gf_index")) |> ignore
  numth__ef(Nil, fn() {
    if numth__eqi(symval(q_ear_gf_exp), 1) {
      d_zn_log(a, gf_x2n(symval(q_ear_gf_prim)), numth__gf_char())
    } else {
      gf_dlog(gf_p2x(a))
    }
  })
}

///|
fn d_ef_index(a : Value) -> Value raise {
  ef_data_q(Str("ef_index")) |> ignore
  gf_log_errchk1(symval(q_ear_ef_prim), Str("ef_index")) |> ignore
  numth__ef(t, fn() {
    let a = gf_p2x(a)
    if numth__eqi(symval(q_ear_ef_exp), 1) {
      numth__ef(Nil, fn() { gf_dlog(gf_n2x(cadr(a))) })
    } else {
      ef_dlog(a)
    }
  })
}

///|
fn d_gf_log(a : Value, b? : Value = Nil) -> Value raise {
  gf_data_q(Str("gf_log")) |> ignore
  gf_log_errchk1(symval(q_ear_gf_prim), Str("gf_log")) |> ignore
  numth__ef(Nil, fn() {
    if numth__eqi(symval(q_ear_gf_exp), 1) {
      // $zn_log checks if b is primitive
      d_zn_log(
        a,
        if b.truthy() {
          b
        } else {
          gf_x2n(symval(q_ear_gf_prim))
        },
        numth__gf_char(),
      )
    } else {
      let a = gf_p2x(a)
      let mut b = b
      if b.truthy() {
        b = gf_p2x(b)
        if b.truthy() {
          gf_log_errchk2(b, q_gf_prim_p, Str("gf_log")) |> ignore
        }
      }
      if b.truthy() {
        gf_dlogb(a, b)
      } else {
        gf_dlog(a)
      }
    }
  })
}

///|
fn gf_log_errchk1(prim : Value, fun : Value) -> Value raise {
  if prim is Nil {
    numth__err("`~m': there is no primitive element.", [fun]) |> ignore
  }
  if equal(prim, q_d_unknown) {
    numth__err("`~m': a primitive element is not known.", [fun])
  } else {
    Nil
  }
}

///|
fn gf_log_errchk2(x : Value, prim_p_fn : Value, fun : Value) -> Value raise {
  if !funcall(prim_p_fn, [x]).truthy() {
    numth__err("Second argument to `~m' must be a primitive element.", [fun])
  } else {
    Nil
  }
}

///|
fn d_ef_log(a : Value, b? : Value = Nil) -> Value raise {
  ef_data_q(Str("ef_log")) |> ignore
  gf_log_errchk1(symval(q_ear_ef_prim), Str("ef_log")) |> ignore
  let mut a = a
  let mut b = b
  numth__ef(t, fn() {
    a = gf_p2x(a)
    if b.truthy() {
      b = gf_p2x(b)
      if b.truthy() {
        gf_log_errchk2(b, q_ef_prim_p, Str("ef_log")) |> ignore
      }
    }
  })
  if numth__eqi(symval(q_ear_ef_exp), 1) {
    numth__ef(Nil, fn() {
      a = gf_n2x(cadr(a))
      if b.truthy() {
        gf_dlogb(a, gf_n2x(cadr(b)))
      } else {
        gf_dlog(a)
      }
    })
  } else {
    numth__ef(t, fn() {
      if b.truthy() {
        ef_dlogb(a, b)
      } else {
        ef_dlog(a)
      }
    })
  }
}

///|
fn gf_dlogb(a : Value, b : Value) -> Value raise {
  n_starf_dlogb(a, b, q_gf_dlog, numth__gf_ord())
}

///|
fn ef_dlogb(a : Value, b : Value) -> Value raise {
  n_starf_dlogb(a, b, q_ef_dlog, symval(q_ear_ef_ord))
}

///|
fn n_starf_dlogb(a : Value, b : Value, dlog_fn : Value, ord : Value) -> Value raise {
  let a_ind = funcall(dlog_fn, [a])
  let b_ind = funcall(dlog_fn, [b])
  let d = num_gcd(num_gcd(a_ind, b_ind), ord)
  let m = numth__trunc(ord, d)
  zn_quo(numth__trunc(a_ind, d), numth__trunc(b_ind, d), m)
}

///|
/// Pohlig and Hellman reduction
fn gf_dlog(a : Value) -> Value raise {
  n_starf_dlog(
    a,
    symval(q_ear_gf_prim),
    numth__gf_red(),
    numth__gf_ord(),
    symval(q_ear_gf_fs_ord),
  )
}

///|
fn ef_dlog(a : Value) -> Value raise {
  n_starf_dlog(
    a,
    symval(q_ear_ef_prim),
    numth__ef_red(),
    symval(q_ear_ef_ord),
    symval(q_ear_ef_fs_ord),
  )
}

///|
fn n_starf_dlog(
  a : Value,
  g : Value,
  red : Value,
  ord : Value,
  fs_ord : Value,
) -> Value raise {
  if a is Nil || g is Nil {
    return Nil
  }
  if num_ge(car(a), car(red)) {
    return Nil
  }
  if numth__is_one(a) {
    return Fix(0L)
  }
  if equal(g, a) {
    return Fix(1L)
  }
  if !gf_unit_p(a, red).truthy() {
    return Nil
  }
  let mut dlogs : Value = Nil
  let mut mods : Value = Nil
  let g_inv = gf_inv(g, red)
  for f in fs_ord.iter() {
    let p = car(f)
    let e = cadr(f)
    let mut ord_p = numth__trunc(ord, p)
    let om = gf_pow(g, ord_p, red)
    let mut xp : Value = Fix(0L)
    let mut b = a
    let mut k : Value = Fix(0L)
    let mut pk : Value = Fix(1L)
    let mut acc = g_inv
    let e1 = one_minus(e)
    while true {
      let xk = gf_dlog_rho_brent(gf_pow(b, ord_p, red), om, p, red)
      xp = num_add(xp, num_mul(xk, pk))
      k = one_plus(k)
      if num_eq(k, e) {
        break
      }
      ord_p = numth__trunc(ord_p, p)
      pk = num_mul(pk, p)
      if !numth__eqi(xk, 0) {
        b = gf_times(b, gf_pow(acc, xk, red), red)
      }
      if !num_eq(k, e1) {
        acc = gf_pow(acc, p, red)
      }
    }
    mods = cons(expt(p, e), mods)
    dlogs = cons(xp, dlogs)
  }
  car(solve_congruences(dlogs, mods))
}

///|
/// iteration for Pollard rho:  b = g^y * a^z in each step
fn gf_dlog_f(
  b : Value,
  y : Value,
  z : Value,
  a : Value,
  g : Value,
  p : Value,
  red : Value,
) -> (Value, Value, Value) raise {
  let m = num_mod(cadr(b), Fix(3L))
  if numth__eqi(m, 0) {
    (gf_sq(b, red), num_mod(ash(y, 1), p), num_mod(ash(z, 1), p))
  } else if numth__eqi(m, 1) {
    // avoid stationary case b=1 => b^2=1
    (gf_times(g, b, red), num_mod(one_plus(y), p), z)
  } else {
    (gf_times(a, b, red), y, num_mod(one_plus(z), p))
  }
}

///|
/// brute-force
fn gf_dlog_naive(a : Value, g : Value, red : Value) -> Value raise {
  let mut i : Value = Fix(0L)
  let mut gi = list2(Fix(0L), Fix(1L))
  while !equal(gi, a) {
    i = one_plus(i)
    gi = gf_times(gi, g, red)
  }
  i
}

///|
/// baby-steps-giant-steps: g is generator of order prime p
fn gf_dlog_baby_giant(a : Value, g : Value, p : Value, red : Value) -> Value raise {
  let m = one_plus(isqrt(p))
  let gi = gf_inv(g, red)
  let babies = make_hash_table(kind=Equal)
  let mut r : Value = Fix(0L)
  let mut b = a
  while true {
    if numth__is_one(b) {
      clrhash(babies) |> ignore
      return r
    }
    sethash(b, babies, r) |> ignore
    r = one_plus(r)
    if num_eq(r, m) {
      break
    }
    b = gf_times(gi, b, red)
  }
  let g_m = gf_pow(g, m, red)
  let mut rr : Value = Fix(0L)
  let mut bb = list2(Fix(0L), Fix(1L))
  while true {
    let r = gethash(bb, babies)
    if r.truthy() {
      clrhash(babies) |> ignore
      return num_add(r, num_mul(rr, m))
    }
    rr = one_plus(rr)
    bb = gf_times(g_m, bb, red)
  }
  Nil
}

///|
/// Pollard rho for dlog computation (Brents variant of collision detection)
/// g is generator of order p
fn gf_dlog_rho_brent(a : Value, g : Value, p : Value, red : Value) -> Value raise {
  if numth__is_one(a) {
    Fix(0L)
  } else if equal(g, a) {
    Fix(1L)
  } else if equal(a, gf_sq(g, red)) {
    Fix(2L)
  } else if numth__is_one(gf_times(a, g, red)) {
    one_minus(p)
  } else if num_lt(p, Fix(32L)) {
    gf_dlog_naive(a, g, red)
  } else if num_lt(p, Fix(1024L)) {
    gf_dlog_baby_giant(a, g, p, red)
  } else {
    // b = g^y * a^z, bb = g^yy * a^zz
    let mut b = list2(Fix(0L), Fix(1L))
    let mut y : Value = Fix(0L)
    let mut z : Value = Fix(0L)
    let mut bb = list2(Fix(0L), Fix(1L))
    let mut yy : Value = Fix(0L)
    let mut zz : Value = Fix(0L)
    while true {
      // rho
      let mut i = 0
      let mut j = 1
      while true {
        let (b1, y1, z1) = gf_dlog_f(b, y, z, a, g, p, red)
        b = b1
        y = y1
        z = z1
        if equal(b, bb) {
          break // g^y * a^z = g^yy * a^zz
        }
        i += 1
        if i == j {
          j = 1 + (j << 1)
          bb = b
          yy = y
          zz = z
        }
      }
      let dy = num_mod(num_sub(yy, y), p)
      let dz = num_mod(num_sub(z, zz), p) // g^dy = a^dz = g^(x*dz)
      if numth__eqi(num_gcd(dz, p), 1) {
        return zn_quo(dy, dz, p) // x = dy/dz mod p (since g is generator of order p)
      }
      y = Fix(0L)
      z = Fix(0L)
      b = list2(Fix(0L), Fix(1L))
      yy = one_plus(mt_random(one_minus(p)))
      zz = one_plus(mt_random(one_minus(p)))
      bb = gf_times(gf_pow(g, yy, red), gf_pow(a, zz, red), red)
    }
    Nil
  }
}

// nth root in Galois Fields ---------------------------------------------------

///|
fn d_ef_nth_root(a : Value, r : Value) -> Value raise {
  ef_field_q(Str("ef_nth_root")) |> ignore
  if !(integerp(r) && num_gt(r, Fix(0L))) {
    numth__err(
      "Second argument to `ef_nth_root' must be a positive integer. Found ~m.",
      [a, r],
    )
    |> ignore
  }
  numth__ef(t, fn() {
    let rts = gf_nrt(gf_p2x(a), r, numth__ef_red(), symval(q_ear_ef_ord))
    gf_nrt_exit(rts)
  })
}

///|
fn d_gf_nth_root(a : Value, r : Value) -> Value raise {
  gf_field_q(Str("gf_nth_root")) |> ignore
  if !(integerp(r) && num_gt(r, Fix(0L))) {
    numth__err(
      "Second argument to `gf_nth_root' must be a positive integer. Found ~m.",
      [a, r],
    )
    |> ignore
  }
  numth__ef(Nil, fn() {
    let rts = gf_nrt(gf_p2x(a), r, numth__gf_red(), numth__gf_ord())
    gf_nrt_exit(rts)
  })
}

///|
fn gf_nrt_exit(rts : Value) -> Value raise {
  if rts.truthy() {
    let rts = mapcar(
      x => gf_n2x(x),
      numth__sort_num(mapcar(x => gf_x2n(x), rts)),
    )
    cons(numth__mlist(), mapcar(x => gf_x2p(x), rts))
  } else {
    Nil
  }
}

///|
/// e.g. r=i*i*j*k, then x^(1/r) = (((x^(1/i))^(1/i))^(1/j))^(1/k)
fn gf_nrt(x : Value, r : Value, red : Value, ord : Value) -> Value raise {
  let x = gf_nred(x, red)
  if x is Nil {
    Nil
  } else if numth__eqi(r, 1) || primep(r).truthy() {
    gf_amm(x, r, red, ord)
  } else {
    numth__nofaclim(fn() {
      let mut rs = get_factor_list(r)
      rs = numth__sort_car(rs)
      rs = numth__apply_nconc(
        mapcar(pe => numth__make_list(cadr(pe), car(pe)), rs),
      )
      let mut rts = gf_amm(x, car(rs), red, ord)
      for r in cdr(rs).iter() {
        rts = numth__apply_nconc(mapcar(y => gf_amm(y, r, red, ord), rts))
      }
      rts
    })
  }
}

///|
/// inspired by Bach,Shallit 7.3.2
/// r prime, red irreducible
fn gf_amm(x : Value, r : Value, red : Value, ord : Value) -> Value raise {
  if numth__eqi(r, 1) {
    return list1(x)
  }
  let mut m : Value = Nil
  let mut rt : Value = Nil
  if numth__eqi(r, 2) {
    m = num_mod(ord, Fix(2L))
    if numth__eqi(m, 0) &&
      !numth__eqi(
        gf_jacobi(
          x,
          red,
          if numth__efp() {
            numth__gf_card()
          } else {
            numth__gf_char()
          },
        ),
        1,
      ) {
      return Nil
    } else if numth__eqi(m, 1) {
      // q = 2^n : unique solution
      return list1(
        gf_pow(x, ash(num_add(ash(ord, 1), Fix(2L)), -2), red),
      )
    } else if numth__eqi(num_mod(ord, Fix(4L)), 2) {
      rt = gf_pow(x, ash(num_add(ord, Fix(2L)), -2), red)
      return list2(rt, gf_minus(rt))
    } else if numth__eqi(num_mod(ord, Fix(8L)), 4) {
      let twox = gf_plus(x, x)
      let y = gf_pow(twox, ash(num_sub(ord, Fix(4L)), -3), red)
      let i = gf_times(twox, gf_times(y, y, red), red)
      let rt = gf_times(
        x,
        gf_times(y, gf_nplus(i, list2(Fix(0L), gf_cminus_b(Fix(1L)))), red),
        red,
      )
      return list2(rt, gf_minus(rt))
    }
  }
  let (s, m1) = num_truncate(ord, b=r)
  m = m1
  if numth__eqi(m, 0) && !numth__is_one(gf_pow(x, s, red)) {
    return Nil
  }
  // r = 3, first 2 cases:
  if numth__eqi(r, 3) {
    m = num_mod(ord, Fix(3L))
    if numth__eqi(m, 1) {
      // unique solution
      return list1(
        gf_pow(x, numth__trunc(one_plus(ash(ord, 1)), Fix(3L)), red),
      )
    } else if numth__eqi(m, 2) {
      // unique solution
      return list1(gf_pow(x, numth__trunc(one_plus(ord), Fix(3L)), red))
    }
  }
  // compute u,e with ord = u*r^e and r,u coprime:
  let mut u = ord
  let mut e : Value = Fix(0L)
  let mut u1 = u
  while true {
    let (q1, m2) = num_truncate(u1, b=r)
    u1 = q1
    m = m2
    if !numth__eqi(m, 0) {
      break
    }
    u = u1
    e = one_plus(e)
  }
  if numth__eqi(e, 0) {
    rt = gf_pow(x, inv_mod(r, u), red) // unique solution, see Bach,Shallit 7.3.1
    list1(rt)
  } else {
    let mut n = gf_n2x(Fix(2L))
    while numth__is_one(gf_pow(n, s, red)) {
      // n is no r-th power
      n = gf_n2x(one_plus(gf_x2n(n)))
    }
    let g = gf_pow(n, u, red)
    let re = expt(r, e)
    let om = gf_pow(g, numth__trunc(re, r), red) // r-th root of unity
    if !numth__eqi(r, 3) ||
      {
        m = num_mod(ord, Fix(9L))
        numth__eqi(m, 0)
      } {
      let xr = gf_pow(x, u, red)
      let xu = gf_pow(x, re, red)
      let k = n_starf_dlog(xr, g, red, re, list1(list2(r, e))) // g^k = xr
      let br = gf_pow(g, numth__trunc(k, r), red) // br^r = xr
      let bu = gf_pow(xu, inv_mod(r, u), red) // bu^r = xu
      let ab = cdr(zn_gcdex1(u, re))
      let mut alpha = car(ab)
      let mut beta = cadr(ab)
      if minusp(alpha) {
        alpha = num_add(alpha, ord)
      } else {
        beta = num_add(beta, ord)
      }
      rt = gf_times(gf_pow(br, alpha, red), gf_pow(bu, beta, red), red)
    } else if numth__eqi(m, 3) {
      // r = 3, remaining cases:
      rt = gf_pow(x, numth__trunc(num_add(ash(ord, 1), Fix(3L)), Fix(9L)), red)
    } else if numth__eqi(m, 6) {
      rt = gf_pow(x, numth__trunc(num_add(ord, Fix(3L)), Fix(9L)), red)
    }
    let mut i : Value = Fix(1L)
    let mut j = list2(Fix(0L), Fix(1L))
    let mut res = list1(rt)
    while !num_eq(i, r) {
      j = gf_times(j, om, red)
      res = cons(gf_times(rt, j, red), res)
      i = one_plus(i)
    }
    res
  }
}

// tables of small fields ------------------------------------------------------

///|
fn d_gf_add_table() -> Value raise {
  gf_data_q(Str("gf_add_table")) |> ignore
  numth__ef(Nil, fn() { gf_add_table(numth__gf_card()) })
}

///|
fn d_ef_add_table() -> Value raise {
  ef_data_q(Str("ef_add_table")) |> ignore
  numth__ef(t, fn() { gf_add_table(symval(q_ear_ef_card)) })
}

///|
fn gf_add_table(card : Value) -> Value raise {
  d_genmatrix(
    lfunc("gf-add-table", args => gf_x2n(
      gf_plus(gf_n2x(one_minus(args[0])), gf_n2x(one_minus(args[1]))),
    )),
    card,
    j2=card,
  )
}

///|
fn d_gf_mult_table(all_q? : Value = Nil) -> Value raise {
  gf_data_q(Str("gf_mult_table")) |> ignore
  numth__ef(Nil, fn() {
    gf_mult_table(
      numth__gf_red(),
      symval(q_ear_gf_irred_q),
      numth__gf_card(),
      all_q,
    )
  })
}

///|
fn d_ef_mult_table(all_q? : Value = Nil) -> Value raise {
  ef_data_q(Str("ef_mult_table")) |> ignore
  numth__ef(t, fn() {
    gf_mult_table(
      numth__ef_red(),
      symval(q_ear_ef_irred_q),
      symval(q_ear_ef_card),
      all_q,
    )
  })
}

///|
fn gf_mult_table(
  red : Value,
  irred_q : Value,
  card : Value,
  all_q : Value,
) -> Value raise {
  if irred_q.truthy() || equal(all_q, q_d_all) {
    // field
    d_genmatrix(
      lfunc("gf-mult-table", args => gf_x2n(
        gf_times(gf_n2x(args[0]), gf_n2x(args[1]), red),
      )),
      one_minus(card),
      j2=one_minus(card),
    )
  } else {
    // units only
    let mut units : Value = Nil
    let mut i : Value = Fix(1L)
    while !num_eq(i, card) {
      let x = gf_n2x(i)
      if gf_unit_p(x, red).truthy() {
        units = cons(x, units)
      }
      i = one_plus(i)
    }
    let mut res : Value = Nil
    for x in units.iter() {
      res = cons(
        cons(numth__mlist(), mapcar(y => gf_x2n(gf_times(x, y, red)), units)),
        res,
      )
    }
    cons(numth__matrix(), nreverse(res))
  }
}

///|
fn d_gf_power_table(args : Value) -> Value raise {
  gf_data_q(Str("gf_power_table")) |> ignore
  numth__ef(Nil, fn() {
    let (all_q, cols0) = gf_power_table_args(cons(Str("gf_power_table"), args))
    let mut cols = cols0
    if cols is Nil {
      cols = numth__gf_ord()
      if all_q.truthy() {
        cols = one_plus(cols)
      }
    }
    gf_power_table(
      numth__gf_red(),
      symval(q_ear_gf_irred_q),
      numth__gf_card(),
      cols,
      all_q,
    )
  })
}

///|
fn d_ef_power_table(args : Value) -> Value raise {
  ef_data_q(Str("ef_power_table")) |> ignore
  numth__ef(t, fn() {
    let (all_q, cols0) = gf_power_table_args(cons(Str("ef_power_table"), args))
    let mut cols = cols0
    if cols is Nil {
      cols = symval(q_ear_ef_ord)
      if all_q.truthy() {
        cols = one_plus(cols)
      }
    }
    gf_power_table(
      numth__ef_red(),
      symval(q_ear_ef_irred_q),
      symval(q_ear_ef_card),
      cols,
      all_q,
    )
  })
}

///|
fn gf_power_table_args(args : Value) -> (Value, Value) raise {
  let str = car(args)
  let x = cadr(args)
  let y = caddr(args)
  let mut all_q : Value = Nil
  let mut cols : Value = Nil
  if x.truthy() {
    if integerp(x) {
      cols = x
    } else if equal(x, q_d_all) {
      all_q = t
    } else {
      numth__err("First argument to `~m' must be `all' or a small fixnum.", [
        str,
      ])
      |> ignore
    }
  }
  if y.truthy() {
    if integerp(x) && equal(y, q_d_all) {
      all_q = t
    } else if equal(x, q_d_all) && integerp(y) {
      cols = y
    } else {
      format(t, "Only the first argument to `~a' has been used.~%", [str])
      |> ignore
    }
  }
  (all_q, cols)
}

///|
fn gf_power_table(
  red : Value,
  irred_q : Value,
  card : Value,
  cols : Value,
  all_q : Value,
) -> Value raise {
  if irred_q.truthy() || all_q.truthy() {
    d_genmatrix(
      lfunc("gf-power-table", args => gf_x2n(
        gf_pow(gf_n2x(args[0]), args[1], red),
      )),
      one_minus(card),
      j2=cols,
    )
  } else {
    // units only
    let mut res : Value = Nil
    let mut i : Value = Fix(1L)
    while !num_eq(i, card) {
      let x = gf_n2x(i)
      if gf_unit_p(x, red).truthy() {
        res = cons(
          cons(
            numth__mlist(),
            mapcar(
              j => gf_x2n(gf_pow(x, j, red)),
              cdr(mfuncall(q_d_makelist, list([q_d_j, q_d_j, Fix(1L), cols]))),
            ),
          ),
          res,
        )
      }
      i = one_plus(i)
    }
    cons(numth__matrix(), nreverse(res))
  }
}

// ---------------------------------------------------------------------------
// Top-level forms of numth.lisp

///|
/// The 'assign property installed by `(defmvar var val doc boolean)`.
fn numth__boolean_assign(name : String) -> Value {
  lfunc(name, args => {
    let v = args[1]
    if !(v is Nil || eq(v, t)) {
      mseterr(args[0], v, reason=Str("must be one of: true, false"))
    } else {
      Nil
    }
  })
}

///|
fn init_numth() -> Unit raise {
  // The :print-function options of the gf-data and ef-data defstructs.
  @lisp.struct_print_functions["gf-data"] = lfunc("gf-data-short-print", args => {
    gf_data_short_print(args[0], args[1], args[2])
  })
  @lisp.struct_print_functions["ef-data"] = lfunc("ef-data-short-print", args => {
    ef_data_short_print(args[0], args[1], args[2])
  })
  // (defmvar $zn_primroot_limit 1000 ... :setting-predicate #'integer-predicate)
  putprop(
    q_d_zn_primroot_limit,
    lfunc("$zn_primroot_limit-assign", args => {
      let (ok, reason) = integer_predicate(args[1])
      if !ok.truthy() {
        mseterr(args[0], args[1], reason~)
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
  // boolean defmvars
  putprop(
    q_d_zn_primroot_verbose,
    numth__boolean_assign("$zn_primroot_verbose-assign"),
    q_assign,
  )
  |> ignore
  putprop(
    q_d_zn_primroot_pretest,
    numth__boolean_assign("$zn_primroot_pretest-assign"),
    q_assign,
  )
  |> ignore
  putprop(q_d_gf_rat, numth__boolean_assign("$gf_rat-assign"), q_assign)
  |> ignore
  putprop(
    q_d_gf_symmetric,
    numth__boolean_assign("$gf_symmetric-assign"),
    q_assign,
  )
  |> ignore
  putprop(
    q_d_gf_balanced,
    numth__boolean_assign("$gf_balanced-assign"),
    q_assign,
  )
  |> ignore
  // (putprop '$gf_symmetric 'gf-balanced-info 'assign)
  putprop(q_d_gf_symmetric, q_gf_balanced_info, q_assign) |> ignore
  // (putprop '$gf_coeff_limit 'gf-coeff-check 'assign)
  putprop(q_d_gf_coeff_limit, q_gf_coeff_check, q_assign) |> ignore
  putprop(
    q_d_gf_cantor_zassenhaus,
    numth__boolean_assign("$gf_cantor_zassenhaus-assign"),
    q_assign,
  )
  |> ignore
}

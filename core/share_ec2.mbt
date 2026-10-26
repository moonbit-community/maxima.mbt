// Port of share/contrib/elliptic_curves/ec2.lisp (Volker van Nek, 2015):
// elliptic curves over binary fields.
//
// Maxima functions: ec2_set_curve, ec2_reduction, ec2_add, ec2_mult,
// ec2_random, f2_solve_quadratic, ec2_point_p, ec2_point_order.

///|
/// define a curve over a binary field (as global variables)
fn d_ec2_set_curve(red : Value, a : Value, b : Value) -> Value raise {
  set(
    q_ear_ec2_red,
    if integerp(red) {
      red
    } else {
      with_specials([(q_ear_gf_char, Fix(2L)), (q_ear_ef_arith_q, Nil)], () => gf_x2n(
        gf_p2x_red(red, Str("ec2_set_curve")),
      ))
    },
  )
  |> ignore
  if !(integerp(a) && integerp(b)) {
    let fn_ : Value = Str("ec2_set_curve")
    ec__err(
      "Second and third argument to `~m' must be an integer.",
      [fn_],
    )
    |> ignore
  }
  with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
    let f2red = symval(q_ear_f2_red)
    set(q_ear_ec2_exp, ec__i(integer_length(f2red) - 1)) |> ignore
    set(q_ear_ec2_a, if num_lt(a, f2red) { a } else { f2_red(a) }) |> ignore
    set(q_ear_ec2_b, if num_lt(b, f2red) { b } else { f2_red(b) }) |> ignore
    set(q_ear_ec2_delta, Nil) |> ignore
    set(q_ear_ec2_tab, Nil) |> ignore
    set(q_ear_ec2_set_q, t)
  })
}

///|
fn ec2_set_q(fun : Value) -> Value raise {
  if symval(q_ear_ec2_set_q).truthy() {
    t
  } else {
    ec__err("`~m': The curve is not defined yet.", [fun])
  }
}

///|
/// the reduction polynomial; optional: return poly as number
fn d_ec2_reduction(rtype? : Value = Nil) -> Value raise {
  ec2_set_q(Str("ec2_reduction")) |> ignore
  with_specials([(q_ear_gf_char, Fix(2L)), (q_ear_ef_arith_q, Nil)], () => if equal(
      rtype,
      q_d_number,
    ) {
    symval(q_ear_ec2_red)
  } else {
    gf_x2p(gf_n2x(symval(q_ear_ec2_red)))
  })
}

///|
/// convert between Maxima and Lisp level
fn ec2_m2l(pt_m : Value, fn_ : Value) -> Value raise {
  ec2_set_q(fn_) |> ignore
  if equal(pt_m, q_d_ec2_inf) {
    return Nil
  }
  let pt = cdr(pt_m)
  if !(d_listp(pt_m).truthy() && pt.truthy() && every(n => integerp(n), pt)) {
    return ec__err("`~m': Unsuitable argument: ~m", [fn_, pt_m])
  }
  with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => mapcar(
    n => f2_red(n),
    pt,
  ))
}

///|
fn ec2_l2m(pt : Value) -> Value raise {
  if pt.truthy() {
    cons(list2(q_mlist, q_simp), pt)
  } else {
    q_d_ec2_inf
  }
}

///|
/// point addition (in affine coords)
fn d_ec2_add(pt : Value, qt : Value) -> Value raise {
  ec2_l2m(
    ec2_add(ec2_m2l(pt, Str("ec2_add")), ec2_m2l(qt, Str("ec2_add"))),
  )
}

///|
/// point multiplication
fn d_ec2_mult(n : Value, pt : Value) -> Value raise {
  ec2_l2m(ec2_mult(n, ec2_m2l(pt, Str("ec2_mult"))))
}

// -------------------------------------------------------------------------- //
//
// arithmetic in affine coordinates
//

///|
fn ec2_add(pt : Value, qt : Value) -> Value raise {
  if pt is Nil {
    qt
  } else if qt is Nil {
    pt
  } else if equal(pt, qt) {
    ec2_double(pt)
  } else if equal(pt, ec2_neg(qt)) {
    Nil
  } else {
    with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
      let xp = car(pt)
      let yp = cadr(pt)
      let xq = car(qt)
      let yq = cadr(qt)
      let xpq = logxor(xp, xq)
      let m = f2_times(logxor(yp, yq), f2_inv(xpq))
      let xx = logxor(
        logxor(logxor(f2_times(m, m), m), xpq),
        symval(q_ear_ec2_a),
      )
      let yy = logxor(logxor(f2_times(m, logxor(xp, xx)), xx), yp)
      list2(xx, yy)
    })
  }
}

///|
fn ec2_double(pt : Value) -> Value raise {
  if pt is Nil {
    Nil
  } else if num_eq(Fix(0L), car(pt)) {
    Nil
  } else {
    with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
      let x = car(pt)
      let y = cadr(pt)
      let x2 = f2_times(x, x)
      let xi = f2_inv(x)
      let xx = logxor(x2, f2_times(symval(q_ear_ec2_b), f2_times(xi, xi)))
      let tt = logxor(x, f2_times(y, xi))
      let yy = logxor(logxor(x2, f2_times(tt, xx)), xx)
      list2(xx, yy)
    })
  }
}

///|
fn ec2_mult(n : Value, pt : Value) -> Value raise {
  let mut n = n
  let mut pt = pt
  if num_eq(Fix(0L), n) || pt is Nil {
    return Nil
  }
  if minusp(n) {
    n = num_neg(n)
    pt = ec2_neg(pt)
  }
  let mut res : Value = Nil
  while true {
    if oddp(n) {
      res = ec2_add(pt, res)
      if num_eq(Fix(1L), n) {
        return res
      }
    }
    n = ash(n, -1)
    pt = ec2_double(pt)
  }
  Nil
}

///|
fn ec2_neg(pt : Value) -> Value raise {
  if pt.truthy() {
    let xp = car(pt)
    list2(xp, logxor(xp, cadr(pt)))
  } else {
    Nil
  }
}

// -------------------------------------------------------------------------- //

///|
/// find random point on given curve
fn d_ec2_random() -> Value raise {
  ec2_set_q(Str("ec2_random")) |> ignore
  ec2_l2m(ec2_random()) // does not return $ec2_inf
}

///|
fn ec2_random() -> Value raise { // does not return null
  let a = symval(q_ear_ec2_a)
  let b = symval(q_ear_ec2_b)
  let n = symval(q_ear_ec2_exp)
  let q = ash(Fix(1L), to_int(n))
  while true {
    let x = d_random(q) // $random is set by set_random_state
    let y = ec2_comp_y(x, a, b, n)
    if y.truthy() {
      let y = if num_eq(d_random(ec__i(2)), Fix(0L)) { car(y) } else { cadr(y) }
      return list2(x, y)
    }
  }
  Nil
}

///|
/// y^2 + x*y = x^3 + a*x^2 + b
/// --> y = x*z, where z^2 + z = x + a + b/x^2
fn ec2_comp_y(x : Value, a : Value, b : Value, n : Value) -> Value raise { // q = 2^n
  with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
    let xi = f2_inv(x)
    let xi2 = f2_times(xi, xi)
    let tmp = f2_times(b, xi2)
    let beta = logxor(logxor(x, a), tmp)
    let zz = cdr(d_f2_solve_quadratic(beta, n))
    if zz.truthy() {
      mapcar(z => f2_times(x, z), zz)
    } else {
      Nil
    }
  })
}

// -------------------------------------------------------------------------- //
//
// Solving quadratic equations in F2n
//
//    (Blake, Seroussi, Smart - Elliptic Curves in Cryptography, II.2.4)
//

///|
/// x^2 + x + beta = 0 in Fq, q = 2^n
fn d_f2_solve_quadratic(beta : Value, n : Value) -> Value raise {
  let ht = f2_trace(beta, n)
  if !num_eq(car(ht), Fix(0L)) {
    return Nil
  }
  let x = if oddp(n) {
    cadr(ht) // cadr is halftrace
  } else {
    if !symval(q_ear_ec2_delta).truthy() {
      let q = ash(Fix(1L), to_int(n))
      while true {
        set(q_ear_ec2_delta, mt_random(q)) |> ignore
        if num_eq(car(f2_trace(symval(q_ear_ec2_delta), n)), Fix(1L)) { // car is trace
          break
        }
      }
    }
    f2_solve_even(symval(q_ear_ec2_delta), beta, n)
  }
  list3(list2(q_mlist, q_simp), x, logxor(x, Fix(1L)))
}

///|
/// compute trace and half-trace in parallel
fn f2_trace(b : Value, n : Value) -> Value raise {
  with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
    let mut b = b
    let mut tr = b
    let mut ht = b
    let n = to_int(n)
    for i = 1; i != n; i = i + 1 {
      b = f2_times(b, b)
      tr = logxor(tr, b)
      if i % 2 == 0 {
        ht = logxor(ht, b)
      }
    }
    list2(tr, ht)
  })
}

///|
/// Blake, Seroussi, Smart - equation (II.8) - n is even
fn f2_solve_even(d : Value, b : Value, n : Value) -> Value raise {
  if !symval(q_ear_ec2_tab).truthy() {
    set(q_ear_ec2_tab, f2_solve_even_table(d, n)) |> ignore
  }
  with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
    let s_tab = symval(q_ear_ec2_tab)
    let mut s = car(s_tab)
    let tab = cadr(s_tab)
    let mut b = b
    let mut x = f2_times(s, b)
    let n = to_int(n)
    for i = 1; i != n - 1; i = i + 1 {
      b = f2_times(b, b)
      s = logxor(aref1(tab, i), s)
      x = logxor(f2_times(s, b), x)
    }
    x
  })
}

///|
fn f2_solve_even_table(d : Value, n : Value) -> Value raise {
  let nn = to_int(n)
  let tab = ec__vec(nn, init=Fix(0L))
  with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
    let mut s : Value = Fix(0L)
    let mut d = d
    for j = 1; j != nn; j = j + 1 {
      d = f2_times(d, d)
      s = logxor(d, s)
      aset1(tab, j, d) |> ignore
    }
    list2(s, tab)
  })
}

// -------------------------------------------------------------------------- //

///|
/// check if point is on the current curve
fn d_ec2_point_p(pt : Value) -> Value raise {
  let fn_ : Value = Str("ec2_point_p")
  ec2_set_q(fn_) |> ignore
  if equal(pt, q_d_ec2_inf) {
    t
  } else {
    ec2_point_p(ec2_m2l(pt, fn_))
  }
}

///|
fn ec2_point_p(pt : Value) -> Value raise { // check only non-infinite points
  with_special(q_ear_f2_red, symval(q_ear_ec2_red), () => {
    let x = car(pt)
    let y = cadr(pt)
    let l = logxor(f2_times(y, y), f2_times(x, y))
    let r = logxor(
      logxor(
        f2_pow(x, ec__i(3)),
        f2_times(symval(q_ear_ec2_a), f2_times(x, x)),
      ),
      symval(q_ear_ec2_b),
    )
    lbool(num_eq(l, r))
  })
}

///|
/// order of a point (as a factor of a given group order)
fn d_ec2_point_order(pt : Value, ord : Value, fs_ord? : Value = Nil) -> Value raise {
  let fn_ : Value = Str("ec2_point_order")
  ec2_set_q(fn_) |> ignore
  let pt = ec2_m2l(pt, fn_)
  if !ec2_point_p(pt).truthy() {
    ec__err("`~m': [~m,~m] is no curve point.", [fn_, car(pt), cadr(pt)])
    |> ignore
  }
  if !(integerp(ord) && num_gt(ord, Fix(0L))) {
    ec__err(
      "`~m': Second argument must be a positive integer. Found ~m.",
      [fn_, ord],
    )
    |> ignore
  }
  let fs_ord = ec__fs_ord(fs_ord, ord, fn_)
  ec2_point_order(pt, ord, fs_ord)
}

///|
fn ec2_point_order(pt : Value, ord : Value, fs_ord : Value) -> Value raise {
  let mut s = ord
  for f in fs_ord.iter() {
    let fp = car(f)
    let fe = cadr(f)
    s = num_truncate(s, b=expt(fp, fe)).0
    while true {
      let qt = ec2_mult(s, pt)
      if qt is Nil {
        break
      }
      ec2_mult(fp, qt) |> ignore
      s = num_mul(fp, s)
    }
  }
  s
}

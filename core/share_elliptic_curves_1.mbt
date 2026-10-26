// Port of share/contrib/elliptic_curves/elliptic_curves.lisp (Volker van
// Nek, 2015): elliptic curves over prime fields.
//
// Maxima functions: ec_set_curve, ec_add, ec_mult, ec_random, ec_point_p,
// ec_point_order, ec_log, ec_twist_curve, ec_trace.
// Option variables: ec_balanced, ec_sea_verbose.
//
// Part 1: curve definition, affine and projective point arithmetic, random
// points, point order, discrete logarithm, twist. The SEA algorithm for
// ec_trace is in share_elliptic_curves_2.mbt.

///|
fn ec__i(n : Int) -> Value {
  Fix(n.to_int64())
}

///|
fn ec__eqi(x : Value, n : Int) -> Bool raise {
  num_eq(x, ec__i(n))
}

///|
fn ec__err(msg : String, args : Array[Value]) -> Value raise {
  gf_merror(Str(msg), list(args))
}

///|
/// `(ldb (byte size pos) n)`
fn ec__ldb(size : Int, pos : Int, n : Value) -> Value raise {
  logand(ash(n, -pos), num_sub(ash(Fix(1L), size), Fix(1L)))
}

///|
/// `(svref v i)` with a Lisp integer index.
fn ec__svref(v : Value, i : Value) -> Value raise {
  aref1(v, to_int(i))
}

///|
/// `(setf (svref v i) x)` with a Lisp integer index.
fn ec__svset(v : Value, i : Value, x : Value) -> Value raise {
  aset1(v, to_int(i), x)
}

///|
/// A simple vector of length n, initial elements `init`.
fn ec__vec(n : Int, init? : Value = Nil) -> Value {
  make_array([n], initial=init)
}

///|
/// `(sort v pred)` on a simple vector: sorts in place and returns v.
fn ec__sort_vec(v : Value, lt : (Value, Value) -> Bool raise) -> Value raise {
  match v {
    Vec(a) => {
      let sorted = sort_array(a.data, lt)
      for i in 0..<sorted.length() {
        a.data[i] = sorted[i]
      }
      v
    }
    _ => v
  }
}

///|
/// `(mod (+ (power-mod x 3 p) (* a x) b) p)`
fn ec__rhs(x : Value, a : Value, b : Value, p : Value) -> Value raise {
  num_mod(num_sum([power_mod(x, ec__i(3), p), num_mul(a, x), b]), p)
}

///|
/// define a curve over a prime field (as global variables)
fn d_ec_set_curve(p : Value, a : Value, b : Value) -> Value raise {
  let fn_ : Value = Str("ec_set_curve")
  if !(integerp(p) && integerp(a) && integerp(b)) {
    ec__err("`~m': Arguments must be a integers.", [fn_]) |> ignore
  }
  if !(primep(p).truthy() && num_gt(p, ec__i(3))) {
    ec__err(
      "`~m': First argument must be a prime number greater than 3. Found ~m.",
      [fn_, p],
    )
    |> ignore
  }
  if num_eq(
      Fix(0L),
      num_mod(
        num_add(num_prod([ec__i(4), a, a, a]), num_prod([ec__i(27), b, b])),
        p,
      ),
    ) {
    set(q_ear_ec_set_q, Nil)
  } else {
    set(q_ear_ec_p, p) |> ignore
    set(q_ear_ec_a, num_mod(a, p)) |> ignore
    set(q_ear_ec_b, num_mod(b, p)) |> ignore
    set(q_ear_ec_inv2, inv_mod(ec__i(2), p)) |> ignore
    set(q_ear_ec_set_q, t)
  }
}

///|
fn ec_set_q(fun : Value) -> Value raise {
  if symval(q_ear_ec_set_q).truthy() {
    t
  } else {
    ec__err("`~m': The curve is not defined yet.", [fun])
  }
}

///|
/// convert between Maxima and Lisp level
fn ec_m2l(pt_m : Value, fn_ : Value) -> Value raise {
  if equal(pt_m, q_d_ec_inf) {
    // neutral element, point of infinity (nil at Lisp level)
    return Nil
  }
  let pt = cdr(pt_m)
  if !(d_listp(pt_m).truthy() && pt.truthy() && every(n => integerp(n), pt)) {
    return ec__err("`~m': Unsuitable argument: ~m", [fn_, pt_m])
  }
  let p = symval(q_ear_ec_p)
  mapcar(n => num_mod(n, p), pt)
}

///|
fn ec_l2m(pt : Value) -> Value raise {
  if pt.truthy() {
    cons(list2(q_mlist, q_simp), ec_balance(pt))
  } else {
    q_d_ec_inf
  }
}

///|
fn ec_balance(pt : Value) -> Value raise {
  if symval(q_d_ec_balanced).truthy() {
    let p = symval(q_ear_ec_p)
    mapcar(
      n => if num_lt(ash(p, -1), n) { num_sub(n, p) } else { n },
      pt,
    )
  } else {
    pt
  }
}

///|
/// point addition (use affine coords at Maxima level, projective at Lisp
/// level)
fn d_ec_add(pt : Value, qt : Value) -> Value raise {
  let fn_ : Value = Str("ec_add")
  ec_set_q(fn_) |> ignore
  let pt = ec_projectify(ec_m2l(pt, fn_))
  let qt = ec_projectify(ec_m2l(qt, fn_))
  ec_l2m(ec_affinify(ec_padd(pt, qt)))
}

///|
/// point multiplication
fn d_ec_mult(n : Value, pt : Value) -> Value raise {
  let fn_ : Value = Str("ec_mult")
  ec_set_q(fn_) |> ignore
  if !integerp(n) {
    ec__err("`~m': First argument must be an integer.", [fn_]) |> ignore
  }
  let pt = ec_projectify(ec_m2l(pt, fn_))
  ec_l2m(ec_affinify(ec_pmult(n, pt)))
}

// -------------------------------------------------------------------------- //
//
// arithmetic in affine coordinates
//

///|
fn ec_add(pt : Value, qt : Value) -> Value raise {
  if pt is Nil {
    qt
  } else if qt is Nil {
    pt
  } else if equal(pt, qt) {
    ec_double(pt)
  } else if eql(car(pt), car(qt)) {
    // erroneous if pt or qt is not on the curve
    Nil
  } else {
    let p = symval(q_ear_ec_p)
    let xp = car(pt)
    let yp = cadr(pt)
    let xq = car(qt)
    let yq = cadr(qt)
    let m = zn_quo(num_sub(yq, yp), num_sub(xq, xp), p)
    let xx = num_mod(num_sub(num_sub(num_mul(m, m), xq), xp), p)
    let yy = num_mod(num_sub(num_mul(m, num_sub(xp, xx)), yp), p)
    list2(xx, yy)
  }
}

///|
fn ec_double(pt : Value) -> Value raise {
  if pt is Nil {
    Nil
  } else if num_eq(Fix(0L), cadr(pt)) {
    Nil
  } else {
    let p = symval(q_ear_ec_p)
    let x = car(pt)
    let y = cadr(pt)
    let m = zn_quo(
      num_add(num_prod([ec__i(3), x, x]), symval(q_ear_ec_a)),
      ash(y, 1),
      p,
    )
    let xx = num_mod(num_sub(num_mul(m, m), ash(x, 1)), p)
    let yy = num_mod(num_sub(num_mul(m, num_sub(x, xx)), y), p)
    list2(xx, yy)
  }
}

///|
fn ec_mult(n : Value, pt : Value) -> Value raise {
  let mut n = n
  let mut pt = pt
  if num_eq(Fix(0L), n) || pt is Nil {
    return Nil
  }
  if minusp(n) {
    n = num_neg(n)
    pt = ec_neg(pt)
  }
  let mut res : Value = Nil
  while true {
    if oddp(n) {
      res = ec_add(pt, res)
      if num_eq(Fix(1L), n) {
        return res
      }
    }
    n = ash(n, -1)
    pt = ec_double(pt)
  }
  Nil
}

///|
fn ec_neg(pt : Value) -> Value raise {
  if pt.truthy() {
    list2(car(pt), num_sub(symval(q_ear_ec_p), cadr(pt)))
  } else {
    Nil
  }
}

//
// arithmetic in projective coordinates ------------------------------------- //
//

///|
fn ec_projectify(pt : Value) -> Value raise {
  if pt.truthy() {
    nconc(pt, list1(Fix(1L)))
  } else {
    list3(Fix(1L), Fix(1L), Fix(0L))
  }
}

///|
fn ec_affinify(pt : Value) -> Value raise {
  if num_eq(caddr(pt), Fix(0L)) {
    Nil
  } else {
    let p = symval(q_ear_ec_p)
    let i = inv_mod(caddr(pt), p)
    let ii = num_mul(i, i)
    let x = num_mod(num_mul(ii, car(pt)), p)
    let y = num_mod(num_prod([ii, i, cadr(pt)]), p)
    list2(x, y)
  }
}

///|
fn ec_pdouble(pt : Value) -> Value raise {
  if num_eq(caddr(pt), Fix(0L)) {
    return pt
  }
  let p = symval(q_ear_ec_p)
  let a = symval(q_ear_ec_a)
  let x1 = car(pt)
  let y1 = cadr(pt)
  let z1 = caddr(pt)
  let y11 = num_mul(y1, y1)
  let z11 = num_mul(z1, z1)
  let l1 = if num_eq(a, ec__i(-3)) {
    // NIST curves have a = -3
    num_prod([ec__i(3), num_sub(x1, z11), num_add(x1, z11)])
  } else {
    num_add(num_prod([ec__i(3), x1, x1]), num_prod([a, z11, z11]))
  }
  let z3 = ash(num_mul(y1, z1), 1)
  let l2 = ash(num_mul(x1, y11), 2)
  let x3 = num_sub(num_mul(l1, l1), ash(l2, 1))
  let l3 = ash(num_mul(y11, y11), 3)
  let y3 = num_sub(num_mul(l1, num_sub(l2, x3)), l3)
  list3(num_mod(x3, p), num_mod(y3, p), num_mod(z3, p))
}

///|
fn ec_padd(pt : Value, qt : Value) -> Value raise {
  if num_eq(caddr(pt), Fix(0L)) {
    return qt
  }
  if num_eq(caddr(qt), Fix(0L)) {
    return pt
  }
  let p = symval(q_ear_ec_p)
  let x1 = car(pt)
  let y1 = cadr(pt)
  let z1 = caddr(pt)
  let x2 = car(qt)
  let y2 = cadr(qt)
  let z2 = caddr(qt)
  let z11 = num_mul(z1, z1)
  let z22 = num_mul(z2, z2)
  let l1 = num_mul(x1, z22)
  let l2 = num_mul(x2, z11)
  let l3 = num_mod(num_sub(l1, l2), p)
  let l4 = num_prod([y1, z22, z2])
  let l5 = num_prod([y2, z11, z1])
  let l6 = num_mod(num_sub(l4, l5), p)
  if num_eq(l3, Fix(0L)) {
    if num_eq(l6, Fix(0L)) {
      ec_pdouble(pt)
    } else {
      list3(Fix(1L), Fix(1L), Fix(0L))
    }
  } else {
    let l7 = num_add(l1, l2)
    let l8 = num_add(l4, l5)
    let z3 = num_mod(num_prod([z1, z2, l3]), p)
    let l33 = num_mul(l3, l3)
    let l733 = num_mul(l7, l33)
    let x3 = num_mod(num_sub(num_mul(l6, l6), l733), p)
    let l9 = num_sub(l733, ash(x3, 1))
    let y3 = num_mod(
      num_mul(
        symval(q_ear_ec_inv2),
        num_sub(num_mul(l9, l6), num_prod([l8, l33, l3])),
      ),
      p,
    )
    list3(x3, y3, z3)
  }
}

///|
fn ec_pmult(n : Value, pt : Value) -> Value raise {
  let mut n = n
  let mut pt = pt
  if num_eq(Fix(0L), n) || num_eq(caddr(pt), Fix(0L)) {
    return list3(Fix(1L), Fix(1L), Fix(0L))
  }
  if minusp(n) {
    n = num_neg(n)
    pt = ec_pneg(pt)
  }
  if fixnump(n) {
    let mut res = list3(Fix(1L), Fix(1L), Fix(0L))
    while true {
      if oddp(n) {
        res = ec_padd(pt, res)
        if num_eq(Fix(1L), n) {
          return res
        }
      }
      n = ash(n, -1)
      pt = ec_pdouble(pt)
    }
    Nil
  } else {
    ec_pmult_sliding_window(n, pt)
  }
}

///|
fn ec_pneg(pt : Value) -> Value raise {
  if pt.truthy() {
    list3(car(pt), num_sub(symval(q_ear_ec_p), cadr(pt)), caddr(pt))
  } else {
    Nil
  }
}

///|
/// window size of the sliding-window exponentiations
fn ec__window_size(l : Int) -> Int {
  if l <= 64 {
    3
  } else if l <= 160 {
    4
  } else if l <= 384 {
    5
  } else if l <= 896 {
    6
  } else {
    7
  }
}

///|
fn ec_pmult_sliding_window(n : Value, pt : Value) -> Value raise {
  let l = integer_length(n)
  let k = ec__window_size(l)
  let tab = ec_pmult_table(pt, ec__i(k))
  let mut i = l - 1
  let mut res = list3(Fix(1L), Fix(1L), Fix(0L))
  while i >= 0 {
    if logbitp(i, n) {
      let mut s = if i - k + 1 > 0 { i - k + 1 } else { 0 }
      while !logbitp(s, n) {
        s += 1
      }
      let h = i - s + 1
      for _ in 0..<h {
        res = ec_pdouble(res)
      }
      let u = ec__ldb(h, s, n)
      if !num_eq(u, Fix(0L)) {
        res = ec_padd(res, ec__svref(tab, ash(u, -1)))
      }
      i = s - 1
    } else {
      res = ec_pdouble(res)
      i -= 1
    }
  }
  res
}

///|
fn ec_pmult_table(pt : Value, k : Value) -> Value raise {
  let l = 1 << (to_int(k) - 1)
  let tab = ec__vec(l)
  let mut pti = pt
  let pt2 = ec_pdouble(pt)
  aset1(tab, 0, pt) |> ignore
  for i in 1..<l {
    pti = ec_padd(pti, pt2)
    aset1(tab, i, pti) |> ignore
  }
  tab
}

// -------------------------------------------------------------------------- //

///|
/// find random point on given curve
fn d_ec_random() -> Value raise {
  ec_set_q(Str("ec_random")) |> ignore
  ec_l2m(ec_random()) // does not return $ec_inf
}

///|
fn ec_random() -> Value raise { // does not return null
  let p = symval(q_ear_ec_p)
  let a = symval(q_ear_ec_a)
  let b = symval(q_ear_ec_b)
  while true {
    let x = d_random(p) // $random is set by set_random_state
    let mut y = ec__rhs(x, a, b, p)
    if num_eq(y, Fix(0L)) {
      return list2(x, y)
    }
    if num_eq(Fix(1L), d_jacobi(y, p)) {
      let rts = zn_nrt(y, ec__i(2), p, fs_n=list1(list2(p, Fix(1L))))
      // y#0, p>3: 2 solutions
      y = if num_eq(Fix(0L), d_random(ec__i(2))) { car(rts) } else { cadr(rts) }
      if y.truthy() {
        return list2(x, y)
      }
    }
  }
  Nil
}

///|
/// check if point is on the current curve
fn d_ec_point_p(pt : Value) -> Value raise {
  let fn_ : Value = Str("ec_point_p")
  ec_set_q(fn_) |> ignore
  if equal(pt, q_d_ec_inf) {
    t
  } else {
    ec_point_p(ec_m2l(pt, fn_))
  }
}

///|
fn ec_point_p(pt : Value) -> Value raise { // check only non-infinite points
  let p = symval(q_ear_ec_p)
  let x = car(pt)
  let y = cadr(pt)
  lbool(
    num_eq(
      power_mod(y, ec__i(2), p),
      ec__rhs(x, symval(q_ear_ec_a), symval(q_ear_ec_b), p),
    ),
  )
}

///|
/// Checks and converts the optional factorization argument
/// [[p1, e1], ..., [pk, ek]] of ec_point_order and ec2_point_order.
fn ec__fs_ord(fs_ord : Value, ord : Value, fn_ : Value) -> Value raise {
  if fs_ord.truthy() {
    let fs = cdr(fs_ord)
    if d_listp(fs_ord).truthy() &&
      fs.truthy() &&
      every(x => d_listp(x).truthy(), fs) {
      mapcar(x => cdr(x), fs)
    } else {
      ec__err(
        "Third argument to `~m' must be of the form [[p1, e1], ..., [pk, ek]].",
        [fn_],
      )
    }
  } else {
    with_special(q_d_intfaclim, Nil, () => get_factor_list(ord))
  }
}

///|
/// order of a point (as a factor of a given group order)
fn d_ec_point_order(pt : Value, ord : Value, fs_ord? : Value = Nil) -> Value raise {
  let fn_ : Value = Str("ec_point_order")
  ec_set_q(fn_) |> ignore
  let pt = ec_m2l(pt, fn_)
  if !ec_point_p(pt).truthy() {
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
  ec_point_order(pt, ord, fs_ord)
}

///|
fn ec_point_order(pt : Value, ord : Value, fs_ord : Value) -> Value raise {
  let pt = ec_projectify(pt)
  let mut s = ord
  for f in fs_ord.iter() {
    let fp = car(f)
    let fe = cadr(f)
    s = num_truncate(s, b=expt(fp, fe)).0
    while true {
      let qt = ec_pmult(s, pt)
      if num_eq(caddr(qt), Fix(0L)) {
        break
      }
      ec_pmult(fp, qt) |> ignore
      s = num_mul(fp, s)
    }
  }
  s
}

///|
/// discrete logarithm (simple baby-giant-variant, p < 2^36)
fn d_ec_log(pt : Value, gen : Value) -> Value raise {
  let fn_ : Value = Str("ec_log")
  ec_set_q(fn_) |> ignore
  if integer_length(symval(q_ear_ec_p)) > 36 {
    ec__err(
      "`~m': The characteristic should not exceed a length of 36 bit.",
      [fn_],
    )
    |> ignore
  }
  let pt = ec_m2l(pt, fn_)
  let gen = ec_m2l(gen, fn_)
  ec_dlog_baby_giant(pt, gen, symval(q_ear_ec_p))
}

///|
fn ec_dlog_baby_giant(pt : Value, gen : Value, p : Value) -> Value raise {
  let lim = num_sum([p, ec__i(2), num_mul(ec__i(2), isqrt(p))])
  let m = one_plus(isqrt(lim))
  let gi = ec_neg(gen) // additive inverse
  let babies = make_hash_table(kind=Equal)
  let mut r : Value = Fix(0L)
  let mut acc : Value = Nil
  while true {
    let b = ec_add(pt, acc)
    if b is Nil { // point of infinity
      clrhash(babies) |> ignore
      return r
    }
    sethash(b, babies, r) |> ignore
    r = one_plus(r)
    if num_eq(r, m) {
      break
    }
    acc = ec_add(gi, acc)
  }
  let mg = ec_mult(m, gen)
  let mut rr : Value = Fix(1L)
  let mut bb = mg
  while !num_gt(rr, m) {
    // points don't match if we would use projective coords
    let r = gethash(bb, babies)
    if r.truthy() {
      clrhash(babies) |> ignore
      return num_add(num_mul(rr, m), r)
    }
    rr = one_plus(rr)
    bb = ec_add(mg, bb)
  }
  Nil
}

///|
/// curve twist
fn d_ec_twist_curve() -> Value raise {
  ec_set_q(Str("ec_twist_curve")) |> ignore
  cons(list2(q_mlist, q_simp), ec_twist_curve())
}

///|
fn ec_twist_curve() -> Value raise {
  let p = symval(q_ear_ec_p)
  let mut n = ec__i(2)
  while !num_eq(d_jacobi(n, p), ec__i(-1)) {
    n = one_plus(n)
  }
  let nn = num_mul(n, n)
  let a = num_mod(num_mul(nn, symval(q_ear_ec_a)), p)
  let b = num_mod(num_prod([n, nn, symval(q_ear_ec_b)]), p)
  list3(n, a, b)
}

///|
/// Binds *gf-char* to the curve characteristic and *ef-arith?* to nil, as
/// the test functions and ec_trace do.
fn ec__with_gf_char(p : Value, f : () -> Value raise) -> Value raise {
  with_specials([(q_ear_gf_char, p), (q_ear_ef_arith_q, Nil)], f)
}

///|
/// trace of Frobenius (ord = #E = p+1 - trace)
fn d_ec_trace() -> Value raise {
  ec_set_q(Str("ec_trace")) |> ignore
  let p = symval(q_ear_ec_p)
  ec__with_gf_char(p, () => ec_mueller_10_5(
    symval(q_ear_ec_a),
    symval(q_ear_ec_b),
    symval(q_ear_ec_p),
  )) // naive, Shanks-Mestre or SEA
}

// *** SEA ****************************************************************** //
//
// This implementation of the Schoof-Elkies-Atkin algorithm is based on
//        Ein Algorithmus zur Bestimmung der Punktanzahl elliptischer
//     Kurven ueber endlichen Koerpern der Charakteristic groesser drei
// by Volker Mueller.

///|
/// Mueller 2.22
fn d_ec_j_invariant() -> Value raise { // test function
  ec_set_q(Str("ec_j_invariant")) |> ignore
  ec_j_invariant(
    symval(q_ear_ec_a),
    symval(q_ear_ec_b),
    symval(q_ear_ec_p),
  )
}

///|
fn ec_j_invariant(a : Value, b : Value, p : Value) -> Value raise {
  let a4aa = num_prod([ec__i(4), a, a, a])
  zn_quo(
    num_mul(ec__i(1728), a4aa),
    num_add(a4aa, num_prod([ec__i(27), b, b])),
    p,
  )
}

///|
/// modular polynomials: we use precomputed Mueller and Atkin polynomials.
fn ec_sea_data_q() -> Value raise {
  if !boundp(q_ear_ec_sea_data_q) {
    d_load(Str("elliptic_curves/modular_polynomials.lisp"))
  } else {
    Nil
  }
}

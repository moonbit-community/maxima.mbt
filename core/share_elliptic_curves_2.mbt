// Port of share/contrib/elliptic_curves/elliptic_curves.lisp, part 2:
// the Schoof-Elkies-Atkin algorithm (Mueller 7.3 - 9.5): isogenous curves,
// division polynomials, Karatsuba multiplication, the factor f_C of the
// division polynomial and the eigenvalue c mod l (resp. mod l^i).

///|
fn ec__list(xs : Array[Value]) -> Value {
  list(xs)
}

///|
/// The modular polynomial for l: Mueller's if there is one, else Atkin's.
fn ec__gl(l : Value) -> Value raise {
  let g = ec__svref(symval(q_ear_ec_g), l)
  if g.truthy() {
    g
  } else {
    ec__svref(symval(q_ear_ec_g1), l)
  }
}

// -------------------------------------------------------------------------- //
//
// Mueller 7.3 [Computation of at,bt] (find isogenous curve)
//

///|
fn d_ec_mueller_7_3(l : Value, g : Value) -> Value raise { // test function
  ec_set_q(Str("ec_mueller_7_3")) |> ignore
  ec_sea_data_q() |> ignore
  let p = symval(q_ear_ec_p)
  ec__with_gf_char(p, () => {
    let a = symval(q_ear_ec_a)
    let b = symval(q_ear_ec_b)
    let j = ec_j_invariant(a, b, p)
    let mueller = ec__svref(symval(q_ear_ec_g), l).truthy()
    if mueller { // Mueller modular poly
      let gl = ec__svref(symval(q_ear_ec_g), l)
      let (at, bt, p1) = ec_mueller_7_3(l, ec_gl_mod_p(gl, p), g, j, a, b, p)
      list([list2(q_mlist, q_simp), at, bt, p1])
    } else { // Atkin modular poly
      let gl = ec__svref(symval(q_ear_ec_g1), l)
      let (at, bt, fc) = ec_isogenous_from_atkin(
        l,
        ec_gl_mod_p(gl, p),
        g,
        j,
        a,
        b,
        p,
      )
      // (values) when the isogeny cannot be computed
      if at is Nil && bt is Nil && fc is Nil {
        list1(list2(q_mlist, q_simp))
      } else {
        list([list2(q_mlist, q_simp), at, bt, fc])
      }
    }
  })
}

///|
/// g is a root of gl(x,j). (-> ec-glj-roots)
fn ec_mueller_7_3(
  l : Value,
  gl : Value,
  g : Value,
  j : Value,
  a : Value,
  b : Value,
  p : Value,
) -> (Value, Value, Value) raise {
  let glx = ec_dx(gl)
  let gly = ec_dy(gl)
  let glxgj = ec_at_xy(glx, g, j)
  let glygj = ec_at_xy(gly, g, j)
  let glxxgj = ec_at_xy(ec_dx(glx), g, j)
  let glxygj = ec_at_xy(ec_dy(glx), g, j)
  let glyygj = ec_at_xy(ec_dy(gly), g, j)
  // choose s minimal, so that s*(l-1)/12 is an integer (page 58):
  let ggt = num_gcd(one_minus(l), ec__i(12)) // 12/s
  let s = num_truncate(ec__i(12), b=ggt).0
  let s_12 = inv_mod(ggt, p)
  // step 1:
  let e4 = zn_quo(a, ec__i(-3), p)
  let e6 = zn_quo(b, ec__i(-2), p)
  let delta = zn_quo(num_prod([e4, e4, e4]), j, p) // = (e4^3 - e6^2)/1728
  let deltal = zn_quo(
    num_mul(delta, power_mod(g, ggt, p)),
    power_mod(l, ec__i(12), p),
    p,
  )
  // step 2:
  let dg = num_mod(num_mul(g, glxgj), p) // DF in Mueller 7.3
  let dj = num_mod(num_mul(j, glygj), p)
  if num_eq(Fix(0L), dj) {
    // remark 7.2, page 110:
    // p = 65537, a = 1, b = 33965, l = 19 => j = 19797, roots = [24273,1616]
    // with g = 24273 we have dj = 0
    // steps 3-6:
    let e4l = zn_quo(e4, num_mul(l, l), p)
    let at = num_mod(
      num_prod([ec__i(-3), e4l, power_mod(l, ec__i(4), p)]),
      p,
    )
    let jl = zn_quo(num_prod([e4l, e4l, e4l]), deltal, p)
    let e6l = car(
      zn_nrt(num_mul(num_sub(jl, ec__i(1728)), deltal), ec__i(2), p),
    )
    // Mueller suggests to return the neg. and pos. root (step 6).
    let bt = num_mod(
      num_prod([ec__i(2), e6l, power_mod(l, ec__i(6), p)]),
      p,
    )
    let p1 : Value = Fix(0L)
    (at, bt, p1)
  } else {
    // dj # 0:
    // steps 7-9:
    let e2_star = zn_quo(
      num_prod([ec__i(-12), e6, dj]),
      num_prod([s, e4, dg]),
      p,
    )
    let e0 = zn_quo(e6, num_mul(e4, e2_star), p)
    let gq = num_mod(num_prod([ec__i(-1), s_12, e2_star, g]), p)
    let jq = zn_quo(num_prod([ec__i(-1), e4, e4, e6]), delta, p)
    // step 10:
    let dgq = num_mod(
      num_add(
        num_mul(gq, glxgj),
        num_mul(g, num_add(num_mul(gq, glxxgj), num_mul(jq, glxygj))),
      ),
      p,
    )
    let djq = num_mod(
      num_add(
        num_mul(jq, glygj),
        num_mul(j, num_add(num_mul(jq, glyygj), num_mul(gq, glxygj))),
      ),
      p,
    )
    // steps 11-14:
    let e0q = zn_quo(
      num_sub(num_prod([ec__i(-1), s_12, dgq]), num_mul(e0, djq)),
      dj,
      p,
    )
    let tmp = num_add(
      num_prod([ec__i(12), e0q, inv_mod(e0, p)]),
      num_sub(
        num_prod([ec__i(6), e4, e4, inv_mod(e6, p)]),
        num_prod([ec__i(4), e6, inv_mod(e4, p)]),
      ),
    )
    let e4l = zn_quo(
      num_add(e4, num_mul(e2_star, num_sub(e2_star, tmp))),
      num_mul(l, l),
      p,
    )
    let jl = zn_quo(num_prod([e4l, e4l, e4l]), deltal, p)
    let ff = zn_quo(power_mod(l, s, p), g, p)
    let fq = num_mod(num_prod([s_12, e2_star, ff]), p)
    // step 15:
    let dg2 = ec_at_xy(glx, ff, jl)
    let dj2 = ec_at_xy(gly, ff, jl)
    // steps 16-17:
    let jlq = zn_quo(num_prod([ec__i(-1), fq, dg2]), num_mul(l, dj2), p)
    let e6l : Value = if num_eq(e4l, Fix(0L)) {
      Fix(0L)
    } else {
      zn_quo(num_prod([ec__i(-1), e4l, jlq]), jl, p)
    }
    // TODO (original): case e4l = 0: e6l = ?
    // step 18:
    let at = num_mod(
      num_prod([ec__i(-3), e4l, power_mod(l, ec__i(4), p)]),
      p,
    )
    let bt = num_mod(
      num_prod([ec__i(-2), e6l, power_mod(l, ec__i(6), p)]),
      p,
    )
    let p1 = zn_quo(num_prod([ec__i(-1), l, e2_star]), ec__i(2), p)
    (at, bt, p1)
  }
}

//
// f = f(x,y) mod p
//
// x? and y? indicate whether this variable is present,
// e.g. if y? is nil then f is effectively a univariate poly in x.
//
// The global *gf-char* is used for reduction.
//

///|
fn ec_at_y(f : Value, x_q : Value, y : Value) -> Value raise {
  if f is Nil {
    Fix(0L)
  } else if x_q.truthy() {
    let res = Collector::new()
    let mut itr = f
    while itr.truthy() {
      let mut cy = cadr(itr)
      if cy is Cons(_) {
        cy = gf_at(cy, y)
      }
      res.add(car(itr))
      res.add(cy)
      itr = cddr(itr)
    }
    res.result()
  } else {
    gf_at(f, y)
  }
}

///|
fn ec_at_x(f : Value, x : Value, y_q : Value) -> Value raise {
  if f is Nil {
    return Fix(0L)
  }
  if !y_q.truthy() {
    return gf_at(f, x)
  }
  let mut f = f
  let mut res : Value = Nil
  while true {
    let mut cy = cadr(f)
    if !(cy is Cons(_)) {
      cy = list2(Fix(0L), cy)
    }
    res = gf_nplus(res, cy)
    if cddr(f) is Nil {
      let xx = gf_cpow(x, car(f))
      return gf_xctimes(res, xx)
    }
    let xx = gf_cpow(x, num_sub(car(f), caddr(f)))
    res = gf_xctimes(res, xx)
    f = cddr(f)
  }
  Nil
}

///|
fn ec_at_xy(f : Value, x : Value, y : Value) -> Value raise {
  if f is Nil {
    Fix(0L)
  } else {
    ec_at_x(ec_at_y(f, t, y), x, Nil)
  }
}

///|
/// partial derivative by x
fn ec_dx(f : Value) -> Value raise {
  let res = Collector::new()
  let mut itr = f
  while itr.truthy() {
    let e = car(itr)
    if num_eq(e, Fix(0L)) {
      break
    }
    let cy = cadr(itr)
    let cy = if cy is Cons(_) { gf_xctimes(cy, e) } else { gf_ctimes(e, cy) }
    res.add(one_minus(e))
    res.add(cy)
    itr = cddr(itr)
  }
  res.result()
}

///|
/// partial derivative by y
fn ec_dy(f : Value) -> Value raise {
  let res = Collector::new()
  let mut itr = f
  while itr.truthy() {
    let mut cy = cadr(itr)
    if cy is Cons(_) {
      cy = gf_diff(cy)
      if num_eq(Fix(0L), car(cy)) {
        cy = cadr(cy)
      }
      res.add(car(itr))
      res.add(cy)
    }
    itr = cddr(itr)
  }
  res.result()
}

///|
/// For l > 43 a lot of mueller polynomials have sizes of more than 100 kB.
/// We use Atkin polynomials instead. Mueller 7.3 needs some modifications.
/// These are copied from pari-gp/src/modules/ellsea.c/find_isogenous_from_Atkin
/// (license GPL). g is a root of gl(x,j).
fn ec_isogenous_from_atkin(
  l : Value,
  gl : Value,
  g : Value,
  j : Value,
  a : Value,
  b : Value,
  p : Value,
) -> (Value, Value, Value) raise {
  let glx = ec_dx(gl)
  let gly = ec_dy(gl)
  let glxgj = ec_at_xy(glx, g, j)
  let glygj = ec_at_xy(gly, g, j)
  let glxxg = ec_at_x(ec_dx(glx), g, t)
  let glxyg = ec_at_x(ec_dy(glx), g, t)
  let glyyg = ec_at_x(ec_dy(gly), g, t)
  let e4 = zn_quo(a, ec__i(-3), p)
  let e6 = zn_quo(b, ec__i(-2), p)
  let dg = num_mod(num_mul(g, glxgj), p) // dx in pari-gp
  let dj = num_mod(num_mul(j, glygj), p) // dJ
  let aa = num_mod(num_prod([dj, g, e6]), p)
  let bb = num_mod(num_mul(dg, e4), p)
  if num_eq(aa, Fix(0L)) || num_eq(bb, Fix(0L)) {
    return (Nil, Nil, Nil)
  }
  let gp = zn_quo(aa, bb, p) // gprime
  let u1 = ec_compute_u(
    gp,
    glxxg,
    glxyg,
    glyyg,
    j,
    glygj,
    glxgj,
    Fix(1L),
    e4,
    e6,
    p,
  )
  let mut ck : Value = Nil
  let mut wp : Value = Nil
  for jt in ec_glg_roots(gl, g, p).iter() {
    let pg_star = ec_at_xy(glx, g, jt)
    let dg_star = num_mod(num_mul(g, pg_star), p)
    let pj_star = ec_at_xy(gly, g, jt)
    let dj_star = num_mod(num_prod([jt, l, pj_star]), p)
    let u = num_mod(num_prod([dg_star, dj, e6]), p)
    let v = num_mod(num_prod([dj_star, dg, e4]), p)
    let e4t = zn_quo(
      num_prod([u, u, jt]),
      num_prod([v, v, num_sub(jt, ec__i(1728))]),
      p,
    )
    let e6t = zn_quo(num_mul(u, e4t), v, p)
    let u2 = ec_compute_u(
      gp, glxxg, glxyg, glyyg, jt, pj_star, pg_star, l, e4t, e6t, p,
    )
    let p1 = num_mod(num_prod([ec__i(3), l, num_sub(u1, u2)]), p)
    let at = num_mod(
      num_prod([ec__i(-3), power_mod(l, ec__i(4), p), e4t]),
      p,
    )
    let bt = num_mod(
      num_prod([ec__i(-2), power_mod(l, ec__i(6), p), e6t]),
      p,
    )
    let (fc, ck1, wp1) = ec_mueller_7_8(l, at, bt, p1, ck, wp, a, b, p)
    ck = ck1
    wp = wp1
    ec_set_div_poly_mod(l, l, fc, a, b, p) |> ignore
    if ec__svref(symval(q_ear_ec_psi), l) is Nil {
      return (at, bt, fc)
    }
  }
  (Nil, Nil, Nil)
}

///|
fn ec_compute_u(
  gp : Value,
  glxxg : Value,
  glxyg : Value,
  glyyg : Value,
  j : Value,
  glygj : Value,
  glxgj : Value,
  q : Value,
  e4 : Value,
  e6 : Value,
  p : Value,
) -> Value raise {
  let glxxgj = ec_at_y(glxxg, Nil, j)
  let glxygj = ec_at_y(glxyg, Nil, j)
  let glyygj = ec_at_y(glyyg, Nil, j)
  let e6_e4 = zn_quo(e6, e4, p)
  let aa = num_mod(num_mul(gp, glxxgj), p)
  let bb = num_mod(num_prod([ec__i(2), j, q, glxygj, e6_e4]), p)
  let cc = num_mod(num_mul(zn_quo(num_mul(e6_e4, e6_e4), gp, p), j), p)
  let dd = num_mod(
    num_prod([cc, q, q, num_add(glygj, num_mul(j, glyygj))]),
    p,
  )
  let ee = num_mod(
    num_sub(
      zn_quo(e6_e4, ec__i(3), p),
      zn_quo(num_mul(e4, e4), num_mul(ec__i(2), e6), p),
    ),
    p,
  )
  let ff = num_mod(num_sub(num_sub(bb, aa), dd), p)
  num_mod(num_add(zn_quo(ff, glxgj, p), num_mul(ee, q)), p)
}

///|
fn ec_glg_roots(gl : Value, g : Value, p : Value) -> Value raise {
  let glg = ec_at_x(gl, g, t)
  let glg = gf_xctimes(glg, inv_mod(cadr(glg), p)) // monicize poly
  let x_p = gf_pow_sliding_window(list2(Fix(1L), Fix(1L)), p, glg)
  let ggt = gf_gcd(gf_plus(x_p, list2(Fix(1L), one_minus(p))), glg)
  ec_extract_roots(
    gf_equal_degree_factors(list2(ggt, Fix(1L)), p, Fix(1L)),
    p,
  )
}

// -------------------------------------------------------------------------- //
//
// division polynomials (Mueller, definition 4.11, page 39)
//

///|
fn ec_set_div_poly_mod(
  cap : Value,
  n : Value,
  red : Value,
  a : Value,
  b : Value,
  p : Value,
) -> Value raise {
  let n = if num_lt(n, ec__i(4)) { ec__i(4) } else { n }
  let aa = num_mul(a, a)
  let cub = if num_eq(Fix(0L), a) {
    list([ec__i(3), ec__i(1), ec__i(0), b])
  } else if num_eq(Fix(0L), b) {
    list([ec__i(3), ec__i(1), ec__i(1), a])
  } else {
    list([ec__i(3), ec__i(1), ec__i(1), a, ec__i(0), b])
  }
  let size = to_int(cap) + 3
  let psi = set(q_ear_ec_psi, ec__vec(size))
  let psi2 = set(q_ear_ec_psi2, ec__vec(size))
  let psi3 = set(q_ear_ec_psi3, ec__vec(size))
  set(q_ear_ec_poly, gf_nred(cub, red)) |> ignore
  set(q_ear_ec_poly2, gf_sq(symval(q_ear_ec_poly), red)) |> ignore
  set(q_ear_ec_psi_red, red) |> ignore
  // (svref psi 0) nil ;; 0
  aset1(psi, 1, list2(Fix(0L), Fix(1L))) |> ignore // 1
  aset1(psi, 2, list2(Fix(0L), Fix(2L))) |> ignore // 2
  // 3*x^4+6*a*x^2+12*b*x-a^2
  aset1(
    psi,
    3,
    gf_nred(
      gf_mod(
        list([
          ec__i(4),
          ec__i(3),
          ec__i(2),
          num_mul(ec__i(6), a),
          ec__i(1),
          num_mul(ec__i(12), b),
          ec__i(0),
          num_neg(aa),
        ]),
      ),
      red,
    ),
  )
  |> ignore
  aset1(psi2, 1, list2(Fix(0L), Fix(1L))) |> ignore
  aset1(psi2, 2, list2(Fix(0L), num_mod(ec__i(4), p))) |> ignore
  aset1(psi3, 1, list2(Fix(0L), Fix(1L))) |> ignore
  aset1(psi3, 2, list2(Fix(0L), num_mod(ec__i(8), p))) |> ignore
  // 4*x^6+20*a*x^4+80*b*x^3-20*a^2*x^2-16*a*b*x-4*a^3-32*b^2
  aset1(
    psi,
    4,
    gf_nred(
      gf_mod(
        list([
          ec__i(6),
          ec__i(4),
          ec__i(4),
          num_mul(ec__i(20), a),
          ec__i(3),
          num_mul(ec__i(80), b),
          ec__i(2),
          num_neg(num_mul(ec__i(20), aa)),
          ec__i(1),
          num_neg(num_prod([ec__i(16), a, b])),
          ec__i(0),
          num_neg(
            num_add(num_prod([ec__i(32), b, b]), num_prod([ec__i(4), a, aa])),
          ),
        ]),
      ),
      red,
    ),
  )
  |> ignore
  aset1(psi2, 3, gf_sq(aref1(psi, 3), red)) |> ignore
  aset1(psi3, 3, gf_times(aref1(psi, 3), aref1(psi2, 3), red)) |> ignore
  set(q_ear_ec_psi_i, ec__i(4)) |> ignore
  ec_set_div_poly_mod1(n, cap)
}

///|
fn ec_set_div_poly_mod1(n : Value, cap : Value) -> Value raise {
  let mut i = one_plus(symval(q_ear_ec_psi_i))
  while !num_gt(i, n) {
    ec_set_psi(i, cap) |> ignore
    i = one_plus(i)
  }
  if num_gt(n, symval(q_ear_ec_psi_i)) {
    set(q_ear_ec_psi_i, n)
  } else {
    Nil
  }
}

///|
fn ec_set_psi(i : Value, cap : Value) -> Value raise {
  let ii = to_int(i)
  let j = ii >> 1
  let cub2 = symval(q_ear_ec_poly2)
  let psi = symval(q_ear_ec_psi)
  let psi2 = symval(q_ear_ec_psi2)
  let psi3 = symval(q_ear_ec_psi3)
  let red = symval(q_ear_ec_psi_red)
  let v = if ii % 2 == 0 {
    if !num_eq(i, cap) {
      aset1(
        psi3,
        j + 1,
        gf_ktimes(aref1(psi, j + 1), aref1(psi2, j + 1), red),
      )
      |> ignore
    }
    // f[j] * (f[j+2]*f[j-1]^2 - f[j-2]*f[j+1]^2) / 2
    gf_xctimes(
      gf_ktimes(
        aref1(psi, j),
        gf_plus(
          gf_ktimes(aref1(psi, j + 2), aref1(psi2, j - 1), red),
          gf_nminus(gf_ktimes(aref1(psi, j - 2), aref1(psi2, j + 1), red)),
        ),
        red,
      ),
      symval(q_ear_ec_inv2),
    )
  } else {
    if !num_eq(i, cap) {
      aset1(psi2, j + 2, gf_ksq(aref1(psi, j + 2), red)) |> ignore
    }
    if j % 2 == 0 {
      // cub^2*f[j+2]*f[j]^3 - f[j-1]*f[j+1]^3
      gf_plus(
        gf_ktimes(
          gf_ktimes(aref1(psi, j + 2), aref1(psi3, j), red),
          cub2,
          red,
        ),
        gf_nminus(gf_ktimes(aref1(psi, j - 1), aref1(psi3, j + 1), red)),
      )
    } else {
      // f[j+2]*f[j]^3 - cub^2*f[j-1]*f[j+1]^3
      gf_plus(
        gf_ktimes(aref1(psi, j + 2), aref1(psi3, j), red),
        gf_nminus(
          gf_ktimes(
            gf_ktimes(aref1(psi, j - 1), aref1(psi3, j + 1), red),
            cub2,
            red,
          ),
        ),
      )
    }
  }
  aset1(psi, ii, v)
}

//
// Karatsuba splitting:
//
// x*y = (x1*b^(n/2) + x0) * (y1*b^(n/2) + y0) =
//
//    x1*y1*(b^n - b^(n/2)) + (x0+x1)*(y0+y1)*b^(n/2) + x0*y0*(1 - b^(n/2))
//

///|
fn gf_ktimes(x : Value, y : Value, red : Value) -> Value raise {
  if x is Nil || y is Nil {
    return Nil
  }
  let mut n = to_int(num_max(car(x), car(y)))
  if n < 24 {
    gf_times(x, y, red)
  } else {
    if n % 2 == 1 {
      n += 1
    }
    gf_nktimes(copy_list(x), copy_list(y), ec__i(n), red)
  }
}

///|
fn gf_nktimes(x : Value, y : Value, n : Value, red : Value) -> Value raise { // modify x
  let mut n = to_int(n)
  if n < 24 {
    return gf_times(x, y, red)
  }
  if n % 2 == 1 {
    n += 1
  }
  let n_2 = ec__i(n >> 1)
  let (x1, x0) = gf_nsplit(x, n_2)
  let (y1, y0) = gf_nsplit(y, n_2)
  let mut z1 = gf_times(x1, y1, red)
  z1 = gf_nplus(
    gf_nxetimes(copy_list(z1), ec__i(n)),
    gf_nminus(gf_nxetimes(z1, n_2)),
  )
  let mut z0 = gf_times(x0, y0, red)
  z0 = gf_nplus(copy_list(z0), gf_nminus(gf_nxetimes(z0, n_2)))
  let zz = gf_nxetimes(gf_times(gf_nplus(x0, x1), gf_nplus(y0, y1), red), n_2)
  gf_nred(gf_nplus(gf_nplus(z0, z1), zz), red)
}

//
// x^2 = (z1*b^(n/2) + z0)^2 = b^n*z1^2 + 2*b^(n/2)*z0*z1 + z0^2
//
//   where the characteristic is assumed to be odd
//

///|
fn gf_ksq(x : Value, red : Value) -> Value raise {
  if x is Nil {
    return Nil
  }
  let mut n = to_int(car(x))
  if n < 16 {
    gf_sq(x, red)
  } else {
    if n % 2 == 1 {
      n += 1
    }
    gf_nksq(copy_list(x), ec__i(n), red)
  }
}

///|
fn gf_nksq(x : Value, n : Value, red : Value) -> Value raise { // modify x
  let mut n = to_int(n)
  if n < 16 {
    return gf_sq(x, red)
  }
  if n % 2 == 1 {
    n += 1
  }
  let n_2 = ec__i(n >> 1)
  let (z1, z0) = gf_nsplit(x, n_2)
  if z1 is Nil {
    gf_nred(gf_nksq(z0, n_2, red), red)
  } else if z0 is Nil {
    gf_nred(gf_nxetimes(gf_nksq(z1, n_2, red), ec__i(n)), red)
  } else {
    let zz = gf_xectimes(gf_times(z1, z0, red), n_2, ec__i(2))
    let z0 = gf_nksq(z0, n_2, red)
    let z1 = gf_nxetimes(gf_nksq(z1, n_2, red), ec__i(n))
    gf_nred(gf_nplus(gf_nplus(z0, z1), zz), red)
  }
}

///|
fn gf_nsplit(x : Value, n : Value) -> (Value, Value) raise { // modify x
  if x is Nil {
    return (Nil, Nil)
  }
  if num_lt(car(x), n) {
    return (Nil, x)
  }
  rplaca(x, num_sub(car(x), n)) |> ignore
  let mut r = cdr(x)
  while true {
    if cdr(r) is Nil {
      return (x, Nil)
    }
    if num_lt(cadr(r), n) {
      let r0 = cdr(r)
      rplacd(r, Nil) |> ignore
      return (x, r0)
    }
    r = cdr(r)
    rplaca(r, num_sub(car(r), n)) |> ignore
    r = cdr(r)
  }
  (Nil, Nil)
}

// -------------------------------------------------------------------------- //
//
// Mueller 7.8 [Computation of f_C]
//

///|
fn d_ec_mueller_7_8(l : Value, at : Value, bt : Value, p1 : Value) -> Value raise { // test function
  ec_set_q(Str("ec_mueller_7_8")) |> ignore
  ec__with_gf_char(symval(q_ear_ec_p), () => gf_x2p(
    ec_mueller_7_8(
      l,
      at,
      bt,
      p1,
      Nil,
      Nil,
      symval(q_ear_ec_a),
      symval(q_ear_ec_b),
      symval(q_ear_ec_p),
    ).0,
  ))
}

///|
fn ec_mueller_7_8(
  l : Value,
  at : Value,
  bt : Value,
  p1 : Value,
  ck : Value,
  wpv : Value,
  a : Value,
  b : Value,
  p : Value,
) -> (Value, Value, Value) raise {
  let d = ash(num_sub(l, Fix(1L)), -1)
  let d1 = one_plus(d) // step 1
  let l3 = one_plus(ash(num_sub(l, ec__i(3)), -1))
  let mut ck = ck
  let mut wpv = wpv
  if ck is Nil {
    // ck,wp do not depend on at,bt,p1 and can be reused in a second run
    ck = ec_ck(l3, a, b, p) // 2,3
    wpv = ec_wpv(d1, l3, ck) // 4-6
  }
  let ctk = ec_ck(l3, at, bt, p) // 8,9
  let hlp = ec_hlp(l, l3, ck, ctk, p1, p) // 10, second sum
  let h = ec_h_init(d1, hlp, p) // 10
  let fc = ec_fc(d, h, wpv, p) // 11-14
  (fc, ck, wpv)
}

///|
/// Lemma 6.2, Mueller, page 90:
fn ec_ck(ll : Value, a : Value, b : Value, p : Value) -> Value raise {
  let ll = to_int(ll)
  let ck = ec__vec(ll + 1, init=Fix(0L))
  if ll > 0 {
    aset1(ck, 1, zn_quo(num_sub(p, a), ec__i(5), p)) |> ignore
  }
  if ll > 1 {
    aset1(ck, 2, zn_quo(num_sub(p, b), ec__i(7), p)) |> ignore
  }
  if ll > 2 {
    for k = 3; k != ll; k = k + 1 {
      aset1(ck, k, Fix(0L)) |> ignore
      let k1 = k - 1
      for i = 1; i != k1; i = i + 1 {
        aset1(
          ck,
          k,
          num_add(aref1(ck, k), num_mul(aref1(ck, i), aref1(ck, k - 1 - i))),
        )
        |> ignore
      }
      aset1(
        ck,
        k,
        zn_quo(
          num_mul(ec__i(3), aref1(ck, k)),
          ec__i((k - 2) * (2 * k + 3)),
          p,
        ),
      )
      |> ignore
    }
  }
  ck
}

///|
/// steps 4-6:
fn ec_wpv(d1 : Value, l3 : Value, ck : Value) -> Value raise {
  let n = to_int(d1)
  let wp = ec__vec(n)
  let red = list2(d1, Fix(1L)) // reduce by x^(d+1), remainder has necessary precision
  let wp1 = ec_weierstrass(l3, ck) // wp1(z), where z^2 is replaced by x
  let wp1 = gf_nxetimes(wp1, Fix(1L)) // adjust exponents by z^2
  aset1(wp, 1, wp1) |> ignore
  // store wpv(z) (with exponents adjusted)
  for v in 2..<n {
    aset1(wp, v, gf_times(aref1(wp, v - 1), wp1, red)) |> ignore
  }
  wp
}

///|
fn ec_weierstrass(l : Value, ck : Value) -> Value raise {
  let mut wp = list2(ec__i(-1), Fix(1L)) // contains 1/x
  let l = to_int(l)
  for k in 1..<l {
    wp = cons(aref1(ck, k), wp)
    wp = cons(ec__i(k), wp)
  }
  wp
}

///|
/// step 10: return sum(coeffs*x^k , k,1,(l-3)/2) - p1, where x = z^2
fn ec_hlp(
  l : Value,
  l3 : Value,
  ck : Value,
  ctk : Value,
  p1 : Value,
  p : Value,
) -> Value raise {
  let mut hlp : Value = if num_eq(p1, Fix(0L)) {
    Nil
  } else {
    list2(Fix(1L), num_sub(p, p1))
  }
  let l3 = to_int(l3)
  let mut k = 1
  while k != l3 {
    let twok = 2 * k
    let tmp = zn_quo(
      num_sub(num_mul(l, aref1(ck, k)), aref1(ctk, k)),
      ec__i((twok + 1) * (twok + 2)),
      p,
    )
    if !num_eq(tmp, Fix(0L)) {
      hlp = cons(tmp, hlp)
    }
    k += 1
    if !num_eq(tmp, Fix(0L)) {
      hlp = cons(ec__i(k), hlp)
    }
  }
  hlp
}

///|
/// step 10: return h * x^d
fn ec_h_init(d1 : Value, hlp : Value, p : Value) -> Value raise {
  let red = list2(d1, Fix(1L)) // reduce by x^(d+1)
  let mut h = list2(Fix(0L), Fix(1L))
  let mut r_fact : Value = Fix(1L)
  let mut hlp_r = list2(Fix(0L), Fix(1L))
  let n = to_int(d1)
  for r in 1..<n {
    r_fact = num_mul(r_fact, ec__i(r))
    hlp_r = gf_times(hlp_r, hlp, red)
    h = gf_nplus(h, gf_xctimes(hlp_r, inv_mod(r_fact, p)))
  }
  h
}

///|
/// steps 11-14:
fn ec_fc(d : Value, h : Value, wpv : Value, p : Value) -> Value raise {
  let mut h = h
  let mut av : Value = Fix(1L)
  let mut fc = list2(d, Fix(1L))
  let mut v = to_int(d) - 1
  while v >= 0 {
    h = gf_nplus(h, gf_xctimes(aref1(wpv, v + 1), num_sub(p, av)))
    h = gf_nxetimes(h, ec__i(-1)) // h/x
    av = car(last(h))
    fc = nconc(fc, list2(ec__i(v), av))
    v -= 1
  }
  fc
}

// -------------------------------------------------------------------------- //
//
// Mueller 7.9 [Computation of c mod l]
//

///|
fn d_ec_mueller_7_9(l : Value, fc : Value) -> Value raise { // test function
  ec_set_q(Str("ec_mueller_7_9")) |> ignore
  let p = symval(q_ear_ec_p)
  ec__with_gf_char(p, () => {
    ec_set_div_poly_mod(l, l, fc, symval(q_ear_ec_a), symval(q_ear_ec_b), p)
    |> ignore
    let (c, alpha) = ec_mueller_7_9(l, gf_p2x(fc), p)
    list3(list2(q_mlist, q_simp), c, alpha)
  })
}

///|
fn ec_mueller_7_9(l : Value, fc : Value, p : Value) -> (Value, Value) raise {
  // steps 1,2: (ec-set-div-poly-mod called within ec-elkies)
  let psi2 = symval(q_ear_ec_psi2)
  let psi3 = symval(q_ear_ec_psi3)
  // step 3:
  let lx = gf_pow_sliding_window(list2(Fix(1L), Fix(1L)), p, fc)
  // step 4:
  let cub = symval(q_ear_ec_poly)
  let ly = gf_times(
    gf_xctimes(cub, ec__i(4)),
    gf_pow_sliding_window(cub, ash(one_minus(p), -1), fc),
    fc,
  )
  // step 5:
  let ll = to_int(l)
  let l1 = 1 + ((ll - 1) >> 1)
  for alpha0 = 1; alpha0 != l1; alpha0 = alpha0 + 1 {
    let mut alpha = alpha0
    // step 7:
    let mut lhs = gf_ktimes(lx, aref1(psi2, alpha), fc)
    if alpha % 2 == 0 {
      lhs = gf_times(cub, lhs, fc)
    }
    if equal(lhs, ec_rx(ec__i(alpha), cub, fc)) {
      // steps 9-12:
      lhs = gf_ktimes(ly, aref1(psi3, alpha), fc)
      if alpha % 2 == 0 {
        lhs = gf_times(cub, lhs, fc)
      }
      let ry = ec_ry(ec__i(alpha), cub, fc)
      let ok = if equal(lhs, ry) {
        true
      } else if equal(lhs, gf_minus(ry)) {
        alpha = ll - alpha
        true
      } else {
        false
      }
      if ok {
        let c = num_add(ec__i(alpha), zn_quo(p, ec__i(alpha), l))
        return (num_mod(c, l), ec__i(alpha))
      }
    }
  }
  (Nil, Nil)
}

///|
/// step 6:
fn ec_rx(n : Value, cub : Value, fc : Value) -> Value raise { // n >= 1
  let psi = symval(q_ear_ec_psi)
  let nn = to_int(n)
  let mut r1 = gf_times(
    list2(Fix(1L), Fix(1L)),
    aref1(symval(q_ear_ec_psi2), nn),
    fc,
  )
  let mut r2 = gf_nminus(
    gf_ktimes(aref1(psi, nn - 1), aref1(psi, nn + 1), fc),
  )
  if nn % 2 == 0 {
    r1 = gf_times(cub, r1, fc)
  } else {
    r2 = gf_times(cub, r2, fc)
  }
  gf_nplus(r1, r2)
}

///|
/// step 8:
fn ec_ry(n : Value, cub : Value, fc : Value) -> Value raise { // n >= 1
  let psi = symval(q_ear_ec_psi)
  let psi2 = symval(q_ear_ec_psi2)
  let nn = to_int(n)
  let r1 = gf_ktimes(aref1(psi, nn + 2), aref1(psi2, nn - 1), fc)
  let mut r2 = aref1(psi2, nn + 1)
  if nn > 1 {
    r2 = gf_nminus(gf_ktimes(aref1(psi, nn - 2), r2, fc))
  }
  let mut ry = gf_nplus(r1, r2)
  if nn % 2 == 1 {
    ry = gf_times(cub, ry, fc)
  }
  ry
}

///|
/// sliding-window polynomial exponentiation using Karatsuba multiplication
fn gf_pow_sliding_window(x : Value, e : Value, red : Value) -> Value raise {
  let l = integer_length(e)
  let k = ec__window_size(l)
  let tab = gf_pow_sliding_window_table(x, ec__i(k), red)
  let mut res = list2(Fix(0L), Fix(1L))
  let mut i = l - 1
  while i >= 0 {
    if logbitp(i, e) {
      let mut s = if i - k + 1 > 0 { i - k + 1 } else { 0 }
      while !logbitp(s, e) {
        s += 1
      }
      let tmp = i - s + 1
      for _ in 0..<tmp {
        res = gf_sq(res, red)
      }
      let u = ec__ldb(tmp, s, e)
      if !num_eq(u, Fix(0L)) {
        res = gf_ktimes(res, ec__svref(tab, ash(u, -1)), red)
      }
      i = s - 1
    } else {
      res = gf_sq(res, red)
      i -= 1
    }
  }
  res
}

///|
fn gf_pow_sliding_window_table(x : Value, k : Value, red : Value) -> Value raise {
  let l = 1 << (to_int(k) - 1)
  let tab = ec__vec(l)
  let mut xi = x
  let x2 = gf_sq(x, red)
  aset1(tab, 0, x) |> ignore
  for i in 1..<l {
    xi = gf_ktimes(xi, x2, red)
    aset1(tab, i, xi) |> ignore
  }
  tab
}

// -------------------------------------------------------------------------- //
//
// Mueller 8.4 [Computation of c mod l^i in the Elkies case]
//

///|
/// `(meval '(($substitute) ,new '$x ,expr))`
fn ec__subst_x(new_ : Value, expr : Value) -> Value raise {
  meval(mk(q_d_substitute, [new_, list2(q_quote, q_d_x), expr]))
}

///|
/// `(meval '(($num) (($substitute) ,new '$x ,expr)))`
fn ec__num_subst_x(new_ : Value, expr : Value) -> Value raise {
  meval(
    mk(q_d_num, [mk(q_d_substitute, [new_, list2(q_quote, q_d_x), expr])]),
  )
}

///|
/// E = [a0,b0] (passed through to ec-set-div-poly-mod), the postfix 1
/// indicates the corresponding value of the last round.
///
/// Different from the steps 1-3 in Mueller 8.4 the polynomial gt is not
/// computed by Lemma 8.1. These steps are replaced by an algorithm from
/// Couveignes, Dewaghe, Morain - Isogeny cycles and the Schoof-Elkies-Atkin
/// algorithm, 4.1 procedure ComputeTModLn. Steps 1-2b are done in ec-elkies.
fn ec_elkies_l_hati(
  i : Value,
  n : Value,
  l : Value,
  l1 : Value,
  gl : Value,
  tau1 : Value,
  i1_m : Value,
  iso1 : Value,
  a0 : Value,
  b0 : Value,
  a1 : Value,
  b1 : Value,
  a : Value,
  b : Value,
  p : Value,
) -> Value raise {
  // step 2c:
  // i) find next curve E11:
  let j = ec_j_invariant(a, b, p)
  let rts = ec_glj_roots(l, j, p).0
  let mut ck : Value = Nil
  let mut wpv : Value = Nil
  let mut res : Value = Nil
  for g in rts.iter() {
    let (at, bt, p1) = ec_mueller_7_3(l, gl, g, j, a, b, p)
    if !(num_eq(at, Fix(0L)) || num_eq(bt, Fix(0L))) {
      // ii) compute the isogeny, the factor h11 of psi_l(E11) and
      // iii) the new factor h of psi_l^(i+1)(E):
      let (h11, ck1, wpv1) = ec_mueller_7_8(l, at, bt, p1, ck, wpv, a, b, p)
      ck = ck1
      wpv = wpv1
      let h11_m = gf_x2p(h11)
      let num = gf_p2x(ec__num_subst_x(i1_m, h11_m))
      ec_set_div_poly_mod(l, l, num, a1, b1, p) |> ignore
      if ec__svref(symval(q_ear_ec_psi), l).truthy() {
        let (iso11, h) = if num_eq(i, ec__i(2)) {
          (iso1, num)
        } else {
          let iso11 = ec__subst_x(iso1, i1_m)
          (iso11, gf_p2x(ec__num_subst_x(iso11, h11_m)))
        }
        // iv) find eigenvalue mod l^(i+1) by Mueller 8.4, steps 4-10:
        let (c, tau11) = ec_c_mod_l_hati(l1, l, tau1, h, a0, b0, p)
        let l_hati = num_mul(l1, l)
        if tau11 is Nil {
          ()
        } else {
          res = list2(l_hati, list1(c))
          if num_eq(i, n) {
            break
          }
          let k11_m = gf_x2p(ec_k1(l, a, b, at, bt, h11, p))
          let h11_2_m = gf_x2p(gf_sq(h11, Nil))
          let i11_m = meval(mk(q_mquotient, [k11_m, h11_2_m]))
          let lc = ec_elkies_l_hati(
            one_plus(i),
            n,
            l,
            l_hati,
            gl,
            tau11,
            i11_m,
            iso11,
            a0,
            b0,
            a,
            b,
            at,
            bt,
            p,
          )
          if lc.truthy() {
            res = lc
            break
          }
        }
      }
    }
  }
  res
}

///|
/// 4.2. computing h1 and i1; pre-process: k1
fn ec_k1(
  l : Value,
  a : Value,
  b : Value,
  at : Value,
  bt : Value,
  h1 : Value,
  p : Value,
) -> Value raise {
  let ck = ec_ck(l, a, b, p)
  let w = ec_weierstrass(l, ck)
  let ckt = ec_ck(l, at, bt, p)
  let w1 = ec_weierstrass(l, ckt)
  let red = list2(l, Fix(1L))
  let h1w_2 = gf_sq(gf_compose(w, h1, red), red) // reduce by x^l (x = z^2)
  let k1w = gf_times(w1, h1w_2, list2(Fix(1L), Fix(1L))) // reduce by x^1
  // now we know k1(w) = w1*h1(w)^2, but we want to know k1(x)
  //
  // adjusting exponents:
  let mut val = gf_nxetimes(k1w, l) // x^l*k1w
  let arg = gf_nxetimes(w, Fix(1L)) // x*w
  let mut k1x : Value = Nil
  // given two power series arg = w and val = k1(w)
  // we want to find a poly k1(x) such that val = k1(arg):
  let mut i = l
  while true {
    let c = car(last(val)) // c = coeff(val,x,0)
    k1x = nconc(k1x, list2(i, c)) // k1x = k1x + c*x^i
    if num_eq(i, Fix(0L)) {
      return k1x
    }
    // y = - c*arg^i mod x^(i+1)
    let y = gf_xctimes(
      gf_pow(arg, i, list2(one_plus(i), Fix(1L))),
      num_sub(p, c),
    )
    val = gf_nxetimes(gf_nplus(val, y), ec__i(-1)) // val = (val + y)/x
    i = one_minus(i)
  }
  Nil
}

///|
/// Mueller 8.4, steps 4-10:
fn ec_c_mod_l_hati(
  l_hati : Value,
  l : Value,
  alpha : Value,
  gt : Value,
  a0 : Value,
  b0 : Value,
  p : Value,
) -> (Value, Value) raise {
  let mut l_hati = l_hati
  // compute *ec-poly* and the division polynomials psi_0 to psi_l ...
  ec_set_div_poly_mod(num_mul(l_hati, l), l, gt, a0, b0, p) |> ignore
  let psi = symval(q_ear_ec_psi)
  let cub = symval(q_ear_ec_poly)
  // step 4:
  let x_p = gf_pow_sliding_window(list2(Fix(1L), Fix(1L)), p, gt)
  // steps 5,6:
  let mut k : Value = Fix(0L)
  let mut alphat = alpha
  while !num_eq(k, l) {
    // ... and up to psi_{alphat+1} if necessary:
    ec_set_div_poly_mod1(one_plus(alphat), num_mul(l_hati, l)) |> ignore
    // steps 7,8:
    let at = to_int(alphat)
    let tmp = gf_ksq(aref1(psi, at), gt)
    let mut rhs1 = gf_times(list2(Fix(1L), Fix(1L)), tmp, gt)
    let mut rhs2 = gf_ktimes(aref1(psi, at - 1), aref1(psi, at + 1), gt)
    let mut lhs = gf_ktimes(x_p, tmp, gt)
    if at % 2 == 0 {
      lhs = gf_times(cub, lhs, gt)
      rhs1 = gf_times(cub, rhs1, gt)
    } else {
      rhs2 = gf_times(cub, rhs2, gt)
    }
    lhs = gf_nplus(lhs, rhs2)
    lhs = gf_nplus(lhs, gf_nminus(rhs1))
    // steps 9,10:
    if num_gt(car(gf_gcd(lhs, gt)), Fix(0L)) {
      l_hati = num_mul(l, l_hati)
      return (
        num_mod(num_add(alphat, zn_quo(p, alphat, l_hati)), l_hati),
        alphat,
      )
    }
    k = one_plus(k)
    alphat = num_add(alphat, l_hati)
  }
  (Nil, Nil)
}

// -------------------------------------------------------------------------- //
//
// Mueller 9.2 [supersingularity]
//

///|
fn ec_mueller_9_2(p : Value) -> Value raise { // assume p > 3
  ec_check_trace(Fix(0L), p) // prime fields: d = 1, m = p+1
}

///|
/// Mueller 9.5 [j-invariants 0 and 1728]; use only: d = 1
fn ec_mueller_9_5(b : Value, p : Value) -> Value raise {
  let trs = if num_eq(b, Fix(0L)) { // j = 1728 (mod p)
    // cornacchia replaces Mueller 9.4
    let x = num_mul(ec__i(2), car(cornacchia(ec__i(4), p)))
    let i2 = cons(Fix(1L), cdr(zn_nrt(ec__i(-1), ec__i(2), p))) // 1,i
    with_special(q_modulus, p, () => mapcar(n => cmod(num_mul(x, n)), i2)) // symmetric mod
  } else {
    // j = 0:
    let x = num_mul(ec__i(2), car(cornacchia(ec__i(3), p)))
    let om3 = zn_nrt(Fix(1L), ec__i(3), p) // 1,om,om^2
    with_special(q_modulus, p, () => mapcar(n => cmod(num_mul(x, n)), om3))
  }
  for tr in nconc(trs, mapcar(x => neg(x), trs)).iter() {
    // steps 8,15: check trace for "some" random points:
    if ec_check_trace(tr, p).truthy() {
      return tr
    }
  }
  Nil
}

///|
/// Blake,Seroussi,Smart - Elliptic Curves in Cryptography, Algorithm 8.1
///
/// compute a solution to x^2+d*y^2 mod p
fn d_cornacchia(d : Value, p : Value) -> Value raise { // test function
  let xy = cornacchia(d, p)
  if xy.truthy() {
    cons(list2(q_mlist, q_simp), xy)
  } else {
    Nil
  }
}

///|
fn cornacchia(d : Value, p : Value) -> Value raise {
  let rts = zn_nrt(num_sub(p, d), ec__i(2), p)
  if rts is Nil {
    return Nil
  }
  let rt = car(rts)
  let mut x = if num_gt(num_mul(ec__i(2), rt), p) { num_sub(p, rt) } else { rt }
  let mut h = p
  let bound = isqrt(p)
  while !num_le(x, bound) {
    let h0 = h
    h = x
    x = num_mod(h0, x)
  }
  h = num_sub(p, num_mul(x, x))
  let (q, r) = num_truncate(h, b=d)
  let mut y : Value = Nil
  if !num_eq(r, Fix(0L)) {
    return Nil
  }
  y = isqrt(q)
  if y.truthy() && !num_eq(num_mul(y, y), q) {
    return Nil
  }
  list2(x, y)
}

///|
/// check trace for "some" random points:
fn ec_check_trace(tr : Value, p : Value) -> Value raise {
  let ord = num_sub(one_plus(p), tr)
  for _ in 0..<3 { // "some" = 3 (?)
    if !num_eq(
        caddr(ec_pmult(ord, ec_projectify(ec_random()))),
        Fix(0L),
      ) {
      return Nil
    }
  }
  t
}

// Port of share/contrib/elliptic_curves/elliptic_curves.lisp, part 3:
// Mueller 10.1 - 10.5 (splitting type of the modular polynomial, Elkies and
// Atkin primes, combination of the partial information, complete
// algorithm) and the Shanks-Mestre algorithm.

///|
/// `(apply #'* l)`
fn ec__prod_list(l : Value) -> Value raise {
  let mut r : Value = Fix(1L)
  for x in l.iter() {
    r = num_mul(r, x)
  }
  r
}

///|
fn ec__verbose() -> Bool {
  symval(q_d_ec_sea_verbose).truthy()
}

// -------------------------------------------------------------------------- //
//
// Mueller 10.1 [information about c mod l]
//
// Compute the splitting type of gl(x,j) and call the appropriate subroutines.
//
// Assume j # 0, j # 1728 and l < odd prime p.
//

///|
fn d_ec_mueller_10_1(l : Value) -> Value raise { // l < p, test function
  ec_set_q(Str("ec_mueller_10_1")) |> ignore
  ec_sea_data_q() |> ignore
  let p = symval(q_ear_ec_p)
  let a = symval(q_ear_ec_a)
  let b = symval(q_ear_ec_b)
  ec__with_gf_char(p, () => {
    let j = ec_j_invariant(a, b, p)
    let res = ec_mueller_10_1(l, j, a, b, p)
    list3(list2(q_mlist, q_simp), car(res), cons(list2(q_mlist, q_simp), cadr(res)))
  })
}

///|
fn ec_mueller_10_1(
  l : Value,
  j : Value,
  a : Value,
  b : Value,
  p : Value,
) -> Value raise { // l < p
  // steps 1-7:
  let (rts, gl, glj, x_p) = ec_glj_roots(l, j, p)
  if rts is Nil {
    // step 13:
    if ec__verbose() {
      format(t, "atkin : ", []) |> ignore
    }
    return ec_atkin(l, glj, x_p, p)
  }
  let nr = length(rts)
  if nr == 1 {
    if ec__verbose() {
      format(t, "1 root: ", []) |> ignore
    }
    let one_rt = ec_one_root(l, p)
    let elkies = ec_elkies(Fix(1L), l, gl, rts, j, a, b, p) // ec-elkies might fail
    if elkies.truthy() {
      elkies
    } else {
      one_rt
    }
  } else if num_eq(ec__i(nr), one_plus(l)) {
    if ec__verbose() {
      format(t, "~d roots: ", [one_plus(l)]) |> ignore
    }
    ec_lp1_roots(l, p)
  } else {
    // steps 8-11: nr = 2
    if ec__verbose() {
      format(t, "elkies: ", []) |> ignore
    }
    let len = integer_length(p)
    let li = to_int(l)
    let k = if len < 52 {
      1
    } else if li == 3 {
      if len < 128 {
        3
      } else {
        4
      }
    } else if li == 5 {
      if len < 192 {
        2
      } else {
        3
      }
    } else if li == 7 {
      2
    } else if li == 11 {
      if len < 160 {
        1
      } else {
        2
      }
    } else if li == 13 {
      if len < 192 {
        1
      } else {
        2
      }
    } else {
      1
    }
    ec_elkies(ec__i(k), l, gl, rts, j, a, b, p)
  }
}

///|
fn d_ec_glj_roots(l : Value) -> Value raise { // test function
  ec_set_q(Str("ec_glj_roots")) |> ignore
  ec_sea_data_q() |> ignore
  let p = symval(q_ear_ec_p)
  ec__with_gf_char(p, () => {
    let j = ec_j_invariant(symval(q_ear_ec_a), symval(q_ear_ec_b), p)
    let rts = ec_glj_roots(l, j, p).0
    if rts.truthy() {
      cons(list2(q_mlist, q_simp), rts)
    } else {
      Nil
    }
  })
}

///|
/// 10.1, steps 1-7:
/// Compute the splitting type of gl(x,j) and roots if there are any.
fn ec_glj_roots(
  l : Value,
  j : Value,
  p : Value,
) -> (Value, Value, Value, Value) raise {
  // steps 1-3: use pre-computed polynomials instead
  let gl = ec_gl_mod_p(ec__gl(l), p)
  // step 4:
  let glj = ec_at_y(gl, t, j)
  let x_p = gf_pow_sliding_window(list2(Fix(1L), Fix(1L)), p, glj)
  // step 5:
  let ggt = gf_gcd(gf_plus(x_p, list2(Fix(1L), one_minus(p))), glj)
  let mut rts : Value = Nil
  // step 7:
  if !num_eq(Fix(0L), car(ggt)) {
    rts = ec_extract_roots(
      gf_equal_degree_factors(list2(ggt, Fix(1L)), p, Fix(1L)),
      p,
    )
  }
  (rts, gl, glj, x_p)
}

///|
fn ec_gl_mod_p(gl : Value, p : Value) -> Value raise { // gl = gl(x,y)
  let res = Collector::new()
  let mut itr = gl
  while itr.truthy() {
    let cy = cadr(itr)
    let cy = if cy is Cons(_) { gf_mod(cy) } else { num_mod(cy, p) }
    res.add(car(itr))
    res.add(cy)
    itr = cddr(itr)
  }
  res.result()
}

///|
fn ec_extract_roots(factors : Value, p : Value) -> Value raise {
  let mut roots : Value = Nil
  let mut fs = factors
  while fs.truthy() {
    let fs1 = car(fs)
    let len = length(fs1)
    if len == 4 {
      roots = cons(num_sub(p, car(last(fs1))), roots)
    } else if len == 2 {
      roots = cons(Fix(0L), roots)
    }
    fs = cddr(fs)
  }
  sort_list(roots, (x, y) => num_lt(x, y))
}

///|
/// 10.1, steps 8-11 (the Elkies case)
fn ec_elkies(
  k : Value,
  l : Value,
  gl : Value,
  rts : Value,
  j : Value,
  a : Value,
  b : Value,
  p : Value,
) -> Value raise {
  let mut at : Value = Nil
  let mut bt : Value = Nil
  let mut fc : Value = Nil
  let mut ck : Value = Nil
  let mut wpv : Value = Nil
  let mut found = false
  let mut res : Value = Nil
  for g in rts.iter() {
    if ec__svref(symval(q_ear_ec_g), l) is Nil {
      // using Atkin modular poly:
      // steps 8,9:
      let (at1, bt1, fc1) = ec_isogenous_from_atkin(l, gl, g, j, a, b, p)
      at = at1
      bt = bt1
      fc = fc1
      if at.truthy() {
        found = true
      }
    } else {
      // using Mueller modular poly:
      // step 8:
      let (at1, bt1, p1) = ec_mueller_7_3(l, gl, g, j, a, b, p)
      at = at1
      bt = bt1
      if !(num_eq(at, Fix(0L)) || num_eq(bt, Fix(0L))) { // see example in ec-mueller-7-3
        // step 9:
        let (fc1, ck1, wpv1) = ec_mueller_7_8(l, at, bt, p1, ck, wpv, a, b, p)
        fc = fc1
        ck = ck1
        wpv = wpv1
        ec_set_div_poly_mod(l, l, fc, a, b, p) |> ignore
        if ec__svref(symval(q_ear_ec_psi), l) is Nil {
          found = true
        }
      }
    }
    if found {
      // steps 10,11:
      let (c, alpha) = ec_mueller_7_9(l, fc, p)
      if alpha is Nil {
        ()
      } else {
        res = list2(l, list1(c))
        if num_eq(k, Fix(1L)) {
          break
        }
        let k1_m = gf_x2p(ec_k1(l, a, b, at, bt, fc, p))
        let h1_2_m = gf_x2p(gf_sq(fc, Nil))
        let i1_m = meval(mk(q_mquotient, [k1_m, h1_2_m]))
        let iso = with_special(q_modulus, p, () => d_rat(i1_m, Nil))
        let lc = ec_elkies_l_hati(
          ec__i(2),
          k,
          l,
          l,
          gl,
          alpha,
          i1_m,
          iso,
          a,
          b,
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
  res
}

// -------------------------------------------------------------------------- //
//
// Mueller 10.2 [partial information] (the non-Elkies-case)
//

///|
/// 10.2, steps 1,2:
fn ec_one_root(l : Value, p : Value) -> Value raise {
  let rt = car(zn_nrt(p, ec__i(2), l, fs_n=list1(list2(l, Fix(1L)))))
  if rt.truthy() { // e.g. [a,b,p,l]:[233,38,9743,11] fails
    let h = num_mod(num_mul(ec__i(2), rt), l)
    list2(l, list2(h, num_sub(l, h)))
  } else {
    Nil
  }
}

///|
/// 10.2, steps 3-5:
fn ec_lp1_roots(l : Value, p : Value) -> Value raise {
  let ll = num_mul(l, l)
  let alpha = car(zn_nrt(p, ec__i(2), ll, fs_n=list1(list2(l, ec__i(2)))))
  if alpha.truthy() {
    let h = num_mod(num_add(alpha, zn_quo(p, alpha, ll)), ll)
    list2(ll, list2(h, num_sub(ll, h)))
  } else {
    Nil
  }
}

///|
/// 10.2, steps 6-19 (the Atkin case) (l < p only):
fn ec_atkin(l : Value, glj : Value, x_hatp : Value, p : Value) -> Value raise {
  // step 6:
  let d_rest = car(glj)
  // step 7:
  let odd_inc = if num_eq(d_jacobi(p, l), Fix(1L)) { 0 } else { 1 }
  // prepare computation in F_l^2:
  let mut n = ec__i(2)
  while !num_eq(d_jacobi(n, l), ec__i(-1)) { // non-square mod l
    n = one_plus(n)
  }
  let ord = one_minus(num_mul(l, l)) // order of F_l^2
  // ($intfaclim) is bound to nil for the rest of the function
  with_special(q_d_intfaclim, Nil, () => {
    let fs = get_factor_list(ord)
    let fs_ord = sort_list(fs, (x, y) => num_lt(car(x), car(y)))
    let mut ds : Value = Nil
    let mut cs : Value = Nil
    // steps 8,14:
    for d in nreverse(cddr(meval(mk(q_d_divisors, [d_rest])))).iter() {
      // evenp is effectively oddp when odd-inc is 1 resp. jacobi(p,l) # 1
      if evenp(
          num_add(
            num_mul(one_minus(d), num_truncate(d_rest, b=d).0),
            ec__i(odd_inc),
          ),
        ) {
        ds = cons(d, ds)
      }
    }
    let d = if length(ds) == 1 { // shortcut: just one possible d
      car(ds)
    } else {
      // here we compute d different from steps 9,15 in Mueller and use the
      // approach of pari-gp in src/modules/ellsea.c/study_modular_eqn
      // (license GPL):
      ec_comp_d(l, glj, x_hatp, p)
    }
    // steps 12,13, 18,19:
    if num_eq(d, ec__i(2)) {
      cs = cons(Fix(0L), cs)
    } else {
      with_special(q_ear_gf_char, l, () => { // locally compute in F_l^2
        // reduction poly x^2 - n, n is non-square mod l
        let red = list([ec__i(2), ec__i(1), ec__i(0), num_sub(l, n)])
        let phi = d_totient(d) // number of possible traces
        let mut gen : Value = Nil
        let mut i : Value = Fix(1L)
        while true {
          gen = list([ec__i(1), ec__i(1), ec__i(0), i])
          if n_starf_prim_p_1(gen, red, ord, fs_ord).truthy() {
            break
          }
          i = one_plus(i)
        }
        // gen is primitive element
        let gam = gf_pow(gen, num_truncate(ord, b=d).0, red) // gam is d-th root of unity
        let mut gam_i = gam
        // compute the set of possible traces:
        let mut i : Value = Fix(1L)
        let mut old_i : Value = Fix(1L)
        let mut nr : Value = Fix(0L)
        while !num_eq(nr, phi) {
          if num_eq(num_gcd(i, d), Fix(1L)) { // ord(gam^i) = d
            gam_i = gf_times(gam_i, gf_pow(gam, num_sub(i, old_i), red), red)
            old_i = i
            let g1 = if length(gam_i) == 4 { car(last(gam_i)) } else { Fix(0L) }
            let z = zn_quo(num_mul(p, one_plus(g1)), ec__i(2), l)
            if num_eq(d_jacobi(z, l), Fix(1L)) {
              let rts = zn_nrt(z, ec__i(2), l, fs_n=list1(list2(l, Fix(1L))))
              for rt in rts.iter() {
                let rt = num_mod(num_mul(ec__i(2), rt), l)
                if member(rt, cs) is Nil {
                  nr = one_plus(nr)
                  cs = cons(rt, cs)
                }
              }
            }
          }
          i = one_plus(i)
        }
        (Nil : Value)
      })
      |> ignore
    }
    list2(l, sort_list(cs, (x, y) => num_lt(x, y)))
  })
}

///|
fn ec_comp_d(l : Value, glj : Value, x_hatp : Value, p : Value) -> Value raise {
  let lp1 = one_plus(l)
  let n = to_int(lp1)
  let mut cs = nreverse(gf_x2l(copy_list(x_hatp), lp1))
  let c = nth(1, cs)
  rplaca(
    nthcdr(1, cs),
    if num_eq(c, Fix(0L)) {
      one_minus(p)
    } else {
      one_minus(c)
    },
  )
  |> ignore
  let x_p_i = mapcar(x => list1(x), cs)
  let mut acc = x_hatp
  for i in 2..<n {
    acc = gf_times(acc, x_hatp, glj)
    cs = nreverse(gf_x2l(acc, lp1))
    let c = nth(i, cs)
    rplaca(
      nthcdr(i, cs),
      if num_eq(c, Fix(0L)) {
        one_minus(p)
      } else {
        one_minus(c)
      },
    )
    |> ignore
    mapcar2((x, y) => nconc(x, y), x_p_i, mapcar(x => list1(x), cs)) |> ignore
  }
  // now x^p^i is a coefficient-matrix of powers of x^p as columns, where the
  // (l+1)-identity-matrix is already subtracted and the first (zero) column
  // omitted:
  let r = zn_nrank(x_p_i, p)
  num_truncate(lp1, b=num_sub(lp1, r)).0
}

///|
fn zn_nrank(m : Value, p : Value) -> Value raise { // nulls m
  let mut m = m
  let mut r : Value = Fix(0L)
  let mut piv : Value = Nil
  while m.truthy() {
    let mut m1 : Value = Nil
    let mut piv_q = false
    while m.truthy() {
      let mut row = car(m)
      m = cdr(m)
      let c1 = car(row)
      row = cdr(row)
      if num_eq(c1, Fix(0L)) {
        if !every(x => zerop(x), row) {
          m1 = cons(row, m1)
        }
      } else if piv_q {
        zn_naddrows(row, num_sub(p, c1), piv, p) |> ignore // modify row
        if row.truthy() {
          m1 = cons(row, m1)
        }
      } else {
        r = one_plus(r)
        piv = row
        piv_q = true
        let inv = inv_mod(c1, p)
        zn_ncrow(piv, inv, p) |> ignore // modify piv
      }
    }
    m = m1
  }
  r
}

///|
fn zn_ncrow(row : Value, c : Value, p : Value) -> Value raise { // c*row mod p, modifies row
  let mut itr = row
  while itr.truthy() {
    rplaca(itr, num_mod(num_mul(c, car(itr)), p)) |> ignore
    itr = cdr(itr)
  }
  Nil
}

///|
/// row + c*piv mod p, modifies row, assumes len(row) = len(piv)
fn zn_naddrows(row : Value, c : Value, piv : Value, p : Value) -> Value raise {
  let mut itr = row
  let mut piv = piv
  while itr.truthy() {
    rplaca(itr, num_mod(num_add(car(itr), num_mul(c, car(piv))), p)) |> ignore
    piv = cdr(piv)
    itr = cdr(itr)
  }
  Nil
}

// -------------------------------------------------------------------------- //
//
// Mueller 10.4 [combination of the partial information]
//
// Preprocessing: Computation of the two sets C_i with possible traces
// c mod m_i:
//
// Algorithme de Nicolas pour le calcul de champions
//
// This algorithm reduces the work of the baby-step-giant-step-phase to a
// minimum by computing the optimal combination of given results from
// ec-atkin. The return value is a list containing the number of remaining
// possible traces and a binary pattern from which the combination can be
// recovered.
//
// (see Reynald Lercier,
//      ALGORITHMIQUE DES COURBES ELLIPTIQUES DANS LES CORPS FINIS, 11.2.1)
//

///|
fn ec_champions(cost : Value, profit : Value, atkin_bound : Value) -> Value raise {
  if num_eq(atkin_bound, Fix(0L)) {
    return Nil
  }
  if length(profit) == 1 {
    return if num_gt(car(profit), atkin_bound) {
      list2(Fix(1L), car(profit))
    } else {
      Nil
    }
  }
  let cost = list_to_vector(cost)
  let profit = list_to_vector(profit)
  let k = match cost {
    Vec(v) => v.data.length()
    _ => 0
  }
  let kv = ec__i(k)
  let s = if 256 > (1 << k) { 256 } else { 1 << k }
  let a = ec__vec(s, init=Fix(0L))
  let aq = ec__vec(s, init=Fix(0L))
  let mut n = 2
  aset1(aq, 2, Fix(1L)) |> ignore
  for j = 2; j <= k; j = j + 1 {
    let mut i = 1
    let mut i1 = 2
    let mut i2 = 1
    let bit = ash(Fix(1L), j - 1)
    while i1 <= n {
      let b1 = aref1(aq, i1)
      let b2 = logior(aref1(aq, i2), bit)
      let b = if num_lt(
          ec_pattern2val(b1, profit, kv),
          ec_pattern2val(b2, profit, kv),
        ) {
        i1 += 1
        b1
      } else {
        i2 += 1
        b2
      }
      let cst = ec_pattern2val(b, cost, kv)
      while num_lt(cst, ec_pattern2val(aref1(a, i), cost, kv)) {
        i -= 1
      }
      i += 1
      aset1(a, i, b) |> ignore
    }
    while i2 <= n {
      let b = logior(aref1(aq, i2), bit)
      let cst = ec_pattern2val(b, cost, kv)
      while num_lt(cst, ec_pattern2val(aref1(a, i), cost, kv)) {
        i -= 1
      }
      i += 1
      aset1(a, i, b) |> ignore
      i2 += 1
    }
    n = i
    for c = 1; c <= n; c = c + 1 {
      aset1(aq, c, aref1(a, c)) |> ignore
    }
  }
  let mut res : Value = Nil
  for i in 1..<s {
    let ai = aref1(a, i)
    if !num_eq(Fix(0L), ai) {
      let pro = ec_pattern2val(ai, profit, kv)
      if num_ge(pro, atkin_bound) {
        let cst = ec_pattern2val(ai, cost, kv)
        if res is Nil || num_lt(cst, cadr(res)) {
          res = list2(ai, cst)
        }
      }
    }
  }
  res
}

///|
fn ec_pattern2val(pattern : Value, vec : Value, k : Value) -> Value raise {
  let mut val : Value = Fix(1L)
  let k = to_int(k)
  for i in 0..<k {
    if logbitp(i, pattern) {
      val = num_mul(val, aref1(vec, i))
    }
  }
  val
}

///|
/// Lercier notes that the size of the two sets C_i should have a quotient of
/// about #C_babies = 3/4 #C_giants. Here 0.4 seems to be a better value.
///
/// ec-cm12 tries to split atkin accordingly.
fn ec_cm12(atkin : Value) -> (Value, Value, Value, Value, Value, Value) raise {
  let cost_l = mapcar(x => ec__i(length(x)), mapcar(x => cadr(x), atkin))
  let prod = ec__prod_list(cost_l) // nb*ng = prod
  let p4 = num_mul(Flo(0.45), prod) // nb = 0.45*ng   => nb^2 = p4
  let mut delta = prod // start value
  let clen = length(cost_l)
  let mut pattern : Value = Fix(0L) // baby set pattern
  let mut n1 : Value = Nil
  let cost = list_to_vector(cost_l)
  // find the pattern:
  let imax = 1 << clen
  for i in 1..<imax {
    let iv = ec__i(i)
    let ilen = integer_length(iv)
    let mut nb : Value = Fix(1L)
    for k in 0..<ilen {
      if logbitp(k, iv) {
        nb = num_mul(nb, aref1(cost, k))
        let d = num_abs(num_sub(num_mul(nb, nb), p4)) // search for min(|nb^2 - p4|)
        if num_lt(d, delta) {
          delta = d
          n1 = nb
          pattern = ec__ldb(k + 1, 0, iv)
        }
      }
    }
  }
  let n2 = num_truncate(prod, b=n1).0
  // recover the combination from the pattern:
  let mut h1 : Value = Nil
  let mut h2 : Value = Nil
  let mut itr = atkin
  for k in 0..<clen {
    if logbitp(k, pattern) {
      h1 = cons(car(itr), h1)
    } else {
      h2 = cons(car(itr), h2)
    }
    itr = cdr(itr)
  }
  // compute possible traces using CRT:
  let mut l1 = ec_combine_init(car(h1))
  h1 = cdr(h1)
  let mut l2 = ec_combine_init(car(h2))
  h2 = cdr(h2)
  for h in h1.iter() {
    l1 = ec_combine(h, l1)
  }
  for h in h2.iter() {
    l2 = ec_combine(h, l2)
  }
  let m1 = ec__prod_list(car(l1))
  let m2 = ec__prod_list(car(l2))
  let c1 = mapcar(l => car(solve_congruences(l, car(l1))), cadr(l1))
  let c2 = mapcar(l => car(solve_congruences(l, car(l2))), cadr(l2))
  (c1, n1, m1, c2, n2, m2)
}

///|
fn ec_combine_init(l : Value) -> Value raise {
  list2(list1(car(l)), mapcar(x => list1(x), cadr(l)))
}

///|
fn ec_combine(l1 : Value, l2 : Value) -> Value raise {
  let mods = cons(car(l1), car(l2))
  let mut res : Value = Nil
  for r in cadr(l1).iter() {
    for rs in cadr(l2).iter() {
      res = cons(cons(r, rs), res)
    }
  }
  list2(mods, res)
}

///|
/// `(floor (* k (sqrt (coerce p 'double-float))))`
fn ec__sqrt_bound(k : Double, p : Value) -> Value raise {
  floor1(Flo(k * to_double(p).sqrt()))
}

///|
/// Mueller 10.4
fn ec_mueller_10_4(elkies : Value, atkin : Value, p : Value) -> Value raise {
  // elkies should always be non-null: (trace mod 2) is an elkies
  let cm3 = if elkies.truthy() {
    solve_congruences(mapcar(x => caadr(x), elkies), mapcar(x => car(x), elkies))
  } else {
    list2(Fix(0L), Fix(1L))
  }
  let c3 = car(cm3)
  let m3 = cadr(cm3)
  let la = length(atkin)
  let bound = ec__sqrt_bound(4.0, p)
  let mut run1 = true
  let mut c1 : Value = Nil
  let mut m1 : Value = Nil
  let mut inv_m3 : Value = Nil
  let mut c2 : Value = Nil
  let mut m2 : Value = Nil
  let mut c1_len : Value = Nil
  let mut c2_len : Value = Nil
  let mut inv_m2m3 : Value = Nil
  let mut inv_m1m3 : Value = Nil
  let mut m1_2 : Value = Nil
  // step 19: if we fail after 3 tries we exit and change c3,m3
  for i in 0..<3 {
    let mut h : Value = Fix(0L) // step 2
    if la == 0 {
      h = num_sub(c3, num_mul(ec__i(i), m3))
    } else if la == 1 {
      if run1 {
        let mc1 = car(atkin)
        m1 = car(mc1)
        c1 = cadr(mc1)
        inv_m3 = inv_mod(m3, m1)
        run1 = false
      }
      let pt = ec_random()
      let ptp = ec_projectify(pt)
      let q0 = ec_affinify(ec_pmult(num_sub(one_plus(p), c3), ptp))
      let q1p = ec_pmult(m3, ptp)
      let q1 = ec_affinify(q1p)
      let q3 = ec_affinify(ec_pmult(m1, q1p))
      if q0 is Nil {
        h = c3
      } else {
        let q1_2i = ec_mult_table(q1, m1)
        for x in c1.iter() {
          let r1q = num_sub(num_mod(num_mul(num_sub(x, c3), inv_m3), m1), m1)
          if num_eq(x, Fix(0L)) && equal(q0, ec_neg(q3)) { // r1q = - m1
            h = num_sub(c3, num_mul(m1, m3))
            break
          }
          let mut pt1 = ec_mult_by_table(r1q, q1, q1_2i)
          if equal(q0, pt1) {
            h = num_sub(
              num_add(c3, num_mul(num_add(r1q, m1), m3)),
              num_mul(m1, m3),
            )
            break
          }
          pt1 = ec_add(pt1, q3)
          if equal(q0, pt1) {
            h = num_add(c3, num_mul(num_add(r1q, m1), m3))
            break
          }
        }
      }
    } else if run1 {
      let (c1_, c1_len_, m1_, c2_, c2_len_, m2_) = ec_cm12(atkin)
      c1 = c1_
      c1_len = c1_len_
      m1 = m1_
      c2 = c2_
      c2_len = c2_len_
      m2 = m2_
      inv_m2m3 = inv_mod(num_mul(m2, m3), m1)
      inv_m1m3 = inv_mod(num_mul(m1, m3), m2)
      m1_2 = ash(m1, -1)
      run1 = false
      h = ec__mueller_10_4_bsgs(
        p, c3, m3, c1, c1_len, m1, c2, c2_len, m2, inv_m2m3, inv_m1m3, m1_2,
      )
    }
    let hh : Value = if num_gt(num_abs(h), ash(bound, -1)) {
      Nil
    } else if ec_check_trace(h, p).truthy() {
      // steps 15,16:
      h
    } else {
      // steps 17,18:
      let divs = cdr(meval(mk(q_d_divisors, [h])))
      let divs = delete(h, nconc(divs, mapcar(x => neg(x), divs)))
      let mut r : Value = Nil
      for d in divs.iter() {
        if ec_check_trace(d, p).truthy() {
          r = d
          break
        }
      }
      r
    }
    if hh.truthy() {
      return hh
    }
  }
  Nil
  // step 19: else return nil and change c3,m3
}

///|
/// The baby-step giant-step phase of ec-mueller-10-4 for two or more Atkin
/// primes (steps 1-14). Returns h (0 when nothing was found).
fn ec__mueller_10_4_bsgs(
  p : Value,
  c3 : Value,
  m3 : Value,
  c1 : Value,
  c1_len : Value,
  m1 : Value,
  c2 : Value,
  c2_len : Value,
  m2 : Value,
  inv_m2m3 : Value,
  inv_m1m3 : Value,
  m1_2 : Value,
) -> Value raise {
  let mut h : Value = Fix(0L)
  // step 1:
  let pt = ec_random()
  let ptp = ec_projectify(pt)
  // step 2:
  let q0 = ec_affinify(ec_pmult(num_sub(one_plus(p), c3), ptp))
  let qhp = ec_pmult(m3, ptp)
  let q1p = ec_pmult(m2, qhp)
  let q1 = ec_affinify(q1p)
  let q2 = ec_affinify(ec_pmult(m1, qhp))
  let q3 = ec_affinify(ec_pmult(m1, q1p))
  let mut k = 0
  let mut done = false
  let c1n = to_int(c1_len)
  let c2n = to_int(c2_len)
  let babies = ec__vec(c1n)
  if q0 is Nil {
    h = c3
    done = true
  }
  // steps 3-5:
  if !done {
    let r1q_tab = ec__vec(c1n, init=Fix(0L))
    for x in c1.iter() {
      let r1q = num_mod(num_mul(num_sub(x, c3), inv_m2m3), m1)
      aset1(r1q_tab, k, if num_gt(r1q, m1_2) { num_sub(r1q, m1) } else { r1q })
      |> ignore
      k += 1
    }
    ec__sort_vec(r1q_tab, (x, y) => num_lt(x, y)) |> ignore
    let q1_2i = ec_mult_table(q1, m1)
    let mut r1q0 = aref1(r1q_tab, 0)
    let mut pt1 = ec_add(q0, ec_neg(ec_mult_by_table(r1q0, q1, q1_2i)))
    k = 1
    if pt1 is Nil {
      h = num_add(c3, num_prod([r1q0, m2, m3]))
      done = true
    }
    if !done {
      aset1(babies, 0, nconc(pt1, list1(r1q0))) |> ignore
      while k != c1n {
        let r1q = aref1(r1q_tab, k)
        let dr1q = num_sub(r1q, r1q0)
        r1q0 = r1q
        pt1 = ec_add(pt1, ec_neg(ec_mult_by_table(dr1q, q1, q1_2i)))
        if pt1 is Nil {
          h = num_add(c3, num_prod([r1q0, m2, m3]))
          done = true
          break
        }
        aset1(babies, k, nconc(pt1, list1(r1q0))) |> ignore
        k += 1
      }
    }
  }
  if !done {
    ec__sort_vec(babies, (a, b) => num_lt(car(a), car(b)) ||
      (num_eq(car(a), car(b)) && num_lt(cadr(a), cadr(b))))
    |> ignore
  }
  // steps 6-14:
  let r2q_tab = ec__vec(c2n, init=Fix(0L))
  if !done {
    k = 0
    for y in c2.iter() {
      // steps 7-9:
      let r2q = num_sub(num_mod(num_mul(num_sub(y, c3), inv_m1m3), m2), m2)
      if num_eq(r2q, num_neg(m2)) {
        if q3.truthy() {
          let r1q = ec_binary_pt_search(q3, babies)
          if r1q.truthy() {
            h = num_sub(
              num_add(c3, num_prod([r1q, m2, m3])),
              num_prod([m1, m2, m3]),
            )
            done = true
            break
          }
        }
      }
      aset1(r2q_tab, k, r2q) |> ignore
      k += 1
    }
  }
  if !done {
    ec__sort_vec(r2q_tab, (x, y) => num_lt(x, y)) |> ignore
    // steps 10-14:
    let q2_2i = ec_mult_table(q2, m2)
    let mut r2q0 = aref1(r2q_tab, 0)
    let mut pt2 = ec_mult_by_table(r2q0, q2, q2_2i)
    let r1q = if pt2.truthy() { ec_binary_pt_search(pt2, babies) } else { Nil }
    if r1q.truthy() {
      h = num_sum([c3, num_prod([r1q, m2, m3]), num_prod([r2q0, m1, m3])])
    } else {
      let tmp = ec_add(pt2, q3)
      let r1q = if tmp.truthy() { ec_binary_pt_search(tmp, babies) } else { Nil }
      if r1q.truthy() {
        h = num_sum([
          c3,
          num_prod([r1q, m2, m3]),
          num_prod([num_add(r2q0, m2), m1, m3]),
        ])
      } else {
        for k = 1; k != c2n; k = k + 1 {
          let r2q = aref1(r2q_tab, k)
          let dr2q = num_sub(r2q, r2q0)
          r2q0 = r2q
          pt2 = ec_add(pt2, ec_mult_by_table(dr2q, q2, q2_2i))
          let r1q = if pt2.truthy() {
            ec_binary_pt_search(pt2, babies)
          } else {
            Nil
          }
          if r1q.truthy() {
            h = num_sum([c3, num_prod([r1q, m2, m3]), num_prod([r2q, m1, m3])])
            break
          }
          let tmp = ec_add(pt2, q3)
          let r1q = if tmp.truthy() {
            ec_binary_pt_search(tmp, babies)
          } else {
            Nil
          }
          if r1q.truthy() {
            h = num_sum([
              c3,
              num_prod([r1q, m2, m3]),
              num_prod([num_add(r2q, m2), m1, m3]),
            ])
            break
          }
        }
      }
    }
  }
  h
}

///|
fn ec_binary_pt_search(pt : Value, a : Value) -> Value raise {
  let px = car(pt)
  let py = cadr(pt)
  let mut lo = 0
  let mut hi = match a {
    Vec(v) => v.data.length() - 1
    _ => -1
  }
  while !(hi < lo) {
    let m = (lo + hi) >> 1
    let am = aref1(a, m)
    let x = car(am)
    if num_lt(px, x) {
      hi = m - 1
    } else if num_gt(px, x) {
      lo = m + 1
    } else {
      let y = cadr(am)
      if num_lt(py, y) {
        hi = m - 1
      } else if num_gt(py, y) {
        lo = m + 1
      } else {
        return caddr(am)
      }
    }
  }
  Nil
}

///|
fn ec_mult_by_table(n : Value, pt : Value, pt_star2i : Value) -> Value raise {
  if num_eq(Fix(0L), n) || pt is Nil {
    return Nil
  }
  if minusp(n) {
    return ec_neg(ec_mult_by_table(num_neg(n), pt, pt_star2i))
  }
  let mut n = n
  let mut pt = pt
  let mut res : Value = Nil
  let mut i = 1
  while true {
    if oddp(n) {
      res = ec_add(pt, res)
      if num_eq(Fix(1L), n) {
        return res
      }
    }
    n = ash(n, -1)
    pt = aref1(pt_star2i, i)
    i += 1
  }
  Nil
}

///|
fn ec_mult_table(pt : Value, range : Value) -> Value raise {
  let ilen = integer_length(range)
  let pt_2i = ec__vec(ilen)
  let mut pt = pt
  for i in 1..<ilen {
    pt = ec_add(pt, pt)
    aset1(pt_2i, i, pt) |> ignore
  }
  pt_2i
}

// -------------------------------------------------------------------------- //
//
// Mueller 10.5 [complete algorithm]
//
// assume p prime
//

///|
fn d_ec_mueller_10_5() -> Value raise { // test function
  ec_set_q(Str("ec_mueller_10_5")) |> ignore
  ec__with_gf_char(symval(q_ear_ec_p), () => ec_mueller_10_5(
    symval(q_ear_ec_a),
    symval(q_ear_ec_b),
    symval(q_ear_ec_p),
  ))
}

///|
fn ec_mueller_10_5(a : Value, b : Value, p : Value) -> Value raise {
  // steps 1,2:
  if (num_eq(a, Fix(0L)) && num_eq(num_mod(p, ec__i(3)), ec__i(2))) || // see 9.2.1, case 1
    (num_eq(b, Fix(0L)) && num_eq(num_mod(p, ec__i(4)), ec__i(3))) || // see 9.2.2, case 1
    ec_mueller_9_2(p).truthy() {
    if ec__verbose() {
      format(t, "supersingular~%", []) |> ignore
    }
    return Fix(0L)
  }
  // steps 3,4:
  if num_eq(a, Fix(0L)) || num_eq(b, Fix(0L)) { // j = 0 or 1728 (mod p)
    let tr = ec_mueller_9_5(b, p)
    if tr.truthy() {
      if ec__verbose() {
        format(t, "j = 0 or 1728~%", []) |> ignore
      }
      return tr
    }
  }
  // use naive algorithm or Shanks-Mestre for small primes:
  if num_le(p, ec__i(457)) {
    return ec_trace_naive(a, b, p)
  }
  if num_lt(p, Fix(4503599627370496L)) { // 2^52
    return ec_shanks_mestre(a, b, p)
  }
  // SEA:
  ec_sea_data_q() |> ignore
  let bound = ec__sqrt_bound(4.0, p)
  let ilen = integer_length(p)
  let mut m3 = ec__i(2)
  let lmax = 151
  let mut m_atkin : Value = Fix(1L)
  let bound_bsgs = if ilen >= 256 { // max. number of possible traces in 10.4
    ec__i(400000000)
  } else if ilen >= 160 {
    ec__i(300000000)
  } else {
    ec__i(100000000)
  }
  let mut cost : Value = Nil
  let mut profit : Value = Nil
  let mut atkin : Value = Nil
  let elkies = ec__vec(lmax + 1)
  // include trace mod 2:
  let tr2 = ec_trace_mod_2(a, b, p)
  aset1(elkies, 2, tr2) |> ignore // process l = 2 as Elkies
  if ec__verbose() {
    format(t, "mod 2 : [2, [~d]]~%", [caadr(tr2)]) |> ignore
  }
  // steps 6-9:
  let ls = cdr(d_primes(ec__i(3), ec__i(lmax)))
  let j = ec_j_invariant(a, b, p) // Mueller 10.1, step 4
  for l in ls.iter() {
    let mut lc = ec_mueller_10_1(l, j, a, b, p)
    if lc is Nil {
      if ec__verbose() {
        format(t, "failure~%", []) |> ignore
      }
    }
    if lc.truthy() {
      let l_hati = car(lc)
      let cs = cadr(lc)
      let mut nrcs = ec__i(length(cs))
      if ec__verbose() {
        format(t, "[~d, [~{~d~^,~}]]~%", [l_hati, cs]) |> ignore
      }
      if num_eq(Fix(1L), nrcs) {
        ec__svset(elkies, l, lc) |> ignore // process Atkin with c = 0 as Elkies
        m3 = num_mul(l_hati, m3)
      } else {
        cost = cons(nrcs, cost)
        profit = cons(l_hati, profit)
        atkin = cons(lc, atkin) // process Elkies with nrcs > 1 as Atkin
        m_atkin = num_mul(l_hati, m_atkin)
      }
      // steps 10-13:
      if num_ge(num_mul(m3, m_atkin), bound) {
        let mut elkies1 = list1(tr2)
        for l in ls.iter() {
          lc = ec__svref(elkies, l)
          if lc.truthy() {
            elkies1 = cons(lc, elkies1)
          }
        }
        if num_gt(m3, bound) {
          let tr = ec_mueller_10_4(elkies1, Nil, p)
          if tr.truthy() {
            return tr
          } else {
            ec_elkies_fallback(elkies, j, a, b, p) |> ignore
          }
        } else {
          let champ = ec_champions(cost, profit, num_floor(bound, b=m3).0)
          let mut pattern = if champ.truthy() { car(champ) } else { Fix(0L) }
          nrcs = if champ.truthy() { cadr(champ) } else { Fix(0L) }
          if num_lt(nrcs, bound_bsgs) {
            let mut atkin1 : Value = Nil
            for lc in atkin.iter() {
              if oddp(pattern) {
                atkin1 = cons(lc, atkin1)
              }
              pattern = ash(pattern, -1)
            }
            if atkin1.truthy() {
              atkin1 = sort_list(atkin1, (a, b) => length(cadr(a)) <
                length(cadr(b)))
            }
            let tr = ec_mueller_10_4(elkies1, atkin1, p)
            if tr.truthy() {
              return tr
            } else {
              ec_elkies_fallback(elkies, j, a, b, p) |> ignore
            }
          }
        }
      }
    }
  }
  gf_merror(Str("`ec_trace': Not enough modular polynomials."), Nil)
}

///|
fn ec_elkies_fallback(
  elkies : Value,
  j : Value,
  a : Value,
  b : Value,
  p : Value,
) -> Value raise {
  for li in [3, 5, 7, 11, 13] {
    let l = ec__i(li)
    let lc = aref1(elkies, li)
    if lc.truthy() && !num_eq(car(lc), l) {
      let (rts, gl, _, _) = ec_glj_roots(l, j, p)
      let lc = ec_elkies(Fix(1L), l, gl, rts, j, a, b, p)
      if ec__verbose() {
        format(t, "fallback: [~d, [~{~d~^,~}]]~%", [car(lc), cadr(lc)])
        |> ignore
      }
      aset1(elkies, li, lc) |> ignore
    }
  }
  Nil
}

///|
/// tr = 1 mod 2 if and only if x^3+a*x+b is irreducible over Fp
fn ec_trace_mod_2(a : Value, b : Value, p : Value) -> Value raise {
  let cub = if num_eq(Fix(0L), a) {
    list([ec__i(3), ec__i(1), ec__i(0), b])
  } else if num_eq(Fix(0L), b) {
    list([ec__i(3), ec__i(1), ec__i(1), a])
  } else {
    list([ec__i(3), ec__i(1), ec__i(1), a, ec__i(0), b])
  }
  let x_p = gf_pow_sliding_window(list2(Fix(1L), Fix(1L)), p, cub)
  let x_p_x = gf_nplus(x_p, list2(Fix(1L), one_minus(p)))
  let c = if num_eq(Fix(0L), car(gf_gcd(cub, x_p_x))) { 1 } else { 0 }
  list2(ec__i(2), list1(ec__i(c)))
}

///|
fn ec_trace_naive(a : Value, b : Value, p : Value) -> Value raise {
  let mut s : Value = Fix(0L)
  let mut x : Value = Fix(0L)
  while !num_eq(x, p) {
    let y = ec__rhs(x, a, b, p)
    s = num_sub(s, d_jacobi(y, p))
    x = one_plus(x)
  }
  s
}

// ************************************************************************** //

// *** SHANKS-MESTRE ******************************************************** //
//
// This version of the Shanks-Mestre-Algorithm follows
//
// Algorithm 7.4.12, Cohen - A Course in Computational Algebraic Number Theory
//

///|
fn d_ec_shanks_mestre() -> Value raise { // test function
  ec_set_q(Str("ec_shanks_mestre")) |> ignore
  ec__with_gf_char(symval(q_ear_ec_p), () => ec_shanks_mestre(
    symval(q_ear_ec_a),
    symval(q_ear_ec_b),
    symval(q_ear_ec_p),
  ))
}

///|
fn ec_shanks_mestre(a : Value, b : Value, p : Value) -> Value raise {
  let delta = ec__sqrt_bound(2.0, p)
  let p_1 = one_plus(p)
  let lo = num_sub(p_1, delta)
  let hi = num_add(p_1, delta)
  let mut aa : Value = Fix(0L)
  let mut bb : Value = Fix(1L) // big-a, big-a1, big-b in Cohen
  let mut k : Value = Fix(0L)
  let mut k_old : Value = Fix(0L)
  let mut n : Value = Nil
  let mut x : Value = Fix(0L)
  let mut i : Value = Fix(0L)
  while true {
    if num_eq(i, p) {
      return gf_merror(Str("`ec_trace': unexpected failure"), Nil)
    }
    let mut d : Value = Nil
    while true {
      d = ec__rhs(x, a, b, p)
      k = d_jacobi(d, p)
      if !num_eq(k, Fix(0L)) && !num_eq(k, k_old) {
        break
      }
      x = one_plus(x)
    }
    k_old = k
    let aa1 = if num_eq(k, Fix(1L)) {
      aa
    } else {
      num_mod(num_sub(num_mul(ec__i(2), p_1), aa), bb)
    }
    let r = num_mod(num_sub(lo, aa1), bb)
    let m = if num_eq(r, Fix(0L)) { lo } else { num_add(lo, num_sub(bb, r)) }
    let xd = num_mod(num_mul(x, d), p)
    let dd = num_mod(num_mul(d, d), p)
    // twist curve locally
    let h = with_special(
      q_ear_ec_a,
      num_mod(num_mul(dd, symval(q_ear_ec_a)), p),
      () => {
        let pt = list2(xd, dd) // point on twisted curve
        n = ec_baby_giant(pt, m, bb, p)
        let fs_n = with_special(q_d_intfaclim, Nil, () => get_factor_list(n))
        ec_point_order(pt, n, fs_n)
      },
    )
    // assume aa1 = 0 mod gcd(bb,h)
    let gc = zn_gcdex2(h, bb) // third and first entry of $gcdex
    let g = car(gc)
    let c = cadr(gc)
    let h_g = num_truncate(h, b=g).0
    let lcm_hb = num_mul(h_g, bb)
    let h1 = if num_eq(Fix(0L), aa1) {
      lcm_hb
    } else {
      num_mod(num_prod([c, h_g, aa1]), lcm_hb)
    }
    if num_lt(num_sub(n, h), lo) && num_gt(num_add(n, h), hi) {
      break
    }
    bb = num_lcm(bb, h)
    aa = if num_eq(Fix(1L), k) {
      num_mod(h1, bb)
    } else {
      num_mod(num_sub(num_mul(ec__i(2), p_1), h1), bb)
    }
    i = one_plus(i)
  }
  num_mul(k, num_sub(p_1, n))
}

///|
fn ec_baby_giant(pt : Value, m : Value, bb : Value, p : Value) -> Value raise {
  let w = ceiling1(
    num_mul(
      Flo(2.0),
      expt(num_div(Flo(to_double(p)), num_mul(bb, bb)), Flo(0.25)),
    ),
  )
  let ptp = ec_projectify(pt)
  let m_pt = ec_affinify(ec_pmult(m, ptp))
  let bb_pt = ec_affinify(ec_pmult(bb, ptp))
  let babies = make_hash_table(kind=Equal)
  let mut r : Value = Fix(0L)
  let mut qt = m_pt
  while true {
    if qt is Nil {
      clrhash(babies) |> ignore
      return num_add(m, num_mul(bb, r))
    }
    sethash(qt, babies, r) |> ignore
    r = one_plus(r)
    if num_eq(r, w) {
      break
    }
    qt = ec_add(bb_pt, qt)
  }
  let w_bb_pt = ec_affinify(ec_pmult(w, ec_projectify(ec_neg(bb_pt))))
  let mut rr : Value = Fix(1L)
  let mut qt = w_bb_pt
  while true {
    let r = gethash(qt, babies)
    if r.truthy() {
      clrhash(babies) |> ignore
      return num_sum([m, num_mul(bb, r), num_prod([w, bb, rr])])
    }
    rr = one_plus(rr)
    if num_gt(rr, w) {
      gf_merror(Str("`ec_trace': unexpected failure"), Nil) |> ignore
    }
    qt = ec_add(w_bb_pt, qt)
  }
  Nil
}

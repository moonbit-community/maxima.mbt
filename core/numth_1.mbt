// Port of src/numth.lisp, part 1: various number theory functions --
// divsum, totient, jacobi, Gaussian factoring, and the functions in (Z/nZ)*
// (zn_h_order, zn_primroot, zn_log, solve_congruences, zn_nth_root, tables).
//
// Parts 2 and 3 (numth_2.mbt, numth_3.mbt) hold the Galois field code.

// ---------------------------------------------------------------------------
// Private helpers shared by numth_*.mbt.

///|
fn numth__i(n : Int) -> Value {
  Fix(n.to_int64())
}

///|
/// `(= x n)` for a small integer n.
fn numth__eqi(x : Value, n : Int) -> Bool raise {
  num_eq(x, Fix(n.to_int64()))
}

///|
/// `(truncate a b)`, primary value.
fn numth__trunc(a : Value, b : Value) -> Value raise {
  num_truncate(a, b~).0
}

///|
/// A fresh `(0 1)`, the polynomial 1 in the internal representation.
fn numth__one() -> Value {
  list2(Fix(0L), Fix(1L))
}

///|
/// `(equal '(0 1) x)`
fn numth__is_one(x : Value) -> Bool {
  equal(numth__one(), x)
}

///|
/// A fresh `(mlist simp)` header.
fn numth__mlist() -> Value {
  list2(q_mlist, q_simp)
}

///|
/// A fresh `($matrix simp)` header.
fn numth__matrix() -> Value {
  list2(q_d_matrix, q_simp)
}

///|
/// `(let (($intfaclim nil)) ...)`
fn[T] numth__nofaclim(f : () -> T raise) -> T raise {
  with_special(q_d_intfaclim, Nil, f)
}

///|
/// `(let ((*ef-arith?* v)) ...)`
fn[T] numth__ef(v : Value, f : () -> T raise) -> T raise {
  with_special(q_ear_ef_arith_q, v, f)
}

///|
/// `(let ((*gf-char* v)) ...)`
fn[T] numth__with_char(v : Value, f : () -> T raise) -> T raise {
  with_special(q_ear_gf_char, v, f)
}

///|
/// `(let ((modulus v)) ...)`
fn[T] numth__with_modulus(v : Value, f : () -> T raise) -> T raise {
  with_special(q_modulus, v, f)
}

///|
fn numth__efp() -> Bool {
  symval(q_ear_ef_arith_q).truthy()
}

///|
/// `(sort l #'< :key #'car)`
fn numth__sort_car(l : Value) -> Value raise {
  sort_list(l, (a, b) => num_lt(car(a), car(b)))
}

///|
/// `(sort l #'<)`
fn numth__sort_num(l : Value) -> Value raise {
  sort_list(l, (a, b) => num_lt(a, b))
}

///|
/// `(last l 2)`
fn numth__last2(l : Value) -> Value {
  let n = length(l)
  if n <= 2 {
    l
  } else {
    nthcdr(n - 2, l)
  }
}

///|
/// `(make-list n :initial-element x)`
fn numth__make_list(n : Value, x : Value) -> Value raise {
  let c = Collector::new()
  let mut i = to_int64(n)
  while i > 0L {
    c.add(x)
    i -= 1L
  }
  c.result()
}

///|
/// `(apply #'nconc lists)`
fn numth__apply_nconc(lists : Value) -> Value {
  nconc_n(list_to_array(lists))
}

///|
/// `(gf-merror msg args...)` with a MoonBit string.
fn numth__err(msg : String, args : Array[Value]) -> Value raise {
  gf_merror(Str(msg), list(args))
}

///|
/// Remove the first element of l satisfying pred (`:count 1`).
fn numth__remove_first(l : Value, pred : (Value) -> Bool raise) -> Value raise {
  let c = Collector::new()
  let mut r = l
  while r is Cons(_) {
    if pred(car(r)) {
      c.append_list(cdr(r))
      return c.result()
    }
    c.add(car(r))
    r = cdr(r)
  }
  c.result()
}

///|
/// CL `(merge 'list a b pred)`.
fn numth__merge(
  a : Value,
  b : Value,
  pred : (Value, Value) -> Bool raise,
) -> Value raise {
  let c = Collector::new()
  let mut x = a
  let mut y = b
  while x is Cons(_) && y is Cons(_) {
    if pred(car(y), car(x)) {
      c.add(car(y))
      y = cdr(y)
    } else {
      c.add(car(x))
      x = cdr(x)
    }
  }
  c.append_list(if x is Cons(_) { x } else { y })
  c.result()
}

// ---------------------------------------------------------------------------
// Sum of divisors and Totient functions

///|
/// compute the sum of the k'th powers of the divisors of the absolute
/// value of n
fn d_divsum(n : Value, k? : Value = Fix(1L)) -> Value raise {
  if integerp(k) && integerp(n) {
    let n = num_abs(n)
    if minusp(k) {
      list([list1(q_rat), divsum(n, num_neg(k)), expt(n, num_neg(k))])
    } else {
      divsum(n, k)
    }
  } else {
    list([list1(q_d_divsum), n, k])
  }
}

///|
/// divsum assumes its arguments to be non-negative integers.
fn divsum(n : Value, k : Value) -> Value raise {
  numth__nofaclim(fn() {
    if num_le(n, Fix(1L)) {
      Fix(1L)
    } else if zerop(k) {
      // product over e+1
      let mut prod : Value = Fix(1L)
      for pe in get_factor_list(n).iter() {
        prod = num_mul(prod, one_plus(cadr(pe)))
      }
      prod
    } else {
      // product over ((p^k)^(e+1)-1)/(p^k-1)
      let mut prod : Value = Fix(1L)
      for pe in get_factor_list(n).iter() {
        let p = car(pe)
        let e = cadr(pe)
        let tmp = expt(p, k)
        prod = num_mul(
          prod,
          numth__trunc(one_minus(expt(tmp, one_plus(e))), one_minus(tmp)),
        )
      }
      prod
    }
  })
}

///|
/// totient computes the euler totient function
/// i.e. the count of numbers relatively prime to n between 1 and n.
fn d_totient(n : Value) -> Value raise {
  if integerp(n) {
    totient(num_abs(n))
  } else {
    list([list1(q_d_totient), n])
  }
}

///|
/// totient assumes its argument to be an integer.
fn totient(n : Value) -> Value raise {
  numth__nofaclim(fn() {
    if num_lt(n, Fix(2L)) {
      n
    } else {
      let mut prod : Value = Fix(1L)
      for pe in get_factor_list(n).iter() {
        let p = car(pe)
        let e = cadr(pe)
        prod = num_mul(prod, num_mul(one_minus(p), expt(p, one_minus(e))))
      }
      prod
    }
  })
}

// ---------------------------------------------------------------------------
// JACOBI symbol and Gaussian factoring

///|
/// $jacobi/jacobi implement the Kronecker-Jacobi symbol, a light
/// generalization of the Legendre/Jacobi symbols.
/// (for a prime b, $jacobi(a b) is the Legendre symbol).
fn d_jacobi(a : Value, b : Value) -> Value raise {
  if integerp(a) && integerp(b) {
    jacobi(a, b)
  } else {
    list([list1(q_d_jacobi), a, b])
  }
}

///|
/// The implementation follows algorithm 1.4.10 in 'A Course in
/// Computational Algebraic Number Theory' by H. Cohen
fn jacobi(a : Value, b : Value) -> Value raise {
  if zerop(b) {
    return if numth__eqi(num_abs(a), 1) { Fix(1L) } else { Fix(0L) }
  }
  if evenp(a) && evenp(b) {
    return Fix(0L)
  }
  let tab2 : Array[Int] = [0, 1, 0, -1, 0, -1, 0, 1]
  let mut a = a
  let mut b = b
  let mut k = 1
  // remove 2's from b
  let mut v = 0
  while evenp(b) {
    b = ash(b, -1)
    v += 1
  }
  if v % 2 == 1 {
    k = tab2[to_int(logand(a, Fix(7L)))] // (-1)^(a^2-1)/8
  }
  if minusp(b) {
    b = num_neg(b)
    if minusp(a) {
      k = -k
    }
  }
  while true {
    if zerop(a) {
      return if num_gt(b, Fix(1L)) { Fix(0L) } else { numth__i(k) }
    }
    let mut v = 0
    while evenp(a) {
      a = ash(a, -1)
      v += 1
    }
    if v % 2 == 1 {
      if tab2[to_int(logand(b, Fix(7L)))] < 0 {
        // (-1)^(b^2-1)/8
        k = -k
      }
    }
    // compute (-1)^(a-1)(b-1)/4
    if plusp(logand(logand(a, b), Fix(2L))) {
      k = -k
    }
    let r = num_abs(a)
    a = num_rem(b, r)
    b = r
  }
  Nil
}

///|
/// factor over the gaussian primes
fn d_gcfactor(n : Value) -> Value raise {
  let n = cdr(
    d_totaldisrep(
      d_bothcoef(d_rat(d_rectform(n), list1(q_d__pcti)), q_d__pcti),
    ),
  )
  if !(integerp(first(n)) && integerp(second(n))) {
    return gcdisp(nreverse(n))
  }
  let mut res : Value = Nil
  let mut l = gcfactor(second(n), first(n))
  while l is Cons(_) {
    let term = car(l)
    let exp = cadr(l)
    res = cons(
      if numth__eqi(exp, 1) {
        gcdisp(term)
      } else {
        list([list2(q_mexpt, q_simp), gcdisp(term), exp])
      },
      res,
    )
    l = cddr(l)
  }
  if res is Nil {
    Fix(1L)
  } else if cdr(res) is Nil {
    if mexptp(car(res)).truthy() {
      cons(list3(q_mexpt, q_simp, q_gcfactored), cdar(res))
    } else {
      car(res)
    }
  } else {
    cons(list3(q_mtimes, q_simp, q_gcfactored), nreverse(res))
  }
}

///|
fn imodp(p : Value) -> Value raise {
  if !numth__eqi(num_rem(p, Fix(4L)), 1) {
    Nil
  } else if numth__eqi(num_rem(p, Fix(8L)), 5) {
    power_mod(Fix(2L), ash(one_minus(p), -2), p)
  } else if numth__eqi(num_rem(p, Fix(24L)), 17) {
    // p=2(mod 3)
    power_mod(Fix(3L), ash(one_minus(p), -2), p)
  } else {
    // p=1(mod 24)
    let mut i : Value = Fix(5L)
    let mut j : Value = Fix(2L)
    while true {
      if numth__eqi(jacobi(i, p), -1) {
        return power_mod(i, ash(one_minus(p), -2), p)
      }
      let oj = j
      i = num_add(i, oj)
      j = num_sub(Fix(6L), oj)
    }
    Nil
  }
}

///|
fn psumsq(p : Value) -> Value raise {
  if numth__eqi(p, 2) {
    list2(Fix(1L), Fix(1L))
  } else {
    let x = imodp(p)
    if x is Nil {
      Nil
    } else {
      let sp = isqrt(p)
      let mut r1 = p
      let mut r2 = x
      while num_gt(r1, sp) {
        let o1 = r1
        let o2 = r2
        r1 = o2
        r2 = num_rem(o1, o2)
      }
      list2(r1, r2)
    }
  }
}

///|
fn gctimes(a : Value, b : Value, c : Value, d : Value) -> Value raise {
  list2(
    num_sub(num_mul(a, c), num_mul(b, d)),
    num_add(num_mul(a, d), num_mul(b, c)),
  )
}

///|
fn gcdisp(term : Value) -> Value raise {
  if atom(term) {
    term
  } else {
    let rp = car(term)
    let ip0 = cadr(term)
    let ip = if eql(ip0, Fix(1L)) {
      q_d__pcti
    } else {
      list3(list1(q_mtimes), ip0, q_d__pcti)
    }
    if eql(Fix(0L), rp) {
      ip
    } else {
      list3(list1(q_mplus), rp, ip)
    }
  }
}

///|
fn gcfactor(a : Value, b : Value) -> Value raise {
  if zerop(a) && zerop(b) {
    return list2(Fix(0L), Fix(1L))
  }
  numth__nofaclim(fn() {
    let mut e1 : Value = Fix(0L)
    let mut e2 : Value = Fix(0L)
    let mut econt : Value = Fix(0L)
    let g = num_gcd(a, b)
    let mut a = numth__trunc(a, g)
    let mut b = numth__trunc(b, g)
    let mut p : Value = Fix(0L)
    let mut nl = cfactorw(num_add(num_mul(a, a), num_mul(b, b)))
    let mut gl = cfactorw(g)
    let mut cd : Value = Nil
    let mut dc : Value = Nil
    let mut ans : Value = Nil
    let mut plis : Value = Nil
    if numth__eqi(car(gl), 1) {
      gl = Nil
    }
    if numth__eqi(car(nl), 1) {
      nl = Nil
    }
    while true {
      // loop
      if gl is Nil {
        if nl is Nil {
          break
        } else {
          p = car(nl)
        }
      } else if nl is Nil {
        p = car(gl)
      } else {
        p = num_max(car(gl), car(nl))
      }
      cd = psumsq(p)
      if cd is Nil {
        plis = cons(p, cons(cadr(gl), plis))
        gl = cddr(gl)
        continue
      } else if equal(p, car(nl)) {
        // gcremainder: remainder(real((a+bi)cd~),p), z~ is complex conjugate
        if zerop(
            num_rem(num_add(num_mul(a, car(cd)), num_mul(b, cadr(cd))), p),
          ) {
          e1 = cadr(nl)
          dc = cd
        } else {
          e2 = cadr(nl)
          dc = reverse(cd)
        }
        dc = gcexpt(dc, cadr(nl))
        dc = gctimes(a, b, car(dc), num_neg(cadr(dc)))
        a = numth__trunc(car(dc), p)
        b = numth__trunc(cadr(dc), p)
        nl = cddr(nl)
      }
      if equal(p, car(gl)) {
        econt = num_add(econt, cadr(gl))
        if equal(p, Fix(2L)) {
          e1 = num_add(e1, num_mul(Fix(2L), cadr(gl)))
        } else {
          e1 = num_add(e1, cadr(gl))
          e2 = num_add(e2, cadr(gl))
        }
        gl = cddr(gl)
      }
      if !zerop(e1) {
        ans = cons(cd, cons(e1, ans))
        e1 = Fix(0L)
      }
      if !zerop(e2) {
        ans = cons(reverse(cd), cons(e2, ans))
        e2 = Fix(0L)
      }
    }
    // ret
    let cd = gcexpt(list2(Fix(0L), Fix(-1L)), num_rem(econt, Fix(4L)))
    let rcd = first(cd)
    let icd = second(cd)
    let l = mapcar(x => signum(x), gctimes(a, b, rcd, icd))
    let r = first(l)
    let i = second(l)
    if numth__eqi(r, -1) || numth__eqi(i, -1) {
      plis = cons(Fix(-1L), cons(Fix(1L), plis))
    }
    if zerop(r) {
      ans = cons(list2(Fix(0L), Fix(1L)), cons(Fix(1L), ans))
    }
    append(plis, ans)
  })
}

///|
fn gcsqr(a : Value) -> Value raise {
  let r = first(a)
  let i = second(a)
  list2(num_sub(num_mul(r, r), num_mul(i, i)), ash(num_mul(r, i), 1))
}

///|
fn gctime1(a : Value, b : Value) -> Value raise {
  gctimes(car(a), cadr(a), car(b), cadr(b))
}

///|
fn gcexpt(a : Value, n : Value) -> Value raise {
  if zerop(n) {
    list2(Fix(1L), Fix(0L))
  } else if numth__eqi(n, 1) {
    a
  } else if evenp(n) {
    gcexpt(gcsqr(a), ash(n, -1))
  } else {
    gctime1(a, gcexpt(gcsqr(a), ash(n, -1)))
  }
}

// ---------------------------------------------------------------------------
// Maxima functions in (Z/nZ)*
//
// zn_h_order, zn_primroot_p, zn_primroot, zn_log,
// solve_congruences, zn_characteristic_factors, zn_factor_generators,
// zn_nth_root, zn_add_table, zn_mult_table, zn_power_table
//
// 2012 - 2020, Volker van Nek

///|
fn zn_quo(n : Value, d : Value, p : Value) -> Value raise {
  num_mod(num_mul(n, inv_mod(d, p)), p)
}

///|
/// `fs-phi` given as Maxima list [[p1, e1], ..., [pk, ek]]: Lispify it and
/// prepend the totient.
fn numth__lispify_fs(fs : Value, msg : String) -> Value raise {
  if d_listp(fs).truthy() && d_listp(cadr(fs)).truthy() {
    let fs = mapcar(x => cdr(x), cdr(fs)) // Lispify fs-phi
    cons(totient_from_factors(fs), fs)
  } else {
    numth__err(msg, [])
  }
}

///|
/// compute the order of x in (Z/nZ)*
///
/// optional argument: ifactors of totient(n) as returned in Maxima by
///    block([factors_only:false], ifactors(totient(n)))
///    e.g. [[2, 3], [3, 1], ... ]
fn d_zn_order(x : Value, n : Value, fs_phi? : Value = Nil) -> Value raise {
  if !(integerp(x) && integerp(n)) {
    return if fs_phi.truthy() {
      list([list1(q_d_zn_order), x, n, fs_phi])
    } else {
      list([list1(q_d_zn_order), x, n])
    }
  }
  if num_lt(n, Fix(1L)) {
    return Nil
  }
  let x = num_mod(x, n)
  if numth__eqi(x, 0) {
    Nil
  } else if numth__eqi(x, 1) {
    if numth__eqi(n, 1) {
      Nil
    } else {
      Fix(1L)
    }
  } else if !numth__eqi(num_gcd(x, n), 1) {
    Nil
  } else {
    let fs_phi = if fs_phi.truthy() {
      numth__lispify_fs(
        fs_phi, "Third argument to `zn_h_order' must be of the form [[p1, e1], ..., [pk, ek]].",
      )
    } else {
      totient_with_factors(n)
    }
    zn_h_order(
      x,
      n,
      car(fs_phi), // phi
      cdr(fs_phi),
    ) // factors of phi with multiplicity
  }
}

///|
fn zn_order(x : Value, n : Value, phi : Value, fs_phi : Value) -> Value raise {
  format(t, "`zn_h_order' is deprecated. ~%Please use `zn-order' instead.~%", [])
  |> ignore
  zn_h_order(x, n, phi, fs_phi)
}

///|
/// compute order of x as a divisor of the known group order
fn zn_h_order(x : Value, n : Value, ord : Value, fs_ord : Value) -> Value raise {
  let mut ord = ord
  for f in fs_ord.iter() {
    let p = car(f)
    let mut e = cadr(f)
    ord = numth__trunc(ord, expt(p, e))
    let mut z = power_mod(x, ord, n)
    // ord(z) = p^i, i from [0,e]
    // replace p^e in ord by p^i : x^(ord*p^i/p^e) = 1
    while !numth__eqi(z, 1) {
      ord = num_mul(ord, p)
      if numth__eqi(e, 1) {
        break
      }
      e = one_minus(e)
      z = power_mod(z, p, n)
    }
  }
  ord
}

///|
/// compute totient (euler-phi) of n and its factors in one function
///
/// returns a list of the form (phi ((p1 e1) ... (pk ek)))
fn totient_with_factors(n : Value) -> Value raise {
  numth__nofaclim(fn() {
    let mut phi : Value = Fix(1L)
    let mut fs : Value = Nil
    let fs_n = get_factor_list(n)
    for f in fs_n.iter() {
      let p = car(f)
      let e = cadr(f)
      phi = num_mul(phi, num_mul(one_minus(p), expt(p, one_minus(e))))
      if num_gt(e, Fix(1L)) {
        fs = cons(list2(p, one_minus(e)), fs)
      }
      fs = append(get_factor_list(one_minus(p)), fs)
    }
    fs = copy_tree(fs) // this deep copy is a workaround to avoid references
    // to the list returned by ifactor.lisp/get-factor-list.
    // see bug 3510983
    fs = numth__sort_car(fs)
    let mut g = car(fs)
    let mut fs_phi : Value = Nil
    for f in cdr(fs).iter() {
      if num_eq(car(f), car(g)) {
        rplaca(cdr(g), num_add(cadr(g), cadr(f))) |> ignore // assignment
      } else {
        fs_phi = cons(g, fs_phi)
        g = f
      }
    }
    cons(phi, reverse(cons(g, fs_phi)))
  })
}

///|
/// recompute totient from given factors
///
/// fs-phi: factors of totient with multiplicity: ((p1 e1) ... (pk ek))
fn totient_from_factors(fs_phi : Value) -> Value raise {
  let mut phi : Value = Fix(1L)
  for f in fs_phi.iter() {
    phi = num_mul(phi, expt(car(f), cadr(f)))
  }
  phi
}

///|
/// for n > 2 is x a primitive root modulo n
///   when n does not divide x
///   and for all prime factors p of phi = totient(n)
///   x^(phi/p) mod n # 1
///
/// optional argument: ifactors of totient(n)
fn d_zn_primroot_p(x : Value, n : Value, fs_phi? : Value = Nil) -> Value raise {
  if !(integerp(x) && integerp(n)) {
    return if fs_phi.truthy() {
      list([list1(q_d_zn_primroot_p), x, n, fs_phi])
    } else {
      list([list1(q_d_zn_primroot_p), x, n])
    }
  }
  let x = num_mod(x, n)
  if numth__eqi(x, 0) {
    Nil
  } else if numth__eqi(x, 1) {
    if numth__eqi(n, 2) {
      t
    } else {
      Nil
    }
  } else if num_le(n, Fix(2L)) {
    Nil
  } else {
    let fs_phi = if fs_phi.truthy() {
      numth__lispify_fs(
        fs_phi, "Third argument to `zn_primroot_p' must be of the form [[p1, e1], ..., [pk, ek]].",
      )
    } else {
      totient_with_factors(n)
    }
    zn_primroot_p(
      x,
      n,
      car(fs_phi), // phi
      mapcar(f => car(f), cdr(fs_phi)),
    ) // factors only (omitting multiplicity)
  }
}

///|
fn zn_primroot_p(x : Value, n : Value, phi : Value, fs_phi : Value) -> Value raise {
  if !numth__eqi(num_gcd(x, n), 1) {
    return Nil
  }
  for p in fs_phi.iter() {
    if numth__eqi(power_mod(x, numth__trunc(phi, p), n), 1) {
      return Nil
    }
  }
  t
}

///|
/// find the smallest primitive root modulo n
///
/// optional argument: ifactors of totient(n)
fn d_zn_primroot(n : Value, fs_phi? : Value = Nil) -> Value raise {
  if !integerp(n) {
    return if fs_phi.truthy() {
      list([list1(q_d_zn_primroot), n, fs_phi])
    } else {
      list([list1(q_d_zn_primroot), n])
    }
  }
  if num_le(n, Fix(1L)) {
    Nil
  } else if numth__eqi(n, 2) {
    Fix(1L)
  } else {
    if symval(q_d_zn_primroot_pretest).truthy() {
      if !cyclic_p(n).truthy() {
        return Nil
      }
    }
    let fs_phi = if fs_phi.truthy() {
      numth__lispify_fs(
        fs_phi, "Second argument to `zn_primroot' must be of the form [[p1, e1], ..., [pk, ek]].",
      )
    } else {
      totient_with_factors(n)
    }
    zn_primroot(
      n,
      car(fs_phi), // phi
      mapcar(f => car(f), cdr(fs_phi)),
    ) // factors only (omitting multiplicity)
  }
}

///|
/// (Z/nZ)* is cyclic if n = 2, 4, p^k or 2*p^k where p prime > 2
fn cyclic_p(n : Value) -> Value raise {
  let mut n = n
  if num_lt(n, Fix(2L)) {
    return Nil
  }
  if num_lt(n, Fix(8L)) {
    return t // 2,3,4,5,2*3,7
  }
  if evenp(n) {
    // 2*p^k
    n = ash(n, -1) // -> p^k
    if evenp(n) {
      return Nil
    }
  }
  numth__nofaclim(fn() {
    let mut len = 0
    let (n1, fs) = get_small_factors(n)
    let n = n1
    if fs.truthy() {
      len = length(fs)
    }
    if numth__eqi(n, 1) {
      return lbool(len == 1)
    }
    if len > 0 {
      return Nil
    }
    if primep(n).truthy() {
      return t
    }
    let fs = convert_list(get_large_factors(n))
    lbool(length(fs) == 1)
  })
}

///|
fn zn_primroot(n : Value, phi : Value, fs_phi : Value) -> Value raise {
  let mut i : Value = Fix(2L)
  while !num_eq(i, n) {
    if zn_primroot_p(i, n, phi, fs_phi).truthy() {
      return i
    }
    if num_eq(i, symval(q_d_zn_primroot_limit)) {
      if symval(q_d_zn_primroot_verbose).truthy() {
        format(
          t,
          "`zn_primroot' stopped at zn_primroot_limit = ~A~%",
          [symval(q_d_zn_primroot_limit)],
        )
        |> ignore
      }
      return Nil
    }
    i = one_plus(i)
  }
  Nil
}

// Chinese Remainder Theorem

///|
let numth__chinese_warned : Ref[Bool] = Ref::new(false)

///|
/// `chinese` is deprecated in favour of `solve_congruences`.
fn d_chinese(a : Value) -> Value raise {
  // the deprecation warning of (defmfun ($chinese :deprecated-p ...))
  if !numth__chinese_warned.val {
    numth__chinese_warned.val = true
    mwarning(
      list1(
        aformat(
          Nil,
          Str("~M is deprecated; use ~M."),
          list2(q_d_chinese, q_d_solve_congruences),
        ),
      ),
    )
    |> ignore
  }
  apply(q_d_solve_congruences, a)
}

///|
fn d_solve_congruences(
  rems : Value,
  mods : Value,
  return_lcm_q? : Value = Nil,
) -> Value raise {
  let mut rems = rems
  let mut mods = mods
  if !(d_listp(rems).truthy() && d_listp(mods).truthy()) {
    return list([list1(q_d_solve_congruences), rems, mods])
  }
  let lr = d_length(rems)
  let lm = d_length(mods)
  if numth__eqi(lr, 0) || numth__eqi(lm, 0) || !num_eq(lr, lm) {
    return numth__err("Unsuitable arguments to `solve_congruences': ~m ~m", [
      rems, mods,
    ])
  }
  rems = cdr(rems)
  if !every(x => integerp(x), rems) {
    return list([list1(q_d_solve_congruences), cons(numth__mlist(), rems), mods])
  }
  mods = cdr(mods)
  if !every(x => integerp(x), mods) {
    return list([
      list1(q_d_solve_congruences),
      cons(numth__mlist(), rems),
      cons(numth__mlist(), mods),
    ])
  }
  if eql(return_lcm_q, q_d_lcm) {
    cons(numth__mlist(), solve_congruences(rems, mods))
  } else {
    car(solve_congruences(rems, mods))
  }
}

///|
fn solve_congruences(rems : Value, mods : Value) -> Value raise {
  if length(mods) == 1 {
    list2(car(rems), car(mods))
  } else {
    let rp = car(rems)
    let p = car(mods)
    let rq_q = solve_congruences(cdr(rems), cdr(mods))
    if rq_q.truthy() {
      let rq = car(rq_q)
      let q = cadr(rq_q)
      let gc = zn_gcdex2(q, p)
      let g = car(gc) // gcd
      let c = cadr(gc) // CRT-coefficient
      if numth__eqi(g, 1) {
        // coprime moduli
        let h = num_mod(num_mul(num_sub(rp, rq), c), p)
        let x = num_add(num_mul(h, q), rq)
        list2(x, num_mul(p, q))
      } else if zerop(num_mod(num_sub(rp, rq), g)) {
        // ensures unique solution
        let h = num_mul(num_sub(rp, rq), c)
        let q_g = numth__trunc(q, g)
        let lcm_pq = num_mul(p, q_g)
        list2(num_mod(num_add(rq, num_mul(h, q_g)), lcm_pq), lcm_pq)
      } else {
        Nil
      }
    } else {
      Nil
    }
  }
}

///|
/// (zn-gcdex2 x y) returns `(,g ,c) where c*x + d*y = g = gcd(x,y)
fn zn_gcdex2(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  let mut x1 : Value = Fix(1L)
  let mut y1 : Value = Fix(0L)
  while !numth__eqi(y, 0) {
    let (q, r) = num_truncate(x, b=y)
    x = y
    y = r
    let ox1 = x1
    x1 = y1
    y1 = num_sub(ox1, num_mul(q, y1))
  }
  list2(x, x1)
}

///|
/// discrete logarithm:
/// solve g^x = a mod n, where g is a generator of (Z/nZ)* or of a subgroup
/// containing a
///
/// optional argument: ifactors of zn_h_order(g,n)
fn d_zn_log(a : Value, g : Value, n : Value, fs_ord? : Value = Nil) -> Value raise {
  if !(integerp(a) && integerp(g) && integerp(n)) {
    return if fs_ord.truthy() {
      list([list1(q_d_zn_log), a, g, n, fs_ord])
    } else {
      list([list1(q_d_zn_log), a, g, n])
    }
  }
  let mut a = a
  if minusp(a) {
    a = num_mod(a, n)
  }
  if numth__eqi(a, 0) || num_ge(a, n) {
    Nil
  } else if numth__eqi(a, 1) {
    Fix(0L)
  } else if num_eq(g, a) {
    Fix(1L)
  } else if num_gt(num_gcd(a, n), Fix(1L)) {
    Nil
  } else {
    let fs_ord = if fs_ord.truthy() {
      // totient resp. order in general
      numth__lispify_fs(
        fs_ord, "Fourth argument to `zn_log' must be of the form [[p1, e1], ..., [pk, ek]].",
      )
    } else {
      let ord = d_zn_order(g, n)
      numth__nofaclim(fn() { cons(ord, get_factor_list(ord)) })
    }
    if zerop(num_mod(num_sub(a, num_mul(g, g)), n)) {
      Fix(2L)
    } else if numth__eqi(num_mod(num_mul(a, g), n), 1) {
      num_mod(Fix(-1L), car(fs_ord))
    } else {
      zn_dlog(
        a,
        g,
        n,
        car(fs_ord), // order
        cdr(fs_ord),
      ) // factors with multiplicity
    }
  }
}

///|
/// Pohlig-Hellman-reduction:
///
///   Solve g^x = a mod n.
///   Assume, that a is an element of (Z/nZ)*
///     and g is a generator of (Z/nZ)* or of a subgroup containing a.
fn zn_dlog(a : Value, g : Value, n : Value, ord : Value, fs_ord : Value) -> Value raise {
  let mut mods : Value = Nil
  let mut dlogs : Value = Nil
  let g_inv = inv_mod(g, n)
  for f in fs_ord.iter() {
    let p = car(f)
    let e = cadr(f)
    let mut ord_p = numth__trunc(ord, p)
    let om = power_mod(g, ord_p, n) // om is a generator of prime order p
    let mut xp : Value = Fix(0L)
    // Let op = ord/p^e, gp = g^op (mod n), ap = a^op (mod n) and
    //     xp = x (mod p^e).
    // gp is of order p^e and therefore
    //   (*) gp^xp = ap (mod n).
    let mut b = a
    let mut k : Value = Fix(0L)
    let mut pk : Value = Fix(1L)
    let mut acc = g_inv
    let e1 = one_minus(e)
    while true {
      // Solve (*) by solving e logs in subgroups of order p.
      let xk = dlog_rho(power_mod(b, ord_p, n), om, p, n)
      xp = num_add(xp, num_mul(xk, pk))
      k = one_plus(k)
      if num_eq(k, e) {
        break // => xp = x_0+x_1*p+x_2*p^2+...+x_{e-1}*p^{e-1} < p^e
      }
      ord_p = numth__trunc(ord_p, p)
      pk = num_mul(pk, p)
      if !numth__eqi(xk, 0) {
        b = num_mod(num_mul(b, power_mod(acc, xk, n)), n)
      }
      if !num_eq(k, e1) {
        acc = power_mod(acc, p, n)
      }
    }
    mods = cons(expt(p, e), mods)
    dlogs = cons(xp, dlogs)
  }
  // Find x (mod ord) with x = xp (mod p^e) for all p,e.
  car(solve_congruences(dlogs, mods))
}

///|
/// baby-steps-giant-steps: g is generator of order p mod n
fn dlog_baby_giant(a : Value, g : Value, p : Value, n : Value) -> Value raise {
  let m = one_plus(isqrt(p))
  let gi = inv_mod(g, n)
  let babies = make_hash_table(kind=Eql)
  let mut r : Value = Fix(0L)
  let mut b = a
  while true {
    if numth__eqi(b, 1) {
      clrhash(babies) |> ignore
      return r
    }
    sethash(b, babies, r) |> ignore
    r = one_plus(r)
    if num_eq(r, m) {
      break
    }
    b = num_mod(num_mul(gi, b), n)
  }
  let g_m = power_mod(g, m, n)
  let mut rr : Value = Fix(0L)
  let mut bb : Value = Fix(1L)
  while true {
    let r = gethash(bb, babies)
    if r.truthy() {
      clrhash(babies) |> ignore
      return num_add(num_mul(rr, m), r)
    }
    rr = one_plus(rr)
    bb = num_mod(num_mul(g_m, bb), n)
  }
  Nil
}

///|
/// brute-force
fn dlog_naive(a : Value, g : Value, n : Value) -> Value raise {
  let mut i : Value = Fix(0L)
  let mut gi : Value = Fix(1L)
  while !num_eq(gi, a) {
    i = one_plus(i)
    gi = num_mod(num_mul(gi, g), n)
  }
  i
}

///|
/// Pollard rho for dlog computation (Brents variant of collision detection)
/// g is generator of prime order p mod n
fn dlog_rho(a : Value, g : Value, p : Value, n : Value) -> Value raise {
  if numth__eqi(a, 1) {
    Fix(0L)
  } else if num_eq(g, a) {
    Fix(1L)
  } else if zerop(num_mod(num_sub(a, num_mul(g, g)), n)) {
    Fix(2L)
  } else if numth__eqi(num_mod(num_mul(a, g), n), 1) {
    one_minus(p)
  } else if num_lt(p, Fix(512L)) {
    dlog_naive(a, g, n)
  } else if num_lt(p, Fix(65536L)) {
    dlog_baby_giant(a, g, p, n)
  } else {
    // b = g^y * a^z, bb = g^yy * a^zz
    let mut b : Value = Fix(1L)
    let mut y : Value = Fix(0L)
    let mut z : Value = Fix(0L)
    let mut bb : Value = Fix(1L)
    let mut yy : Value = Fix(0L)
    let mut zz : Value = Fix(0L)
    while true {
      // rho
      let mut i = 0
      let mut j = 1
      while true {
        let (b1, y1, z1) = dlog_f(b, y, z, a, g, p, n)
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
      let dy = num_mod(num_sub(y, yy), p)
      let dz = num_mod(num_sub(zz, z), p) // g^dy = a^dz = g^(x*dz)
      if numth__eqi(num_gcd(dz, p), 1) {
        return zn_quo(dy, dz, p) // x = dy/dz mod p (since g is generator of order p)
      }
      y = Fix(0L)
      z = Fix(0L)
      b = Fix(1L)
      yy = one_plus(mt_random(one_minus(p)))
      zz = one_plus(mt_random(one_minus(p)))
      bb = num_mod(num_mul(power_mod(g, yy, n), power_mod(a, zz, n)), n)
    }
    Nil
  }
}

///|
/// iteration for Pollard rho:  b = g^y * a^z in each step
fn dlog_f(
  b : Value,
  y : Value,
  z : Value,
  a : Value,
  g : Value,
  ord : Value,
  n : Value,
) -> (Value, Value, Value) raise {
  let m = num_mod(b, Fix(3L))
  if numth__eqi(m, 0) {
    (num_mod(num_mul(b, b), n), num_mod(ash(y, 1), ord), num_mod(ash(z, 1), ord))
  } else if numth__eqi(m, 1) {
    // avoid stationary case b=1 => b*b=1
    (num_mod(num_mul(a, b), n), y, num_mod(num_add(z, Fix(1L)), ord))
  } else {
    (num_mod(num_mul(g, b), n), num_mod(num_add(y, Fix(1L)), ord), z)
  }
}

// characteristic factors:

///|
fn d_zn_characteristic_factors(m : Value) -> Value raise {
  if !(integerp(m) && num_gt(m, Fix(1L))) {
    // according to Shanks no result for m = 1
    numth__err(
      "`zn_characteristic_factors': Argument must be an integer greater than 1.",
      [],
    )
    |> ignore
  }
  cons(numth__mlist(), zn_characteristic_factors(m))
}

///|
fn d_zn_carmichael_lambda(m : Value) -> Value raise {
  if integerp(m) && num_gt(m, Fix(0L)) {
    if numth__eqi(m, 1) {
      Fix(1L)
    } else {
      zn_characteristic_factors(m, lambda_only=t)
    }
  } else {
    numth__err(
      "`zn_carmichael_lambda': Argument must be a positive integer.",
      [],
    )
  }
}

///|
/// D. Shanks - Solved and unsolved problems in number theory, 2. ed
/// definition 29 and 30 (p. 92 - 94)
///
/// (zn-characteristic-factors 104) --> (2 2 12)
/// => Z104* is isomorphic to M2 x M2 x M12
///    the direct product of modulo multiplication groups of order 2 resp. 12
fn zn_characteristic_factors(m : Value, lambda_only? : Value = Nil) -> Value raise {
  numth__nofaclim(fn() {
    let pe_list = get_factor_list(m) // def. 29 part A
    let shanks_phi = sort_list(
      // part D
      numth__apply_nconc(mapcar(pe => zn_shanks_phi_step_bc(pe), pe_list)),
      (a, b) => zn_pe_gt(a, b).truthy(),
    )
    // def. 30 :
    let mut todo = shanks_phi
    let mut fs : Value = Nil
    while todo is Cons(_) {
      let mut p : Value = Fix(0L)
      let mut f : Value = Fix(1L)
      let mut left : Value = Nil
      for qd in todo.iter() {
        let q = car(qd)
        let d = cadr(qd)
        if num_eq(q, p) {
          left = cons(qd, left)
        } else {
          p = q
          f = num_mul(f, expt(q, d))
        }
      }
      if lambda_only.truthy() {
        return f
      }
      fs = cons(f, fs)
      todo = nreverse(left)
    }
    fs
  })
}

///|
/// definition 29 parts B,C (p. 92)
fn zn_shanks_phi_step_bc(pe : Value) -> Value raise {
  let p = car(pe)
  let e = cadr(pe)
  let mut qd : Value = Nil
  if numth__eqi(p, 2) {
    qd = list1(
      if num_gt(e, Fix(1L)) {
        list2(Fix(2L), Fix(1L))
      } else {
        list2(Fix(1L), Fix(1L))
      },
    )
    if num_gt(e, Fix(2L)) {
      qd = nconc(qd, list1(list2(Fix(2L), num_sub(e, Fix(2L)))))
    }
  } else {
    qd = numth__nofaclim(fn() { get_factor_list(one_minus(p)) })
    if num_gt(e, Fix(1L)) {
      qd = nconc(qd, list1(list2(p, one_minus(e))))
    }
  }
  qd
}

///|
fn zn_pe_gt(a : Value, b : Value) -> Value raise {
  if num_gt(car(a), car(b)) {
    t
  } else if num_lt(car(a), car(b)) {
    Nil
  } else {
    lbool(num_gt(cadr(a), cadr(b)))
  }
}

// factor generators:

///|
fn d_zn_factor_generators(m : Value) -> Value raise {
  if !(integerp(m) && num_gt(m, Fix(1L))) {
    numth__err(
      "`zn_factor_generators': Argument must be an integer greater or equal 2.",
      [],
    )
    |> ignore
  }
  cons(numth__mlist(), zn_factor_generators(m))
}

///|
/// D. Shanks - Solved and unsolved problems in number theory, 2. ed
/// Theorem 44, page 94
///
/// zn_factor_generators(104);                     --> [79,27,89]
/// zn_characteristic_factors(104);                --> [2,2,12]
/// map(lambda([g], zn_h_order(g,104)), [79,27,89]); --> [2,2,12]
///
/// Every element in Z104* can be expressed as
///   79^i * 27^j * 89^k (mod m) where 0 <= i,j < 2 and 0 <= k < 12
///
/// The proof of theorem 44 contains the construction of the factor
/// generators.
fn zn_factor_generators(m : Value) -> Value raise {
  numth__nofaclim(fn() {
    let mut fs = numth__sort_car(get_factor_list(m))
    let mut pe = car(fs)
    let mut p = car(pe)
    let mut e = cadr(pe)
    let mut a = expt(p, e)
    let mut phi : Value = Nil
    let mut fs_phi : Value = Nil
    let mut gs : Value = Nil
    let mut ords : Value = Nil
    let mut fs_ords : Value = Nil
    // lemma 1, page 98 :
    // (Z/mZ)* is cyclic when m =
    if numth__eqi(m, 2) {
      // 2
      return list1(Fix(1L))
    }
    if num_lt(m, Fix(8L)) || // 3,4,5,6,7
      (num_gt(p, Fix(2L)) && cdr(fs) is Nil) || // p^k, p#2
      (numth__eqi(p, 2) && numth__eqi(e, 1) && cddr(fs) is Nil) {
      // 2*p^k, p#2
      phi = totient_by_fs_n(fs)
      fs_phi = numth__sort_num(mapcar(x => car(x), get_factor_list(phi)))
      let ga = zn_primroot(m, phi, fs_phi)
      return list1(ga)
    }
    fs = cdr(fs)
    if numth__eqi(p, 2) {
      if !(numth__eqi(e, 1) && cdr(fs).truthy()) {
        // phi(2*m) = phi(m) if m#1 is odd
        gs = cons(one_minus(a), gs) // a = 2^e
      }
      if num_gt(e, Fix(1L)) {
        ords = list1(Fix(2L))
        fs_ords = list1(list1(list2(Fix(2L), Fix(1L))))
      }
      if num_gt(e, Fix(2L)) {
        gs = cons(Fix(3L), gs)
        ords = cons(expt(Fix(2L), num_sub(e, Fix(2L))), ords)
        fs_ords = cons(list1(list2(Fix(2L), num_sub(e, Fix(2L)))), fs_ords)
      }
    } else {
      // lemma 2, page 100 :
      phi = num_mul(one_minus(p), expt(p, one_minus(e)))
      fs_phi = numth__sort_car(get_factor_list(one_minus(p)))
      if num_gt(e, Fix(1L)) {
        fs_phi = nconc(fs_phi, list1(list2(p, one_minus(e))))
      }
      let ga = zn_primroot(a, phi, mapcar(x => car(x), fs_phi)) // factors only
      gs = list1(ga)
      ords = list1(phi)
      fs_ords = list1(fs_phi)
    }
    while fs is Cons(_) {
      pe = car(fs)
      fs = cdr(fs)
      p = car(pe)
      e = cadr(pe)
      phi = num_mul(one_minus(p), expt(p, one_minus(e)))
      fs_phi = numth__sort_car(get_factor_list(one_minus(p)))
      if num_gt(e, Fix(1L)) {
        fs_phi = nconc(fs_phi, list1(list2(p, one_minus(e))))
      }
      let b = expt(p, e)
      let gb = zn_primroot(b, phi, mapcar(x => car(x), fs_phi))
      let c = num_mod(num_mul(inv_mod(b, a), num_sub(Fix(1L), gb)), a) // CRT: h = gb mod b
      let h = num_add(num_mul(b, c), gb) // CRT: h =  1 mod a
      let ia = inv_mod(a, b)
      let a0 = a
      gs = mapcar(
        g => num_add(num_mul(a0, num_mod(num_mul(ia, num_sub(Fix(1L), g)), b)), g),
        gs,
      )
      gs = cons(h, gs)
      ords = cons(phi, ords)
      fs_ords = cons(fs_phi, fs_ords)
      a = num_mul(a, b)
    }
    // lemma 3, page 101 :
    let pegs_c = Collector::new()
    let mut rg = gs
    let mut ro = ords
    let mut rf = fs_ords
    while rg is Cons(_) && ro is Cons(_) && rf is Cons(_) {
      let g = car(rg)
      let ord = car(ro)
      let f = car(rf)
      pegs_c.add(
        mapcar(
          pe => append(
            pe,
            list1(power_mod(g, numth__trunc(ord, expt(car(pe), cadr(pe))), m)),
          ),
          f,
        ),
      )
      rg = cdr(rg)
      ro = cdr(ro)
      rf = cdr(rf)
    }
    let pegs = sort_list(append_n(list_to_array(pegs_c.result())), (a, b) => zn_pe_gt(
        a, b,
      ).truthy())
    let mut todo = pegs
    let mut fgs : Value = Nil
    while todo is Cons(_) {
      let mut q : Value = Fix(0L)
      let mut fg : Value = Fix(1L)
      let mut left : Value = Nil
      for peg in todo.iter() {
        let p = car(peg)
        let g = caddr(peg)
        if num_eq(p, q) {
          left = cons(peg, left)
        } else {
          q = p
          fg = num_mod(num_mul(fg, g), m)
        }
      }
      fgs = cons(fg, fgs)
      todo = nreverse(left)
    }
    fgs
  })
}

// r-th roots --------------------------------------------------------------- ;;

///|
/// If the residue class a is an r-th power modulo n and contained in a
/// multiplication subgroup of (Z/nZ), return all r-th roots from this
/// subgroup and false otherwise.
fn d_zn_nth_root(a : Value, r : Value, n : Value, fs_n? : Value = Nil) -> Value raise {
  let mut fs_n = fs_n
  if !(integerp(a) && integerp(r) && integerp(n)) {
    numth__err("`zn_nth_root' needs three integer arguments. Found ~m, ~m, ~m.", [
      a, r, n,
    ])
    |> ignore
  }
  if !(num_gt(r, Fix(0L)) && num_gt(n, Fix(0L))) {
    numth__err(
      "`zn_nth_root': Second and third arg must be pos integers. Found ~m, ~m.",
      [r, n],
    )
    |> ignore
  }
  if fs_n.truthy() {
    if d_listp(fs_n).truthy() && d_listp(cadr(fs_n)).truthy() {
      fs_n = mapcar(x => cdr(x), cdr(fs_n)) // Lispify fs-n
    } else {
      numth__err(
        "`zn_nth_root': The opt fourth arg must be of the form [[p1, e1], ..., [pk, ek]].",
        [],
      )
      |> ignore
    }
  }
  let rts = zn_nrt(a, r, n, fs_n~)
  if rts.truthy() {
    cons(numth__mlist(), rts)
  } else {
    Nil
  }
}

///|
fn zn_nrt(a : Value, r : Value, n : Value, fs_n? : Value = Nil) -> Value raise {
  let mut a = a
  let mut fs_n = fs_n
  if !fs_n.truthy() {
    fs_n = numth__nofaclim(fn() { get_factor_list(n) })
  }
  a = num_mod(a, n)
  if every(x => onep(x).truthy(), mapcar(x => second(x), fs_n)) {
    // RSA-like case (n is squarefree)
    if numth__eqi(a, 0) {
      return list1(Fix(0L)) // n = 1: exit here
    }
  } else if !numth__eqi(num_gcd(a, n), 1) {
    // Handle residue classes not coprime to n (n is not squarefree):
    // Use Theorems 49 and 50 from
    //   Shanks - Solved and Unsolved Problems in Number Theory
    let g = num_gcd(a, n)
    let n_g = numth__trunc(n, g)
    if !numth__eqi(num_gcd(g, n_g), 1) {
      // a is not contained in any mult. subgroup (Th. 50):
      return Nil //   exit here
    }
    if numth__eqi(a, 0) {
      return list1(Fix(0L))
    }
    // g = gcd(a,n). Now assume gcd(g,n/g) = 1.
    // There are totient(n/g) multiples of g, i*g, with gcd(i,n/g) = 1,
    //   which form a modulo multiplication subgroup of (Z/nZ),
    //   isomorphic to (Z/mZ)*, where m = n/g.
    // a is one of these multiples of g.
    // Find the r-th roots of a resp. mod(a,m) in (Z/mZ)* and then
    //   by using CRT all corresponding r-th roots of a in (Z/nZ).
    a = num_mod(a, n_g)
    let rts = zn_nrt(a, r, n_g)
    let c = inv_mod(g, n_g) // CRT-coeff
    // isomorphic mapping (Th. 49):
    //   (use CRT with x = 0 mod g and x = rt mod n/g)
    let res = mapcar(rt => num_mul(g, num_mod(num_mul(c, rt), n_g)), rts)
    return numth__sort_num(res)
  }
  // for every prime power factor of n
  //   reduce a and r if possible and call zq-nrt:
  let mut qs : Value = Nil
  let mut rts : Value = Nil
  let mut rt : Value = Nil
  for pe in fs_n.iter() {
    let p = car(pe)
    let q = expt(car(pe), cadr(pe))
    let aq = num_mod(a, q)
    let ord = num_mul(one_minus(p), numth__trunc(q, p))
    let mut ro : Value = Nil
    if num_gt(r, ord) {
      ro = num_mod(r, ord)
      if numth__eqi(ro, 0) {
        ro = ord
      }
    } else {
      ro = r
    }
    if numth__eqi(aq, 0) {
      if num_eq(p, q) || numth__eqi(ro, 1) {
        rt = list1(Fix(0L))
      } else {
        return Nil
      }
    } else if numth__eqi(ro, 1) {
      rt = list1(aq)
    } else {
      rt = zq_nrt(aq, ro, p, q)
      if rt is Nil {
        return Nil
      }
    }
    qs = cons(q, qs)
    rts = cons(rt, rts)
  }
  // CRT in case n splits into more than one factor:
  let res = if length(fs_n) == 1 {
    rt // n is a prime power
  } else {
    qs = nreverse(qs)
    let rems = zn_distrib_lists(nreverse(rts))
    let qs0 = qs
    mapcar(rs => car(solve_congruences(rs, qs0)), rems)
  }
  numth__sort_num(res)
}

///|
/// return all possible combinations containing one entry per list:
/// (zn-distrib-lists '((1 2 3) (4) (5 6)))
/// --> ((1 4 5) (1 4 6) (2 4 5) (2 4 6) (3 4 5) (3 4 6))
fn zn_distrib_lists(ll : Value) -> Value raise {
  let mut res = car(ll)
  for l in cdr(ll).iter() {
    let mut tmp : Value = Nil
    for r in res.iter() {
      for n in l.iter() {
        let e = if listp(r) { copy_list(r) } else { list1(r) }
        tmp = cons(nconc(e, list1(n)), tmp)
      }
    }
    res = nreverse(tmp)
  }
  res
}

///|
/// handle composite r (which are not coprime to totient(q)):
///   e.g. r=x*x*y*z, then a^(1/r) = (((a^(1/x))^(1/x))^(1/y))^(1/z)
fn zq_nrt(a : Value, r : Value, p : Value, q : Value) -> Value raise {
  // prime power q = p^e
  // assume a < q, r <= q
  let mut rts : Value = Nil
  if numth__eqi(r, 1) || primep(r).truthy() {
    rts = zq_amm(a, r, p, q)
  } else if numth__eqi(num_gcd(r, one_minus(p)), 1) &&
    (num_eq(p, q) || numth__eqi(num_gcd(r, p), 1)) {
    // r is coprime to totient(q):
    let ord = num_mul(one_minus(p), numth__trunc(q, p))
    rts = list1(power_mod(a, inv_mod(r, ord), q)) //   unique solution
  } else {
    rts = numth__nofaclim(fn() {
      let mut rs = get_factor_list(r)
      rs = numth__sort_car(rs)
      rs = numth__apply_nconc(
        mapcar(pe => numth__make_list(cadr(pe), car(pe)), rs),
      )
      let mut rts = zq_amm(a, car(rs), p, q)
      for r in cdr(rs).iter() {
        rts = numth__apply_nconc(mapcar(a => zq_amm(a, r, p, q), rts))
      }
      rts
    })
  }
  if numth__eqi(p, 2) && num_gt(q, Fix(2L)) && evenp(r) {
    // this case needs a postprocess (see below)
    nconc(mapcar(rt => num_sub(q, rt), rts), rts) // add negative solutions
  } else {
    rts
  }
}

///|
/// Computing r-th roots modulo a prime power p^n, where r is a prime
///
///   inspired by
///     Bach,Shallit - Algorithmic Number Theory, Theorem 7.3.2
///   and
///     Shanks - Solved and Unsolved Problems in Number Theory, Th. 46,
///     Lemma 1 to Th. 44
///
///   The algorithm AMM (Adleman, Manders, Miller) is essentially based on
///   properties of cyclic groups and with the exception of q = 2^n, n > 2
///   it can be applied to any multiplicative group (Z/qZ)* where q = p^n.
///
///   Doing so, the order q-1 of Fq* in Th. 7.3.2 has to be replaced by the
///   group order totient(q) of (Z/qZ)*.
///
///   But how to include q = 8,16,32,... ?
///   r > 2: r is prime. There exists a unique solution for all a in (Z/qZ)*.
///   r = 2 (the square root case):
///   - (Z/qZ)* has k = 2 characteristic factors [2,q/4] with [-1,3] as
///       possible factor generators (see Shanks, Lemma 1 to Th. 44).
///       I.e. 3 is of order q/4 and 3^2 = 9 of order q/8.
///   - (Z/qZ)* has totient/2^k = q/8 quadratic residues with 2^k = 4 roots
///       each (see Shanks, Th. 46).
///   - It follows that the subgroup <3> generated by 3 contains all
///       quadratic residues of (Z/qZ)* (which must be all the powers of 9
///       located in <3>).
///   - We apply the algorithm AMM for cyclic groups to <3> and compute two
///       square roots x,y.
///   - The numbers -x and -y, obviously roots as well, both lie in (-1)*<3>
///       and therefore they differ from x,y and complete the set of 4 roots.
fn zq_amm(a : Value, r : Value, p : Value, q : Value) -> Value raise {
  // r,p prime, q = p^n
  // assume a < q, r <= q
  if numth__eqi(r, 1) {
    return list1(a)
  }
  if numth__eqi(q, 2) {
    return if numth__eqi(a, 1) { list1(Fix(1L)) } else { Nil }
  }
  if numth__eqi(q, 4) {
    return if numth__eqi(a, 1) || (numth__eqi(a, 3) && oddp(r)) {
      list1(a)
    } else {
      Nil
    }
  }
  let mut ord = num_mul(one_minus(p), numth__trunc(q, p)) // group order: totient(q)
  let mut rt : Value = Nil
  if numth__eqi(r, 2) {
    if numth__eqi(p, 2) {
      if !numth__eqi(num_mod(a, Fix(8L)), 1) {
        return Nil // a must be a power of 9
      }
    } else if !numth__eqi(d_jacobi(num_mod(a, p), p), 1) {
      return Nil
    } else if numth__eqi(num_mod(ord, Fix(4L)), 2) {
      rt = power_mod(a, ash(num_add(ord, Fix(2L)), -2), q)
      return list2(rt, num_sub(q, rt))
    } else if num_eq(p, q) && numth__eqi(num_mod(p, Fix(8L)), 5) {
      let x = ash(a, 1)
      let y = power_mod(x, ash(num_sub(p, Fix(5L)), -3), p)
      let i = num_mod(num_mul(x, num_mul(y, y)), p)
      let rt = num_mod(num_mul(a, num_mul(y, one_minus(i))), p)
      return list2(rt, num_sub(p, rt))
    }
  }
  if numth__eqi(p, 2) {
    // q = 8,16,32,..
    ord = ash(ord, -1) // factor generator 3 is of order ord/2
  }
  let (s, m0) = num_truncate(ord, b=r)
  let mut m = m0
  if numth__eqi(m, 0) && !numth__eqi(power_mod(a, s, q), 1) {
    return Nil
  }
  // r = 3, first 2 cases:
  if numth__eqi(r, 3) {
    m = num_mod(ord, Fix(3L))
    if numth__eqi(m, 1) {
      // unique solution
      return list1(
        power_mod(a, numth__trunc(one_plus(ash(ord, 1)), Fix(3L)), q),
      )
    } else if numth__eqi(m, 2) {
      // unique solution
      return list1(power_mod(a, numth__trunc(one_plus(ord), Fix(3L)), q))
    }
  }
  // compute u,e with ord = u*r^e and r,u coprime:
  let mut u = ord
  let mut e : Value = Fix(0L)
  let mut u1 = u
  while true {
    let (q1, m1) = num_truncate(u1, b=r)
    u1 = q1
    m = m1
    if !numth__eqi(m, 0) {
      break
    }
    u = u1
    e = one_plus(e)
  }
  if numth__eqi(e, 0) {
    rt = power_mod(a, inv_mod(r, u), q) // unique solution, see Bach,Shallit 7.3.1
    list1(rt)
  } else {
    // a is an r-th power
    let mut g : Value = Nil
    // find generator of order r^e:
    if numth__eqi(p, 2) {
      // p = 2: then r = 2 (other r: e = 0)
      g = Fix(3L)
    } else {
      let mut n : Value = Fix(2L)
      while true {
        if numth__eqi(num_gcd(n, q), 1) &&
          !numth__eqi(power_mod(n, s, q), 1) {
          // n is no r-th power
          g = power_mod(n, u, q)
          break
        }
        n = d_next_prime(n)
      }
    }
    let re = expt(r, e)
    let om = power_mod(g, numth__trunc(re, r), q) // r-th root of unity
    if !numth__eqi(r, 3) ||
      {
        m = num_mod(ord, Fix(9L))
        numth__eqi(m, 0)
      } {
      // map a from Zq* to C_{r^e} x C_u:
      let ar = power_mod(a, u, q) // in C_{r^e}
      let au = power_mod(a, re, q) // in C_u
      // compute direct factors of rt:
      //  (the loop in algorithm AMM is effectively a Pohlig-Hellman-reduction,
      //   equivalent to zn-dlog)
      let k = zn_dlog(ar, g, q, re, list1(list2(r, e))) // g^k = ar, where r|k
      let br = power_mod(g, numth__trunc(k, r), q) // br^r = g^k (factor of rt in C_{r^e})
      let bu = power_mod(au, inv_mod(r, u), q) // bu^r = au  (factor of rt in C_u)
      // mapping from C_{r^e} x C_u back to Zq*:
      let ab = cdr(zn_gcdex1(u, re))
      let mut alpha = car(ab)
      let mut beta = cadr(ab)
      if minusp(alpha) {
        alpha = num_add(alpha, ord)
      } else {
        beta = num_add(beta, ord)
      }
      rt = num_mod(num_mul(power_mod(br, alpha, q), power_mod(bu, beta, q)), q)
    } else if numth__eqi(m, 3) {
      // r = 3, remaining cases:
      rt = power_mod(a, numth__trunc(num_add(ash(ord, 1), Fix(3L)), Fix(9L)), q)
    } else if numth__eqi(m, 6) {
      rt = power_mod(a, numth__trunc(num_add(ord, Fix(3L)), Fix(9L)), q)
    }
    // mult with r-th roots of unity:
    let mut i : Value = Fix(1L)
    let mut j : Value = Fix(1L)
    let mut res = list1(rt)
    while !num_eq(i, r) {
      j = num_mod(num_mul(j, om), q)
      res = cons(num_mod(num_mul(rt, j), q), res)
      i = one_plus(i)
    }
    res
  }
}

// Two variants of gcdex:

///|
/// returns gcd as first entry:
/// (zn-gcdex1 12 45) --> (3 4 -1), so 4*12 + -1*45 = 3
fn zn_gcdex1(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  let mut x1 : Value = Fix(1L)
  let mut x2 : Value = Fix(0L)
  let mut y1 : Value = Fix(0L)
  let mut y2 : Value = Fix(1L)
  while !numth__eqi(y, 0) {
    let (q, r) = num_truncate(x, b=y)
    x = y
    y = r
    let ox1 = x1
    x1 = y1
    y1 = num_sub(ox1, num_mul(q, y1))
    let ox2 = x2
    x2 = y2
    y2 = num_sub(ox2, num_mul(q, y2))
  }
  list3(x, x1, x2)
}

///|
/// returns gcd as last entry:
/// (zn-gcdex 12 45 21) --> (4 -1 0 3), so 4*12 + -1*45 + 0*21 = 3
fn zn_gcdex(args : Value) -> Value raise {
  let mut ex = zn_gcdex1(car(args), cadr(args))
  let mut g = car(ex)
  let mut cs = cdr(ex)
  for a in cddr(args).iter() {
    ex = zn_gcdex1(g, a)
    g = car(ex)
    ex = cdr(ex)
    let c1 = car(ex)
    cs = nconc(mapcar(c => num_mul(c, c1), cs), cdr(ex))
  }
  nconc(cs, list1(g))
}

// for educational purposes: tables of small residue class rings

///|
fn zn_table_errchk(n : Value, fun : Value) -> Value raise {
  if !(fixnump(n) && num_lt(Fix(1L), n)) {
    numth__err("Argument to `~m' must be a small fixnum greater than 1.", [fun])
  } else {
    Nil
  }
}

///|
fn d_zn_add_table(n : Value) -> Value raise {
  zn_table_errchk(n, Str("zn_add_table")) |> ignore
  let mut res : Value = Nil
  let mut i : Value = Fix(0L)
  while !num_eq(i, n) {
    // `((mod) (+ ,i $j) ,n)`: the Lisp `+` form is evaluated by MEVAL as
    // a function call; MPLUS gives the same value.
    res = cons(
      mfuncall(
        q_d_makelist,
        list([
          list3(list1(q_mod), list3(list1(q_mplus), i, q_d_j), n),
          q_d_j,
          Fix(0L),
          one_minus(n),
        ]),
      ),
      res,
    )
    i = one_plus(i)
  }
  cons(numth__matrix(), nreverse(res))
}

///|
/// multiplication table modulo n
///
///  The optional g allows to choose subsets of (Z/nZ). Show i with
///  gcd(i,n) = g resp. all i#0.
///  If n # 1 add row and column headings for better readability.
fn d_zn_mult_table(n : Value, g? : Value = Nil) -> Value raise {
  zn_table_errchk(n, Str("zn_mult_table")) |> ignore
  let mut g = g
  let mut i0 : Value = Fix(1L)
  let mut all = false
  let mut header = false
  let mut choice : Value = Nil
  let mut res : Value = Nil
  if g is Nil {
    g = Fix(1L)
  } else if equal(g, q_d_all) {
    all = true
  } else if !fixnump(g) {
    numth__err(
      "`zn_mult_table': The opt second arg must be `all' or a small fixnum.",
      [],
    )
    |> ignore
  } else {
    if num_eq(n, g) {
      i0 = Fix(0L)
    }
    choice = cons(Fix(1L), choice) // creates the headers
    header = true
  }
  let mut i = i0
  while !num_eq(i, n) {
    if all || num_eq(g, num_gcd(i, n)) {
      choice = cons(i, choice)
    }
    i = one_plus(i)
  }
  choice = cons(numth__mlist(), nreverse(choice))
  if header && length(choice) == 2 {
    return Nil
  }
  for i in cdr(choice).iter() {
    // `((mod) (* ,i $j) ,n)`, see $zn_add_table
    res = cons(
      mfuncall(
        q_d_makelist,
        list([
          list3(list1(q_mod), list3(list1(q_mtimes), i, q_d_j), n),
          q_d_j,
          choice,
        ]),
      ),
      res,
    )
  }
  res = nreverse(res)
  if header {
    rplaca(cdar(res), Str("*")) |> ignore
  }
  cons(numth__matrix(), res)
}

///|
/// power table modulo n
///
///  The optional g allows to choose subsets of (Z/nZ). Show i with
///  gcd(i,n) = g resp. all i.
fn d_zn_power_table(n : Value, g? : Value = Nil, e? : Value = Nil) -> Value raise {
  zn_table_errchk(n, Str("zn_power_table")) |> ignore
  let mut g = g
  let mut e = e
  let mut all = false
  if g is Nil {
    g = Fix(1L)
  } else if equal(g, q_d_all) {
    all = true
  } else if !fixnump(g) {
    numth__err(
      "`zn_power_table': The opt second arg must be `all' or a small fixnum.",
      [],
    )
    |> ignore
  }
  if e is Nil {
    e = zn_characteristic_factors(n, lambda_only=t)
  } else if !fixnump(e) {
    numth__err(
      "`zn_power_table': The opt third arg must be a small fixnum.",
      [],
    )
    |> ignore
  }
  let mut res : Value = Nil
  let mut i : Value = Fix(0L)
  while !num_eq(i, n) {
    if all || num_eq(g, num_gcd(i, n)) {
      res = cons(
        mfuncall(
          q_d_makelist,
          list([
            list([list1(q_power_mod), i, q_d_j, n]),
            q_d_j,
            Fix(1L),
            e,
          ]),
        ),
        res,
      )
    }
    i = one_plus(i)
  }
  if res.truthy() {
    cons(numth__matrix(), nreverse(res))
  } else {
    Nil
  }
}

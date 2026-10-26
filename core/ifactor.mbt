// Port of src/ifactor.lisp: Maxima integer factorization package.
//
//   - ifactors     : factorization of integers
//   - primep       : probabilistic primality test
//   - next_prime   : smallest prime > n
//   - prev_prime   : greatest prime < n
//   - primes       : list of primes
//   - power_mod    : fast modular powers
//   - inv_mod      : modular inverse
//
// Random numbers come from the port of Maxima's MT19937 `random`.

///|
fn number_of_digits(n : Value) -> Value raise {
  int(format_to_string("~d", [n]).length())
}

///|
fn ifactor__verbose() -> Bool {
  symval(q_d_ifactor_verbose).truthy()
}

///|
fn ifactor__say(ctl : String, args : Array[Value]) -> Unit raise {
  format(t, ctl, args) |> ignore
}

///|
fn ifactor__diff(i : Int) -> Value raise {
  aref1(symval(q_ear_prime_diffs), i)
}

///|
fn get_factor_list(n : Value) -> Value raise {
  if ifactor__verbose() {
    ifactor__say("~%Starting factorization of n = ~d~%", [n])
  }
  init_prime_diffs(Fix(640000L)) |> ignore
  let (large_part, factor_list) = get_small_factors(n)
  if num_gt(large_part, Fix(1L)) {
    append(convert_list(get_large_factors(large_part)), factor_list)
  } else {
    factor_list
  }
}

///|
fn d_ifactors(n : Value) -> Value raise {
  let mut n = n
  let mut ok = integerp(n)
  if !ok && d_integerp(n).truthy() {
    n = d_fix(n)
    ok = n.truthy()
  }
  ok = ok && plusp(n)
  if !ok {
    merr("ifactors: argument must be a positive integer; found: ~M", [n]) |> ignore
  }
  let b = bind(q_d_intfaclim, Nil)
  defer unbind(b)
  let factor_list = get_factor_list(n)
  let factor_list = if symval(q_d_factors_only).truthy() {
    mapcar(u => car(u), factor_list)
  } else {
    mapcar(u => mk_simp(q_mlist, [car(u), cadr(u)]), factor_list)
  }
  d_sort(cons(list2(q_mlist, q_simp), factor_list))
}

///|
/// CFACTOR is the function used by maxima to factor integers.
fn cfactor(x : Value) -> Value raise {
  if !symval(q_d_factorflag).truthy() {
    list2(x, Fix(1L))
  } else if floatp(x) {
    rat_error(list1(Str("`factor' given floating arg")))
  } else if pzerop(x).truthy() {
    list2(pzero(), Fix(1L))
  } else if equal(x, Fix(-1L)) {
    list2(Fix(-1L), Fix(1L))
  } else if minusp(x) {
    cons(Fix(-1L), cons(Fix(1L), cfactor(num_neg(x))))
  } else if num_lt(x, Fix(2L)) {
    list2(x, Fix(1L))
  } else {
    let factor_list = get_factor_list(x)
    let factor_list = sort_list(factor_list, (a, b) => num_lt(car(a), car(b)))
    let mut ans : Value = Nil
    for fac in factor_list.iter() {
      ans = cons(car(fac), cons(cadr(fac), ans))
    }
    ans
  }
}

///|
/// Factor out primes < *prime-diffs-limit* by trial division.
fn get_small_factors(n : Value) -> (Value, Value) raise {
  let mut n = n
  if num_eq(n, Fix(1L)) {
    return (Fix(1L), Nil)
  }
  if num_lt(n, Fix(4L)) {
    return (Fix(1L), list1(list2(n, Fix(1L))))
  }
  let mut factors : Value = Nil
  // first divide off the even part
  let mut deg = 0
  while num_gt(n, Fix(1L)) && evenp(n) {
    n = ash(n, -1)
    deg += 1
  }
  if deg > 0 {
    factors = cons(list2(Fix(2L), int(deg)), factors)
    if ifactor__verbose() {
      ifactor__say("Factoring out 2: 2 (degree:~A)~%", [int(deg)])
    }
  }
  if num_eq(n, Fix(1L)) {
    return (Fix(1L), factors)
  }
  // now use the *prime-diffs* array for trial-factoring
  let maxindex = to_int(symval(q_ear_prime_diffs_maxindex))
  let mut d : Value = Fix(3L)
  for i = 0; i <= maxindex; i = i + 1 {
    if i > 0 {
      d = num_add(d, ifactor__diff(i - 1))
    }
    if num_gt(num_mul(d, d), n) {
      factors = cons(list2(n, Fix(1L)), factors)
      if ifactor__verbose() {
        ifactor__say("small prime cofactor: ~A~%", [n])
      }
      return (Fix(1L), factors)
    }
    let mut deg = 0
    while num_gt(n, Fix(1L)) && zerop(num_mod(n, d)) {
      n = num_truncate(n, b=d).0
      deg += 1
    }
    if deg > 0 {
      factors = cons(list2(d, int(deg)), factors)
      if ifactor__verbose() {
        ifactor__say("Factoring out small prime: ~A (degree:~A)~%", [
          d,
          int(deg),
        ])
      }
    }
    if num_eq(n, Fix(1L)) {
      return (Fix(1L), factors)
    }
  }
  (n, factors)
}

///|
/// Returns the list of factors of integer n (n has no small factor at this
/// stage).
fn get_large_factors(n : Value) -> Value raise {
  if primep(n).truthy() {
    if ifactor__verbose() {
      ifactor__say("========> Prime factor: ~d~%~%", [n])
    }
    list1(n)
  } else {
    get_large_factors_1(n)
  }
}

///|
fn get_large_factors_1(n : Value) -> Value raise {
  let f = get_one_factor(n)
  if num_eq(f, n) {
    if ifactor__verbose() {
      ifactor__say("Warning: could not find factors of composite:~%~A~%", [n])
    }
    list1(n)
  } else {
    let a = get_large_factors(f)
    append(a, get_large_factors(num_div(n, f)))
  }
}

///|
fn get_one_factor(n : Value) -> Value raise {
  if ifactor__verbose() {
    ifactor__say("Factoring n = ~d~%", [n])
  }
  let mut lim_pollard = symval(q_d_pollard_rho_limit)
  let mut lim_p_1 = symval(q_d_pollard_pm1_limit)
  let b = bind(q_d_ecm_number_of_curves, symval(q_d_ecm_number_of_curves))
  defer unbind(b)
  // If $intfaclim is not false then we don't want to spend too much time
  // factoring integers so we return n and leave it unfactored.
  if symval(q_d_intfaclim).truthy() {
    return n
  }
  // first try known large primes
  for p in symval(q_ear_large_primes).iter() {
    if zerop(num_mod(n, p)) {
      return p
    }
  }
  // try factoring smaller factors with pollard-rho
  let rho_tests = to_int(symval(q_d_pollard_rho_tests))
  for i in 0..<rho_tests {
    if ifactor__verbose() {
      ifactor__say("Pollard rho: round #~d of ~d (lim=~d)~%", [
        int(i + 1),
        symval(q_d_pollard_rho_tests),
        lim_pollard,
      ])
    }
    let f = get_one_factor_pollard(n, lim_pollard)
    if num_lt(Fix(1L), f) && num_lt(f, n) {
      if ifactor__verbose() {
        ifactor__say("Pollard rho: found factor ~A (~d digits)~%", [
          f,
          number_of_digits(f),
        ])
      }
      return f
    }
    if num_gt(lim_pollard, Fix(0L)) {
      lim_pollard = num_add(lim_pollard, symval(q_d_pollard_rho_limit_step))
    }
  }
  // now try factoring with pollards p-1 method
  let pm1_tests = to_int(symval(q_d_pollard_pm1_tests))
  for i in 0..<pm1_tests {
    if ifactor__verbose() {
      ifactor__say("Pollard p-1: round #~d of ~d (lim=~d)~%", [
        int(i + 1),
        symval(q_d_pollard_pm1_tests),
        lim_p_1,
      ])
    }
    let f = get_one_factor_p_1(n, lim=lim_p_1)
    if num_lt(Fix(1L), f) && num_lt(f, n) {
      if ifactor__verbose() {
        ifactor__say("Pollard p-1: found factor ~A (~d digits)~%", [
          f,
          number_of_digits(f),
        ])
      }
      return f
    }
    if plusp(lim_pollard) {
      lim_p_1 = num_add(lim_p_1, symval(q_d_pollard_pm1_limit_step))
    }
  }
  // continue with ecm
  while true {
    let f = get_one_factor_ecm(n)
    if f.truthy() {
      return f
    }
    set(
      q_d_ecm_number_of_curves,
      num_add(symval(q_d_ecm_number_of_curves), Fix(50L)),
    )
    |> ignore
  }
  Nil
}

///|
/// Brent's variant of Pollard's rho method.
fn get_one_factor_pollard(n : Value, lim : Value) -> Value raise {
  let mut x = num_add(mt_random(num_sub(n, Fix(3L))), Fix(2L))
  let a = num_add(mt_random(num_sub(n, Fix(2L))), Fix(1L))
  let mut b = num_add(mt_random(num_sub(n, Fix(5L))), Fix(1L))
  let mut y = x
  let mut d : Value = Fix(1L)
  let mut r : Value = Fix(2L)
  let mut j : Value = Fix(1L)
  let terms = int(integer_length(n))
  b = num_div(b, num_gcd(a, b))
  while num_eq(d, Fix(1L)) {
    y = x
    j = num_add(j, r)
    let ri = to_int64(r)
    for _ in 0L..<ri {
      x = num_mod(num_add(num_mul(a, num_mod(num_mul(x, x), n)), b), n)
    }
    let mut k : Value = Fix(0L)
    while num_lt(k, r) && equal(d, Fix(1L)) {
      let cnt = to_int64(num_min(terms, num_sub(r, k)))
      for _ in 0L..<cnt {
        x = num_mod(num_add(num_mul(a, num_mod(num_mul(x, x), n)), b), n)
        d = num_mod(num_mul(d, num_sub(x, y)), n)
      }
      d = num_gcd(d, n)
      k = num_add(k, terms)
    }
    r = num_mul(Fix(2L), r)
    if num_lt(Fix(0L), lim) && num_lt(lim, j) {
      return d
    }
  }
  d
}

///|
/// Product of all primes low < p < high and all integers
/// isqrt(low) < n < isqrt(high).
fn ppexpo(low : Value, high : Value) -> Value raise {
  let mut low = low
  let mut x : Value = Fix(1L)
  let mut i = num_max(Fix(2L), one_plus(isqrt(low)))
  let ih = isqrt(high)
  while num_le(i, ih) {
    x = num_mul(i, x)
    i = one_plus(i)
  }
  if oddp(low) {
    low = one_plus(low)
  }
  let mut i = one_plus(low)
  while num_le(i, high) {
    if primep(i).truthy() {
      x = num_mul(i, x)
    }
    i = one_plus(i)
  }
  x
}

///|
fn big_prime_var(y : Value, n : Value, bound : Value) -> Value raise {
  let mut y = y
  let half = to_int(ash(symval(q_ear_prime_diffs_maxdiff), -1))
  let x : Array[Value] = Array::make(half + 1, Fix(1L))
  let y2 = num_mod(num_mul(y, y), n)
  let mut q : Value = Fix(3L)
  let mut count = 1
  let mut d : Value = Fix(0L)
  for i in 1..=half {
    x[i] = num_mod(num_mul(y2, x[i - 1]), n)
  }
  y = power_mod(y, q, n)
  let mut z = one_minus(y)
  let bound = num_min(bound, symval(q_ear_prime_diffs_limit))
  let mut i = 0
  while num_lt(q, bound) {
    let k = ifactor__diff(i)
    q = num_add(q, k)
    y = num_mod(num_mul(y, x[to_int(ash(k, -1))]), n)
    z = num_mod(num_mul(z, one_minus(y)), n)
    count += 1
    if count > 1000 {
      count = 0
      d = num_gcd(z, n)
      if num_gt(d, Fix(1L)) {
        return d
      }
    }
    i += 1
  }
  d
}

///|
/// Pollard's p-1 factoring algorithm: in general a prime factor p of x is
/// found, if p-1 is a product of prime powers q^k <= lim.
fn get_one_factor_p_1(n : Value, lim? : Value = Fix(16000L)) -> Value raise {
  let mut base = num_add(Fix(2L), mt_random(num_sub(n, Fix(2L))))
  let anz : Value = Fix(256L)
  let mut d = num_gcd(base, n)
  if num_lt(Fix(1L), d) && num_lt(d, n) {
    return d
  }
  let mut n0 : Value = Fix(0L)
  let top = one_minus(lim)
  while num_le(n0, top) {
    let ex = ppexpo(n0, num_min(lim, num_add(n0, anz)))
    base = power_mod(base, ex, n)
    if num_le(base, Fix(1L)) {
      return Fix(1L)
    }
    d = num_gcd(one_minus(base), n)
    if num_gt(d, Fix(1L)) {
      return d
    }
    n0 = num_add(n0, anz)
  }
  if num_eq(d, Fix(1L)) {
    return big_prime_var(base, n, symval(q_ear_prime_diffs_limit))
  }
  Fix(1L)
}

///|
/// Differences between consecutive primes, for trial division, stage 2 of
/// ecm and the big prime variation of Pollard p-1.
fn init_prime_diffs(n : Value) -> Value raise {
  if !num_gt(n, symval(q_ear_prime_diffs_limit)) {
    return Nil
  }
  let n = to_int(n) * 2
  if ifactor__verbose() {
    ifactor__say("Initializing prime diffs up to n=~d~%", [int(n)])
  }
  let sieve : FixedArray[Bool] = FixedArray::make(n + 1, true)
  let sq = to_int(isqrt(int(n)))
  let mut p = 3
  while p <= sq {
    let mut d = 2 * p
    while d <= n {
      sieve[d] = false
      d += p
    }
    p = to_int(d_next_prime(int(p)))
  }
  let mut q1 = 3
  let mut i = 0
  let mut q2 = 5
  while q2 <= n {
    if sieve[q2] {
      let arr = symval(q_ear_prime_diffs)
      if i >= length(arr) {
        let nl = 2 * length(arr)
        set(q_ear_prime_diffs, adjust_array(arr, [nl], initial=Fix(0L)))
        |> ignore
        if ifactor__verbose() {
          ifactor__say("init-prime-diffs: adjusting *prime-diffs* to size ~d~%", [
            int(2 * length(symval(q_ear_prime_diffs))),
          ])
        }
      }
      set(q_ear_prime_diffs_limit, int(q2)) |> ignore
      let diff = q2 - q1
      aset1(symval(q_ear_prime_diffs), i, int(diff)) |> ignore
      if diff > to_int(symval(q_ear_prime_diffs_maxdiff)) {
        set(q_ear_prime_diffs_maxdiff, int(diff)) |> ignore
      }
      q1 = q2
      i += 1
    }
    q2 += 2
  }
  set(q_ear_prime_diffs_maxindex, int(i - 1))
}

///|
/// Modular inverse of a (modulus m).  Returns a positive modulo or nil in
/// case of a zero divisor.
fn inv_mod(a : Value, m : Value) -> Value raise {
  let mut u1 : Value = Fix(0L)
  let mut u2 = m
  let mut v1 : Value = Fix(1L)
  let mut v2 = num_mod(a, m)
  while !zerop(v2) {
    let (q, r) = num_truncate(u2, b=v2)
    let nu1 = v1
    let nv1 = num_sub(u1, num_mul(q, v1))
    u1 = nu1
    v1 = nv1
    u2 = v2
    v2 = r
  }
  if num_eq(Fix(1L), u2) {
    num_mod(u1, m)
  } else {
    Nil
  }
}

///|
fn d_inv_mod(a : Value, m : Value) -> Value raise {
  if !(integerp(a) && integerp(m)) {
    merr("inv_mod: arguments must be integers; found: ~M, ~M", [a, m]) |> ignore
  }
  if num_eq(Fix(0L), a) {
    Nil
  } else {
    inv_mod(a, m)
  }
}

// Computations on the elliptic curve: we use the elliptic curve in
// projective coordinates (x,y,z), but only use x and z.

///|
fn ecm_product(q : Value, p1 : Value, p2 : Value, n : Value) -> Value raise {
  let x1 = car(p1)
  let x2 = car(p2)
  let z1 = cadr(p1)
  let z2 = cadr(p2)
  let pr1 = num_mod(num_mul(num_sub(x1, z1), num_add(x2, z2)), n)
  let pr2 = num_mod(num_mul(num_add(x1, z1), num_sub(x2, z2)), n)
  let sq1 = num_mod(expt(num_add(pr1, pr2), Fix(2L)), n)
  let sq2 = num_mod(expt(num_sub(pr1, pr2), Fix(2L)), n)
  let x3 = num_mod(num_mul(cadr(q), sq1), n)
  let z3 = num_mod(num_mul(car(q), sq2), n)
  list2(x3, z3)
}

///|
fn ecm_square(p : Value, n : Value, a : Value) -> Value raise {
  let x1 = car(p)
  let z1 = cadr(p)
  let sq1 = num_mod(num_mul(num_add(x1, z1), num_add(x1, z1)), n)
  let sq2 = num_mod(num_mul(num_sub(x1, z1), num_sub(x1, z1)), n)
  let f1 = num_sub(sq1, sq2)
  let f2 = num_mod(num_mul(a, f1), n)
  let x2 = num_mod(num_mul(sq1, sq2), n)
  let z2 = num_mod(num_mul(f1, num_add(sq2, f2)), n)
  list2(x2, z2)
}

///|
fn ecm_power(base : Value, e : Value, n : Value, a : Value) -> Value raise {
  let mut p = base
  let mut ptb = ecm_square(base, n, a)
  let l = integer_length(e)
  let mut i = l - 2
  while i >= 0 {
    if logbitp(i, e) {
      p = ecm_product(base, p, ptb, n)
      ptb = ecm_square(ptb, n, a)
    } else {
      ptb = ecm_product(base, p, ptb, n)
      p = ecm_square(p, n, a)
    }
    i -= 1
  }
  p
}

///|
fn ecm_factor_with_curve(
  n : Value,
  x : Value,
  z : Value,
  a : Value,
  lim1 : Value,
) -> Value raise {
  let g = num_gcd(num_sub(num_mul(a, a), Fix(4L)), n)
  if !num_eq(g, Fix(1L)) {
    return g
  }
  let a = num_mod(num_floor(num_add(a, Fix(2L)), b=Fix(4L)).0, n)
  //
  // stage 1: compute p^M where M=p1^e1*...*pk^ek where
  //          p1,...,pk are primes < lim1 and ei=log[pi](n)
  //
  let mut q : Value = Fix(1L)
  let last_q = d_prev_prime(lim1)
  let mut p = list2(x, z)
  let gcd_interval = num_floor(lim1, b=Fix(4L)).0
  let mut next_gcd = gcd_interval
  let llim1 = to_double(lim1)
  while !num_gt(q, lim1) {
    q = d_next_prime(q)
    let mut ex = (@math.ln(llim1) / @math.ln(to_double(q))).floor().to_int64()
    if num_eq(q, Fix(2L)) {
      ex += 2L
    } else if num_eq(q, Fix(3L)) {
      ex += 1L
    }
    p = ecm_power(p, expt(q, Fix(ex)), n, a)
    if num_ge(q, next_gcd) {
      let g = num_gcd(cadr(p), n)
      if num_lt(Fix(1L), g) && num_lt(g, n) {
        if ifactor__verbose() {
          ifactor__say("ECM: found factor in stage 1: ~d (~d digits)~%", [
            g,
            number_of_digits(g),
          ])
        }
        return g
      }
      next_gcd = num_min(num_add(next_gcd, gcd_interval), last_q)
    }
  }
  //
  // stage 2: compute (p^M)^pi for each prime lim1<pi<lim2 (and some
  //          other exponents)
  //          Uses "Improved standard continuation".
  //
  let lim2 = num_mul(lim1, Fix(100L))
  let power_after_1 = p
  let step_size = num_min(
    num_div(lim1, Fix(2L)),
    isqrt(num_div(lim2, Fix(2L))),
  )
  let d_step_size = num_mul(Fix(2L), step_size)
  let ss = to_int(step_size)
  let power_table : Array[Value] = Array::make(ss + 2, Nil)
  let d_step_size_power = ecm_power(power_after_1, d_step_size, n, a)
  let mut step_power = ecm_power(power_after_1, one_plus(d_step_size), n, a)
  let mut last_step_power = power_after_1
  let mut step_pos : Value = Fix(1L)
  let mut q1 : Value = Fix(3L)
  let mut prime_diffs_pos = 0
  init_prime_diffs(lim2) |> ignore
  power_table[1] = ecm_square(power_after_1, n, a)
  power_table[2] = ecm_square(power_table[1], n, a)
  for i in 3..=ss {
    power_table[i] = ecm_product(
      power_table[i - 2],
      power_table[1],
      power_table[i - 1],
      n,
    )
  }
  while !num_gt(step_pos, num_sub(lim2, d_step_size)) {
    let mut buff_prod : Value = Fix(1L)
    let q_limit = num_add(step_pos, d_step_size)
    let mut power_table_pos = num_div(num_sub(q1, step_pos), Fix(2L))
    if zerop(power_table_pos) {
      d_error(list2(q1, step_pos)) |> ignore
    }
    while !num_gt(q1, q_limit) {
      let sp1 = car(step_power)
      let sp2 = cadr(step_power)
      let pte = power_table[to_int(power_table_pos)]
      let pp1 = car(pte)
      let pp2 = cadr(pte)
      let coord_diffs = num_mod(num_sub(num_mul(sp1, pp2), num_mul(sp2, pp1)), n)
      buff_prod = num_mod(num_mul(coord_diffs, buff_prod), n)
      let dd = ifactor__diff(prime_diffs_pos)
      q1 = num_add(q1, dd)
      power_table_pos = num_add(power_table_pos, num_div(dd, Fix(2L)))
      prime_diffs_pos += 1
    }
    let g = num_gcd(n, buff_prod)
    if num_gt(g, Fix(1L)) {
      if ifactor__verbose() {
        ifactor__say("ECM: found factor in stage 2: ~d (~d digits)~%", [
          g,
          number_of_digits(g),
        ])
      }
      return g
    }
    let step_power_buff = step_power
    step_power = ecm_product(last_step_power, d_step_size_power, step_power, n)
    last_step_power = step_power_buff
    step_pos = num_add(step_pos, d_step_size)
  }
  Nil
}

///|
fn get_one_factor_ecm(n : Value) -> Value raise {
  if primep(n).truthy() {
    return n
  }
  let mut sigma = num_add(Fix(6L), mt_random(ash(Fix(1L), 20)))
  let mut lim1 = symval(q_d_ecm_limit)
  let curves = to_int(symval(q_d_ecm_number_of_curves))
  for i in 0..<curves {
    let u = num_mod(num_sub(num_mul(sigma, sigma), Fix(5L)), n)
    let v = num_mod(num_mul(Fix(4L), sigma), n)
    let x = num_mod(expt(u, Fix(3L)), n)
    let z = num_mod(expt(v, Fix(3L)), n)
    let a1 = num_mod(
      num_mul(
        expt(num_sub(v, u), Fix(3L)),
        num_add(num_mul(Fix(3L), u), v),
      ),
      n,
    )
    let a2 = num_mod(num_mul(num_mul(Fix(4L), x), v), n)
    let a2_inv = inv_mod(a2, n)
    if a2_inv is Nil {
      return num_gcd(a2, n)
    }
    let a = num_mod(num_mul(a1, a2_inv), n)
    sigma = num_max(Fix(6L), num_mod(num_add(num_mul(sigma, sigma), Fix(1L)), n))
    if ifactor__verbose() {
      ifactor__say("ECM: trying with curve #~d of ~d (lim=~d)~%", [
        int(i + 1),
        symval(q_d_ecm_number_of_curves),
        lim1,
      ])
    }
    let fact = ecm_factor_with_curve(n, x, z, a, lim1)
    if fact.truthy() && num_lt(fact, n) {
      return fact
    }
    lim1 = num_min(
      num_add(lim1, symval(q_d_ecm_limit_delta)),
      symval(q_d_ecm_max_limit),
    )
  }
  Nil
}

///|
/// Convert (3 5 3 5 3 7) to ((3 3) (5 2) (7 1)).
fn convert_list(l : Value) -> Value raise {
  let l1 = sort_list(l, (a, b) => num_gt(a, b))
  let mut e = car(l1)
  let mut n = 1
  let mut rest = cdr(l1)
  let mut l2 : Value = Nil
  while !(rest is Nil) {
    if num_eq(e, car(rest)) {
      n += 1
    } else {
      l2 = cons(list2(e, int(n)), l2)
      e = car(rest)
      n = 1
    }
    rest = cdr(rest)
  }
  cons(list2(e, int(n)), l2)
}

///|
fn d_primep(n : Value) -> Value raise {
  if integerp(n) {
    primep(num_abs(n))
  } else {
    merr("primep: argument must be an integer; found: ~M", [n])
  }
}

///|
let ifactor__b1 : Value = from_big(
  @bigint.BigInt::from_string("318665857834031151167461"),
)

///|
let ifactor__b2 : Value = from_big(
  @bigint.BigInt::from_string("3317044064679887385961981"),
)

///|
fn primep(n : Value) -> Value raise {
  if num_eq(n, Fix(1L)) {
    Nil
  } else if evenp(n) {
    lbool(num_eq(n, Fix(2L)))
  } else if num_le(n, symval(q_ear_largest_small_prime)) {
    if member(n, symval(q_ear_small_primes)).truthy() {
      t
    } else {
      Nil
    }
  } else if num_lt(n, Fix(9080191L)) {
    primep_small(n, list([Fix(31L), Fix(73L)]))
  } else if num_lt(n, Fix(4759123141L)) {
    primep_small(n, list([Fix(2L), Fix(7L), Fix(61L)]))
  } else if num_lt(n, Fix(2152302898747L)) {
    primep_small(n, ifactor__bases(5))
  } else if num_lt(n, Fix(3474749660383L)) {
    primep_small(n, ifactor__bases(6))
  } else if num_lt(n, Fix(341550071728321L)) {
    primep_small(n, ifactor__bases(7))
  } else if num_lt(n, Fix(3825123056546413051L)) {
    primep_small(n, ifactor__bases(9))
  } else if num_lt(n, ifactor__b1) {
    primep_small(n, ifactor__bases(12))
  } else if num_lt(n, ifactor__b2) {
    primep_small(n, ifactor__bases(13))
  } else if member(n, symval(q_ear_large_primes)).truthy() {
    t
  } else {
    primep_prob(n)
  }
}

///|
/// The first K primes, as a list.
fn ifactor__bases(k : Int) -> Value {
  let ps : Array[Int64] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  list(ps[0:k].to_array().map(p => Fix(p)))
}

///|
/// A Miller-Rabin test is deterministic for small n if we test for small
/// bases (Jaeschke 1993; Jiang, Deng 2014; Sorenson, Webster 2015).
fn primep_small(n : Value, bases : Value) -> Value raise {
  let (q, k) = miller_rabin_decomposition(n)
  for x in bases.iter() {
    if !miller_rabin_kernel(n, q, k, x~).truthy() {
      return Nil
    }
  }
  t
}

///|
/// Strong primality test: $primep_number_of_tests Miller-Rabin tests and one
/// Lucas test.
fn primep_prob(n : Value) -> Value raise {
  let (q, k) = miller_rabin_decomposition(n)
  let tests = to_int(symval(q_d_primep_number_of_tests))
  for _ in 0..<tests {
    if !miller_rabin_kernel(n, q, k).truthy() {
      return Nil
    }
  }
  primep_lucas(n)
}

///|
/// Return values q,k with n-1 = q*2^k (assumes n > 2).
fn miller_rabin_decomposition(n : Value) -> (Value, Value) raise {
  let mut k = 1
  let mut q = ash(n, -1)
  while !logbitp(0, q) {
    k += 1
    q = ash(q, -1)
  }
  (q, int(k))
}

///|
/// Miller-Rabin (algorithm P from D. Knuth, TAOCP, 4.5.4); assumes
/// n-1 = q*2^k, k >= 1.
fn miller_rabin_kernel(
  n : Value,
  q : Value,
  k : Value,
  x? : Value = Nil,
) -> Value raise {
  let x = if x is Nil {
    num_add(mt_random(num_sub(n, Fix(2L))), Fix(2L))
  } else {
    x
  }
  let mut y = power_mod(x, q, n) // j = 0
  let minus1 = one_minus(n)
  if num_eq(y, Fix(1L)) || num_eq(y, minus1) {
    t
  } else {
    let kk = to_int(k)
    for _ in 1..<kk {
      y = power_mod(y, Fix(2L), n)
      if num_eq(y, minus1) {
        return t
      }
      if num_eq(y, Fix(1L)) {
        return Nil
      }
    }
    Nil
  }
}

///|
fn d_power_mod(b : Value, e : Value, m : Value) -> Value raise {
  if !(integerp(b) && integerp(e) && integerp(m)) {
    merr("power_mod: arguments must be integers; found: ~M, ~M, ~M", [b, e, m])
    |> ignore
  }
  if num_ge(e, Fix(0L)) {
    power_mod(b, e, m)
  } else {
    let inv = inv_mod(b, m)
    if inv.truthy() {
      power_mod(inv, num_neg(e), m)
    } else {
      Nil
    }
  }
}

///|
fn power_mod(b : Value, e : Value, m : Value) -> Value raise {
  if zerop(e) {
    num_mod(Fix(1L), m)
  } else if e is Fix(_) {
    let mut e = e
    let mut b = b
    let mut res : Value = Fix(1L)
    while true {
      if logbitp(0, e) {
        res = num_mod(num_mul(res, b), m)
        if num_eq(Fix(1L), e) {
          return res
        }
      }
      e = ash(e, -1)
      b = num_mod(num_mul(b, b), m)
    }
    res
  } else {
    // sliding window variant
    let l = integer_length(e)
    let k = if l < 65 {
      3
    } else if l < 161 {
      4
    } else if l < 385 {
      5
    } else if l < 897 {
      6
    } else {
      7
    }
    let tab = power_mod_tab(b, int(k), m)
    let mut res : Value = Fix(1L)
    let mut i = l - 1
    while i >= 0 {
      if logbitp(i, e) {
        let mut s = if i - k + 1 > 0 { i - k + 1 } else { 0 }
        while !logbitp(s, e) {
          s += 1
        }
        let tmp = i - s + 1
        for _ in 0..<tmp {
          res = num_mod(num_mul(res, res), m)
        }
        let u = logand(ash(e, -s), one_minus(ash(Fix(1L), tmp)))
        if !num_eq(u, Fix(0L)) {
          res = num_mod(num_mul(res, aref1(tab, to_int(ash(u, -1)))), m)
        }
        i = s - 1
      } else {
        res = num_mod(num_mul(res, res), m)
        i -= 1
      }
    }
    res
  }
}

///|
fn power_mod_tab(b : Value, k : Value, m : Value) -> Value raise {
  let l = to_int(ash(Fix(1L), to_int(k) - 1))
  let tab : Array[Value] = Array::make(l, Fix(1L))
  let mut bi = b
  let bb = num_mod(num_mul(b, b), m)
  tab[0] = b
  for i in 1..<l {
    bi = num_mod(num_mul(bi, bb), m)
    tab[i] = bi
  }
  vector(tab)
}

///|
/// Lucas test: we calculate U[p+1] for x^2-b*x+1 where jacobi(b^2-4,n)=-1
/// and test if p divides U[p+1].
fn primep_lucas(n : Value) -> Value raise {
  let mut b : Value = Fix(3L)
  while !num_eq(d_jacobi(num_sub(num_mul(b, b), Fix(4L)), n), Fix(-1L)) {
    b = one_plus(b)
  }
  let prmp = zerop(lucas_sequence(one_plus(n), b, n))
  if prmp && symval(q_d_save_primes).truthy() {
    set(q_ear_large_primes, cons(n, symval(q_ear_large_primes))) |> ignore
  }
  lbool(prmp)
}

///|
/// Get element U[p+1] of Lucas sequence for x^2-p*x+1, using the algorithm
/// of M. Joye and J.-J. Quisquater, Efficient computation of full Lucas
/// sequences, 1996.
fn lucas_sequence(k : Value, p : Value, n : Value) -> Value raise {
  let mut k = k
  let mut uh : Value = Fix(1L)
  let mut vl : Value = Fix(2L)
  let mut vh = p
  let mut s = 0
  while !logbitp(0, k) {
    k = ash(k, -1)
    s += 1
  }
  let l = integer_length(k)
  let mut j = l - 1
  while j != 0 {
    if logbitp(j, k) {
      uh = num_mod(num_mul(uh, vh), n)
      vl = num_mod(num_sub(num_mul(vh, vl), p), n)
      vh = num_mod(num_sub(num_mul(vh, vh), Fix(2L)), n)
    } else {
      uh = num_mod(one_minus(num_mul(uh, vl)), n)
      vh = num_mod(num_sub(num_mul(vh, vl), p), n)
      vl = num_mod(num_sub(num_mul(vl, vl), Fix(2L)), n)
    }
    j -= 1
  }
  uh = num_mod(one_minus(num_mul(uh, vl)), n)
  vl = num_mod(num_sub(num_mul(vh, vl), p), n)
  for _ in 0..<s {
    uh = num_mod(num_mul(uh, vl), n)
    vl = num_mod(num_sub(num_mul(vl, vl), Fix(2L)), n)
  }
  uh
}

///|
fn d_next_prime(n : Value) -> Value raise {
  if !integerp(n) {
    merr("next_prime: argument must be an integer; found: ~M", [n]) |> ignore
  }
  if num_lt(n, Fix(2L)) {
    Fix(2L)
  } else if num_le(n, Fix(6L)) {
    aref1(symval(q_ear_next_prime_ar), to_int(n))
  } else if num_lt(n, Fix(100000L)) {
    next_prime_det(n, symval(q_deltaprimes_next))
  } else {
    next_prime_prob(n, symval(q_deltaprimes_next))
  }
}

///|
fn d_prev_prime(n : Value) -> Value raise {
  if !(integerp(n) && num_gt(n, Fix(2L))) {
    merr(
      "prev_prime: argument must be an integer greater than 2; found: ~M",
      [n],
    )
    |> ignore
  }
  if num_le(n, Fix(11L)) {
    return aref1(symval(q_ear_prev_prime_ar), to_int(n))
  }
  if num_lt(n, Fix(100000L)) {
    return next_prime_det(n, symval(q_deltaprimes_prev))
  }
  next_prime_prob(n, symval(q_deltaprimes_prev))
}

///|
/// Find next/prev prime using deterministic test that checks all divisors
/// < sqrt(n) and skipping all multiples of 2,3,5,7.
/// Preconditions: 11 < n < 9973*9973.
fn next_prime_det(n : Value, deltaprimes : Value) -> Value raise {
  let mut n = num_add(n, nth(to_int(mmod(n, Fix(210L))), deltaprimes))
  while true {
    for p in symval(q_ear_small_primes).iter() {
      if num_eq(mmod(n, p), Fix(0L)) {
        break
      }
      if num_ge(num_mul(p, p), n) {
        return n
      }
    }
    n = num_add(n, nth(to_int(mmod(n, Fix(210L))), deltaprimes))
  }
  n
}

///|
/// Find next/prev prime using probabilistic test, skipping all multiples of
/// 2,3,5,7 using the deltaprimes list and calculating gcd's with products of
/// prime numbers.
fn next_prime_prob(n : Value, deltaprimes : Value) -> Value raise {
  let mut n = num_add(n, nth(to_int(mmod(n, Fix(210L))), deltaprimes))
  while true {
    if num_eq(num_gcd(n, Fix(955049953L)), Fix(1L)) &&
      num_eq(num_gcd(n, Fix(162490421L)), Fix(1L)) &&
      num_eq(num_gcd(n, symval(q_bigprimemultiple)), Fix(1L)) &&
      primep(n).truthy() {
      return n
    }
    n = num_add(n, nth(to_int(mmod(n, Fix(210L))), deltaprimes))
  }
  n
}

///|
fn next_prime(n : Value, c : Value) -> Value raise {
  let mut n = n
  if evenp(n) {
    n = num_add(n, c)
  }
  while true {
    if primep(n).truthy() {
      return n
    }
    n = num_add(n, num_mul(Fix(2L), c))
  }
  n
}

///|
/// Return a list of all primes between start and end.
fn d_primes(start : Value, end : Value) -> Value raise {
  if !(integerp(start) && integerp(end)) {
    merr("primes: arguments must be integers; found: ~M, ~M", [start, end])
    |> ignore
  }
  let mut start = start
  let mut primes : Value = Nil
  let lsp = symval(q_ear_largest_small_prime)
  if num_le(start, lsp) {
    for n in symval(q_ear_small_primes).iter() {
      if num_le(start, n) && num_le(n, end) {
        primes = cons(n, primes)
      }
    }
    start = lsp
  } else {
    start = one_minus(start)
  }
  let mut n = d_next_prime(start)
  while !num_gt(n, end) {
    primes = cons(n, primes)
    n = d_next_prime(one_plus(n))
  }
  cons(list1(q_mlist), reverse(primes))
}

///|
/// Record the initial value of a defmvar (globals.lisp `maybe-reset`).
fn ifactor__defmvar_reset(var_ : Value) -> Unit raise {
  let h = symval(q_ear_variable_initial_values)
  if hash_table_p(h) && !gethash(var_, h).truthy() {
    sethash(var_, h, symval(var_)) |> ignore
  }
}

///|
/// The ASSIGN property installed by defmvar's `:setting-predicate`.
fn ifactor__integer_setting(var_ : Value) -> Unit raise {
  putprop(
    var_,
    lfunc("integer-setting-predicate", args => {
      let (ok, reason) = integer_predicate(arg(args, 1))
      if !ok.truthy() {
        mseterr(arg(args, 0), arg(args, 1), reason~)
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
}

///|
/// The ASSIGN property installed by defmvar's `boolean` option.
fn ifactor__boolean_setting(var_ : Value) -> Unit raise {
  putprop(
    var_,
    lfunc("boolean-setting", args => {
      let v = arg(args, 1)
      if member(v, list2(t, Nil)) is Nil {
        let names = [princ_to_string(stripdollar(t)), princ_to_string(stripdollar(Nil))]
        mseterr(
          arg(args, 0),
          v,
          reason=Str("must be one of: " + names[0] + ", " + names[1]),
        )
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
}

///|
fn init_ifactor() -> Unit raise {
  for v in [
    q_d_save_primes, q_d_primep_number_of_tests, q_d_pollard_rho_limit, q_d_pollard_pm1_limit,
    q_d_pollard_rho_tests, q_d_pollard_pm1_tests, q_d_pollard_rho_limit_step, q_d_pollard_pm1_limit_step,
    q_d_ecm_number_of_curves, q_d_ecm_limit, q_d_ecm_max_limit, q_d_ecm_limit_delta,
    q_d_ifactor_verbose, q_d_factors_only,
  ] {
    ifactor__defmvar_reset(v)
  }
  for v in [q_d_save_primes, q_d_ifactor_verbose, q_d_factors_only] {
    ifactor__boolean_setting(v)
  }
  for v in [
    q_d_primep_number_of_tests, q_d_pollard_rho_limit, q_d_pollard_pm1_limit, q_d_pollard_rho_tests,
    q_d_pollard_pm1_tests, q_d_pollard_rho_limit_step, q_d_pollard_pm1_limit_step, q_d_ecm_number_of_curves,
    q_d_ecm_limit, q_d_ecm_max_limit, q_d_ecm_limit_delta,
  ] {
    ifactor__integer_setting(v)
  }
  defvar_init(q_ear_largest_small_prime, car(last(symval(q_ear_small_primes))))
  defvar_init(q_ear_large_primes, Nil)
  defvar_init(q_ear_prime_diffs, make_array([100000], initial=Fix(0L), elt="fixnum"))
  defvar_init(
    q_ear_next_prime_ar,
    vector([Fix(0L), Fix(2L), Fix(3L), Fix(5L), Fix(5L), Fix(7L), Fix(7L)]),
  )
  defvar_init(
    q_ear_prev_prime_ar,
    vector(
      [0L, 0, 0, 2, 3, 3, 5, 5, 7, 7, 7, 7].map(x => Fix(x)),
    ),
  )
}

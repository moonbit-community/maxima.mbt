// Port of share/combinatorics/combinatorics.lisp (Jaime Villate, 2017):
// Maxima functions to work with permutations.
//
// NOTATION
//  pm    : a permutation as a maxima list
//  pa    : a permutation as a lisp array
//  lpm   : a lisp list of pm's (in reverse order)
//  lmpm  : a maxima list of pm's
//  cm    : a cycle as a maxima list
//  lcm   : a lisp list of cycles as maxima lists
//  lmcm  : a maxima list of cycles as maxima lists

///|
/// (nth i l) with a Lisp integer index
fn share_combinatorics__nth(i : Value, l : Value) -> Value raise {
  nth(to_int(i), l)
}

///|
/// (setf (nth i l) v)
fn share_combinatorics__setnth(i : Int, l : Value, v : Value) -> Unit raise {
  rplaca(nthcdr(i, l), v) |> ignore
}

///|
/// (aref pa i) as an Int
fn share_combinatorics__aref(pa : Value, i : Int) -> Int raise {
  to_int(aref1(pa, i))
}

///|
/// (setf (aref pa i) v)
fn share_combinatorics__aset(pa : Value, i : Int, v : Int) -> Unit raise {
  aset1(pa, i, int(v)) |> ignore
}

///|
/// (concatenate 'list '((mlist simp)) pa)
fn share_combinatorics__pa_to_pm(pa : Value) -> Value raise {
  cons(list2(q_mlist, q_simp), vector_to_list(pa))
}

///|
/// macro (push-array-mlist pa lpm): turn a pa into a pm and push it to the
/// top of an lpm; returns the new lpm (the caller stores it in the place).
fn push_array_mlist(pa : Value, lpm : Value) -> Value raise {
  cons(share_combinatorics__pa_to_pm(pa), lpm)
}

///|
/// macro (array-adjacent-transposition pa i): apply transposition [i,i+1]
/// to a pa (i from 1 to n-1)
fn array_adjacent_transposition(pa : Value, i : Value) -> Value raise {
  let i = to_int(i)
  let x = aref1(pa, i - 1)
  aset1(pa, i - 1, aref1(pa, i)) |> ignore
  aset1(pa, i, x) |> ignore
  Nil
}

///|
/// macro (array-transposition pa i j): apply transposition [i,j] to a pa
/// (i and j from 1 to n)
fn array_transposition(pa : Value, i : Value, j : Value) -> Value raise {
  let i = to_int(i)
  let j = to_int(j)
  let x = aref1(pa, i - 1)
  aset1(pa, i - 1, aref1(pa, j - 1)) |> ignore
  aset1(pa, j - 1, x) |> ignore
  Nil
}

///|
/// $cyclep returns true if its argument is a maxima list of length n or
/// lower, whose elements are integers between 1 and n, without repetitions.
fn d_cyclep(cm : Value, n : Value) -> Value raise {
  // a cycle must be a maxima list
  if !(integerp(n) && num_ge(n, Fix(0L))) {
    return Nil
  }
  if !d_listp(cm).truthy() {
    return Nil
  }
  for i in rest(cm).iter() {
    // cycle elements must be positive integers, less or equal to n
    if !(integerp(i) && plusp(i) && num_le(i, n)) {
      return Nil
    }
    // and cannot be repeated
    if !(count_if(x => eql(i, x), rest(cm)) < 2) {
      return Nil
    }
  }
  t
}

///|
/// $permp returns true if its argument is a maxima list of length n,
/// whose elements are the integers 1, 2, ...n, without repetitions.
fn d_permp(pm : Value) -> Value raise {
  if !d_listp(pm).truthy() {
    return Nil
  }
  let n = d_length(pm)
  // a permutation of degree n is also a valid cycle of degree n
  d_cyclep(pm, n)
}

///|
fn check_perm(pm : Value, caller : Value) -> Value raise {
  let v = d_permp(pm)
  if v.truthy() {
    v
  } else {
    merror(
      Str("~M: argument should be a permutation; found: ~M"),
      list2(caller, pm),
    )
  }
}

///|
fn check_cycle(cm : Value, n : Value, caller : Value) -> Value raise {
  let v = d_cyclep(cm, n)
  if v.truthy() {
    v
  } else {
    merror(
      Str("~M: argument should be a cycle of degree ~M; found: ~M"),
      list3(caller, n, cm),
    )
  }
}

///|
fn check_list_or_set(lsm : Value, caller : Value) -> Value raise {
  let v = d_listp(lsm)
  if v.truthy() {
    return v
  }
  let v = d_setp(lsm)
  if v.truthy() {
    return v
  }
  merror(
    Str("~M: argument should be a list or set; found: ~M"),
    list2(caller, lsm),
  )
}

///|
fn check_list(lm : Value, caller : Value) -> Value raise {
  let v = d_listp(lm)
  if v.truthy() {
    v
  } else {
    merror(Str("~M: argument should be a list; found: ~M"), list2(caller, lm))
  }
}

///|
fn check_list_length(lm : Value, n : Value, caller : Value) -> Value raise {
  if eql(d_length(lm), n) {
    t
  } else {
    merror(
      Str("~M: argument should be a list of length ~M; found: ~M"),
      list3(caller, n, lm),
    )
  }
}

///|
fn check_pos_integer(n : Value, caller : Value) -> Value raise {
  if integerp(n) && num_gt(n, Fix(0L)) {
    t
  } else {
    merror(
      Str("~M: argument must be a positive integer; found: ~M"),
      list2(caller, n),
    )
  }
}

///|
fn check_integer_n1_n2(
  r : Value,
  n1 : Value,
  n2 : Value,
  caller : Value,
) -> Value raise {
  if integerp(r) && num_ge(r, n1) && num_le(r, n2) {
    t
  } else {
    merror(
      Str("~M: argument must be an integer between ~M and ~M; found: ~M"),
      list([caller, n1, n2, r]),
    )
  }
}

///|
/// $permult multiplies permutation pm by the permutations in list lmpm
fn d_permult(pm : Value, lmpm : Value) -> Value raise {
  check_perm(pm, Str("permult")) |> ignore
  let n = d_length(pm)
  let rm = copy_list(pm)
  // multiplies the current product, rm, by each of the permutations in lmpm
  for qm in lmpm.iter() {
    check_list_length(qm, n, Str("permult")) |> ignore
    check_perm(qm, Str("permult")) |> ignore
    // the new product, rm, is the current product, rm, times
    // permutation qm: rm = [qm[rm[1]], qm[rm[2]], ..., qm[rm[n]]]
    for j in 1..=to_int(n) {
      share_combinatorics__setnth(
        j,
        rm,
        share_combinatorics__nth(nth(j, rm), qm),
      )
    }
  }
  rm
}

///|
/// $perm_inverse computes the inverse of permutation p
fn d_perm_inverse(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_inverse")) |> ignore
  let inverse = copy_list(pm)
  // if the element pm[j] of the permutation is equal to i, then
  // the element inverse[i] of the inverse should be equal to j.
  for j in 0..<to_int(d_length(pm)) {
    share_combinatorics__setnth(to_int(nth(j + 1, pm)), inverse, int(j + 1))
  }
  inverse
}

///|
/// $permute permutes the elements of list (or set) lsm according
/// to the permutation pm
fn d_permute(pm : Value, lsm : Value) -> Value raise {
  check_perm(pm, Str("permute")) |> ignore
  check_list_length(lsm, d_length(pm), Str("permute")) |> ignore
  let mut result : Value = Nil
  for j in reverse(rest(pm)).iter() {
    result = cons(share_combinatorics__nth(j, lsm), result)
  }
  cons(car(lsm), result)
}

///|
/// $apply_cycles permutes the elements of list (or set) lsm according to
/// the list of cycles lmcm, applying the cycles on the end of the list
/// first
fn d_apply_cycles(lmcm : Value, lsm : Value) -> Value raise {
  check_list(lmcm, Str("apply_cycles")) |> ignore
  check_list_or_set(lsm, Str("apply_cycles")) |> ignore
  let n = d_length(lsm)
  let r = copy_list(lsm)
  // iterate the cycles, the last in the list first
  for cm in reverse(rest(lmcm)).iter() {
    check_cycle(cm, n, Str("apply_cycles")) |> ignore
    let m = to_int(d_length(cm))
    let tmp = share_combinatorics__nth(nth(1, cm), r)
    for i in 1..=(m - 1) {
      share_combinatorics__setnth(
        to_int(nth(i, cm)),
        r,
        share_combinatorics__nth(nth(i + 1, cm), r),
      )
    }
    share_combinatorics__setnth(to_int(nth(m, cm)), r, tmp)
  }
  r
}

///|
/// $perm_undecomp converts a list of cycles into a permutation,
/// equal to their product, by applying $apply_cycles to [1, 2,..., n]
fn d_perm_undecomp(lmcm : Value, n : Value) -> Value raise {
  check_list(lmcm, Str("perm_undecomp")) |> ignore
  check_pos_integer(n, Str("perm_undecomp")) |> ignore
  let c = Collector::new()
  for i in 1..=to_int(n) {
    c.add(int(i))
  }
  d_apply_cycles(lmcm, cons(list2(q_mlist, q_simp), c.result()))
}

///|
/// $perm_cycles decomposes permutation p into a product of canonical
/// cycles: with lower indices first.
fn d_perm_cycles(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_cycles")) |> ignore
  let n = to_int(d_length(pm))
  let mut result = list1(list2(q_mlist, q_simp))
  let v : Array[Int] = Array::make(n, 1)
  // the i'th bit in bit array v equal to 1 means index i+1 has not been
  // added to any cycles. The next cycle will then start where the first
  // value of 1 is found in v
  while v.search(1) is Some(i) {
    v[i] = 0
    // i= v index where a 1 was found. j=i+1 first index in the current
    // cycle. k=next index in the current cycle
    let j = i + 1
    let mut k = j
    let mut cm = list2(list2(q_mlist, q_simp), int(j))
    // if p[k] is different from k, there's a non-trivial cycle
    while to_int(nth(k, pm)) != j {
      k = to_int(nth(k, pm))
      cm = append(cm, list1(int(k)))
      v[k - 1] = 0
    }
    // a trivial cycle with just one index (length 2) will not be saved
    if length(cm) > 2 {
      result = append(result, list1(cm))
    }
  }
  result
}

///|
/// $perm_lex_rank finds the position of the given permutation in
/// the lexicographic ordering of permutations (from 1 to n!).
/// Algorithm 2.15: from Kreher & Stinson (1999). Combinatorial Algorithms.
fn d_perm_lex_rank(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_lex_rank")) |> ignore
  let mut r : Value = Fix(1L)
  let n = to_int(d_length(pm))
  let qm = copy_list(pm)
  for j in 1..=n {
    r = num_add(
      r,
      num_mul(num_sub(nth(j, qm), Fix(1L)), factorial(int(n - j))),
    )
    for i in (j + 1)..=n {
      if num_gt(nth(i, qm), nth(j, qm)) {
        share_combinatorics__setnth(i, qm, num_sub(nth(i, qm), Fix(1L)))
      }
    }
  }
  r
}

///|
/// $perm_length finds the minimum number of adjacent transpositions
/// necessary to write permutation p as a product of adjacent
/// transpositions.
fn d_perm_length(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_length")) |> ignore
  let mut d : Value = Fix(0L)
  let n = to_int(d_length(pm))
  let qm = copy_list(pm)
  for j in 1..=n {
    d = num_add(d, num_sub(nth(j, qm), Fix(1L)))
    for i in (j + 1)..=n {
      if num_gt(nth(i, qm), nth(j, qm)) {
        share_combinatorics__setnth(i, qm, num_sub(nth(i, qm), Fix(1L)))
      }
    }
  }
  d
}

///|
/// $perm_decomp finds the minimum set of adjacent transpositions
/// whose product equals permutation pm.
fn d_perm_decomp(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_decomp")) |> ignore
  let mut lcm : Value = Nil
  let n = to_int(d_length(pm))
  let qm = copy_list(pm)
  for j in 1..=(n - 1) {
    if to_int(nth(j, qm)) - 1 >= 1 {
      let mut i = to_int(nth(j, qm)) - 2 + j
      while i >= j {
        lcm = cons(list3(list2(q_mlist, q_simp), int(i), int(i + 1)), lcm)
        i = i - 1
      }
    }
    for k in (j + 1)..=n {
      if num_gt(nth(k, qm), nth(j, qm)) {
        share_combinatorics__setnth(k, qm, num_sub(nth(k, qm), Fix(1L)))
      }
    }
  }
  cons(list2(q_mlist, q_simp), lcm)
}

///|
/// $perm_parity finds the parity of permutation p (0 or 1).
fn d_perm_parity(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_parity")) |> ignore
  perm_parity(d_length(pm), rest(pm))
}

///|
/// perm-parity finds the parity of n first elements of p (lisp list)
/// Algorithm 2.19 from Kreher & Stinson (1999). Combinatorial Algorithms.
fn perm_parity(n : Value, p : Value) -> Value raise {
  let n = to_int(n)
  let mut c = 0
  let a : Array[Int] = Array::make(n, 0)
  for j in 0..<n {
    if a[j] == 0 {
      c = c + 1
      a[j] = 1
      let mut i = j
      while to_int(nth(i, p)) - 1 != j {
        i = to_int(nth(i, p)) - 1
        a[i] = 1
      }
    }
  }
  int((n - c) % 2)
}

///|
/// A fresh fixnum array of size n.
fn share_combinatorics__make_pa(n : Value) -> Value raise {
  make_array([to_int(n)], initial=Fix(0L))
}

///|
/// $perms_lex returns a list of permutations of degree n in lexicographic
/// order
fn d_perms_lex(n : Value, r0? : Value = Nil, rf? : Value = Nil) -> Value raise {
  check_pos_integer(n, Str("perms_lex")) |> ignore
  if r0.truthy() {
    check_integer_n1_n2(r0, Fix(1L), factorial(n), Str("perms_lex")) |> ignore
  }
  if rf.truthy() {
    check_integer_n1_n2(rf, r0, factorial(n), Str("perms_lex")) |> ignore
  }
  let pa = share_combinatorics__make_pa(n)
  let mut lpm : Value = Nil
  if r0.truthy() {
    perm_lex_unrank(n, r0, pa) |> ignore
    lpm = push_array_mlist(pa, lpm)
    if rf.truthy() {
      for _ in 0..<to_int(num_sub(rf, r0)) {
        perm_lex_next(n, pa) |> ignore
        lpm = push_array_mlist(pa, lpm)
      }
    }
  } else {
    for i in 0..<to_int(n) {
      share_combinatorics__aset(pa, i, i + 1)
    }
    lpm = push_array_mlist(pa, lpm)
    while perm_lex_next(n, pa).truthy() {
      lpm = push_array_mlist(pa, lpm)
    }
  }
  cons(list2(q_mlist, q_simp), nreverse(lpm))
}

///|
/// $perm_lex_next finds the next permutation in lexicographic order
fn d_perm_lex_next(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_lex_next")) |> ignore
  let n = d_length(pm)
  let pa = share_combinatorics__make_pa(n)
  for i in 0..<to_int(n) {
    aset1(pa, i, nth(i + 1, pm)) |> ignore
  }
  if !perm_lex_next(n, pa).truthy() {
    return Nil
  }
  share_combinatorics__pa_to_pm(pa)
}

///|
/// $perm_lex_unrank finds the n-degree permutation with lexicographic rank r
fn d_perm_lex_unrank(n : Value, r : Value) -> Value raise {
  check_pos_integer(n, Str("perm_lex_unrank")) |> ignore
  check_integer_n1_n2(r, Fix(1L), factorial(n), Str("perm_lex_unrank"))
  |> ignore
  let pa = share_combinatorics__make_pa(n)
  perm_lex_unrank(n, r, pa) |> ignore
  share_combinatorics__pa_to_pm(pa)
}

///|
/// perm-lex-next finds next permutation in the lexicographic order.
/// Based on Algorithm 2.14 from Kreher & Stinson (1999). Combinatorial
/// Algorithms.
fn perm_lex_next(n : Value, pa : Value) -> Value raise {
  let n = to_int(n)
  let mut i = n - 1
  let mut j = n
  while i > 0 &&
    share_combinatorics__aref(pa, i) < share_combinatorics__aref(pa, i - 1) {
    i = i - 1
  }
  if i == 0 {
    return Nil
  }
  while share_combinatorics__aref(pa, j - 1) <
    share_combinatorics__aref(pa, i - 1) {
    j = j - 1
  }
  array_transposition(pa, int(i), int(j)) |> ignore
  for k in 0..<((n - i) / 2) {
    array_transposition(pa, int(k + i + 1), int(n - k)) |> ignore
  }
  t
}

///|
/// perm-lex-unrank finds the n-degree permutation of in position
/// r (from 1 to n!) in the lexicographic ordering of permutations.
/// Algorithm 2.16: from Kreher & Stinson (1999). Combinatorial Algorithms.
fn perm_lex_unrank(n : Value, r : Value, pa : Value) -> Value raise {
  let n = to_int(n)
  let mut r = r
  aset1(pa, n - 1, Fix(1L)) |> ignore
  for j in 0..<(n - 1) {
    let d = num_div(
      num_mod(num_sub(r, Fix(1L)), factorial(int(j + 2))),
      factorial(int(j + 1)),
    )
    r = num_sub(r, num_mul(d, factorial(int(j + 1))))
    aset1(pa, n - j - 2, num_add(Fix(1L), d)) |> ignore
    for i in (n - j - 1)..=(n - 1) {
      if num_gt(aref1(pa, i), d) {
        aset1(pa, i, num_add(Fix(1L), aref1(pa, i))) |> ignore
      }
    }
  }
  t
}

///|
/// $perms returns a list of the permutations of order n
/// in Trotter-Johnson ordering, using a simpler algorithm
fn d_perms(n : Value, r0? : Value = Nil, rf? : Value = Nil) -> Value raise {
  check_pos_integer(n, Str("perms")) |> ignore
  if r0.truthy() {
    check_integer_n1_n2(r0, Fix(1L), factorial(n), Str("perms")) |> ignore
  }
  if rf.truthy() {
    check_integer_n1_n2(rf, r0, factorial(n), Str("perms")) |> ignore
  }
  let pa = share_combinatorics__make_pa(n)
  let mut lpm : Value = Nil
  if r0.truthy() {
    perm_unrank(n, r0, pa) |> ignore
    lpm = push_array_mlist(pa, lpm)
    if rf.truthy() {
      let mut r = r0
      while num_le(r, num_sub(rf, Fix(1L))) {
        array_adjacent_transposition(pa, transposition_next(n, r).0) |> ignore
        lpm = push_array_mlist(pa, lpm)
        r = num_add(r, Fix(1L))
      }
    }
  } else {
    for i in 0..<to_int(n) {
      share_combinatorics__aset(pa, i, i + 1)
    }
    lpm = push_array_mlist(pa, lpm)
    let mut r : Value = Fix(1L)
    let last = num_sub(factorial(n), Fix(1L))
    while num_le(r, last) {
      array_adjacent_transposition(pa, transposition_next(n, r).0) |> ignore
      lpm = push_array_mlist(pa, lpm)
      r = num_add(r, Fix(1L))
    }
  }
  cons(list2(q_mlist, q_simp), nreverse(lpm))
}

///|
/// $perm_unrank finds the n-degree permutation with Trotter-Johnson rank r
fn d_perm_unrank(n : Value, r : Value) -> Value raise {
  check_pos_integer(n, Str("perm_unrank")) |> ignore
  check_integer_n1_n2(r, Fix(1L), factorial(n), Str("perm_unrank")) |> ignore
  let pa = share_combinatorics__make_pa(n)
  perm_unrank(n, r, pa) |> ignore
  share_combinatorics__pa_to_pm(pa)
}

///|
/// $perm_rank finds the position of the given permutation in
/// the Trotter-Johnson ordering of permutations (from 1 to n!).
/// Algorithm 2.17: from Kreher & Stinson (1999). Combinatorial Algorithms.
fn d_perm_rank(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_rank")) |> ignore
  let mut r : Value = Fix(1L)
  let n = to_int(d_length(pm))
  for j in 2..=n {
    let mut k = 1
    let mut i = 1
    while to_int(nth(i, pm)) != j {
      if to_int(nth(i, pm)) < j {
        k = k + 1
      }
      i = i + 1
    }
    if num_eq(num_mod(r, Fix(2L)), Fix(1L)) {
      r = num_sub(num_add(num_mul(int(j), r), Fix(1L)), int(k))
    } else {
      r = num_add(num_mul(int(j), num_sub(r, Fix(1L))), int(k))
    }
  }
  r
}

///|
/// perm-unrank returns the n-degree permutation in position r
/// (from 1 to n!) in the Trotter-Johnson ordering of permutations.
/// Algorithm 2.18: from Kreher & Stinson (1999). Combinatorial Algorithms.
fn perm_unrank(n : Value, r : Value, pa : Value) -> Value raise {
  let mut r2 : Value = Fix(0L)
  aset1(pa, 0, Fix(1L)) |> ignore
  for j in 2..=to_int(n) {
    let r1 = floor1(
      num_div(num_mul(num_sub(r, Fix(1L)), factorial(int(j))), factorial(n)),
    )
    let k = to_int(num_sub(r1, num_mul(int(j), r2)))
    if num_eq(num_mod(r2, Fix(2L)), Fix(0L)) {
      let mut i = j - 1
      while i >= j - k {
        aset1(pa, i, aref1(pa, i - 1)) |> ignore
        i = i - 1
      }
      aset1(pa, j - k - 1, int(j)) |> ignore
    } else {
      let mut i = j - 1
      while i >= k + 1 {
        aset1(pa, i, aref1(pa, i - 1)) |> ignore
        i = i - 1
      }
      aset1(pa, k, int(j)) |> ignore
    }
    r2 = r1
  }
  Nil
}

///|
/// transposition-next finds the first index of the adjacent transposition
/// to be applied to the n-degree permutation of Trotter-Johnson rank r, in
/// order to get the permutation of rank r+1 (r must be between 1 and
/// n!-1). (A single value; the declaration has a second, always NIL.)
fn transposition_next(n : Value, r : Value) -> (Value, Value) raise {
  let mut n = n
  let mut r = r
  let mut d : Value = Fix(0L)
  let (m0, k0) = num_floor(r, b=n)
  let mut m = m0
  let mut k = k0
  while num_eq(k, Fix(0L)) {
    r = m
    n = num_sub(n, Fix(1L))
    if num_eq(num_mod(m, Fix(2L)), Fix(1L)) {
      d = num_add(d, Fix(1L))
    }
    let (m1, k1) = num_floor(r, b=n)
    m = m1
    k = k1
  }
  if num_eq(num_mod(m, Fix(2L)), Fix(0L)) {
    (num_add(num_sub(n, k), d), Nil)
  } else {
    (num_add(k, d), Nil)
  }
}

///|
/// $perm_next finds the next permutation in Trotter-Johnson ordering
fn d_perm_next(pm : Value) -> Value raise {
  check_perm(pm, Str("perm_next")) |> ignore
  let n = d_length(pm)
  let r = d_perm_rank(pm)
  let qm = copy_list(pm)
  if num_eq(r, factorial(n)) {
    return Nil
  }
  let i = to_int(transposition_next(n, r).0)
  let x = nth(i, qm)
  share_combinatorics__setnth(i, qm, nth(i + 1, qm))
  share_combinatorics__setnth(i + 1, qm, x)
  qm
}

///|
/// $random_perm generates a random permutation of degree n, using
/// algorithm 5.4 from Reingold, Nievergelt and Deo. Combinatorial
/// algorithms: theory and practice. 1977
fn d_random_perm(n : Value) -> Value raise {
  check_pos_integer(n, Str("random_perm")) |> ignore
  let c = Collector::new()
  for i in 1..=to_int(n) {
    c.add(int(i))
  }
  let pm = cons(list1(q_mlist), c.result())
  let mut i = to_int(n)
  while i >= 2 {
    let j = to_int(num_add(Fix(1L), d_random(int(i))))
    let x = nth(i, pm)
    share_combinatorics__setnth(i, pm, nth(j, pm))
    share_combinatorics__setnth(j, pm, x)
    i = i - 1
  }
  pm
}

///|
fn init_share_combinatorics() -> Unit raise {

}

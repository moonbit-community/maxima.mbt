// Port of share/linearalgebra/linalg-extra.lisp.

///|
fn d_circulant(lst : Value) -> Value raise {
  d_require_list(lst, q_d_first, q_d_circulant) |> ignore
  let mut n = to_int(d_length(lst))
  let mut lst = rest(lst)
  let mut q = list1(lst)
  n -= 1
  for _ in 0..<n {
    lst = append(rest(lst), list1(car(lst)))
    q = cons(lst, q)
  }
  q = mapcar(s => cons(list1(q_mlist), s), q)
  cons(list1(q_d_matrix), q)
}

///|
fn d_cauchy_matrix(p : Value, q? : Value = Nil) -> Value raise {
  d_require_list(p, q_d_first, q_d_cauchy_matrix) |> ignore
  let mut q = q
  if q.truthy() {
    d_require_list(q, q_d_second, q_d_cauchy_matrix) |> ignore
  } else {
    q = p
  }
  let p = margs(p)
  let q = margs(q)
  let mut mat : Value = Nil
  for pj in p.iter() {
    let mut row : Value = Nil
    for qj in q.iter() {
      row = cons(div(Fix(1L), add2(pj, qj)), row)
    }
    row = nreverse(row)
    row = cons(list1(q_mlist), row)
    mat = cons(row, mat)
  }
  mat = nreverse(mat)
  cons(list1(q_d_matrix), mat)
}

///|
fn d_hessian(e : Value, vars : Value) -> Value raise {
  if d_listp(vars).truthy() {
    let vars = margs(vars)
    let mut mat : Value = Nil
    for vi in vars.iter() {
      let z = d_diff(list2(e, vi))
      mat = cons(
        cons(list1(q_mlist), mapcar(s => d_diff(list2(z, s)), vars)),
        mat,
      )
    }
    cons(list1(q_d_matrix), reverse(mat))
  } else {
    list3(list1(q_d_hessian), e, vars)
  }
}

///|
fn d_jacobian(e : Value, vars : Value) -> Value raise {
  if d_listp(vars).truthy() && d_listp(e).truthy() {
    let e = margs(e)
    let vars = margs(vars)
    let mut mat : Value = Nil
    for ei in e.iter() {
      mat = cons(
        cons(list1(q_mlist), mapcar(s => d_diff(list2(ei, s)), vars)),
        mat,
      )
    }
    cons(list1(q_d_matrix), reverse(mat))
  } else {
    list3(list1(q_d_jacobian), e, vars)
  }
}

///|
fn d_vandermonde_matrix(l : Value) -> Value raise {
  let mut l = require_list(l, q_d_vandermonde_matrix)
  let n = length(l) - 1
  let mut acc : Value = Nil
  while l.truthy() {
    let mut q : Value = Fix(1L)
    let x = car(l)
    l = cdr(l)
    let mut row = list1(Fix(1L))
    for _ in 0..<n {
      q = mul2(q, x)
      row = cons(q, row)
    }
    row = cons(list1(q_mlist), nreverse(row))
    acc = cons(row, acc)
  }
  simplify(cons(list1(q_d_matrix), nreverse(acc)))
}

///|
/// Use Sylvester's criterion to decide if the self-adjoint part of a matrix
/// is negative definite (neg) or positive definite (pos). For all other
/// cases, return pnz.  The argument must be a selfadjoint matrix.
fn matrix_sign_sylvester(m : Value) -> Value raise {
  let mut p_sgn : Value = Nil
  let mut n_sgn : Value = Nil
  let n = to_int(d_first(d_matrix_size(m)))
  for i in 1..=n {
    let det = ratdisrep(newdet(m, int(i), Nil))
    p_sgn = cons(csign(det), p_sgn)
    n_sgn = cons(csign(mul2(power(Fix(-1L), int(i)), det)), n_sgn)
  }
  if every(s => eq(s, q_d_pos), p_sgn) {
    q_d_pos
  } else if every(s => eq(s, q_d_pos), n_sgn) {
    q_d_neg
  } else {
    q_d_pnz
  }
}

///|
fn order_of_root(p : Value, x : Value, pt : Value) -> Value raise {
  let mut order = 0
  let mut p = d_expand(p)
  while alike1(Fix(0L), d_substitute(pt, x, expr=p)).truthy() &&
    !alike1(Fix(0L), p).truthy() {
    order += 1
    p = d_expand(d_diff(list2(p, x)))
  }
  int(order)
}

///|
let share_linalg_extra__not_ratnump : Value = try! lread(
  "((lambda) ((mlist) $s) ((mnot) (($ratnump) $s)))",
)

///|
/// Let M be the self-adjoint part of mat, (M + M^*) / 2.  Return neg, nz,
/// pz, pos when M is negative definite, negative semidefinite, positive
/// semidefinite, positive definite, and pnz otherwise.  When M is a matrix
/// of rational numbers, look at the zeros of the characteristic polynomial;
/// otherwise, use Sylvester's criterion.
fn d_matrix_sign(mat : Value) -> Value raise {
  let z = gensym()
  d_require_square_matrix(mat, q_d_first, q_d_matrix_sign) |> ignore
  let mat = div(add2(mat, d_ctranspose(mat)), Fix(2L))
  if d_some(share_linalg_extra__not_ratnump, list1(mat)).truthy() {
    matrix_sign_sylvester(mat)
  } else {
    let n = d_first(d_matrix_size(mat))
    if d_zeromatrixp(mat).truthy() {
      q_d_zero
    } else {
      let p = d_charpoly(mat, z)
      // number of roots of characteristic poly in {0}
      let nbr_zero_roots = order_of_root(p, z, Fix(0L))
      // number of roots of characteristic poly in (-inf,0)
      let nbr_neg_roots = num_sub(
        d_nroots(p, l=q_d_minf, r=Fix(0L)),
        nbr_zero_roots,
      )
      // number of roots of characteristic poly in (0,inf)
      let nbr_pos_roots = d_nroots(p, l=Fix(0L), r=q_d_inf)
      if num_eq(n, nbr_neg_roots) {
        q_d_neg
      } else if num_eq(Fix(0L), nbr_pos_roots) {
        q_d_nz
      } else if num_eq(n, nbr_pos_roots) {
        q_d_pos
      } else if num_eq(n, num_add(nbr_pos_roots, nbr_zero_roots)) {
        q_d_pz
      } else {
        q_d_pnz
      }
    }
  }
}

///|
fn d_sylvester_matrix(p : Value, q : Value, z : Value) -> Value raise {
  let mut p_coeff : Value = Nil
  let mut q_coeff : Value = Nil
  let mut mat : Value = Nil
  let freeof_z = list3(
    list1(q_lambda),
    list2(list1(q_mlist), q_c),
    list3(list1(q_d_freeof), z, q_c),
  )
  if !d_polynomialp(p, list2(list1(q_mlist), z), coeffp=freeof_z).truthy() ||
    !d_polynomialp(
      q,
      list2(list1(q_mlist), z),
      coeffp=list3(
        list1(q_lambda),
        list2(list1(q_mlist), q_c),
        list3(list1(q_d_freeof), z, q_c),
      ),
    ).truthy() {
    merr(
      "The first two arguments to 'sylvester_matrix' must be polynomials",
      [],
    )
    |> ignore
  }
  let p = d_ratexpand(p)
  let q = d_ratexpand(q)
  let p_deg = to_int(d_hipow(p, z))
  let q_deg = to_int(d_hipow(q, z))
  for _ in 0..<(q_deg - 1) {
    p_coeff = cons(Fix(0L), p_coeff)
  }
  for k in 0..<(p_deg + 1) {
    p_coeff = cons(d_ratcoef(p, z, n=int(k)), p_coeff)
  }
  for _ in 0..<(p_deg - 1) {
    q_coeff = cons(Fix(0L), q_coeff)
  }
  for k in 0..<(1 + q_deg) {
    q_coeff = cons(d_ratcoef(q, z, n=int(k)), q_coeff)
  }
  for _ in 0..<q_deg {
    mat = cons(cons(list1(q_mlist), p_coeff), mat)
    p_coeff = butlast(p_coeff)
    p_coeff = cons(Fix(0L), p_coeff)
  }
  for _ in 0..<p_deg {
    mat = cons(cons(list1(q_mlist), q_coeff), mat)
    q_coeff = butlast(q_coeff)
    q_coeff = cons(Fix(0L), q_coeff)
  }
  simplify(cons(list1(q_d_matrix), reverse(mat)))
}

///|
fn d_krylov_matrix(v : Value, mat : Value, n? : Value = q_no_value) -> Value raise {
  d_require_square_matrix(mat, q_d_second, q_d_krylov_matrix) |> ignore
  let mut v = v
  if d_listp(v).truthy() {
    v = d_transpose(v)
  }
  if !(
      d_matrixp(v).truthy() &&
      num_eq(d_first(d_matrix_size(v)), share_lu__second(d_matrix_size(mat)))
    ) {
    merr("Incompatible matrix sizes", []) |> ignore
  }
  let mut n = n
  if eq(n, q_no_value) {
    n = d_first(d_matrix_size(mat))
  }
  d_require_posinteger(n, q_d_third, q_d_krylov_matrix) |> ignore
  let mut acc = v
  let n = to_int(n) - 1
  for _ in 0..<n {
    v = ncmul_([mat, v])
    acc = d_addcol(acc, list1(v))
  }
  acc
}

///|
fn init_share_linalg_extra() -> Unit raise {
  d_put(q_d_linalgextra, Fix(1L), q_d_version) |> ignore
}

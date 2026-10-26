// Port of src/spgcd.lisp: sparse polynomial routines for GCD (Zippel's
// sparse modular algorithm).

///|
fn len(lobj : Value) -> Value raise {
  cadr(lobj)
}

///|
fn skel(lobj : Value) -> Value raise {
  caddr(lobj)
}

///|
fn matrix(lobj : Value) -> Value raise {
  cadddr(lobj)
}

///|
fn currow(lobj : Value) -> Value raise {
  cadr(cdddr(lobj))
}

///|
fn badrows(lobj : Value) -> Value raise {
  cadr(cddddr(lobj))
}

///|
fn spgcd__aref(mat : Value, i : Value, j : Value) -> Value raise {
  aref(mat, [to_int(i), to_int(j)])
}

///|
fn spgcd__aset(mat : Value, i : Value, j : Value, v : Value) -> Value raise {
  aset(mat, [to_int(i), to_int(j)], v)
}

///|
fn pinterp(x : Value, pts : Value, vals : Value) -> Value raise {
  let mut u = car(vals)
  let mut uk = cdr(vals)
  let mut qk = list([x, Fix(1L), Fix(1L), Fix(0L), cminus(car(pts))])
  let mut xk = cdr(pts)
  while !(xk is Nil) {
    let nu = pplus(
      u,
      ptimes(
        pctimes(crecip(pcsubstz(car(xk), qk)), qk),
        pdifference(car(uk), pcsubstz(car(xk), u)),
      ),
    )
    let nuk = cdr(uk)
    let nqk = ptimes(qk, list([x, Fix(1L), Fix(1L), Fix(0L), cminus(car(xk))]))
    let nxk = cdr(xk)
    u = nu
    uk = nuk
    qk = nqk
    xk = nxk
  }
  u
}

///|
fn pcsubstz(val : Value, p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    p
  } else {
    let mut l = p__terms(p)
    let mut ans : Value = Fix(0L)
    while !(pt_red(l) is Nil) {
      ans = ctimes(
        cplus(ans, pt_lc(l)),
        cexpt(val, num_sub(pt_le(l), pt_le(pt_red(l)))),
      )
      l = pt_red(l)
    }
    ctimes(
      cplus(ans, pt_lc(l)),
      if zerop(pt_le(l)) {
        Fix(1L)
      } else {
        cexpt(val, pt_le(l))
      },
    )
  }
}

// Skeletons consist of list of exponent vectors.  Lifting structures are
// as follows:
//
// (matrix <n>        ;length of <skel>
//         <skel>     ;skeleton of poly being lifted
//         <matrix>   ;partially diagonalized matrix used to obtain sol.
//         <row>      ;we have diagonalized this far
//         <bad rows>)

///|
fn eval_mon(mon : Value, pt : Value) -> Value raise {
  let mut l = mon
  let mut ll = pt
  let mut ans : Value = Fix(1L)
  while !(l is Nil) {
    ans = ctimes(
      if zerop(car(l)) {
        Fix(1L)
      } else {
        cexpt(car(ll), car(l))
      },
      ans,
    )
    l = cdr(l)
    ll = cdr(ll)
  }
  ans
}

///|
/// ONE-STEP causes the (row,col) element of mat to be made to be zero.  It
/// is assumed that row > col, and that the matrix is diagonal above the row.
/// n indicates how wide the rows are supposed to be.
fn one_step(mat : Value, row : Value, col : Value, n : Value) -> Value raise {
  let c = spgcd__aref(mat, row, col) // save this away before it is zeroed
  let mut i = col
  while !num_gt(i, n) {
    spgcd__aset(
      mat,
      row,
      i,
      cdifference(spgcd__aref(mat, row, i), ctimes(c, spgcd__aref(mat, col, i))),
    )
    |> ignore
    i = one_plus(i)
  }
  mat
}

///|
/// MONICIZE-ROW assumes the (row,row) element is non-zero and makes it equal
/// to one by dividing the entire row by it.
fn monicize_row(mat : Value, row : Value, n : Value) -> Value raise {
  let c = crecip(spgcd__aref(mat, row, row))
  let mut i = n
  while !num_eq(i, row) {
    spgcd__aset(mat, row, i, ctimes(spgcd__aref(mat, row, i), c)) |> ignore
    i = one_minus(i)
  }
  spgcd__aset(mat, row, row, Fix(1L))
}

///|
/// FILL-ROW is given a point and the value of the skeleton at the point and
/// fills the appropriate row in the matrix with the values of the
/// monomials.  n is the length of the skeleton.
fn fill_row(
  skel : Value,
  mat : Value,
  n : Value,
  row : Value,
  pt : Value,
  val : Value,
) -> Value raise {
  let mut i : Value = Fix(0L)
  let mut l = skel
  while !num_eq(i, n) {
    spgcd__aset(mat, row, i, eval_mon(car(l), pt)) |> ignore
    i = one_plus(i)
    l = cdr(l)
  }
  if !(l is Nil) {
    merr("FILL-ROW: skeleton too long: ~S", [list([n, q_eq, skel])]) |> ignore
  }
  spgcd__aset(mat, row, n, val) // the value is stored in the last column
}

///|
/// Interchange row m and n.
fn swap_rows(mat : Value, m : Value, n : Value) -> Value raise {
  let l = array_dimension(mat, 0)
  for k in 0..=l {
    let a = aref(mat, [to_int(n), k])
    aset(mat, [to_int(n), k], aref(mat, [to_int(m), k])) |> ignore
    aset(mat, [to_int(m), k], a) |> ignore
  }
  mat
}

///|
/// PARTIAL-DIAG fills in one more row of the matrix and tries to
/// diagonalize what it has so far.  If the row which has just been
/// introduced has a zero element on the diagonal then it is scanned for its
/// first non-zero element and it is placed in the matrix so that the
/// non-zero element is on the diagonal.  The rows which are missing are
/// added to the list in badrows.
fn partial_diag(lobj : Value, pt : Value, val : Value) -> Value raise {
  let n = len(lobj)
  let skel = skel(lobj)
  let mat = matrix(lobj)
  let mut row = currow(lobj)
  let mut badrows = badrows(lobj)
  let mut crow : Value = Nil
  if num_eq(row, n) {
    // All rows already done, must start using the rows in badrows.
    crow = car(badrows)
    fill_row(skel, mat, n, crow, pt, val) |> ignore
  } else if fill_row(skel, mat, n, row, pt, val).truthy() {
    crow = row
  }
  // This loop kills all the elements in the row up to the diagonal.
  badrows = cons(Nil, badrows)
  let mut i : Value = Fix(0L)
  let mut l = badrows
  let mut flag = false
  while !num_eq(i, crow) {
    if !(cdr(l) is Nil) {
      if num_eq(cadr(l), i) {
        if !flag && !zerop(spgcd__aref(mat, crow, i)) {
          swap_rows(mat, crow, i) |> ignore
          rplacd(l, cddr(l)) |> ignore
          flag = true
          crow = i
        } else {
          l = cdr(l)
        }
      } else {
        one_step(mat, crow, i, n) |> ignore
      }
    } else {
      one_step(mat, crow, i, n) |> ignore
    }
    i = one_plus(i)
  }
  badrows = cdr(badrows)
  if zerop(spgcd__aref(mat, crow, crow)) {
    badrows = cons(crow, badrows)
  } else {
    monicize_row(mat, crow, n) |> ignore
    let mut j : Value = Fix(0L)
    while !num_eq(j, crow) {
      one_step(mat, j, crow, n) |> ignore
      j = one_plus(j)
    }
  }
  let last_row = num_eq(one_plus(row), n)
  if last_row {
    row = one_minus(row) // Decrement it just in case
  }
  if last_row && cdr(badrows) is Nil {
    let mut l : Value = Nil
    let mut i = one_minus(n)
    while !minusp(i) {
      l = cons(spgcd__aref(mat, i, n), l)
      i = one_minus(i)
    }
    list([q_solution, n, skel, mat, l])
  } else {
    list([q_matrix, n, skel, mat, one_plus(row), badrows])
  }
}

///|
fn gen_point(vars : Value) -> Value raise {
  let mut l = vars
  let mut ans : Value = Nil
  while !(l is Nil) {
    ans = cons(cmod(mt_random(symval(q_d_pointbound))), ans)
    l = cdr(l)
  }
  ans
}

///|
/// PDIAG-ALL introduces a new row in each matrix in the list of l-lobjs.
/// The RHS of the equations is stripped off of poly.
fn pdiag_all(l_lobjs : Value, poly : Value, pt : Value) -> Value raise {
  let mut l = l_lobjs
  let mut lp = p__terms(poly)
  let mut solved = true
  while !(l is Nil) {
    let mut c : Value = Fix(0L)
    if !(lp is Nil) && num_eq(caar(l), pt_le(lp)) {
      c = pt_lc(lp)
      lp = pt_red(lp)
    }
    if !eq(cadar(l), q_solution) {
      rplacd(car(l), partial_diag(cdar(l), pt, c)) |> ignore
      if solved && !eq(cadar(l), q_solution) {
        solved = false
      }
    }
    l = cdr(l)
  }
  if solved {
    cons(q_solved, l_lobjs)
  } else {
    l_lobjs
  }
}

///|
fn merge_skel(mon : Value, poly : Value) -> Value raise {
  if pcoefp(poly).truthy() {
    list1(cons(Fix(0L), mon))
  } else {
    let mut l = cdr(poly)
    let mut ans : Value = Nil
    while !(l is Nil) {
      ans = cons(cons(car(l), mon), ans)
      l = cddr(l)
    }
    ans
  }
}

///|
fn new_skel(skel : Value, polys : Value) -> Value raise {
  let s = Collector::new()
  let mut a = skel
  let mut b = polys
  while a is Cons(_) && b is Cons(_) {
    s.append_list(merge_skel(car(a), car(b)))
    a = cdr(a)
    b = cdr(b)
  }
  let v = Collector::new()
  for q in polys.iter() {
    if pcoefp(q).truthy() {
      v.add(q)
    } else {
      let mut l = cdr(q)
      let mut ans : Value = Nil
      while !(l is Nil) {
        ans = cons(cadr(l), ans)
        l = cddr(l)
      }
      v.append_list(ans)
    }
  }
  list2(s.result(), v.result())
}

///|
fn create_lobjs(prev_lift : Value) -> Value raise {
  mapcar(
    q => {
      let n = length(cadr(q))
      cons(
        car(q),
        list([
          q_matrix,
          int(n),
          cadr(q),
          make_array([n, n + 1], initial=Fix(0L), elt="fixnum"),
          Fix(0L),
          Nil,
        ]),
      )
    },
    prev_lift,
  )
}

///|
fn clear_lobjs(lobjs : Value) -> Value raise {
  mapcar(
    q => cons(
      car(q),
      list([q_matrix, caddr(q), cadddr(q), caddr(cddr(q)), Fix(0L), Nil]),
    ),
    lobjs,
  )
}

///|
fn sparse_lift(
  c : Value,
  f : Value,
  g : Value,
  l_lobjs : Value,
  vars : Value,
) -> Value raise {
  let mut l_lobjs = l_lobjs
  let mut pt = gen_point(vars)
  while !eq(car(l_lobjs), q_solved) {
    let gcd = lifting_factors_image(
      pcsub(c, pt, vars),
      pcsub(f, pt, vars),
      pcsub(g, pt, vars),
    )
    if pcoefp(gcd).truthy() || !num_eq(pt_le(p__terms(gcd)), caar(l_lobjs)) {
      throw_tag(q_bad_point, Nil) |> ignore
    } else {
      l_lobjs = pdiag_all(l_lobjs, gcd, pt)
    }
    pt = gen_point(vars)
  }
  cdr(l_lobjs)
}

///|
fn lifting_factors_image(c : Value, f : Value, g : Value) -> Value raise {
  let gcd = pgcdu(f, g)
  let w = symval(q_ear_which_factor)
  if spgcd__eqn(w, 1) {
    pctimes(c, gcd)
  } else if spgcd__eqn(w, 2) {
    pquotient(f, gcd)
  } else if spgcd__eqn(w, 3) {
    pquotient(g, gcd)
  } else {
    Nil
  }
}

///|
/// `(eql w n)` for a small integer n.
fn spgcd__eqn(w : Value, n : Int) -> Bool {
  eql(w, Fix(n.to_int64()))
}

///|
fn zgcd_lift_star(
  c : Value,
  f : Value,
  g : Value,
  vars : Value,
  degb : Value,
) -> Value raise {
  let mut vals = gen_point(vars)
  let mut ans : Value = Nil
  while ans is Nil {
    ans = catch_tag(q_bad_point, () => zgcd_lift(c, f, g, vars, vals, degb))
    vals = gen_point(vars)
  }
  ans
}

// ZGCD-LIFT returns objects called lifts.  These have the following
// structure
//      ((n <skel> <poly>) ...  )
// n corresponds to the degree in the main variable to which this guy
// corresponds.

///|
fn zgcd_lift(
  c : Value,
  f : Value,
  g : Value,
  vars : Value,
  vals : Value,
  degb : Value,
) -> Value raise {
  if vars is Nil {
    // No variables left, just the main one.  Compute factor and enforce
    // leading coefficient.
    let p = lifting_factors_image(c, f, g)
    if pcoefp(p).truthy() {
      throw_tag(q_relprime, Fix(1L)) // if the GCD is 1 quit
    } else {
      let mut l = p__terms(p)
      let mut ans : Value = Nil
      while !(l is Nil) {
        ans = cons(list3(pt_le(l), list1(Nil), list1(pt_lc(l))), ans)
        l = pt_red(l)
      }
      nreverse(ans)
    }
  } else {
    let prev_lift = zgcd_lift(
      pcsubsty(car(vals), car(vars), c),
      pcsubsty(car(vals), car(vars), f),
      pcsubsty(car(vals), car(vars), g),
      cdr(vars),
      cdr(vals),
      cdr(degb),
    )
    let mut i : Value = Fix(0L)
    let mut lobjs = create_lobjs(prev_lift)
    let mut pts = add_point(list1(car(vals)))
    let mut linsols = mapcar(x => make_linsols(x), prev_lift)
    while !num_eq(i, car(degb)) {
      let ni = one_plus(i)
      let nlobjs = clear_lobjs(lobjs)
      let npts = add_point(pts)
      let nlinsols = merge_sol_lin(
        linsols,
        sparse_lift(
          pcsubsty(car(pts), car(vars), c),
          pcsubsty(car(pts), car(vars), f),
          pcsubsty(car(pts), car(vars), g),
          lobjs,
          cdr(vars),
        ),
      )
      i = ni
      lobjs = nlobjs
      pts = npts
      linsols = nlinsols
    }
    interp_polys(linsols, cdr(pts), car(vars))
  }
}

///|
fn make_linsols(prev_lift : Value) -> Value raise {
  list3(
    car(prev_lift),
    cadr(prev_lift),
    mapcan(
      q => if pcoefp(q).truthy() {
        list1(list1(q))
      } else {
        let mut l = p__terms(q)
        let mut ans : Value = Nil
        while !(l is Nil) {
          ans = cons(list1(pt_lc(l)), ans)
          l = pt_red(l)
        }
        ans
      },
      caddr(prev_lift),
    ),
  )
}

///|
fn add_point(l : Value) -> Value raise {
  let mut try_ = cmod(mt_random(symval(q_d_pointbound)))
  while member_equal(try_, l).truthy() {
    try_ = cmod(mt_random(symval(q_d_pointbound)))
  }
  cons(try_, l)
}

///|
fn merge_sol_lin(l1 : Value, l2 : Value) -> Value raise {
  let mut l = l1
  let mut l2 = l2
  while !(l is Nil) {
    if num_eq(caar(l), caar(l2)) {
      rplaca(cddar(l), mapcar2((a, b) => cons(a, b), cadddr(cddar(l2)), caddar(l)))
      |> ignore
    }
    l = cdr(l)
    l2 = cdr(l2)
  }
  l1
}

///|
fn interp_polys(l : Value, pts : Value, var_ : Value) -> Value raise {
  mapcar(
    q => cons(car(q), new_skel(cadr(q), mapcar(r => pinterp(var_, pts, r), caddr(q)))),
    l,
  )
}

///|
fn zgcd(f : Value, g : Value) -> Value raise {
  let bs = bind_all([(q_d_algebraic, Nil), (q_algfac_star, Nil)])
  defer unbind_all(bs)
  let f = oldcontent(f) // This is a good spot to initialize random
  let g = oldcontent(g)
  let bw = bind(q_ear_which_factor, Nil)
  defer unbind(bw)
  // *WHICH-FACTOR* is interpreted as follows.  It is set fairly deep in the
  // algorithm, inside ZGCD1.
  // 1 -> Lift the GCD
  // 2 -> Lift the cofactor of F
  // 3 -> Lift the cofactor of G
  let mon = pgcd(car(f), car(g)) // compute GCD of content
  let f = cadr(f) // f and g are now primitive
  let g = cadr(g)
  if pcoefp(f).truthy() || pcoefp(g).truthy() || !eq(car(f), car(g)) {
    merr("ZGCD: incorrect arguments.", []) |> ignore
  }
  let r = while true {
    let gcd = catch_tag(q_relprime, () => zgcd1(f, g))
    let w = symval(q_ear_which_factor)
    let test_ = if spgcd__eqn(w, 1) {
      testdivide(f, gcd)
    } else if spgcd__eqn(w, 2) {
      testdivide(f, gcd)
    } else if spgcd__eqn(w, 3) {
      testdivide(g, gcd)
    } else {
      Nil
    }
    if test_.truthy() {
      break if equal(w, Fix(1L)) { gcd } else { test_ }
    } else if symval(q_modulus).truthy() {
      break with_special(q_d_gcd, q_d_red, () => pgcd(f, g))
    }
  } nobreak {
    Nil
  }
  ptimes(mon, r)
}

///|
fn zgcd1(f : Value, g : Value) -> Value raise {
  let bm = bind(q_modulus, symval(q_modulus))
  defer unbind(bm)
  let mut c : Value = Nil
  let vars = sort_list(union1(listovars(f), listovars(g)), (a, b) => pointergp(
      a, b,
    ).truthy())
  let bg = bind(q_genvar, reverse(vars))
  defer unbind(bg)
  // The elements of the following degree vectors all correspond to the
  // contents of var.  Thus there may be variables missing that are in
  // GENVAR.
  let f_degv = pdegreevector(f)
  let g_degv = pdegreevector(g)
  let gcd_degv = gcd_degree_vector(f, g, vars)
  // First we try to decide which of the gcd and the cofactors of f and g is
  // smallest.  The result of this decision is indicated by *which-factor*.
  // Then the leading coefficient that is to be enforced is changed if a
  // cofactor has been chosen.
  let w = set(
    q_ear_which_factor,
    determine_lifting_factor(f_degv, g_degv, gcd_degv),
  )
  if spgcd__eqn(w, 1) {
    c = pgcd(p__lc(f), p__lc(g))
  } else if spgcd__eqn(w, 2) {
    c = p__lc(f)
  } else if spgcd__eqn(w, 3) {
    c = p__lc(g)
  }
  // Next a degree bound must be chosen.
  let base = if spgcd__eqn(w, 1) {
    gcd_degv
  } else if spgcd__eqn(w, 2) {
    mapcar2((a, b) => num_sub(a, b), f_degv, gcd_degv)
  } else if spgcd__eqn(w, 3) {
    mapcar2((a, b) => num_sub(a, b), g_degv, gcd_degv)
  } else {
    Nil
  }
  let degb = reverse(
    mapcar2((a, b) => num_add(a, b), base, zpdegreevector(c, vars)),
  )
  if symval(q_modulus).truthy() {
    lobj__gtpoly(
      car(vars),
      cdr(vars),
      zgcd_lift_star(c, f, g, cdr(vars), cdr(degb)),
    )
  } else {
    let h = num_mul(maxcoefficient(f), maxcoefficient(g))
    set(q_modulus, symval(q_n_staralpha)) |> ignore // Really should randomize
    let first_lift = zgcd_lift_star(pmod(c), pmod(f), pmod(g), cdr(vars), cdr(
      degb,
    ))
    let mut linsols = mapcar(
      q => cons(car(q), new_skel(cadr(q), caddr(q))),
      first_lift,
    )
    let mut lobjs = create_lobjs(first_lift)
    let mut coef_bound = symval(q_n_staralpha)
    let mut cm : Value = Nil
    let mut fm : Value = Nil
    let mut gm : Value = Nil
    while !num_gt(coef_bound, h) {
      set(q_modulus, newprime(symval(q_modulus))) |> ignore
      cm = pmod(c)
      fm = pmod(f)
      gm = pmod(g)
      let modulus = symval(q_modulus)
      let nlinsols = merge_sol_lin_z(
        linsols,
        sparse_lift(cm, fm, gm, lobjs, cdr(vars)),
        num_mul(coef_bound, crecip(cmod(coef_bound))),
        num_mul(modulus, coef_bound),
      )
      let nlobjs = clear_lobjs(lobjs)
      let ncb = num_mul(symval(q_modulus), coef_bound)
      linsols = nlinsols
      lobjs = nlobjs
      coef_bound = ncb
    }
    set(q_modulus, Nil) |> ignore
    lobj__gtpoly(car(vars), cdr(vars), linsols)
  }
}

///|
fn lobj__gtpoly(var_ : Value, vars : Value, lobj : Value) -> Value raise {
  primpart(
    cons(
      var_,
      mapcan(
        q => {
          let mut x = cadr(q)
          let mut y = caddr(q)
          let mut ans : Value = Fix(0L)
          while !(x is Nil) {
            ans = pplus(ans, disrep_monom(cdar(x), car(y), vars))
            x = cdr(x)
            y = cdr(y)
          }
          list2(car(q), ans)
        },
        lobj,
      ),
    ),
  )
}

///|
fn disrep_monom(monom : Value, c : Value, vars : Value) -> Value raise {
  if monom is Nil {
    c
  } else if equal(Fix(0L), car(monom)) {
    disrep_monom(cdr(monom), c, cdr(vars))
  } else {
    list3(car(vars), car(monom), disrep_monom(cdr(monom), c, cdr(vars)))
  }
}

///|
fn merge_sol_lin_z(
  l1 : Value,
  l2 : Value,
  c : Value,
  new_coef_bound : Value,
) -> Value raise {
  let bm = bind(q_modulus, new_coef_bound)
  defer unbind(bm)
  let mut l = l1
  let mut l2 = l2
  while !(l is Nil) {
    if num_eq(caar(l), caar(l2)) {
      rplaca(
        cddar(l),
        mapcar2(
          (a, b) => {
            let n = cplus(b, ctimes(c, cdifference(a, b)))
            if num_gt(num_abs(n), new_coef_bound) {
              throw_tag(q_relprime, Fix(1L))
            } else {
              n
            }
          },
          cadddr(cddar(l2)),
          caddar(l),
        ),
      )
      |> ignore
    }
    l = cdr(l)
    l2 = cdr(l2)
  }
  l1
}

///|
/// Tries to determine the degree of gcd(f, g) in each variable: all but one
/// of the variables in f and g are replaced by randomly chosen integers, and
/// the degree of the gcd of the resulting univariate polynomials is used.
/// The univariate gcd's are computed with modulus=*alpha.
fn gcd_degree_vector(f : Value, g : Value, vars : Value) -> Value raise {
  let bm = bind(q_modulus, symval(q_n_staralpha))
  defer unbind(bm)
  let f = pmod(f)
  let g = pmod(g)
  let mut vn = cdr(vars)
  let mut vs = remove_equal(car(vars), copy_list(vars))
  let mut l : Value = Nil
  while true {
    let rand = gen_point(vs)
    let f_star = pcsub(f, rand, vs)
    let g_star = pcsub(g, rand, vs)
    if pcoefp(f_star).truthy() || pcoefp(g_star).truthy() {
      l = cons(Fix(0L), l)
    } else {
      let gcd_star = pgcdu(f_star, g_star)
      if pcoefp(gcd_star).truthy() {
        l = cons(Fix(0L), l)
      } else {
        l = cons(pt_le(p__terms(gcd_star)), l)
      }
    }
    if vn is Nil {
      return l // No reverse needed here
    }
    let nvs = remove_equal(car(vn), copy_list(vars))
    vn = cdr(vn)
    vs = nvs
  }
  l
}

///|
fn dlf_mumblify(a : Value, b : Value) -> Value raise {
  let mut s : Value = Fix(0L)
  let mut x = a
  let mut y = b
  while x is Cons(_) && y is Cons(_) {
    s = num_add(s, num_sub(car(x), car(y)))
    x = cdr(x)
    y = cdr(y)
  }
  s
}

///|
fn determine_lifting_factor(
  f_degv : Value,
  g_degv : Value,
  gcd_degv : Value,
) -> Value raise {
  let fv = dlf_mumblify(f_degv, gcd_degv)
  let gv = dlf_mumblify(g_degv, gcd_degv)
  let mut gcdv : Value = Fix(0L)
  for x in gcd_degv.iter() {
    gcdv = num_add(gcdv, x)
  }
  if num_lt(fv, gcdv) {
    if num_lt(fv, gv) {
      Fix(2L)
    } else {
      Fix(3L)
    }
  } else if num_lt(gv, gcdv) {
    Fix(3L)
  } else {
    Fix(1L)
  }
}

///|
fn excise_extra_variables(degv : Value, vars : Value) -> Value raise {
  let mut vars = vars
  let mut l = reverse(degv)
  let mut lv = reverse(symval(q_genvar))
  let mut ndegv : Value = Nil
  while !(l is Nil) {
    if eq(car(lv), car(vars)) {
      ndegv = cons(car(l), ndegv)
      vars = cdr(vars)
    }
    l = cdr(l)
    lv = cdr(lv)
  }
  ndegv
}

///|
fn zpdegreevector(p : Value, vars : Value) -> Value raise {
  excise_extra_variables(pdegreevector(p), vars)
}

///|
fn init_spgcd() -> Unit raise {
  // *alpha (and $pointbound again) is initialized at startup by init-cl.
  if boundp(q_n_staralpha) {
    defvar_init(q_d_pointbound, symval(q_n_staralpha))
    ifactor__defmvar_reset(q_d_pointbound)
  }
}

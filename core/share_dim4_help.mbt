// Port of share/affine/dim4-help.lisp: complexity measures, pivoting and
// minors of matrices of polynomials, used for the dimension-4 algebra
// computations.
//
// dim4-help.lisp redefines `$psublis` (with argument order
// `(a-list poly &optional denom palist)`; the contract's `d_psublis` is the
// sub-proj.lisp version).  The dim4-help version is `dim4_help__psublis`;
// `init_share_dim4_help` installs it in the function cell of `$psublis`,
// as loading the Lisp file does.

///|
let dim4_help__q_degs : Value = sym("degs")

///|
/// `(n* a b)`
fn dim4_help__ntimes(a : Value, b : Value) -> Value raise {
  n_star(list2(a, b))
}

///|
/// `(assert form)`
fn dim4_help__assert(ok : Bool, form : String) -> Unit raise {
  if !ok {
    raise LispError::SimpleError("The assertion " + form + " failed.")
  }
}

///|
fn d_complexity(v : Value, sum? : Value = Nil) -> Value raise {
  if eql(v, int(0)) {
    if sum.truthy() {
      int(-1)
    } else {
      q_d_z
    }
  } else if mbagp(v).truthy() {
    if sum.truthy() {
      let mut acc = int(0)
      for u in cdr(v).iter() {
        acc = num_add(acc, d_complexity(u, sum~))
      }
      acc
    } else {
      cons(car(v), mapcar(x => d_complexity(x), cdr(v)))
    }
  } else {
    gen_pcomplexity(st_rat(v))
  }
}

///|
fn complexity_difference1(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  if eq(x, q_d_z) {
    x = int(-1)
  }
  if eq(y, q_d_z) {
    y = int(-1)
  }
  if numberp(x) {
    num_sub(x, y)
  } else if mbagp(x).truthy() {
    let mut acc = int(0)
    let mut vl = cdr(x)
    let mut wl = cdr(y)
    while consp(vl) && consp(wl) {
      acc = num_add(acc, complexity_difference1(car(vl), car(wl)))
      vl = cdr(vl)
      wl = cdr(wl)
    }
    acc
  } else {
    Nil
  }
}

///|
fn d_complexity_difference(a_list : Value, v : Value) -> Value raise {
  if eql(v, int(0)) {
    int(-1)
  } else {
    let x = d_complexity(dim4_help__psublis(a_list, v))
    let y = d_complexity(v)
    complexity_difference1(y, x)
  }
}

///|
fn d_pdegree(v : Value, va : Value) -> Value raise {
  if eql(v, int(0)) {
    q_d_z
  } else if mbagp(v).truthy() {
    cons(car(v), mapcar(w => d_pdegree(w, va), cdr(v)))
  } else {
    pdegree(st_rat(v), car(st_rat(va)))
  }
}

///|
fn d_delete_matrix_row(mat : Value, i : Value) -> Value raise {
  let c = Collector::new()
  let mut j = 1
  for v in cdr(mat).iter() {
    if !eql(int(j), i) {
      c.add(v)
    }
    j += 1
  }
  cons(car(mat), c.result())
}

///|
fn d_complexity_less_p(x : Value, y : Value) -> Value raise {
  lbool(num_lt(d_complexity(x, sum=t), d_complexity(y, sum=t)))
}

///|
fn d_my_rat(x : Value) -> Value raise {
  if mbagp(x).truthy() {
    cons(car(x), mapcar(u => d_my_rat(u), cdr(x)))
  } else {
    header_poly(st_rat(x))
  }
}

///|
fn d_mat_entry(mat : Value, i : Value, j : Value) -> Value raise {
  nth(to_int(j), nth(to_int(i), mat))
}

///|
fn d_eliminate_pivot(mat : Value, i : Value, j : Value) -> Value raise {
  let mat = d_my_rat(mat)
  let pivot = d_mat_entry(mat, i, j)
  let pivot_row = nth(to_int(i), mat)
  format(t, "~%Using pivot:", []) |> ignore
  sh(pivot) |> ignore
  set(
    q_d_pivot_list,
    d_append(
      list2(
        symval(q_d_pivot_list),
        list([list1(q_mlist), header_poly(pivot), i, j]),
      ),
    ),
  )
  |> ignore
  let rows = Collector::new()
  let mut ii = 1
  for v in cdr(mat).iter() {
    if !eql(i, int(ii)) {
      let this = st_rat(nth(to_int(j), v))
      if eql(int(0), this) {
        rows.add(v)
      } else {
        let quot = nred(this, pivot)
        let row = Collector::new()
        let mut ul = cdr(v)
        let mut al = cdr(pivot_row)
        while consp(ul) && consp(al) {
          let u = car(ul)
          let a = car(al)
          row.add(
            header_poly(
              n__(
                dim4_help__ntimes(function_numerator(quot), a),
                dim4_help__ntimes(function_denominator(quot), u),
              ),
            ),
          )
          ul = cdr(ul)
          al = cdr(al)
        }
        rows.add(cons(car(v), row.result()))
      }
    }
    ii += 1
  }
  cons(car(mat), rows.result())
}

///|
/// dim4-help's `$psublis`: use psublis([y=x^2,v=u^3],denom,poly).
fn dim4_help__psublis(
  a_list : Value,
  poly : Value,
  denom? : Value = Fix(1L),
  palist? : Value = Nil,
) -> Value raise {
  let mut palist = palist
  if !palist.truthy() {
    let c = Collector::new()
    for eqn in cdr(a_list).iter() {
      // (loop for (u v repl) in (cdr a-list) ...)
      let u = car(eqn)
      let v = cadr(eqn)
      let repl = caddr(eqn)
      check_arg(u, lbool(eq(car(u), q_mequal)), list1(Str("Type a=repl")))
      |> ignore
      c.add(cons(p__var(st_rat(v)), st_rat(repl)))
    }
    palist = c.result()
  }
  if mbagp(poly).truthy() {
    cons(
      car(poly),
      mapcar(v => dim4_help__psublis(a_list, v, denom~, palist~), cdr(poly)),
    )
  } else {
    header_poly(psublis(palist, st_rat(denom), st_rat(poly)))
  }
}

///|
fn d_eliminate_pivot_list_hack(matrix : Value, pivot_list : Value) -> Value raise {
  let mut matrix = matrix
  let mut l = cdr(pivot_list)
  while consp(l) {
    let i = cadr(l)
    let j = caddr(l)
    format(t, "~%Pivot in list was :", []) |> ignore
    displa(d_matrix_entry(matrix, i, j)) |> ignore
    matrix = d_eliminate_pivot(matrix, i, j)
    l = cdddr(l)
  }
  matrix
}

///|
fn d_get_relation_matrix(relations : Value, mons : Value) -> Value raise {
  let mons = st_rat(mons)
  let rows = Collector::new()
  for v in cdr(relations).iter() {
    let v = st_rat(v)
    rows.add(cons(list1(q_mlist), mapcar(w => header_poly(pcoeff(v, w)), mons)))
  }
  cons(list1(q_d_matrix), rows.result())
}

///|
fn dim4_help__set_nth(i : Int, l : Value, v : Value) -> Unit raise {
  let cell = nthcdr(i, l)
  if cell is Nil {
    raise LispError::SimpleError(
      format_to_string("~A is too large an index for SETF of NTH.", [int(i)]),
    )
  }
  setf_car(cell, v) |> ignore
}

///|
fn d_switch_rows(mat : Value, i : Value, j : Value) -> Value raise {
  let nmat = copy_list(mat)
  dim4_help__set_nth(to_int(i), nmat, nth(to_int(j), mat))
  dim4_help__set_nth(to_int(j), nmat, nth(to_int(i), mat))
  nmat
}

///|
fn number_zeros(a : Value) -> Value raise {
  let mut n = 0
  for v in a.iter() {
    if eq(v, q_d_z) {
      n += 1
    }
  }
  int(n)
}

///|
fn d_row_less(a : Value, b : Value) -> Value raise {
  lbool(num_gt(number_zeros(a), number_zeros(b)))
}

///|
fn d_row_sort(mat : Value, pred : Value) -> Value raise {
  cons(
    list1(q_d_matrix),
    sort_list(copy_list(cdr(mat)), (a, b) => funcall(pred, [a, b]).truthy()),
  )
}

///|
fn d_reorder_matrix(mat : Value) -> Value raise {
  let rows = Collector::new()
  for u in cdr(mat).iter() {
    let mut s = int(0)
    for v in cdr(u).iter() {
      s = num_add(s, gen_pcomplexity(st_rat(v)))
    }
    rows.add(cons(s, u))
  }
  let sorted = sort_list(rows.result(), (a, b) => num_lt(car(a), car(b)))
  cons(list1(q_d_matrix), mapcar(x => cdr(x), sorted))
}

///|
fn d_best_row(mat : Value) -> Value raise {
  let mut the_min : Value = Nil
  let mut at : Value = Nil
  let mut i = 1
  for u in cdr(mat).iter() {
    let mut tem = int(0)
    for v in cdr(u).iter() {
      tem = num_add(tem, gen_pcomplexity(st_rat(v)))
    }
    the_min = if the_min is Nil { tem } else { num_min(the_min, tem) }
    if eql(tem, the_min) {
      at = int(i)
    }
    i += 1
  }
  at
}

///|
fn d_best_piv(row : Value) -> Value raise {
  let mut the_min : Value = Nil
  let mut at : Value = Nil
  let mut i = 1
  for v in cdr(row).iter() {
    let v = st_rat(v)
    if !eql(v, int(0)) {
      let tem = gen_pcomplexity(st_rat(v))
      the_min = if the_min is Nil { tem } else { num_min(the_min, tem) }
      if eql(tem, the_min) {
        at = int(i)
      }
    }
    i += 1
  }
  at
}

///|
/// Sort by column.
fn d_invertible_pivots(mat : Value, g : Value) -> Value raise {
  let g = st_rat(g)
  let all = Collector::new()
  let mut i = 1
  for ro in cdr(d_transpose(mat)).iter() {
    let mut j = 1
    for u in cdr(ro).iter() {
      let u = st_rat(u)
      if may_invertp(u, g).truthy() {
        all.add(
          list([
            list1(q_mlist),
            header_poly(u),
            int(j),
            int(i),
            d_complexity(ro, sum=t),
            pcomplexity(u),
          ]),
        )
      }
      j += 1
    }
    i += 1
  }
  let pivs = sort_list(all.result(), (a, b) => num_lt(nth(4, a), nth(4, b)))
  cons(list1(q_mlist), pivs)
}

///|
fn d_reduce_by_complexity(mat? : Value = Nil) -> Value raise {
  set(q_d_current, if mat.truthy() { mat } else { symval(q_d_current) })
  |> ignore
  let i = d_best_row(mat)
  let j = d_best_piv(nth(to_int(i), mat))
  print(list2(i, j)) |> ignore
  set(q_d_current, d_eliminate_pivot(mat, i, j))
}

///|
fn d_sort_complexity(list_ : Value) -> Value raise {
  let all = Collector::new()
  for v in cdr(list_).iter() {
    all.add(cons(pcomplexity(st_rat(v)), v))
  }
  let sorted = sort_list(all.result(), (a, b) => num_lt(car(a), car(b)))
  cons(car(list_), mapcar(x => cdr(x), sorted))
}

///|
/// Cancel a gcd of AGCD and the rest of the elements of LIS.  If LIS is a
/// list of lists call this function on each of the lists independently.
fn d_p_projective(lis : Value, agcd? : Value = Nil) -> Value raise {
  let mut agcd = agcd
  let mut zero_row = true
  dim4_help__assert(mbagp(lis).truthy(), "(MBAGP LIS)")
  if agcd.truthy() {
    agcd = st_rat(agcd)
  }
  if mbagp(second(lis)).truthy() {
    cons(car(lis), mapcar(w => d_p_projective(w, agcd~), cdr(lis)))
  } else {
    for v in cdr(lis).iter() {
      let v = st_rat(v)
      dim4_help__assert(
        affine_polynomialp(v).truthy(),
        "(AFFINE-POLYNOMIALP V)",
      )
      if zero_row && !pzerop(v).truthy() {
        zero_row = false
      }
      agcd = if agcd.truthy() { pgcd(agcd, v) } else { v }
    }
    if numberp(agcd) {
      lis
    } else if zero_row {
      lis
    } else {
      set(
        q_d_gcds_used,
        d_append(
          list2(
            symval(q_d_gcds_used),
            list2(list1(q_mlist), header_poly(agcd)),
          ),
        ),
      )
      |> ignore
      format(t, "~%Found a non trivial factor:", []) |> ignore
      sh(agcd) |> ignore
      cons(
        list1(q_mlist),
        mapcar(vv => header_poly(pquotient(st_rat(vv), agcd)), cdr(lis)),
      )
    }
  }
}

///|
fn d_cancel_pivot(lis : Value, piv : Value) -> Value raise {
  let piv = st_rat(piv)
  dim4_help__assert(affine_polynomialp(piv).truthy(), "(AFFINE-POLYNOMIALP PIV)")
  if mbagp(lis).truthy() {
    cons(car(lis), mapcar(w => d_cancel_pivot(w, piv), cdr(lis)))
  } else {
    let lis = st_rat(lis)
    dim4_help__assert(
      affine_polynomialp(lis).truthy(),
      "(AFFINE-POLYNOMIALP LIS)",
    )
    let tem = pgcd(lis, piv)
    if numberp(tem) {
      header_poly(lis)
    } else {
      header_poly(pquotient(lis, tem))
    }
  }
}

///|
fn d_linearize_nc(x : Value) -> Value raise {
  if consp(x) {
    if consp(car(x)) && eq(caar(x), q_mnctimes) {
      setf_car(x, list1(q_mtimes)) |> ignore
      let mut v = cdr(x)
      let mut i = 1
      while consp(v) {
        let term = car(v)
        setf_car(v, sym(format_to_string("~a~d", [term, int(i)]))) |> ignore
        v = cdr(v)
        i += 1
      }
      Nil
    } else {
      cons(d_linearize_nc(car(x)), d_linearize_nc(cdr(x)))
    }
  } else {
    x
  }
}

///|
fn d_linearize_nc_to_nc(x : Value) -> Value raise {
  if consp(x) {
    if consp(car(x)) && eq(caar(x), q_mnctimes) {
      let mut v = cdr(x)
      let mut i = 1
      while consp(v) {
        let term = car(v)
        setf_car(v, sym(format_to_string("~a~d", [term, int(i)]))) |> ignore
        v = cdr(v)
        i += 1
      }
      x
    } else {
      cons(d_linearize_nc_to_nc(car(x)), d_linearize_nc_to_nc(cdr(x)))
    }
  } else {
    x
  }
}

///|
fn times_4_n(n : Value) -> Value raise {
  if zerop(n) {
    int(1)
  } else {
    num_mul(int(4), n)
  }
}

///|
fn hilbert_4(n : Value) -> Value raise {
  round1(ftake(q_p_binomial, [num_add(n, int(3)), int(3)]))
}

///|
fn d_minors2_2(mat : Value, cols : Value) -> Value raise {
  d_minors(int(2), mat, cols)
}

///|
fn d_minors(n : Value, mat : Value, cols : Value) -> Value raise {
  let nmat = d_submatrix(cons(mat, cdr(cols)))
  let c = Collector::new()
  for ro in sheafa__list_tableaux(n, int(length(nmat) - 1)).iter() {
    sheafa__show("RO", ro)
    c.add(cons(list1(q_d_matrix), mapcar(i => nth(to_int(i), nmat), ro)))
  }
  cons(list1(q_mlist), c.result())
}

///|
fn sublist(l : Value, pred : Value) -> Value raise {
  let c = Collector::new()
  for v in l.iter() {
    if apply(pred, v).truthy() {
      c.add(v)
    }
  }
  c.result()
}

///|
fn lis(l : Value) -> Value raise {
  cons(list1(q_mlist), mapcar(w => cons(list1(q_mlist), w), l))
}

///|
/// POLYS is a list of polynomials and a parallel list DEGS of degrees.
/// We compute all monomials in POLYS of deg l.
fn monoms(polys : Value, degs : Value, cross? : Value) -> Value raise {
  ignore(cross)
  if polys is Nil {
    list1(int(1))
  } else {
    let c = Collector::new()
    for v in monoms(cdr(polys), cdr(degs)).iter() {
      let top = to_int(car(degs))
      for j in 0..=top {
        c.add(dim4_help__ntimes(pexpt(car(polys), int(j)), v))
      }
    }
    c.result()
  }
}

///|
fn d_extract_c_equations(poly : Value, vars_to_exclude : Value) -> Value raise {
  let mons = st_rat(vars_to_exclude)
  let vars1 = mapcar(x => car(x), st_rat(vars_to_exclude))
  dim4_help__assert(d_listp(poly).truthy(), "($LISTP POLY)")
  let mut all_monoms : Value = Nil
  let ans = Collector::new()
  for v in cdr(poly).iter() {
    let v = function_numerator(st_rat(v))
    set(dim4_help__q_degs, mapcar(w => pdegree(v, w), vars1)) |> ignore
    let some_monoms = monoms(mons, symval(dim4_help__q_degs))
    all_monoms = append(all_monoms, some_monoms)
    for w in some_monoms.iter() {
      ans.add(new_disrep(pcoeff(v, w, variables_to_exclude_from_cof=vars1)))
    }
  }
  list([
    list1(q_mlist),
    cons(list1(q_mlist), ans.result()),
    cons(list1(q_mlist), mapcar(x => new_disrep(x), all_monoms)),
  ])
}

///|
fn init_share_dim4_help() -> Unit raise {
  // (push 'hilbert_4 *all-rank-functions*)
  set(q_ear_all_rank_functions, cons(q_hilbert_4, symval(q_ear_all_rank_functions)))
  |> ignore
  // dim4-help.lisp redefines $psublis.
  defun(q_d_psublis, args => dim4_help__psublis(
    arg(args, 0),
    arg(args, 1),
    denom?=args.get(2),
    palist?=args.get(3),
  ))
}

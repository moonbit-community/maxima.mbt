// Port of src/mat.lisp: the mat package -- coefficient matrices of linear
// systems and fraction-free Gaussian elimination (Tadatoshi Minamikawa's
// one-step elimination with optimal pivoting).

///|
/// If SYMBOL is an array, return it directly; otherwise return its value
/// cell. Used to follow indirect array references where one symbol is bound
/// to another that holds the actual array.
fn get_array_pointer(symbol : Value) -> Value raise {
  if arrayp(symbol) {
    symbol
  } else if symbol is Nil {
    // (symbol-value nil) is nil
    Nil
  } else {
    symbol_value(symbol)
  }
}

///|
fn solcoef(m : Value, n_starc : Value, varl : Value, flag : Value) -> Value raise {
  with_special(q_n_starc, n_starc, () => {
    let cc = cdr(ratrep_star(n_starc))
    if atom(car(cc)) ||
      !equal(cdar(cc), list2(Fix(1L), Fix(1L))) ||
      !equal(Fix(1L), cdr(cc)) {
      merr("solve: unacceptable variable: ~M", [n_starc]) |> ignore
    }
    let answer = ratreduce(prodcoef(car(cc), car(m)), cdr(m))
    if !flag.truthy() {
      return answer
    }
    let leftover = rdis(ratplus(m, rattimes(ratminus(answer), cc, t)))
    if !freeof(n_starc, leftover).truthy() ||
      dependsall(rdis(answer), varl).truthy() {
      rat_error(list1(Str("`non-linear'"))) |> ignore
    }
    answer
  })
}

///|
/// 2-D `aref` with Lisp integer indices.
fn mat__aref2(a : Value, i : Value, j : Value) -> Value raise {
  aref(a, [to_int(i), to_int(j)])
}

///|
fn mat__aset2(a : Value, i : Value, j : Value, v : Value) -> Unit raise {
  aset(a, [to_int(i), to_int(j)], v) |> ignore
}

///|
fn formx(flag : Value, nam : Value, eql_ : Value, varl : Value) -> Value raise {
  set(q_varlist, varl) |> ignore
  mapc(e => newvar(e) |> ignore, eql_) |> ignore
  if !symval(q_d_algebraic).truthy() &&
    some(v => algp(v).truthy(), symval(q_varlist)) {
    set(q_d_algebraic, t) |> ignore
  }
  set(q_xn_star, int(length(eql_))) |> ignore
  set(q_xm_star, int(1 + length(varl))) |> ignore
  set(
    nam,
    make_array(
      [1 + to_int(symval(q_xn_star)), 1 + to_int(symval(q_xm_star))],
      initial=Fix(0L),
    ),
  )
  |> ignore
  let nam = get_array_pointer(nam)
  let mut eql_ = eql_
  let mut ix = 0
  while eql_.truthy() {
    let ax = car(eql_)
    eql_ = cdr(eql_)
    ix = ix + 1
    mat__aset2(nam, int(ix), symval(q_xm_star), const_(ax, varl))
    let mut j = 0
    let mut b = varl
    let ax = cdr(ratrep_star(ax))
    while true {
      let x = car(b)
      b = cdr(b)
      j = j + 1
      mat__aset2(nam, int(ix), int(j), solcoef(ax, x, varl, flag))
      if b is Nil {
        break
      }
    }
  }
  symval(q_varlist)
}

///|
fn dependsall(exp_ : Value, l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if !freeof(car(l), exp_).truthy() || dependsall(exp_, cdr(l)).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn ptorat(ax : Value, m : Value, n : Value) -> Value raise {
  let ax = get_array_pointer(ax)
  let mut i = to_int(m) + 1
  let n = to_int(n) + 1
  while true {
    if i == 1 {
      return Nil
    }
    i = i - 1
    let mut j = n
    while j != 1 {
      j = j - 1
      aset(ax, [i, j], cons(aref(ax, [i, j]), Fix(1L))) |> ignore
    }
  }
  Nil
}

///|
/// If Z is of the form lhs = rhs, return the expression lhs - rhs.
/// Otherwise, return Z unchanged.
fn meqhk(z : Value) -> Value raise {
  if !atom(z) && eq(caar(z), q_mequal) {
    simplus(
      list3(list1(q_mplus), cadr(z), list3(list1(q_mtimes), Fix(-1L), caddr(z))),
      Fix(1L),
      Nil,
    )
  } else {
    z
  }
}

///|
fn const_(e : Value, varl : Value) -> Value raise {
  let varl = mapcar(x => caadr(ratrep_star(x)), varl)
  let e = cdr(ratrep_star(e))
  let zl = Collector::new()
  for _ in varl.iter() {
    zl.add(Fix(0L))
  }
  let zl = zl.result()
  ratreduce(
    pctimes(Fix(-1L), pcsubsty(zl, varl, car(e))),
    pcsubsty(zl, varl, cdr(e)),
  )
}

///|
fn make_param() -> Value raise {
  set(q_d__pctrnum, num_add(symval(q_d__pctrnum), Fix(1L))) |> ignore
  let param = sym(
    symbol_name(q_d__pctr) + princ_to_string(symval(q_d__pctrnum)),
  )
  set(q_d__pctrnum_list, nconc(symval(q_d__pctrnum_list), list1(param)))
  |> ignore
  param
}

///|
fn ith(x : Value, n : Value) -> Value raise {
  if atom(x) {
    Nil
  } else {
    nth(to_int(n) - 1, x)
  }
}

///|
fn polyize(ax : Value, r : Value, m : Value, mul : Value) -> Value raise {
  let m = to_int(m)
  for c in 1..=m {
    let mut d = mat__aref2(ax, r, int(c))
    d = if equal(mul, Fix(1L)) {
      car(d)
    } else {
      ptimes(car(d), pquotientchk(mul, cdr(d)))
    }
    mat__aset2(
      ax,
      r,
      int(c),
      if symval(q_d_sparse).truthy() {
        cons(d, Fix(1L))
      } else {
        d
      },
    )
  }
  Nil
}

///|
/// TWO-STEP FRACTION-FREE GAUSSIAN ELIMINATION ROUTINE
fn tfgeli(ax : Value, n : Value, m : Value) -> Value raise {
  let sparse = if symval(q_d_sparse).truthy() &&
    (symval(q_ear_det).truthy() || symval(q_ear_inv).truthy()) {
    t
  } else {
    Nil
  }
  // $sparse is also controlling whether polyize stores polys or ratforms
  with_specials([(q_ax, ax), (q_d_sparse, sparse)], () => {
    set(q_ax, get_array_pointer(symval(q_ax))) |> ignore
    let ax = symval(q_ax)
    set(q_mul_star, Fix(1L)) |> ignore
    let nn = to_int(n)
    let mm = to_int(m)
    for r in 1..=nn {
      let mut mul : Value = Fix(1L)
      for c in 1..=mm {
        let d = cdr(aref(ax, [r, c]))
        if !equal(Fix(1L), d) {
          mul = ptimes(mul, pquotient(d, pgcd(mul, d)))
        }
      }
      if symval(q_ear_det).truthy() {
        set(q_mul_star, ptimes(symval(q_mul_star), mul)) |> ignore
      }
      polyize(ax, int(r), m, mul) |> ignore
    }
    if symval(q_d_sparse).truthy() && symval(q_ear_det).truthy() {
      sprdet(ax, n)
    } else if symval(q_ear_inv).truthy() && symval(q_d_sparse).truthy() {
      newinv(ax, n, m)
    } else {
      tfgeli1(ax, n, m)
    }
  })
}

// The author of the following programs is Tadatoshi Minamikawa (TM).
// This program is one-step fraction-free Gaussian elimination with optimal
// pivoting.

///|
fn mat__iv(s : Value) -> Int raise {
  to_int(symval(s))
}

///|
/// `(aref *row* i)` etc.
fn mat__vref(s : Value, i : Int) -> Int raise {
  to_int(aref1(symval(s), i))
}

///|
fn mat__vset(s : Value, i : Int, v : Int) -> Unit raise {
  aset1(symval(s), i, int(v)) |> ignore
}

///|
/// `(aref ax (aref *row* i) (aref *col* j))` with the special AX.
fn mat__axrc(i : Int, j : Int) -> Value raise {
  aref(symval(q_ax), [mat__vref(q_ear_row, i), mat__vref(q_ear_col, j)])
}

///|
fn mat__set_axrc(i : Int, j : Int, v : Value) -> Unit raise {
  aset(symval(q_ax), [mat__vref(q_ear_row, i), mat__vref(q_ear_col, j)], v)
  |> ignore
}

///|
fn tfgeli1(ax : Value, ear_n : Value, ear_m : Value) -> Value raise {
  with_specials(
    [
      (q_ax, ax),
      (q_ear_n, ear_n),
      (q_ear_m, ear_m),
      (q_delta, Nil),
      (q_variableorder, Nil),
      (q_inconsistentrows, Nil),
      (q_dependentrows, Nil),
      (q_nrow, Nil),
      (q_nvar, Nil),
      (q_rank, Nil),
      (q_permsign, Nil),
    ],
    () => {
      set(q_ax, get_array_pointer(symval(q_ax))) |> ignore
      let n = to_int(ear_n)
      let m = to_int(ear_m)
      set(q_ear_col, make_array([1 + m], initial=Fix(0L))) |> ignore
      set(q_ear_row, make_array([1 + n], initial=Fix(0L))) |> ignore
      set(q_ear_colinv, make_array([1 + m], initial=Fix(0L))) |> ignore
      set(q_nrow, ear_n) |> ignore
      set(
        q_nvar,
        if symval(q_ear_rank).truthy() {
          ear_m
        } else if symval(q_ear_det).truthy() {
          ear_m
        } else if symval(q_ear_inv).truthy() {
          ear_n
        } else if symval(q_ear_ech).truthy() {
          ear_m
        } else if symval(q_ear_tri).truthy() {
          ear_m
        } else {
          int(m - 1)
        },
      )
      |> ignore
      for i in 1..=n {
        mat__vset(q_ear_row, i, i)
      }
      for i in 1..=m {
        mat__vset(q_ear_col, i, i)
        mat__vset(q_ear_colinv, i, i)
      }
      if symval(q_ear_rank).truthy() {
        forward(t) |> ignore
        symval(q_rank)
      } else if symval(q_ear_det).truthy() {
        forward(t) |> ignore
        if mat__iv(q_nrow) == n {
          if symval(q_permsign).truthy() {
            pminus(symval(q_delta))
          } else {
            symval(q_delta)
          }
        } else {
          Fix(0L)
        }
      } else if symval(q_ear_inv).truthy() {
        forward(t) |> ignore
        backward() |> ignore
        recoverorder1()
      } else if symval(q_ear_ech).truthy() {
        forward(Nil) |> ignore
        recoverorder2()
      } else if symval(q_ear_tri).truthy() {
        forward(Nil) |> ignore
        recoverorder2()
      } else {
        forward(t) |> ignore
        if symval(q_d_backsubst).truthy() {
          backward() |> ignore
        }
        recoverorder2() |> ignore
        list3(
          symval(q_dependentrows),
          symval(q_inconsistentrows),
          symval(q_variableorder),
        )
      }
    },
  )
}

///|
/// FORWARD ELIMINATION
/// IF THE SWITCH *CPIVOT IS NIL, IT AVOIDS THE COLUMN PIVOTING.
fn forward(n_starcpivot : Value) -> Value raise {
  set(q_delta, Fix(1L)) |> ignore // DELTA HOLDS THE CURRENT DETERMINANT
  // NVAR protects against temporary resets done in PIVOT
  with_specials([(q_nvar, symval(q_nvar)), (q_ear_m, symval(q_ear_m))], () => {
    let mut k = 1
    while !(k > mat__iv(q_nrow) || k > mat__iv(q_nvar)) {
      // PIVOT IS T IF THERE IS NO MORE NON-ZERO ROW LEFT. THEN GET OUT OF
      // THE LOOP
      if pivot(symval(q_ax), int(k), n_starcpivot).truthy() {
        break
      }
      let nrow = mat__iv(q_nrow)
      let m = mat__iv(q_ear_m)
      let delta = symval(q_delta)
      for i in (k + 1)..=nrow {
        for j in (k + 1)..=m {
          mat__set_axrc(
            i,
            j,
            pquotient(
              pdifference(
                ptimes(mat__axrc(k, k), mat__axrc(i, j)),
                ptimes(mat__axrc(i, k), mat__axrc(k, j)),
              ),
              delta,
            ),
          )
        }
      }
      for i in (k + 1)..=nrow {
        mat__set_axrc(i, k, Fix(0L))
      }
      set(q_delta, mat__axrc(k, k)) |> ignore
      k = k + 1
    }
  })
  // UNDOES COLUMN HACK IN PIVOT.
  if !n_starcpivot.truthy() {
    for i in 1..=mat__iv(q_ear_m) {
      mat__vset(q_ear_col, i, i)
    }
  }
  set(q_rank, num_min(symval(q_nrow), symval(q_nvar)))
}

///|
/// BACKWARD SUBSTITUTION
fn backward() -> Value raise {
  let rank = mat__iv(q_rank)
  let m = mat__iv(q_ear_m)
  let mut i = rank - 1
  while i >= 1 {
    for l in (rank + 1)..=m {
      let mut sum : Value = Fix(0L)
      for j in (i + 1)..=rank {
        sum = pplus(sum, ptimes(mat__axrc(i, j), mat__axrc(j, l)))
      }
      let mess1 = pdifference(
        ptimes(mat__axrc(i, l), mat__axrc(rank, rank)),
        sum,
      )
      let mess2 = mat__axrc(i, i)
      let v : Value = if equal(Fix(0L), mess1) {
        Fix(0L)
      } else if equal(Fix(0L), mess2) {
        Fix(0L)
      } else {
        // The quotient is exact, but with algebraic numbers in the entries,
        // RATREDUCE can leave part of it in the denominator - divide that
        // out. floats can cause the division to fail, then only use the
        // numerator.
        let q = ratreduce(mess1, mess2)
        if equal(cdr(q), Fix(1L)) {
          car(q)
        } else {
          let p = palgquotient(car(q), cdr(q))
          if p.truthy() {
            p
          } else {
            car(q)
          }
        }
      }
      mat__set_axrc(i, l, v)
    }
    for l in (i + 1)..=rank {
      mat__set_axrc(i, l, Fix(0L))
    }
    i = i - 1
  }
  // PUT DELTA INTO THE DIAGONAL MATRIX
  set(q_delta, mat__axrc(rank, rank)) |> ignore
  for i in 1..=rank {
    mat__set_axrc(i, i, symval(q_delta))
  }
  Nil
}

///|
fn mat__push(s : Value, v : Value) -> Unit {
  set(s, cons(v, symval(s))) |> ignore
}

///|
fn mat__sort_rows() -> Unit raise {
  let rank = mat__iv(q_rank)
  let n = mat__iv(q_ear_n)
  let m = mat__iv(q_ear_m)
  for i in (rank + 1)..=n {
    if equal(mat__axrc(i, m), Fix(0L)) {
      mat__push(q_dependentrows, int(mat__vref(q_ear_row, i)))
    } else {
      mat__push(q_inconsistentrows, int(mat__vref(q_ear_row, i)))
    }
  }
}

///|
/// RECOVER THE ORDER OF ROWS AND COLUMNS.
fn recoverorder1() -> Value raise {
  let mut i = mat__iv(q_nvar)
  while i != 0 {
    mat__push(q_variableorder, int(i))
    i = i - 1
  }
  mat__sort_rows()
  let n = mat__iv(q_ear_n)
  let ax = symval(q_ax)
  for i in 1..=n {
    if mat__vref(q_ear_row, mat__vref(q_ear_colinv, i)) != i {
      moverow(ax, symval(q_ear_n), symval(q_ear_m), int(i), Fix(0L)) |> ignore
      let mut l = i
      while true {
        let k = mat__vref(q_ear_row, mat__vref(q_ear_colinv, l))
        mat__vset(q_ear_row, mat__vref(q_ear_colinv, l), l)
        if k == i {
          moverow(ax, symval(q_ear_n), symval(q_ear_m), Fix(0L), int(l))
          |> ignore
          break
        } else {
          moverow(ax, symval(q_ear_n), symval(q_ear_m), int(k), int(l))
          |> ignore
          l = k
        }
      }
    }
  }
  Nil
}

///|
fn recoverorder2() -> Value raise {
  let mut i = mat__iv(q_nvar)
  while i != 0 {
    mat__push(q_variableorder, int(mat__vref(q_ear_col, i)))
    i = i - 1
  }
  mat__sort_rows()
  let n = mat__iv(q_ear_n)
  let ax = symval(q_ax)
  for i in 1..=n {
    if mat__vref(q_ear_row, i) != i {
      moverow(ax, symval(q_ear_n), symval(q_ear_m), int(i), Fix(0L)) |> ignore
      let mut l = i
      while true {
        let k = mat__vref(q_ear_row, l)
        mat__vset(q_ear_row, l, l)
        if k == i {
          moverow(ax, symval(q_ear_n), symval(q_ear_m), Fix(0L), int(l))
          |> ignore
          break
        } else {
          moverow(ax, symval(q_ear_n), symval(q_ear_m), int(k), int(l))
          |> ignore
          l = k
        }
      }
    }
  }
  for i in 1..=mat__iv(q_nvar) {
    if mat__vref(q_ear_col, i) != i {
      movecol(ax, symval(q_ear_n), symval(q_ear_m), int(i), Fix(0L)) |> ignore
      let mut l = i
      while true {
        let k = mat__vref(q_ear_col, l)
        mat__vset(q_ear_col, l, l)
        if k == i {
          movecol(ax, symval(q_ear_n), symval(q_ear_m), Fix(0L), int(l))
          |> ignore
          break
        } else {
          movecol(ax, symval(q_ear_n), symval(q_ear_m), int(k), int(l))
          |> ignore
          l = k
        }
      }
    }
  }
  Nil
}

///|
/// THIS PROGRAM IS USED IN REARRANGEMENT
fn moverow(
  ax : Value,
  ear_n : Value,
  ear_m : Value,
  i : Value,
  j : Value,
) -> Value raise {
  let i = to_int(i)
  let j = to_int(j)
  for k in 1..=to_int(ear_m) {
    aset(ax, [j, k], aref(ax, [i, k])) |> ignore
  }
  Nil
}

///|
fn movecol(
  ax : Value,
  ear_n : Value,
  ear_m : Value,
  i : Value,
  j : Value,
) -> Value raise {
  let i = to_int(i)
  let j = to_int(j)
  for k in 1..=to_int(ear_n) {
    aset(ax, [k, j], aref(ax, [k, i])) |> ignore
  }
  Nil
}

// COMPLEXITY IS DEFINED AS FOLLOWS
//  COMPLEXITY(0)=0
//  COMPLEXITY(CONSTANT)=1
//  COMPLEXITY(POLYNOMIAL)=1+SUM(COMPLEXITY(C(N))+COMPLEXITY(E(N)), FOR N=0,1 ...M)
//  WHERE POLYNOMIAL IS OF THE FORM
//     SUM(C(N)*X^E(N), FOR N=0,1 ... M)     X IS THE VARIABLE

///|
fn mat__complexity(exp_ : Value) -> Int {
  if exp_ is Nil {
    0
  } else if equal(exp_, Fix(0L)) {
    0
  } else if atom(exp_) {
    1
  } else {
    mat__complexity(car(exp_)) + mat__complexity(cdr(exp_))
  }
}

///|
fn complexity(exp_ : Value) -> Value raise {
  int(mat__complexity(exp_))
}

///|
fn mat__complexity_row(ax : Value, i : Int, j1 : Int, j2 : Int) -> Int raise {
  let mut sum = 0
  for j in j1..=j2 {
    sum = sum +
      mat__complexity(
        aref(ax, [mat__vref(q_ear_row, i), mat__vref(q_ear_col, j)]),
      )
  }
  sum
}

///|
fn mat__complexity_col(ax : Value, j : Int, i1 : Int, i2 : Int) -> Int raise {
  let mut sum = 0
  for i in i1..=i2 {
    sum = sum +
      mat__complexity(
        aref(ax, [mat__vref(q_ear_row, i), mat__vref(q_ear_col, j)]),
      )
  }
  sum
}

///|
fn complexity_slrow(ax : Value, i : Value, j1 : Value, j2 : Value) -> Value raise {
  int(mat__complexity_row(ax, to_int(i), to_int(j1), to_int(j2)))
}

///|
fn complexity_slcol(ax : Value, j : Value, i1 : Value, i2 : Value) -> Value raise {
  int(mat__complexity_col(ax, to_int(j), to_int(i1), to_int(i2)))
}

///|
fn mat__zerop_row(ax : Value, i : Int, j1 : Int, j2 : Int) -> Bool raise {
  for j in j1..=j2 {
    if !equal(aref(ax, [mat__vref(q_ear_row, i), mat__vref(q_ear_col, j)]), Fix(0L)) {
      return false
    }
  }
  true
}

///|
fn zerop_slrow(ax : Value, i : Value, j1 : Value, j2 : Value) -> Value raise {
  lbool(mat__zerop_row(ax, to_int(i), to_int(j1), to_int(j2)))
}

///|
/// PIVOTING ALGORITHM
fn pivot(ax : Value, k : Value, n_starcpivot : Value) -> Value raise {
  let k = to_int(k)
  let mut row_optimal = k
  let mut complexity_i_min = 1000000
  let mut complexity_j_min = 1000000
  // TEST THE SINGULARITY
  let mut isallzero = true
  let mut i = k
  while i <= mat__iv(q_nrow) {
    while true {
      if mat__zerop_row(ax, i, k, mat__iv(q_nvar)) {
        if symval(q_ear_inv).truthy() {
          merr("solve: singular matrix.", []) |> ignore
        } else {
          exchangerow(int(i), symval(q_nrow)) |> ignore
          set(q_nrow, int(mat__iv(q_nrow) - 1)) |> ignore
        }
        if i > mat__iv(q_nrow) {
          break
        }
      } else {
        isallzero = false
        break
      }
    }
    i = i + 1
  }
  if isallzero {
    return t
  }
  // FIND AN OPTIMAL ROW
  // IF *CPIVOT IS NIL, (AX I K) WHICH IS TO BE THE PIVOT MUST BE NONZERO.
  // BUT IF *CPIVOT IS T, IT IS UNNECESSARY BECAUSE WE CAN DO THE COLUMN
  // PIVOT.
  while true {
    for i in k..=mat__iv(q_nrow) {
      if n_starcpivot.truthy() ||
        !equal(
          aref(ax, [mat__vref(q_ear_row, i), mat__vref(q_ear_col, k)]),
          Fix(0L),
        ) {
        let complexity_i = mat__complexity_row(ax, i, k, mat__iv(q_ear_m))
        if complexity_i_min > complexity_i {
          row_optimal = i
          complexity_i_min = complexity_i
        }
      }
    }
    // EXCHANGE THE ROWS K AND ROW/OPTIMAL
    exchangerow(int(k), int(row_optimal)) |> ignore
    // IF THE FLAG *CPIVOT IS NIL, THE FOLLOWING STEPS ARE NOT EXECUTED.
    // THIS TREATMENT WAS DONE FOR THE LSA AND ECHELONTHINGS WHICH ARE NOT
    // HAPPY WITH THE COLUMN OPERATIONS.
    if n_starcpivot is Nil {
      if !equal(
          aref(ax, [mat__vref(q_ear_row, k), mat__vref(q_ear_col, k)]),
          Fix(0L),
        ) {
        return Nil
      } else {
        let mut i = k
        while i != mat__iv(q_nvar) {
          mat__vset(q_ear_col, i, mat__vref(q_ear_col, i + 1))
          i = i + 1
        }
        set(q_nvar, int(mat__iv(q_nvar) - 1)) |> ignore
        set(q_ear_m, int(mat__iv(q_ear_m) - 1)) |> ignore
        continue
      }
    }
    break
  }
  // STEP3 ... FIND THE OPTIMAL COLUMN
  let mut col_optimal = 0
  let mut complexity_det_min = 1000000
  complexity_j_min = 1000000
  let n = mat__iv(q_ear_n)
  for j in k..=mat__iv(q_nvar) {
    let a = aref(ax, [mat__vref(q_ear_row, k), mat__vref(q_ear_col, j)])
    if !equal(a, Fix(0L)) {
      let complexity_det = mat__complexity(a)
      if complexity_det_min > complexity_det {
        col_optimal = j
        complexity_det_min = complexity_det
        complexity_j_min = mat__complexity_col(ax, j, k + 1, n)
      } else if complexity_det_min == complexity_det {
        let complexity_j = mat__complexity_col(ax, j, k + 1, n)
        if complexity_j_min > complexity_j {
          col_optimal = j
          complexity_det_min = complexity_det
          complexity_j_min = complexity_j
        }
      }
    }
  }
  // EXCHANGE THE COLUMNS K AND COL/OPTIMAL
  exchangecol(int(k), int(col_optimal)) |> ignore
  let ck = mat__vref(q_ear_col, k)
  let co = mat__vref(q_ear_col, col_optimal)
  let dummy = mat__vref(q_ear_colinv, ck)
  mat__vset(q_ear_colinv, ck, mat__vref(q_ear_colinv, co))
  mat__vset(q_ear_colinv, co, dummy)
  Nil
}

///|
fn exchangerow(i : Value, j : Value) -> Value raise {
  let ii = to_int(i)
  let jj = to_int(j)
  let dummy = mat__vref(q_ear_row, ii)
  mat__vset(q_ear_row, ii, mat__vref(q_ear_row, jj))
  mat__vset(q_ear_row, jj, dummy)
  if ii == jj {
    Nil
  } else {
    set(q_permsign, lnot(symval(q_permsign)))
  }
}

///|
fn exchangecol(i : Value, j : Value) -> Value raise {
  let ii = to_int(i)
  let jj = to_int(j)
  let dummy = mat__vref(q_ear_col, ii)
  mat__vset(q_ear_col, ii, mat__vref(q_ear_col, jj))
  mat__vset(q_ear_col, jj, dummy)
  if ii == jj {
    Nil
  } else {
    set(q_permsign, lnot(symval(q_permsign)))
  }
}

///|
/// Displays list of solutions.
fn solve2(llist : Value, equations : Value) -> (Value, Value) raise {
  let mut equations = equations
  set(q_d_multiplicities, Nil) |> ignore
  map2c(
    lfunc("solve2", args => {
      let equatn = arg(args, 0)
      let multipl = arg(args, 1)
      equations = nconc(equations, list1(displine(equatn)))
      set(q_d_multiplicities, cons(multipl, symval(q_d_multiplicities)))
      |> ignore
      if num_gt(multipl, Fix(1L)) && symval(q_d_dispflag).truthy() {
        mtell(list2(Str("solve: multiplicity ~A~%"), multipl))
      } else {
        Nil
      }
    }),
    llist,
  )
  |> ignore
  let mult = set(
    q_d_multiplicities,
    cons(list2(q_mlist, q_simp), nreverse(symval(q_d_multiplicities))),
  )
  (mult, equations)
}

///|
/// CL `get-internal-run-time` (microseconds, as in SBCL).
fn mat__get_internal_run_time() -> Value {
  int64((cpu_time() * 1000000.0).to_int64())
}

///|
/// Displays an expression and returns its linelabel.
fn displine(exp_ : Value) -> Value raise {
  with_special(q_d_nolabels, Nil, () => {
    let mut tim : Value = Fix(0L)
    elabel(exp_) |> ignore
    if symval(q_d_dispflag).truthy() {
      remprop(symval(q_ear_linelabel), q_nodisp) |> ignore
      tim = mat__get_internal_run_time()
      mterpri() |> ignore
      displa(list3(list1(q_mlabel), symval(q_ear_linelabel), exp_)) |> ignore
      timeorg(tim) |> ignore
    } else {
      putprop(symval(q_ear_linelabel), t, q_nodisp) |> ignore
    }
    symval(q_ear_linelabel)
  })
}

///|
fn init_mat() -> Unit raise {
  set(q_ear_det, Nil) |> ignore
  set(q_ear_ech, Nil) |> ignore
  set(q_ear_tri, Nil) |> ignore
}

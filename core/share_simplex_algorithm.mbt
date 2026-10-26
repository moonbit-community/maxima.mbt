// Port of share/simplex/simplex_algorithm.lisp (Andrej Vodopivec, version
// 1.02): a simple implementation of the two-phase simplex algorithm for
// Linear Programming.
//
// linear_program(A, b, c): find x which minimizes c'.x with constraints
// A.x=b and x>=0. Returns [x, val] if the problem is solvable, or the
// strings "Problem not bounded!" / "Problem not feasible!".
//
// Variables: pivot_count_sx (number of pivots in last computation),
// pivot_max_sx (maximum number of pivots), epsilon_lp (epsilon for numeric
// computation), scale_lp (use equilibratium scaling), warn_rank_sx.

///|
/// `(maref ar i ...)`: the MAREF macro (transm.lisp) expands to MAREF1
/// (trans2.lisp).
fn share_simplex_algorithm__maref(ar : Value, inds : Array[Int]) -> Value raise {
  maref1(ar, list(inds.map(i => int(i))))
}

///|
fn share_simplex_algorithm__aref(tab : Value, i : Int, j : Int) -> Value raise {
  aref(tab, [i, j])
}

///|
fn share_simplex_algorithm__aset(
  tab : Value,
  i : Int,
  j : Int,
  v : Value,
) -> Unit raise {
  aset(tab, [i, j], v) |> ignore
}

///|
/// type checkers
fn lp_rat_mlist_p(x : Value) -> Value raise {
  lbool(listp(x) && cdr(x).iter().all(e => d_ratnump(e).truthy()))
}

///|
fn lp_rat_matrix_p(x : Value) -> Value raise {
  lbool(
    d_matrixp(x).truthy() &&
    cdr(x).iter().all(e => lp_rat_mlist_p(e).truthy()),
  )
}

///|
/// comparison
fn lp_mlsp(a : Value, b : Value) -> Value raise {
  let x = mlsp(a, b)
  if eq(x, t) || x is Nil {
    x
  } else {
    let s = d_asksign(cadr(x))
    if eq(s, q_d_pos) {
      t
    } else {
      Nil
    }
  }
}

///|
fn lp_mgqp(a : Value, b : Value) -> Value raise {
  let v = meqp(a, b)
  if v.truthy() {
    v
  } else {
    lp_mlsp(b, a)
  }
}

///|
/// Two-phase standard simplex method for solving linear program in
/// standard form.
fn d_linear_program(a : Value, b : Value, c : Value) -> Value raise {
  if !d_matrixp(a).truthy() {
    merror(Str("linear_program: first argument not matrix."), Nil) |> ignore
  }
  if !d_listp(b).truthy() {
    merror(Str("linear_program: second argument not list."), Nil) |> ignore
  }
  if !d_listp(c).truthy() {
    merror(Str("linear_program: third argument not list."), Nil) |> ignore
  }
  if !meqp(d_length(b), d_length(a)).truthy() {
    merror(Str("linear_program: second argument not of correct length."), Nil)
    |> ignore
  }
  if !meqp(d_length(c), d_length(d_first(a))).truthy() {
    merror(Str("linear_program: third argument not of correct length."), Nil)
    |> ignore
  }
  let m = to_int(d_length(a))
  let n = to_int(d_length(d_first(a)))
  let tab = make_array([2 + m, n + 1], initial=Fix(0L)) // Tableau
  let mut basis : Value = Nil // which columns are in current basis
  let mut sc_fac : Value = Nil // scaling factors
  let epsilon : Value = if lp_rat_mlist_p(b).truthy() &&
    lp_rat_mlist_p(c).truthy() &&
    lp_rat_matrix_p(a).truthy() {
    Fix(0L)
  } else {
    symval(q_d_epsilon_lp)
  }
  with_specials([(q_d_epsilon_lp, epsilon), (q_d_ratprint, Nil)], () => {
    if lp_mlsp(Fix(0L), symval(q_d_epsilon_lp)).truthy() {
      mwarning(
        list1(
          format(
            Nil,
            "linear_program(A,b,c): non-rat inputs found, epsilon_lp=~e.",
            [symval(q_d_epsilon_lp)],
          ),
        ),
      )
      |> ignore
      mwarning(list1(Str("Solution may be incorrect."))) |> ignore
    }
    set(q_d_pivot_count_sx, Fix(0L)) |> ignore

    // Construct the tableau for phase 1:
    //       [   A      b    ]
    // Tab = [   c'     0    ]
    //       [ sm(A)  sm(b)  ]
    //
    // If b[i]<0 multiply b[i] and A[i] by -1 (required for phase 1).
    for i in 0..<m {
      if lp_mlsp(share_simplex_algorithm__maref(b, [i + 1]), Fix(0L)).truthy() {
        for j in 0..<n {
          share_simplex_algorithm__aset(
            tab,
            i,
            j,
            neg(share_simplex_algorithm__maref(a, [i + 1, j + 1])),
          )
        }
        share_simplex_algorithm__aset(
          tab,
          i,
          n,
          neg(share_simplex_algorithm__maref(b, [i + 1])),
        )
      } else {
        for j in 0..<n {
          share_simplex_algorithm__aset(
            tab,
            i,
            j,
            share_simplex_algorithm__maref(a, [i + 1, j + 1]),
          )
        }
        share_simplex_algorithm__aset(
          tab,
          i,
          n,
          share_simplex_algorithm__maref(b, [i + 1]),
        )
      }
    }
    for i in 0..<n {
      share_simplex_algorithm__aset(
        tab,
        m,
        i,
        neg(share_simplex_algorithm__maref(c, [i + 1])),
      )
    }
    for i in 0..<n {
      share_simplex_algorithm__aset(tab, m + 1, i, Fix(0L))
      for j in 0..<m {
        share_simplex_algorithm__aset(
          tab,
          m + 1,
          i,
          add2(
            share_simplex_algorithm__aref(tab, m + 1, i),
            share_simplex_algorithm__aref(tab, j, i),
          ),
        )
      }
    }
    share_simplex_algorithm__aset(tab, m + 1, n, Fix(0L))
    for i in 0..<m {
      share_simplex_algorithm__aset(
        tab,
        m + 1,
        n,
        add2(
          share_simplex_algorithm__aref(tab, m + 1, n),
          share_simplex_algorithm__aref(tab, i, n),
        ),
      )
    }
    share_simplex_algorithm__aset(tab, m, n, Fix(0L))

    // At the beginning the artificial variables are in the basis.
    for i in 0..<m {
      basis = append(basis, list1(add2(int(n), int(i))))
    }

    // Scaling.
    for _ in 0..<n {
      sc_fac = append(sc_fac, list1(Fix(1L)))
    }
    if symval(q_d_scale_lp).truthy() {
      scale_sx(tab, int(2 + m), int(n + 1), sc_fac) |> ignore
    }

    // Phase 1
    simplex_sx(tab, basis, int(m), int(2 + m), int(n + 1)) |> ignore
    if lp_mlsp(
        symval(q_d_epsilon_lp),
        share_simplex_algorithm__aref(tab, m + 1, n),
      ).truthy() {
      Str("Problem not feasible!")
    } else {
      // Check for artificial variables in basis.
      for i in 0..<m {
        if num_ge(nth(i, basis), int(n)) {
          if !run_out_of_basis_sx(tab, int(m), int(n), basis, int(i)).truthy() &&
            symval(q_d_warn_rank_sx).truthy() {
            d_print(
              list([
                Str("Matrix A is not of full rank:"),
                Str("Row"),
                int(i + 1),
                Str("is redundant!"),
              ]),
            )
            |> ignore
          }
        }
      }

      // Phase 2
      let is_bounded = simplex_sx(tab, basis, int(m), int(m + 1), int(n + 1))
      if is_bounded.truthy() {
        let mut opt_tmp : Value = Nil
        let mut opt : Value = Nil
        for _ in 0..<(m + n) {
          opt_tmp = append(opt_tmp, list1(Fix(0L)))
        }
        for i in 0..<m {
          // undo the scaling
          rplaca(
            nthcdr(to_int(nth(i, basis)), opt_tmp),
            div(
              share_simplex_algorithm__aref(tab, i, n),
              nth(to_int(nth(i, basis)), sc_fac),
            ),
          )
          |> ignore
        }
        for _ in 0..<n {
          opt = append(opt, list1(Fix(0L)))
        }
        for i in 0..<n {
          rplaca(nthcdr(i, opt), nth(i, opt_tmp)) |> ignore
        }
        // build the solution
        opt = cons(list2(q_mlist, q_simp), opt)
        opt = list3(
          list2(q_mlist, q_simp),
          opt,
          share_simplex_algorithm__aref(tab, m, n),
        )
        opt
      } else {
        Str("Problem not bounded!")
      }
    }
  })
}

///|
/// Simplex algorithm.
fn simplex_sx(
  tab : Value,
  basis : Value,
  am : Value,
  m : Value,
  n : Value,
) -> Value raise {
  let am = to_int(am)
  let m = to_int(m)
  let n = to_int(n)
  let mut is_bounded : Value = Nil
  // Repeat while we don't have a solution or know that the problem is
  // unbounded.
  let mut have_solution = false
  while !have_solution {
    // Choose jp so that jp-th column has the biggest reduced cost.
    // If all reduced costs are negative, we have the solution.
    let mut tmp = share_simplex_algorithm__aref(tab, m - 1, 0)
    let mut jp = 0
    for j in 0..<(n - 1) {
      if lp_mlsp(tmp, share_simplex_algorithm__aref(tab, m - 1, j)).truthy() {
        tmp = share_simplex_algorithm__aref(tab, m - 1, j)
        jp = j
      }
    }
    if lp_mgqp(symval(q_d_epsilon_lp), tmp).truthy() {
      is_bounded = t
      have_solution = true
    } else {
      // Choose ip so that Tab[ip,n]/Tab[ip,jp] is the smallest
      // possible among those for which Tab[i,n] is positive. If all
      // Tab[i,n] are negative, the problem is unbounded.
      tmp = Nil
      let mut ip = 0
      for i in 0..<am {
        if lp_mlsp(
            symval(q_d_epsilon_lp),
            share_simplex_algorithm__aref(tab, i, jp),
          ).truthy() {
          if tmp is Nil ||
            lp_mlsp(
              div(
                share_simplex_algorithm__aref(tab, i, n - 1),
                share_simplex_algorithm__aref(tab, i, jp),
              ),
              tmp,
            ).truthy() {
            tmp = div(
              share_simplex_algorithm__aref(tab, i, n - 1),
              share_simplex_algorithm__aref(tab, i, jp),
            )
            ip = i
          }
        }
      }
      if tmp is Nil {
        is_bounded = Nil
        have_solution = true
      } else {
        // Pivot the simplex tableau.
        rplaca(nthcdr(ip, basis), int(jp)) |> ignore
        pivot_sx(tab, int(ip), int(jp), int(m), int(n)) |> ignore
      }
    }
  }
  is_bounded
}

///|
/// Pivoting for the Simplex algorithm.
fn pivot_sx(
  tab : Value,
  ip : Value,
  jp : Value,
  m : Value,
  n : Value,
) -> Value raise {
  let ip = to_int(ip)
  let jp = to_int(jp)
  let m = to_int(m)
  let n = to_int(n)
  let piv = share_simplex_algorithm__aref(tab, ip, jp)
  set(q_d_pivot_count_sx, num_add(symval(q_d_pivot_count_sx), Fix(1L)))
  |> ignore
  if meqp(symval(q_d_pivot_count_sx), symval(q_d_pivot_max_sx)).truthy() {
    d_print(list1(Str("Maximum number of pivots reached."))) |> ignore
    d_print(list1(Str("Try setting a bigger value for pivot_max_sx."))) |> ignore
    d_print(list1(Str("Try setting scale_lp to true."))) |> ignore
    d_print(list1(Str(""))) |> ignore
    d_error(list1(Str("linear_program: maximum number of pivots reached.")))
    |> ignore
  }
  if meqp(piv, Fix(0L)).truthy() {
    d_print(list1(Str("Singular!")))
  } else {
    for i in 0..<n {
      share_simplex_algorithm__aset(
        tab,
        ip,
        i,
        div(share_simplex_algorithm__aref(tab, ip, i), piv),
      )
    }
    for i in 0..<m {
      if i != ip {
        let tm = share_simplex_algorithm__aref(tab, i, jp)
        if !meqp(tm, Fix(0L)).truthy() {
          for j in 0..<n {
            share_simplex_algorithm__aset(
              tab,
              i,
              j,
              sub(
                share_simplex_algorithm__aref(tab, i, j),
                mul(list2(tm, share_simplex_algorithm__aref(tab, ip, j))),
              ),
            )
          }
        }
      }
    }
    Nil
  }
}

///|
/// Run artificial variable out of basis.
fn run_out_of_basis_sx(
  tab : Value,
  m : Value,
  n : Value,
  basis : Value,
  i : Value,
) -> Value raise {
  let nn = to_int(n)
  let ii = to_int(i)
  let mut jp : Int? = None
  let mut j = 0
  while !(j == nn || jp is Some(_)) {
    // if Tab[i,j]#0 then column j is not in the basis
    if !meqp(Fix(0L), share_simplex_algorithm__aref(tab, ii, j)).truthy() {
      jp = Some(j)
    }
    j = j + 1
  }
  match jp {
    None => Nil
    Some(jp) => {
      rplaca(nthcdr(ii, basis), int(jp)) |> ignore
      pivot_sx(tab, i, int(jp), num_add(Fix(2L), m), num_add(Fix(1L), n))
      |> ignore
      Fix(1L)
    }
  }
}

///|
/// Scaling for the simplex algorithm. (Equilibratium scaling)
///
/// After scaling, the maximum absolute value in each row/column is 1.
fn scale_sx(tab : Value, m : Value, n : Value, sc_fac : Value) -> Value raise {
  let m = to_int(m)
  let n = to_int(n)
  let mut r : Value = Fix(0L)
  // Scale the rows of A and b.
  for i in 0..<(m - 2) {
    r = Fix(0L)
    for j in 0..<n {
      let tij = share_simplex_algorithm__aref(tab, i, j)
      let ta = if lp_mlsp(tij, Fix(0L)).truthy() { neg(tij) } else { tij }
      if lp_mlsp(r, ta).truthy() {
        r = ta
      }
    }
    if lp_mlsp(symval(q_d_epsilon_lp), r).truthy() {
      for j in 0..<n {
        share_simplex_algorithm__aset(
          tab,
          i,
          j,
          div(share_simplex_algorithm__aref(tab, i, j), r),
        )
      }
    }
  }
  // Scale the columns of A and c.
  for j in 0..<(n - 1) {
    r = Fix(0L)
    for i in 0..<(m - 2) {
      let tij = share_simplex_algorithm__aref(tab, i, j)
      let ta = if lp_mlsp(tij, Fix(0L)).truthy() { neg(tij) } else { tij }
      if lp_mlsp(r, ta).truthy() {
        r = ta
      }
    }
    if lp_mlsp(symval(q_d_epsilon_lp), r).truthy() {
      for i in 0..<m {
        share_simplex_algorithm__aset(
          tab,
          i,
          j,
          div(share_simplex_algorithm__aref(tab, i, j), r),
        )
      }
      rplaca(nthcdr(j, sc_fac), r) |> ignore
    }
  }
  Nil
}

///|
/// The MAYBE-RESET part of DEFMVAR: record the initial value of a
/// variable so that `reset` restores it.
fn share_simplex_algorithm__defmvar_reset(
  var_ : Value,
  val : Value,
) -> Unit raise {
  let table = symval(q_ear_variable_initial_values)
  if hash_table_p(table) && gethash(var_, table) is Nil {
    sethash(var_, table, val) |> ignore
  }
}

///|
/// The ASSIGN property a `boolean` DEFMVAR installs: only true and false
/// may be assigned.
fn share_simplex_algorithm__boolean_assign() -> Value {
  lfunc("defmvar-boolean", args => {
    let var_ = arg(args, 0)
    let val = arg(args, 1)
    let possible_values = list2(t, Nil)
    if member(val, possible_values) is Nil {
      mseterr(
        var_,
        val,
        reason=format(Nil, "must be one of: ~{~A~^, ~}", [
          mapcar(x => stripdollar(x), possible_values),
        ]),
      )
    } else {
      Nil
    }
  })
}

///|
fn init_share_simplex_algorithm() -> Unit raise {
  d_put(q_d_simplex, Flo(1.02), q_d_version) |> ignore
  share_simplex_algorithm__defmvar_reset(q_d_pivot_count_sx, Fix(0L))
  share_simplex_algorithm__defmvar_reset(q_d_pivot_max_sx, Fix(15000L))
  share_simplex_algorithm__defmvar_reset(q_d_epsilon_lp, Flo(1.0e-8))
  share_simplex_algorithm__defmvar_reset(q_d_scale_lp, Nil)
  putprop(q_d_scale_lp, share_simplex_algorithm__boolean_assign(), q_assign)
  |> ignore
  share_simplex_algorithm__defmvar_reset(q_d_warn_rank_sx, Nil)
  putprop(q_d_warn_rank_sx, share_simplex_algorithm__boolean_assign(), q_assign)
  |> ignore
}

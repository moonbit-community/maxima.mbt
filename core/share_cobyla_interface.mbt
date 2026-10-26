// Port of share/cobyla/cobyla-interface.lisp: fmin_cobyla, the Maxima
// interface to COBYLA (Constrained Optimization BY Linear Approximations),
// on top of the f2cl translation of COBYLA (the MoonBit package
// dii/maxima/cobyla).

///|
/// %%PRETTY-FNAME of fmin_cobyla / bf_fmin_cobyla.
fn cobyla__pretty_fname(name : Value, rhoend : Value) -> Value {
  mk(name, [
    sym("f"),
    sym("vars"),
    sym("init-x"),
    mk(q_mequal, [q_d_constraints, Nil]),
    mk(q_mequal, [q_d_rhobeg, Flo(1.0)]),
    mk(q_mequal, [q_d_rhoend, rhoend]),
    mk(q_mequal, [q_d_iprint, Fix(0L)]),
    mk(q_mequal, [q_d_maxfun, Fix(1000L)]),
  ])
}

///|
/// The argument checks shared by fmin_cobyla and bf_fmin_cobyla.
fn cobyla__check_args(
  pretty : Value,
  vars : Value,
  init_x : Value,
  iprint : Value,
  maxfun : Value,
) -> Unit raise {
  if !listp(vars) {
    merr("~M: vars must be a list of variables. Got: ~M", [pretty, vars])
    |> ignore
  }
  if !listp(init_x) {
    merr("~M: Initial values must be a list of values. Got: ~M", [
      pretty, init_x,
    ])
    |> ignore
  }
  if length(cdr(vars)) != length(cdr(init_x)) {
    merr(
      "~M: Number of initial values (~M) does not match the number of variables ~M~%",
      [
        pretty,
        Fix(length(cdr(init_x)).to_int64()),
        Fix(length(cdr(vars)).to_int64()),
      ],
    )
    |> ignore
  }
  if !(integerp(iprint) &&
    num_le(Fix(0L), iprint) &&
    num_le(iprint, Fix(3L))) {
    merr("~M: iprint must be an integer between 0 and 3, inclusive, not: ~M~%", [
      pretty, iprint,
    ])
    |> ignore
  }
  if !(integerp(maxfun) && plusp(maxfun)) {
    merr("~M: maxfun must be a positive integer, not: ~M~%", [pretty, maxfun])
    |> ignore
  }
}

///|
/// Go through constraints and convert f >= g to f - g, f <= g to g - f, and
/// f = g to f - g and g - f.  This is because cobyla expects all
/// constraints to of the form h>=0.
fn cobyla__normalize_constraints(
  pretty : Value,
  constraints : Value,
) -> Value raise {
  let mut normalized : Value = Nil
  for c in cdr(constraints).iter() {
    let op = d_op(c)
    if cobyla__string_equal(op, ">=") {
      normalized = cons(sub(d_lhs(c), d_rhs(c)), normalized)
    } else if cobyla__string_equal(op, "<=") {
      normalized = cons(sub(d_rhs(c), d_lhs(c)), normalized)
    } else if cobyla__string_equal(op, "=") {
      normalized = cons(sub(d_lhs(c), d_rhs(c)), normalized)
      normalized = cons(sub(d_rhs(c), d_lhs(c)), normalized)
    } else {
      merr("~M: Constraint equation must be =, <= or >=: got ~M", [pretty, op])
      |> ignore
    }
  }
  cons(list1(q_mlist), nreverse(normalized))
}

///|
/// `(string-equal op s)`: OP is a string, or a symbol (its name).
fn cobyla__string_equal(op : Value, s : String) -> Bool raise {
  let name = match op {
    Str(t) => t
    Sym(_) | Nil => invert_case(symbol_name(op))
    _ => return false
  }
  name.to_lower() == s.to_lower()
}

///|
/// COBYLA always calls CALCFC to compute the function value and the
/// constraint equations.  But we want to be able to specify different
/// versions.  So, COBYLA calls CALCFC, which then calls *CALCFC* to do the
/// real computation.
///
/// The f2cl calling convention returns (values n m nil f nil); the port has
/// no multiple values, so the functions stored in *CALCFC* return F, the
/// value COBYLB reads.
fn cobyla_calcfc(
  n : Value,
  m : Value,
  x : Value,
  _f : Value,
  con : Value,
) -> Value raise {
  funcall(symval(q_ear_calcfc), [n, m, x, con])
}

///|
/// COBYLA (Constrained Optimization BY Linear Approximation).
///
/// fmin_cobyla(f, vars, init_x, [args])
///
///  f       Real function to be minimized
///  vars    List of variables over which to minimize
///  init_x  Initial guess.  Do NOT set to all zeroes.
///
/// Optional keyword arguments: constraints, rhobeg (1), rhoend (1d-6),
/// iprint (0), maxfun (1000).
///
/// On return, a vector of four elements is given:
///
///  1:  The value of the variables giving the minimum
///  2:  The minimized function value
///  3:  The number of function evaluations.
///  4:  Success code:
///        0 - success
///        1 - maxfun limit reached
///        2 - rounding issues
///       -1 - maxcv exceeds rhoend probably indicating constraints not
///            satisfied.
fn d_fmin_cobyla(
  f : Value,
  vars : Value,
  init_x : Value,
  constraints? : Value = Nil,
  rhobeg? : Value = Flo(1.0),
  rhoend? : Value = Flo(1.0e-06),
  iprint? : Value = Fix(0L),
  maxfun? : Value = Fix(1000L),
) -> Value raise {
  let pretty = cobyla__pretty_fname(q_d_fmin_cobyla, Flo(1.0e-06))
  cobyla__check_args(pretty, vars, init_x, iprint, maxfun)
  let normalized_constraints = cobyla__normalize_constraints(
    pretty, constraints,
  )
  if symval(q_ear_debug_cobyla).truthy() {
    mformat(list([t, Str("cons = ~M~%"), normalized_constraints])) |> ignore
  }
  let n = length(cdr(vars))
  let m = length(cdr(normalized_constraints))
  let x : FixedArray[Double] = FixedArray::make(n, 0.0)
  let mut k = 0
  for z in cdr(init_x).iter() {
    let r = d_float(z)
    match r {
      Flo(d) => if k < n { x[k] = d }
      _ =>
        merr("~M: Does not evaluate to a float:  ~M", [pretty, z]) |> ignore
    }
    k = k + 1
  }
  // Real work array for cobyla.
  let w : FixedArray[Double] = FixedArray::make(
    n * (3 * n + 2 * m + 11) + (4 * m + 6) + 6,
    0.0,
  )
  // Integer work array for cobyla.
  let iact : FixedArray[Int] = FixedArray::make(m + 1, 0)
  let fv = share_f2cl__coerce_float_fun(f, vars)
  let cv = share_f2cl__coerce_float_fun(normalized_constraints, vars)
  // Compute the function and the constraints at the given xval.  The
  // function value is returned, and the constraint values are stored in
  // cval.
  let calcfc = lfunc("fmin_cobyla-calcfc", args => {
    let xval = args[2]
    let cval = args[3]
    let x_list = cobyla__vector_list(xval)
    let f = apply(fv, x_list)
    let c = apply(cv, x_list)
    // Do we really need these checks?
    if !floatp(f) {
      merr("~M: The objective function did not evaluate to a number at ~M", [
        pretty,
        cons(list1(q_mlist), x_list),
      ])
      |> ignore
    }
    if !every(v => floatp(v), cdr(c)) {
      let bad_cons : Array[Int] = []
      let mut k = 1
      for cval in cdr(c).iter() {
        if !floatp(cval) {
          bad_cons.push(k)
        }
        k = k + 1
      }
      // List the constraints that did not evaluate to a number to make it
      // easier for the user to figure out which constraints were bad.
      mformat(
        list([
          t,
          Str("~M: At the point ~M:~%"),
          pretty,
          cons(list1(q_mlist), x_list),
        ]),
      )
      |> ignore
      let msg = with_output_to_string(msg => for index in bad_cons {
        mformat(
          list([
            msg,
            Str("Constraint ~M: ~M did not evaluate to a number.~%"),
            Fix(index.to_int64()),
            nth(index, normalized_constraints),
          ]),
        )
        |> ignore
      })
      merror(Str(msg), Nil) |> ignore
    }
    // (replace cval c :start2 1)
    let a = as_array(cval)
    let mut j = 0
    for v in cdr(c).iter() {
      if j >= a.data.length() {
        break
      }
      a.data[j] = v
      j = j + 1
    }
    f
  })
  let (neval, ierr) = with_special(q_ear_calcfc, calcfc, () => {
    @cobyla.calcfc_hook.val = fn(nn, mm, xv, _f, con, co) {
      // CALCFC's arrays as Lisp vectors: X, and the section of the work
      // array that holds the constraint values.
      let xa = make_array([xv.length()], initial=Flo(0.0), elt="double-float")
      for i, d in xv {
        aset1(xa, i, Flo(d)) |> ignore
      }
      let ca = make_array([con.length() - co], initial=Flo(0.0), elt="double-float")
      for i in 0..<(con.length() - co) {
        aset1(ca, i, Flo(con[co + i])) |> ignore
      }
      let fval = cobyla_calcfc(
        Fix(nn.to_int64()),
        Fix(mm.to_int64()),
        xa,
        Nil,
        ca,
      )
      for i in 0..<(con.length() - co) {
        con[co + i] = share_f2cl__double(aref1(ca, i))
      }
      share_f2cl__double(fval)
    }
    share_f2cl__install_output()
    @cobyla.cobyla(
      n,
      m,
      x,
      share_f2cl__double(rhobeg),
      share_f2cl__double(rhoend),
      to_int(iprint),
      to_int(maxfun),
      w,
      iact,
      0,
    )
  })
  // Should we put a check here if the number of function evaluations
  // equals maxfun?  When iprint is not 0, the output from COBYLA makes it
  // clear that something bad happened.
  let xs = Collector::new()
  for d in x {
    xs.add(Flo(d))
  }
  let x_list = xs.result()
  let soln = cons(
    list1(q_mlist),
    mapcar2((var_, val) => list3(list1(q_mequal), var_, val), cdr(vars), x_list),
  )
  // The maxcv value.  See cobyla.f MPP value. MPP = M + 2, adjusted for
  // 0-indexing lisp arrays.
  let max_cv = w[m + 1]
  // Return a list off the following items:
  //  1:  The point that gives the optimum in the form var=val
  //  2:  The corresponding value of the function
  //  3:  Number of function evaluations
  //  4:  Return code
  make_mlist(
    list([
      soln,
      apply(fv, x_list),
      Fix(neval.to_int64()),
      if num_gt(Flo(max_cv), rhoend) {
        Fix(-1L)
      } else {
        Fix(ierr.to_int64())
      },
    ]),
  )
}

///|
/// `(coerce v 'list)` of a vector.
fn cobyla__vector_list(v : Value) -> Value raise {
  let c = Collector::new()
  for x in as_array(v).data {
    c.add(x)
  }
  c.result()
}

///|
fn init_share_cobyla_interface() -> Unit raise {
  share_f2cl__install_output()
}

///|
/// cobyla-package.lisp only defines the COBYLA package.
fn init_share_cobyla_package() -> Unit raise {

}

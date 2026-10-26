// Port of share/odepack/dlsode-interface.lisp: the Maxima interface to
// ODEPACK's DLSODE (translated by f2cl; the MoonBit translation is the
// package dii/maxima/odepack).
//
// The work arrays kept in the state list are Lisp arrays, as in the Lisp;
// they are copied to and from the FixedArrays DLSODE works on around each
// call.

///|
fn share_dlsode__to_doubles(v : Value) -> FixedArray[Double] raise {
  let n = length(v)
  let a : FixedArray[Double] = FixedArray::make(n, 0.0)
  for i in 0..<n {
    a[i] = share_f2cl__double(aref1(v, i))
  }
  a
}

///|
fn share_dlsode__to_ints(v : Value) -> FixedArray[Int] raise {
  let n = length(v)
  let a : FixedArray[Int] = FixedArray::make(n, 0)
  for i in 0..<n {
    a[i] = to_int(aref1(v, i))
  }
  a
}

///|
/// Make a double-float array from the elements of the list `l` (the Lisp's
/// (make-array n :element-type 'double-float :initial-contents l)).
fn share_dlsode__double_array(l : Value) -> FixedArray[Double] raise {
  let n = length(l)
  let a : FixedArray[Double] = FixedArray::make(n, 0.0)
  let mut p = l
  for i in 0..<n {
    a[i] = share_f2cl__double(car(p))
    p = cdr(p)
  }
  a
}

///|
/// Initialize for DLSODE.  This must be called before running DLSODE_STEP.
///
/// f is the list of differential equations to be solved, vars the list of
/// the independent variable and the dependent variables (in the same order
/// as the equations in f), mf the method: 10 (nonstiff Adams method, no
/// Jacobian used), 21 (stiff BDF method, user-supplied full Jacobian) or
/// 22 (stiff method, internally generated full Jacobian).  The result is a
/// state object for DLSODE_STEP that the user must not modify.
fn d_dlsode_init(f : Value, vars : Value, mf : Value) -> Value raise {
  // Verify values of mf.
  if !(mf is Fix(10L) || mf is Fix(21L) || mf is Fix(22L)) {
    merr("MF must be 10, 21, or 22", []) |> ignore
  }
  let neq = length(cdr(f))
  let mfi = to_int(mf)
  let lrw = if mfi == 10 { 20 + 16 * neq } else { 22 + 9 * neq + neq * neq }
  let rwork = make_array([lrw], initial=Flo(0.0))
  let liw = if mfi == 10 { 20 } else { 20 + neq }
  let iwork = make_array([liw], initial=Fix(0L))
  let fjac = if mfi == 21 {
    // Jacobian is needed only for mf = 21, so compute only then.
    share_f2cl__coerce_float_fun(
      meval(list3(list1(q_d_jacobian), f, cons(list1(q_mlist), cddr(vars)))),
      vars,
    )
  } else {
    Nil
  }
  // Make sure neq is consistent with the number of elements in f and vars
  if !num_eq(int(neq + 1), d_length(vars)) {
    merr("Expected ~M variables but got ~M: ~M", [
      int(neq + 1),
      d_length(vars),
      vars,
    ])
    |> ignore
  }
  mk(q_mlist, [
    mk(q_mlist, [q_d_f, share_f2cl__coerce_float_fun(f, vars)]),
    mk(q_mlist, [q_d_vars, vars]),
    mk(q_mlist, [q_d_mf, mf]),
    mk(q_mlist, [q_d_neq, int(neq)]),
    mk(q_mlist, [q_d_lrw, int(lrw)]),
    mk(q_mlist, [q_d_liw, int(liw)]),
    mk(q_mlist, [q_d_rwork, rwork]),
    mk(q_mlist, [q_d_iwork, iwork]),
    mk(q_mlist, [q_d_fjac, fjac]),
  ])
}

///|
/// Main DLSODE routine to compute each output point.  Must be called after
/// DLSODE_INIT.  See fortran/dlsode.f for the details of the parameters.
///
/// The result is [t, y, istate, info] where info lists n_steps, n_f_eval,
/// n_j_eval, method_order, len_rwork and len_iwork.
fn d_dlsode_step(
  init_y : Value,
  tt : Value,
  tout : Value,
  rtol : Value,
  atol : Value,
  istate : Value,
  state : Value,
) -> Value raise {
  let f = d_assoc(q_d_f, state)
  let vars = d_assoc(q_d_vars, state)
  let mf = d_assoc(q_d_mf, state)
  let neq = d_assoc(q_d_neq, state)
  let lrw = d_assoc(q_d_lrw, state)
  let liw = d_assoc(q_d_liw, state)
  let rwork = d_assoc(q_d_rwork, state)
  let iwork = d_assoc(q_d_iwork, state)
  let fjac = d_assoc(q_d_fjac, state)
  // Verify that we got something from state.
  if !(f.truthy() &&
    vars.truthy() &&
    mf.truthy() &&
    neq.truthy() &&
    lrw.truthy() &&
    liw.truthy() &&
    rwork.truthy() &&
    iwork.truthy()) {
    merr("State appears to be invalid", []) |> ignore
  }
  let ff = f
  let itol = if listp(atol) { 2 } else { 1 }
  let y_array = share_dlsode__double_array(cdr(d_float(init_y)))
  let fex = fn(
    _neq : FixedArray[Int],
    t_ : Double,
    y : FixedArray[Double],
    y_off : Int,
    ydot : FixedArray[Double],
    ydot_off : Int,
  ) -> Unit raise {
    let y_list = Collector::new()
    for i in y_off..<y.length() {
      y_list.add(Flo(y[i]))
    }
    let yval = apply(ff, cons(Flo(t_), y_list.result()))
    // (replace ydot (cdr yval))
    let mut p = cdr(yval)
    let mut i = ydot_off
    while i < ydot.length() && p is Cons(_) {
      ydot[i] = share_f2cl__double(car(p))
      p = cdr(p)
      i = i + 1
    }
  }
  let jex = fn(
    _neq : FixedArray[Int],
    t_ : Double,
    y : FixedArray[Double],
    _ml : Int,
    _mu : Int,
    pd : FixedArray[Double],
    pd_off : Int,
    nrpd : Int,
  ) -> Unit raise {
    let y_list = Collector::new()
    for v in y {
      y_list.add(Flo(v))
    }
    let j = apply(fjac, cons(Flo(t_), y_list.result()))
    let mut row = 1
    for r in cdr(j).iter() {
      let mut col = 1
      for c in cdr(r).iter() {
        pd[pd_off + (row - 1) + nrpd * (col - 1)] = share_f2cl__double(c)
        col = col + 1
      }
      row = row + 1
    }
  }
  let atol_array = if listp(atol) {
    share_dlsode__double_array(cdr(d_float(atol)))
  } else {
    [share_f2cl__double(d_float(atol))]
  }
  let rw = share_dlsode__to_doubles(rwork)
  let iw = share_dlsode__to_ints(iwork)
  share_f2cl__install_output()
  let (ret_tout, ret_istate) = @odepack.dlsode(
    fex,
    [to_int(neq)],
    y_array,
    share_f2cl__double(tt),
    share_f2cl__double(tout),
    itol,
    [share_f2cl__double(d_float(rtol))],
    atol_array,
    1, // itask
    to_int(istate),
    0, // iopt
    rw,
    to_int(lrw),
    iw,
    to_int(liw),
    jex,
    to_int(mf),
  )
  for i in 0..<rw.length() {
    aset1(rwork, i, Flo(rw[i])) |> ignore
  }
  for i in 0..<iw.length() {
    aset1(iwork, i, int(iw[i])) |> ignore
  }
  let ys = Collector::new()
  for v in y_array {
    ys.add(Flo(v))
  }
  list([
    list1(q_mlist),
    Flo(ret_tout),
    cons(list1(q_mlist), ys.result()),
    int(ret_istate),
    mk(q_mlist, [
      mk(q_mlist, [q_d_n_steps, aref1(iwork, 10)]),
      mk(q_mlist, [q_d_n_f_eval, aref1(iwork, 11)]),
      mk(q_mlist, [q_d_n_j_eval, aref1(iwork, 12)]),
      mk(q_mlist, [q_d_method_order, aref1(iwork, 13)]),
      mk(q_mlist, [q_d_len_rwork, aref1(iwork, 16)]),
      mk(q_mlist, [q_d_len_iwork, aref1(iwork, 17)]),
    ]),
  ])
}

///|
fn d_dlsode(
  f : Value,
  yvars : Value,
  inity : Value,
  trange : Value,
  rtol : Value,
  atol : Value,
  mf : Value,
) -> Value raise {
  let tvar = elt(trange, 1)
  let tstart = d_float(elt(trange, 2))
  let tend = d_float(elt(trange, 3))
  let tstep = d_float(elt(trange, 4))
  let vars = d_cons(tvar, yvars)
  let state = d_dlsode_init(f, vars, mf)
  let result = Collector::new()
  // (loop for tout from tstart upto tend by tstep ...)
  let mut tout = tstart
  while num_le(tout, tend) {
    let r = d_dlsode_step(inity, tstart, tout, rtol, atol, Fix(1L), state)
    if minusp(elt(r, 3)) {
      // See dlsode.f for the definitions for these values.
      let msg = match elt(r, 3) {
        Fix(-1L) => "Excess work done on this call (perhaps wrong MF"
        Fix(-2L) => "Excess accuracy requested (tolerances too small)"
        Fix(-3L) => "Illegal input detected (see printed message)"
        Fix(-4L) => "Repeated error test failures (check all inputs)"
        Fix(-5L) =>
          "Repeated convergence failures (perhaps bad Jacobian supplied or wrong choice of MF or tolerances)"
        Fix(-6L) =>
          "Error weight became zero during problem (solution component i vanished, and ATOL or ATOL(i) = 0.)"
        v =>
          raise LispError::SimpleError(
            prin1_to_string(v) + " fell through ECASE expression.",
          )
      }
      merr("Error ~M: ~M", [elt(r, 3), Str(msg)]) |> ignore
    }
    result.add(d_cons(elt(r, 1), elt(r, 2)))
    tout = num_add(tout, tstep)
  }
  cons(list1(q_mlist), result.result())
}

///|
fn init_share_dlsode_interface() -> Unit raise {
  share_f2cl__install_output()
}

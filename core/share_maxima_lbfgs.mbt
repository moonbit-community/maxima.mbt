// Port of share/lbfgs/maxima-lbfgs.lisp: the Maxima interface to the
// L-BFGS minimizer (Nocedal's LBFGS.F/MCSRCH.F, translated by f2cl; the
// MoonBit translation is the package dii/maxima/lbfgs).

///|
/// A double-float argument of an f2cl routine: the Lisp signals a TYPE-ERROR
/// for anything else.
fn share_f2cl__double(v : Value) -> Double raise {
  match v {
    Flo(d) => d
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(v) + " is not of type DOUBLE-FLOAT",
      )
  }
}

///|
/// Formatted output of the f2cl routines (Fortran unit 6) goes to Maxima's
/// standard output: f2cl-lib's LUN->STREAM caches the *STANDARD-OUTPUT* of
/// the first write in *LUN-HASH* (shared by all f2cl code) and uses that
/// stream from then on.
fn share_f2cl__install_output() -> Unit {
  @f2cl.output_hook.val = s => {
    if share_f2cl__lun6.val is Nil {
      share_f2cl__lun6.val = symval(standard_output)
    }
    write_string(s, stream=share_f2cl__lun6.val)
  }
}

///|
/// The stream cached for Fortran unit 6 (NIL until the first write).
let share_f2cl__lun6 : Ref[Value] = { val: Nil }

///|
/// COERCE-FLOAT-FUN of plot.lisp (ported in intpol.mbt).
fn share_f2cl__coerce_float_fun(expr : Value, lvars : Value) -> Value raise {
  intpol__coerce_float_fun(q_d_float, expr, [lvars])
}

///|
fn d_lbfgs(
  fom_expr : Value,
  x_list : Value,
  x_initial : Value,
  eps : Value,
  iprint_list : Value,
) -> Value raise {
  if (symbolp(fom_expr) && mfboundp(fom_expr).truthy()) ||
    (fom_expr is Cons(_) && eq(caar(fom_expr), q_lambda)) {
    merr(
      "lbfgs: figure of merit, if specified alone, cannot be a function name or lambda.",
      [],
    )
    |> ignore
  }
  let n = length(cdr(x_list))
  let m = to_int(symval(q_d_lbfgs_ncorrections))
  let nwork = n * (2 * m + 1) + 2 * m
  // +flonum-epsilon+ (SBCL's double-float-epsilon)
  let xtol = 0x3CA0000000000001L.reinterpret_as_double()
  let mut iflag = 0
  let scache : FixedArray[Double] = FixedArray::make(n, 0.0)
  let w : FixedArray[Double] = FixedArray::make(nwork, 0.0)
  let diag : FixedArray[Double] = FixedArray::make(n, 0.0)
  let g : FixedArray[Double] = FixedArray::make(n, 0.0)
  let x : FixedArray[Double] = FixedArray::make(n, 0.0)
  let iprint : FixedArray[Int] = FixedArray::make(2, 0)
  let mut return_value : Value = list1(list1(q_mlist))
  let mut f : Value = Flo(0.0)
  let mut fom_function : Value = Nil
  let mut fom_grad_function : Value = Nil
  if d_listp(fom_expr).truthy() {
    fom_function = share_f2cl__coerce_float_fun(d_first(fom_expr), x_list)
    let fom_grad_expr = mfuncall(q_d_second, list1(fom_expr))
    fom_grad_function = share_f2cl__coerce_float_fun(fom_grad_expr, x_list)
  } else {
    fom_function = share_f2cl__coerce_float_fun(fom_expr, x_list)
    // FOM-GRAD-LAMBDA: (lambda (x) (meval (list '($diff) ',FOM-expr x)))
    let fom_grad_expr = cons(
      list1(q_mlist),
      mapcar(v => meval(list3(list1(q_d_diff), fom_expr, v)), cdr(x_list)),
    )
    fom_grad_function = share_f2cl__coerce_float_fun(fom_grad_expr, x_list)
  }
  iprint[0] = to_int(nth(1, iprint_list))
  iprint[1] = to_int(nth(2, iprint_list))
  let diagco = false
  let x_initial = with_special(q_d_numer, t, () => d_float(meval(x_initial)))
  // Fill X from the initial value, skipping over the Maxima mlist marker.
  let mut xi = cdr(x_initial)
  let mut k = 0
  while k < n && xi is Cons(_) {
    x[k] = share_f2cl__double(car(xi))
    xi = cdr(xi)
    k = k + 1
  }
  @lbfgs.blockdata_lb2()
  share_f2cl__install_output()
  let nfeval_max = to_int(symval(q_d_lbfgs_nfeval_max))
  let eps_d = share_f2cl__double(eps)
  for _nfeval in 0..<nfeval_max {
    let xs = () => {
      let c = Collector::new()
      for v in x {
        c.add(Flo(v))
      }
      c.result()
    }
    f = apply(fom_function, xs())
    let g_list = apply(fom_grad_function, xs())
    if eq(t, g_list) {
      merr("Evaluation of gradient at ~M failed.  Bad initial point?~%", [
        cons(list1(q_mlist), xs()),
      ])
      |> ignore
    }
    // Copy the answer from the grad function to the g array, skipping over
    // the mlist marker.
    let mut gl = cdr(g_list)
    let mut j = 0
    while j < n && gl is Cons(_) {
      g[j] = share_f2cl__double(car(gl))
      gl = cdr(gl)
      j = j + 1
    }
    let (_, fl) = @lbfgs.lbfgs(
      n,
      m,
      x,
      share_f2cl__double(f),
      g,
      diagco,
      diag,
      iprint,
      eps_d,
      xtol,
      w,
      iflag,
      scache,
    )
    iflag = fl
    // Set return value to result of line search.  That's what's returned
    // if algorithm doesn't converge; better than nothing, I hope.
    let eqs = Collector::new()
    let mut vars = cdr(x_list)
    for v in scache {
      if !(vars is Cons(_)) {
        break
      }
      eqs.add(list3(list1(q_mequal), car(vars), Flo(v)))
      vars = cdr(vars)
    }
    return_value = cons(list1(q_mlist), eqs.result())
    if iflag == 0 {
      break
    }
  }
  return_value
}

///|
fn init_share_maxima_lbfgs() -> Unit raise {
  share_f2cl__install_output()
}

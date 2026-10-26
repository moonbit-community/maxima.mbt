// Port of share/numeric/romberg.lisp (CFFK, GJC, W. Schelter): Romberg
// numerical integration.
//
// COERCE-FLOAT-FUN (plot.lisp, not part of the port) is the private
// translation in quadpack.mbt, `quadpack__coerce_float_fun`, which
// implements it for :float-fun '$float with *PLOT-REALPART* = NIL, the
// binding $romberg makes around the call.

///|
fn share_romberg__flo(x : Value) -> Double raise {
  to_double(x)
}

///|
fn romberg_subr(
  f : Value,
  left : Value,
  right : Value,
) -> (Value, Value, Value) raise {
  let nit = to_int(symval(q_d_rombergit))
  let tt : Array[Double] = Array::make(nit, 0.0)
  let rr : Array[Double] = Array::make(nit, 0.0)
  let (a, b) = with_specials([(q_d_numer, t), (q_d__pctenumer, t)], () => {
    let a = d_float(left)
    let b = d_float(right)
    (a, b)
  })
  if !(numberp(a) && numberp(b)) {
    return (Nil, a, b)
  }
  let ad = share_romberg__flo(a)
  let bd = share_romberg__flo(b)
  let x = bd - ad
  let fa = funcall(f, [a])
  let fb = funcall(f, [b])
  let fab = funcall(f, [Flo((bd + ad) * 0.5)])
  if !numberp(fa) || !numberp(fb) || !numberp(fab) {
    return (Nil, a, b)
  }
  tt[0] = x * (share_romberg__flo(fb) + share_romberg__flo(fa)) * 0.5
  rr[0] = x * share_romberg__flo(fab)
  let mut l = 1
  let mut m = 2 * 2
  while true {
    if l == nit {
      merror(Str("`romberg' failed to converge"), Nil) |> ignore
    }
    let mut y = m.to_double()
    let z = x / y
    tt[l] = (tt[l - 1] + rr[l - 1]) * 0.5
    rr[l] = 0.0
    let mut i = 1
    while !(i > m) {
      let fzi_a = funcall(f, [Flo(z * i.to_double() + ad)])
      if !numberp(fzi_a) {
        return (Nil, a, b)
      }
      rr[l] = share_romberg__flo(fzi_a) + rr[l]
      i = i + 2
    }
    rr[l] = z * rr[l] * 2.0
    y = 0.0
    let mut k = l
    while k != 0 {
      y = y * 4.0 + 3.0
      tt[k - 1] = (tt[k] - tt[k - 1]) / y + tt[k]
      rr[k - 1] = (rr[k] - rr[k - 1]) / y + rr[k]
      k = k - 1
    }
    y = (tt[0] + rr[0]) * 0.5
    // this is the WIN condition test.
    let mut cerr = (tt[0] - rr[0]).abs()
    let win = !num_lt(symval(q_d_rombergabs), Flo(cerr)) ||
      {
        // cerr = "calculated error"
        cerr = cerr / (if y == 0.0 { 1.0 } else { y.abs() })
        !num_lt(symval(q_d_rombergtol), Flo(cerr))
      }
    if win && num_gt(Fix(l.to_int64()), symval(q_d_rombergmin)) {
      set(q_d_rombergit_used, Fix(l.to_int64())) |> ignore
      return (Flo(y), Nil, Nil)
    }
    l = l + 1
    m = m * 2
  }
  (Nil, Nil, Nil)
}

///|
fn d_romberg(args : Value) -> Value raise {
  if length(args) == 3 {
    let (result, left, right) = with_specials(
      [(q_d_numer, t), (q_d__pctenumer, t), (q_ear_plot_realpart, Nil)],
      () => romberg_subr(
        coerce_float_fun(first(args), Nil),
        second(args),
        third(args),
      ),
    )
    if numberp(result) {
      result
    } else {
      list([list1(q_d_romberg), first(args), left, right])
    }
  } else if length(args) == 4 {
    if d_constantp(second(args)).truthy() {
      merror(
        Str("romberg: variable of integration cannot be a constant; found ~M"),
        list1(second(args)),
      )
      |> ignore
    }
    let (result, left, right) = with_specials(
      [(q_d_numer, t), (q_d__pctenumer, t), (q_ear_plot_realpart, Nil)],
      () => romberg_subr(
        coerce_float_fun(first(args), list1(list2(list1(q_mlist), second(args)))),
        third(args),
        fourth(args),
      ),
    )
    if numberp(result) {
      result
    } else {
      list([list1(q_d_romberg), first(args), second(args), left, right])
    }
  } else {
    wna_err(q_d_romberg)
  }
}

///|
/// The MAYBE-RESET part of DEFMVAR: record the initial value of a
/// variable so that `reset` restores it.
fn share_romberg__defmvar_reset(var_ : Value, val : Value) -> Unit raise {
  let table = symval(q_ear_variable_initial_values)
  if hash_table_p(table) && gethash(var_, table) is Nil {
    sethash(var_, table, val) |> ignore
  }
}

///|
fn init_share_romberg() -> Unit raise {
  share_romberg__defmvar_reset(q_d_rombergit, Fix(11L))
  share_romberg__defmvar_reset(q_d_rombergmin, Fix(0L))
  share_romberg__defmvar_reset(q_d_rombergtol, Flo(0.0001))
  share_romberg__defmvar_reset(q_d_rombergabs, Flo(0.0))
  share_romberg__defmvar_reset(q_d_rombergit_used, Fix(0L))
}

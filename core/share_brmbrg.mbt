// Port of share/numeric/brmbrg.lisp: Romberg integration in bigfloat
// arithmetic (bromberg).
//
// COERCE-BFLOAT-FUN (plot.lisp) is called through `intpol__coerce_float_fun`
// with float-fun '$bfloat, the translation of COERCE-BFLOAT-FUN in
// intpol.mbt.

///|
fn fpscale(x : Value, m : Value) -> Value raise {
  if equal(car(x), int(0)) {
    x
  } else {
    list([car(x), num_add(cadr(x), m)])
  }
}

///|
fn bfmeval3(x1 : Value) -> Value raise {
  let x1 = d_bfloat(meval(x1))
  if d_bfloatp(x1).truthy() {
    cdr(x1)
  } else {
    displa(x1) |> ignore
    merror(Str("bromberg: encountered a non-bigfloat."), Nil)
  }
}

///|
fn bqeval3(f : Value, x : Value) -> Value raise {
  let bf_x = bcons(x)
  let result = funcall(f, [bf_x])
  if atom(result) {
    merror(
      Str("bromberg: integrand evaluates to a nonnumeric value at ~M"),
      list1(bf_x),
    )
  } else {
    cdr(result)
  }
}

///|
fn d_bromberg(l1 : Value) -> Value raise {
  if !(length(l1) == 4 || length(l1) == 3) {
    merror(Str("bromberg: wrong number of arguments."), Nil) |> ignore
  }
  let mut l1 = l1
  with_specials([(q_d_bfloat, t), (q_d_float2bf, t)], () => {
    let lim = cdr(d_bfloat(symval(q_d_brombergtol)))
    let limabs = cdr(d_bfloat(symval(q_d_brombergabs)))
    let nit = to_int(symval(q_d_brombergit))
    let tt : Array[Value] = Array::make(nit, Nil)
    let rr : Array[Value] = Array::make(nit, Nil)
    let zero = intofp(int(0))
    let one = intofp(int(1))
    let three = intofp(int(3))
    let fun = if length(l1) == 4 {
      if d_constantp(cadr(l1)).truthy() {
        merror(
          Str(
            "bromberg: variable of integration cannot be a constant; found ~M",
          ),
          list1(cadr(l1)),
        )
        |> ignore
      }
      let f = intpol__coerce_float_fun(q_d_bfloat, car(l1), [
        list([list1(q_mlist), cadr(l1)]),
      ])
      l1 = cdr(l1)
      f
    } else {
      intpol__coerce_float_fun(q_d_bfloat, car(l1), [])
    }
    let a = bfmeval3(cadr(l1))
    let b = bfmeval3(caddr(l1))
    let x = fpdifference(b, a)
    tt[0] = fpscale(
      fptimes_star(x, fpplus(bqeval3(fun, b), bqeval3(fun, a))),
      int(-1),
    )
    rr[0] = fptimes_star(x, bqeval3(fun, fpscale(fpplus(b, a), int(-1))))
    let mut l = 1
    let mut m = 4
    while true {
      if l == nit {
        merror(Str("bromberg: failed to converge."), Nil) |> ignore
      }
      let mut y = intofp(int(m))
      let z = fpquotient(x, y)
      tt[l] = fpscale(fpplus(tt[l - 1], rr[l - 1]), int(-1))
      rr[l] = zero
      let mut i = 1
      while !(i > m) {
        rr[l] = fpplus(bqeval3(fun, fpplus(fptimes_star(z, intofp(int(i))), a)), rr[l])
        i = i + 2
      }
      rr[l] = fpscale(fptimes_star(z, rr[l]), int(1))
      y = zero
      let mut k = l
      while k != 0 {
        y = fpplus(fpscale(y, int(2)), three)
        tt[k - 1] = fpplus(
          fpquotient(fpdifference(tt[k], tt[k - 1]), y),
          tt[k],
        )
        rr[k - 1] = fpplus(
          fpquotient(fpdifference(rr[k], rr[k - 1]), y),
          rr[k],
        )
        k = k - 1
      }
      y = fpscale(fpplus(tt[0], rr[0]), int(-1))
      let cerr = fpabs(fpdifference(tt[0], rr[0]))
      if (!fplessp(limabs, cerr).truthy() ||
        !fplessp(
          lim,
          fpquotient(
            cerr,
            if equal(y, list([int(0), int(0)])) {
              one
            } else {
              fpabs(y)
            },
          ),
        ).truthy()) &&
        num_gt(int(l), symval(q_d_brombergmin)) {
        return bcons(y)
      }
      l = l + 1
      m = m * 2
    }
    Nil
  })
}

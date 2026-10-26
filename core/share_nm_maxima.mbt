// Port of share/nelder_mead/nm-maxima.lisp: the Maxima interface
// nelder_mead(expr, vars, init, [options]) to NELDERMEAD:GRNM-OPTIMIZE.

///|
fn d_nelder_mead(
  expr : Value,
  vars : Value,
  init_ : Value,
  options : Value,
) -> Value raise {
  // COERCE-FLOAT-FUN of plot.lisp (its port lives in intpol.mbt)
  let fun = coerce_float_fun(expr, list([vars]))
  let maxima_options = cons(list1(q_mlist), options)
  let verbose = d_assoc(q_d_nm_verbose, maxima_options)
  let maxfuncalls = d_assoc(q_d_maxfuncalls, maxima_options)
  let fun1 = lfunc("nelder-mead-objective", args => {
    let arr = arg(args, 0)
    let c = Collector::new()
    for i in 0..<length(arr) {
      c.add(aref1(arr, i))
    }
    mfuncall(q_d_apply, list2(fun, cons(list2(q_mlist, q_simp), c.result())))
  })
  let n = to_int(d_length(init_))
  let init = make_array([n])
  let mut l = cdr(d_float(init_))
  for i in 0..<n {
    aset1(init, i, car(l)) |> ignore
    l = cdr(l)
  }
  let xk = neldermead_grnm_optimize(
    fun1,
    init,
    verbose~,
    max_function_calls=maxfuncalls,
  )
  let c = Collector::new()
  let mut v = cdr(vars)
  let mut i = 0
  while v.truthy() && i < length(xk) {
    c.add(list3(list2(q_mequal, q_simp), car(v), aref1(xk, i)))
    v = cdr(v)
    i = i + 1
  }
  cons(list2(q_mlist, q_simp), c.result())
}

// Port of src/desoln.lisp: desolve (Laplace transform ODE solver).

///|
fn d_desolve(eqns : Value, vars : Value) -> Value raise {
  let lvar = d_gensym()
  with_special(q_d_dispflag, Nil, () => {
    let mut eqns = eqns
    let mut vars = vars
    let mut flag = false
    if d_mapatom(vars).truthy() {
      merr(
        "desolve(<eqn>,<depvar>): dependent variable <depvar> cannot be a mapatom, found: ~M",
        [vars],
      )
      |> ignore
    }
    if !d_listp(vars).truthy() {
      eqns = list2(list1(q_mlist), eqns)
      vars = list2(list1(q_mlist), vars)
      flag = true
    }
    let mut ovar = maref1(vars, list([int(1)]))
    if !num_eq(d_length(ovar), int(1)) {
      merr("desolve: more than one independent variable: ~M", [ovar]) |> ignore
    }
    ovar = simplify(d_inpart(list2(ovar, int(1))))
    let ov = ovar
    let mut teqns = simplify(
      map1(
        list2(
          lfunc("desolve-laplace", args => simplify(
            d_laplace(arg(args, 0), ov, lvar),
          )),
          eqns,
        ),
      ),
    )
    let tvars = simplify(
      map1(
        list2(
          lfunc("desolve-laplace-noun", args => simplify(
            list4(list1(q_p_laplace), arg(args, 0), ov, lvar),
          )),
          vars,
        ),
      ),
    )
    // (let ((errcatch (cons bindlist loclist)) (ret (errset ...))) ...):
    // the ERRSET runs before ERRCATCH is rebound (parallel LET).
    let ec = cons(symval(q_bindlist), symval(q_loclist))
    let te = teqns
    let ret = match errset(() => simplify(d_solve(te, varl=tvars))) {
      Some(v) => list1(v)
      None => Nil
    }
    teqns = with_special(q_errcatch, ec, () => {
      if ret is Nil {
        errlfun1(ec) |> ignore
      }
      cons(list1(q_mlist), ret)
    })
    if like(teqns, list1(list1(q_mlist))).truthy() ||
      like(teqns, list2(list1(q_mlist), list1(list1(q_mlist)))).truthy() {
      merr("desolve: can't handle this case.", []) |> ignore
    }
    teqns = simplify(d_first(teqns))
    if !flag {
      teqns = simplify(d_first(teqns))
    }
    teqns = simplify(
      map1(
        list2(
          lfunc("desolve-ilt", args => simplify(d_ilt(arg(args, 0), lvar, ov))),
          teqns,
        ),
      ),
    )
    if flag && num_eq(d_length(tvars), int(1)) {
      maref1(teqns, list([int(1)]))
    } else {
      teqns
    }
  })
}

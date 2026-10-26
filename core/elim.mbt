// Port of src/elim.lisp: eliminate.

///|
fn d_eliminate(eqns : Value, vars : Value) -> Value raise {
  let mut sv : Value = Nil
  let mut l = d_length(eqns)
  let mut flag = false
  with_special(q_d_dispflag, Nil, () => {
    let mut eqns = eqns
    let mut vars = vars
    if !(d_listp(eqns).truthy() && d_listp(vars).truthy()) {
      merr("eliminate: arguments must both be lists.", []) |> ignore
    }
    if num_gt(d_length(vars), l) {
      merr("eliminate: more variables than equations.", []) |> ignore
    }
    if num_eq(l, int(1)) {
      merr("eliminate: can't eliminate from only one equation.", []) |> ignore
    }
    if num_eq(d_length(vars), l) {
      vars = d_reverse(vars)
      sv = maref1(vars, list([int(1)]))
      vars = d_reverse(simplify(d_rest(vars)))
      flag = true
    }
    eqns = simplify(map1(list2(getopr(q_meqhk), eqns)))
    for v in cdr(vars).iter() {
      let mut teqns = list1(list1(q_mlist))
      let mut j = int(1)
      while !(
          num_gt(j, l) || !d_freeof(list2(v, simplify(d_first(eqns)))).truthy()
        ) {
        teqns = d_cons(simplify(d_first(eqns)), teqns)
        eqns = simplify(d_rest(eqns))
        j = num_add(j, int(1))
      }
      if like(eqns, list1(list1(q_mlist))).truthy() {
        eqns = teqns
      } else {
        teqns = d_append(list2(teqns, simplify(d_rest(eqns))))
        eqns = simplify(d_first(eqns))
        l = num_sub(l, int(1))
        let mut se = list1(list1(q_mlist))
        let mut k = int(0)
        while num_lt(k, l) {
          // maxima starts indices with 1, therefore the 1+
          se = d_cons(
            simplify(
              d_resultant(eqns, maref1(teqns, list([num_add(k, int(1))])), v),
            ),
            se,
          )
          k = num_add(k, int(1))
        }
        eqns = se
      }
    }
    if flag {
      list2(
        list1(q_mlist),
        funcall(q_d_rhs, [
          simplify(
            mfuncall(
              q_d_ev,
              list2(
                simplify(
                  d_last(
                    simplify(d_solve(maref1(eqns, list([int(1)])), varl=sv)),
                  ),
                ),
                q_d_eval,
              ),
            ),
          ),
        ]),
      )
    } else {
      eqns
    }
  })
}

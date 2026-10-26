// Port of share/bernstein/bernstein.lisp (Barton Willis, 2011, 2021):
// Bernstein polynomials bernstein_poly(k,n,x), multibernstein_poly and
// bernstein_approx.

///|
/// Numerical (complex rational, float, or big float) evaluation of
/// bernstein polynomials, in the bigfloat package's generic arithmetic.
fn bf_bernstein_poly(k : Value, n : Value, x : Value) -> Value raise {
  bf_mul(
    bf_mul(bf_to(opcons(q_p_binomial, list2(n, k))), bf_expt(x, k)),
    bf_expt(bf_sub(Fix(1L), x), bf_sub(n, k)),
  )
}

///|
fn d_bernstein_poly(k : Value, n : Value, x : Value) -> Value raise {
  simplify(list4(list1(q_p_bernstein_poly), k, n, x))
}

///|
/// integrate(bernstein_poly(k,n,x),x) =
///   hypergeometric([k+1,k-n],[k+2],x)*x^(k+1)/(k+1)
fn bernstein_integral(k : Value, n : Value, x : Value) -> Value raise {
  div(
    muln_([
      opcons(q_p_binomial, list2(n, k)),
      opcons(q_mexpt, list2(x, add(list2(Fix(1L), k)))),
      opcons(
        q_p_hypergeometric,
        list3(
          opcons(q_mlist, list2(add(list2(Fix(1L), k)), sub(k, n))),
          opcons(q_mlist, list1(add(list2(Fix(2L), k)))),
          x,
        ),
      ),
    ]),
    add(list2(Fix(1L), k)),
  )
}

///|
fn bernstein_poly_simp(e : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  let fn_ = car(car(e))
  let mut e = cdr(e)
  let pop_arg = fn() raise {
    if e is Cons(_) {
      let v = car(e)
      e = cdr(e)
      simpcheck(v, z)
    } else {
      wna_err(fn_)
    }
  }
  let k = pop_arg()
  let n = pop_arg()
  let x = pop_arg()
  if e is Cons(_) {
    wna_err(fn_) |> ignore
  }
  if integerp(k) &&
    integerp(n) &&
    num_ge(k, Fix(0L)) &&
    num_ge(n, k) &&
    complex_number_p(
      x,
      ntypep=lfunc("bernstein-numberp", args => {
        let s = args[0]
        lbool(
          integerp(s) || d_ratnump(s).truthy() || floatp(s) || d_bfloatp(s).truthy(),
        )
      }),
    ).truthy() {
    maxima_to(bf_bernstein_poly(bf_to(k), bf_to(n), bf_to(x)))
  } else if zerop1(x).truthy() {
    opcons(q_p_kron_delta, list2(k, Fix(0L)))
  } else if onep1(x).truthy() {
    opcons(q_p_kron_delta, list2(k, n))
  } else if symval(q_d_bernstein_explicit).truthy() || (integerp(k) && integerp(n)) {
    if integerp(k) && integerp(n) && (num_lt(k, Fix(0L)) || num_gt(k, n)) {
      mul2(Fix(0L), x)
    } else {
      muln_([
        opcons(q_p_binomial, list2(n, k)),
        opcons(q_mexpt, list2(x, k)),
        opcons(q_mexpt, list2(sub(Fix(1L), x), sub(n, k))),
      ])
    }
  } else {
    list4(list2(fn_, q_simp), k, n, x)
  }
}

///|
fn d_bernstein_approx(e : Value, vars : Value, n : Value) -> Value raise {
  if !d_listp(vars).truthy() {
    merr("The second argument to bernstein_approx must be a list", []) |> ignore
  }
  let vars = margs(vars)
  if some(s => !d_mapatom(s).truthy(), vars) {
    merr("The second argument to bernstein_approx must be a list of atoms", [])
    |> ignore
  }
  if !integerp(n) || num_lt(n, Fix(1L)) {
    merr("The third argument to bernstein_approx must be a positive integer", [])
    |> ignore
  }
  let k = length(vars)
  let d : Array[Value] = Array::make(k, Fix(0L))
  let nn = cons(list1(q_mlist), list(Array::make(k, n)))
  let mut acc : Value = Fix(0L)
  let m = expt(num_add(n, Fix(1L)), int(k))
  let mut i : Value = Fix(0L)
  let varr = list_to_array(vars)
  while num_lt(i, m) {
    let eqs = Collector::new()
    for j in 0..<k {
      eqs.add(opcons(q_mequal, list2(varr[j], div(d[j], n))))
    }
    acc = add(
      list2(
        acc,
        mul(
          list2(
            opcons(
              q_p_multibernstein_poly,
              list3(cons(list1(q_mlist), list(d)), nn, cons(list1(q_mlist), vars)),
            ),
            d_substitute(cons(list1(q_mlist), eqs.result()), e),
          ),
        ),
      ),
    )
    let mut carry : Value = Fix(1L)
    for j in 0..<k {
      let mut x = num_add(carry, d[j])
      if num_gt(x, n) {
        x = Fix(0L)
        carry = Fix(1L)
      } else {
        carry = Fix(0L)
      }
      d[j] = x
    }
    i = num_add(i, Fix(1L))
  }
  acc
}

///|
fn d_multibernstein_poly(k : Value, n : Value, x : Value) -> Value raise {
  simplify(list4(list1(q_p_multibernstein_poly), k, n, x))
}

///|
fn multi_bernstein_poly_simp(e : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  let fn_ = car(car(e))
  let mut e = cdr(e)
  let pop_arg = fn() raise {
    if e is Cons(_) {
      let v = car(e)
      e = cdr(e)
      simpcheck(v, z)
    } else {
      wna_err(fn_)
    }
  }
  let k = pop_arg()
  let n = pop_arg()
  let x = pop_arg()
  if e is Cons(_) {
    wna_err(fn_) |> ignore
  }
  if !(d_listp(k).truthy() && d_listp(n).truthy() && d_listp(x).truthy()) ||
    !num_eq(d_length(k), d_length(n)) ||
    !num_eq(d_length(n), d_length(x)) {
    merr("Each argument to multibernstein_poly must be an equal length list", [])
    |> ignore
  }
  let acc = Collector::new()
  let mut pa = margs(k)
  let mut pb = margs(n)
  let mut pc = margs(x)
  while pa is Cons(_) && pb is Cons(_) && pc is Cons(_) {
    acc.add(opcons(q_p_bernstein_poly, list3(car(pa), car(pb), car(pc))))
    pa = cdr(pa)
    pb = cdr(pb)
    pc = cdr(pc)
  }
  muln(acc.result(), t)
}

///|
fn init_share_bernstein() -> Unit raise {
  d_load(Str("bernstein_utilities.mac")) |> ignore
  putprop(q_d_bernstein_poly, q_p_bernstein_poly, q_alias) |> ignore
  putprop(q_d_bernstein_poly, q_p_bernstein_poly, q_verb) |> ignore
  putprop(q_p_bernstein_poly, q_d_bernstein_poly, q_reversealias) |> ignore
  putprop(q_p_bernstein_poly, q_d_bernstein_poly, q_noun) |> ignore
  putprop(
    q_p_bernstein_poly,
    lfunc("bernstein-conjugate-function", args => {
      let e = args[0]
      let k = car(e)
      let n = cadr(e)
      let x = caddr(e)
      if d_featurep(k, q_d_integer).truthy() && d_featurep(n, q_d_integer).truthy() {
        opcons(q_p_bernstein_poly, list3(k, n, opcons(q_d_conjugate, list1(x))))
      } else {
        list2(
          list2(q_d_conjugate, q_simp),
          take(list1(q_p_bernstein_poly), [k, n, x]),
        )
      }
    }),
    q_conjugate_function,
  )
  |> ignore
  putprop(
    q_p_bernstein_poly,
    list4(list3(q_k, q_n, q_x), Nil, Nil, q_bernstein_integral),
    q_integral,
  )
  |> ignore
  putprop(
    q_d_bernstein_poly,
    list4(list3(q_k, q_n, q_x), Nil, Nil, q_bernstein_integral),
    q_integral,
  )
  |> ignore
  putprop(q_p_bernstein_poly, q_bernstein_poly_simp, q_operators) |> ignore
  putprop(
    q_p_bernstein_poly,
    lread(
      (
        #|((k n x)
        #| ((mtimes) ((%bernstein_poly) k n x)
        #|  ((mplus)
        #|   ((mtimes) -1 ((mqapply) (($psi array) 0) ((mplus) 1 k)))
        #|   ((mqapply) (($psi array) 0) ((mplus) 1 ((mtimes) -1 k) n))
        #|   ((mtimes) -1 ((%log) ((mplus) 1 ((mtimes) -1 x))))
        #|   ((%log) x)))
        #| ((mtimes) ((%bernstein_poly) k n x)
        #|  ((mplus)
        #|   ((mqapply) (($psi array) 0) ((mplus) 1 n))
        #|   ((mtimes) -1 ((mqapply) (($psi array) 0) ((mplus) 1 ((mtimes) -1 k) n)))
        #|   ((%log) ((mplus) 1 ((mtimes) -1 x)))))
        #| ((mtimes)
        #|  ((mplus)
        #|   ((%bernstein_poly) ((mplus) -1 k) ((mplus) -1 n) x)
        #|   ((mtimes) -1 ((%bernstein_poly) k ((mplus) -1 n) x))) n))
      ),
    ),
    q_grad,
  )
  |> ignore
  putprop(q_d_multibernstein_poly, q_p_multibernstein_poly, q_alias) |> ignore
  putprop(q_d_multibernstein_poly, q_p_multibernstein_poly, q_verb) |> ignore
  putprop(q_p_multibernstein_poly, q_d_multibernstein_poly, q_reversealias)
  |> ignore
  putprop(q_p_multibernstein_poly, q_d_multibernstein_poly, q_noun) |> ignore
  putprop(q_p_multibernstein_poly, q_multi_bernstein_poly_simp, q_operators)
  |> ignore
}

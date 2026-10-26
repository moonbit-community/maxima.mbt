// Port of src/bessel.lisp, part 3: the Struve functions H and L, $gauss
// and the top-level forms of the file.

///|
/// `(simplify (list '(op) x))`
fn bessel__simp1(op : Value, x : Value) -> Value raise {
  simplify(list2(list1(op), x))
}

///|
/// `(simplify (list '(op) x y))`
fn bessel__simp2(op : Value, x : Value, y : Value) -> Value raise {
  simplify(list3(list1(op), x, y))
}

///|
/// `(let ((index (gensumindex))) (dosum summand index 0 hi t))`
fn bessel__sum(
  summand : (Value) -> Value raise,
  hi : () -> Value raise,
) -> Value raise {
  let index = gensumindex()
  let s = summand(index)
  dosum(s, index, Fix(0L), hi(), t)
}

///|
/// The special values of struve_h and struve_l at a zero argument.
fn bessel__struve_zero(
  order : Value,
  arg : Value,
  name : String,
  give_up : () -> Value raise,
) -> Value raise {
  if eq(d_csign(add2(order, Fix(1L))), q_d_zero) {
    // http://functions.wolfram.com/03.09.03.0018.01
    if d_bfloatp(order).truthy() || d_bfloatp(arg).truthy() {
      d_bfloat(div(Fix(2L), q_d__pctpi))
    } else if floatp(order) || floatp(arg) {
      d_float(div(Fix(2L), q_d__pctpi))
    } else {
      div(Fix(2L), q_d__pctpi)
    }
  } else if eq(d_sign(add2(d_realpart(order), Fix(1L))), q_d_pos) {
    // http://functions.wolfram.com/03.09.03.0001.01
    arg
  } else if memq(
      d_sign(add2(d_realpart(order), Fix(1L))),
      list([q_d_zero, q_d_neg, q_d_nz]),
    ).truthy() {
    simp_domain_error(
      list([Str(name + ": " + name + "(~:M,~:M) is undefined."), order, arg]),
    )
  } else {
    give_up()
  }
}

///|
/// The common factor `((rat simp) 3 2)` hypergeometric of the Struve
/// functions: hypergeometric([1],[3/2,order+3/2],z).
fn bessel__struve_hyp(order : Value, z : Value) -> Value raise {
  simplify(
    list([
      list1(q_p_hypergeometric),
      list2(list1(q_mlist), Fix(1L)),
      list3(list1(q_mlist), bessel__rat(3, 2), add2(order, bessel__rat(3, 2))),
      z,
    ]),
  )
}

// ---------------------------------------------------------------------------
// Implementation of Struve H function

///|
/// (def-simplifier struve_h (order arg) ...)
fn simp__pctstruve_h(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__check_arity(form, q_p_struve_h, [bessel__q_d_order, bessel__q_d_arg])
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_struve_h), list2(order, arg)),
    form,
  )
  let half = bessel__rat(1, 2)
  if zerop1(arg).truthy() {
    // Check for special values
    bessel__struve_zero(order, arg, "struve_h", give_up)
  } else if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    // Check for numerical evaluation
    // A&S 12.1.21
    with_specials([(q_d_numer, t), (q_d_float, t)], () => d_rectform(
      d_float(
        muln_([
          d_rectform(power(arg, add2(order, Flo(1.0)))),
          d_rectform(inv(power(Flo(2.0), order))),
          inv(power(d_float(q_d__pctpi), Flo(0.5))),
          inv(bessel__simp1(q_p_gamma, add2(order, Flo(1.5)))),
          bessel__struve_hyp(order, div(mul2(arg, arg), Flo(-4.0))),
        ]),
      ),
    ))
  } else if complex_bigfloat_numerical_eval_p(list2(order, arg)).truthy() {
    // A&S 12.1.21
    let arg = d_bfloat(arg)
    let order = d_bfloat(order)
    with_special(q_d_ratprint, Nil, () => d_rectform(
      d_bfloat(
        muln_([
          d_rectform(power(arg, add2(order, Fix(1L)))),
          d_rectform(inv(power(Fix(2L), order))),
          inv(power(d_bfloat(q_d__pctpi), d_bfloat(half))),
          inv(bessel__simp1(q_p_gamma, add2(order, d_bfloat(bessel__rat(3, 2))))),
          bessel__struve_hyp(order, div(mul2(arg, arg), d_bfloat(Fix(-4L)))),
        ]),
      ),
    ))
  } else if symval(q_d_besselexpand).truthy() &&
    ratnump(order).truthy() &&
    integerp(mul2(Fix(2L), order)) {
    // Transformations and argument simplifications
    if eq(d_sign(order), q_d_pos) {
      // Expansion of Struve H for a positive half integral order.
      sratsimp(
        add2(
          muln_([
            inv(bessel__simp1(q_mfactorial, sub(order, half))),
            inv(power(q_d__pctpi, half)),
            power(div(arg, Fix(2L)), add2(order, Fix(-1L))),
            bessel__sum(
              index => muln_([
                bessel__simp2(q_d_pochhammer, half, index),
                bessel__simp2(q_d_pochhammer, sub(half, order), index),
                power(
                  muln_([Fix(-1L), arg, arg, inv(Fix(4L))]),
                  mul2(Fix(-1L), index),
                ),
              ]),
              () => sub(order, half),
            ),
          ]),
          muln_([
            power(div(Fix(2L), q_d__pctpi), half),
            power(Fix(-1L), add2(order, half)),
            inv(power(arg, half)),
            add2(
              mul2(
                bessel__simp1(
                  q_p_sin,
                  add2(muln_([half, q_d__pctpi, add2(order, half)]), arg),
                ),
                bessel__sum(
                  index => muln_([
                    power(Fix(-1L), index),
                    bessel__simp1(
                      q_mfactorial,
                      addn_([mul2(Fix(2L), index), order, bessel__rat(-1, 2)]),
                    ),
                    inv(bessel__simp1(q_mfactorial, mul2(Fix(2L), index))),
                    inv(
                      bessel__simp1(
                        q_mfactorial,
                        addn_([mul2(Fix(-2L), index), order, bessel__rat(-1, 2)]),
                      ),
                    ),
                    inv(power(mul2(Fix(2L), arg), mul2(Fix(2L), index))),
                  ]),
                  () => bessel__simp1(
                    q_d_floor,
                    div(sub(mul2(Fix(2L), order), Fix(1L)), Fix(4L)),
                  ),
                ),
              ),
              mul2(
                bessel__simp1(
                  q_p_cos,
                  add2(muln_([half, q_d__pctpi, add2(order, half)]), arg),
                ),
                bessel__sum(
                  index => muln_([
                    power(Fix(-1L), index),
                    bessel__simp1(
                      q_mfactorial,
                      addn_([mul2(Fix(2L), index), order, half]),
                    ),
                    power(
                      mul2(Fix(2L), arg),
                      mul2(Fix(-1L), add2(mul2(Fix(2L), index), Fix(1L))),
                    ),
                    inv(
                      bessel__simp1(
                        q_mfactorial,
                        add2(mul2(Fix(2L), index), Fix(1L)),
                      ),
                    ),
                    inv(
                      bessel__simp1(
                        q_mfactorial,
                        addn_([mul2(Fix(-2L), index), order, bessel__rat(-3, 2)]),
                      ),
                    ),
                  ]),
                  () => bessel__simp1(
                    q_d_floor,
                    div(sub(mul2(Fix(2L), order), Fix(3L)), Fix(4L)),
                  ),
                ),
              ),
            ),
          ]),
        ),
      )
    } else if eq(d_sign(order), q_d_neg) {
      // Expansion of Struve H for a negative half integral order.
      sratsimp(
        addn_([
          muln_([
            power(div(Fix(2L), q_d__pctpi), half),
            power(Fix(-1L), add2(order, half)),
            inv(power(arg, half)),
            add2(
              mul2(
                bessel__simp1(
                  q_p_sin,
                  add2(muln_([half, q_d__pctpi, add2(order, half)]), arg),
                ),
                bessel__sum(
                  index => muln_([
                    power(Fix(-1L), index),
                    bessel__simp1(
                      q_mfactorial,
                      addn_([mul2(Fix(2L), index), neg(order), bessel__rat(-1, 2)]),
                    ),
                    inv(bessel__simp1(q_mfactorial, mul2(Fix(2L), index))),
                    inv(
                      bessel__simp1(
                        q_mfactorial,
                        addn_([
                          mul2(Fix(-2L), index),
                          neg(order),
                          bessel__rat(-1, 2),
                        ]),
                      ),
                    ),
                    inv(power(mul2(Fix(2L), arg), mul2(Fix(2L), index))),
                  ]),
                  () => bessel__simp1(
                    q_d_floor,
                    div(add2(mul2(Fix(2L), order), Fix(1L)), Fix(-4L)),
                  ),
                ),
              ),
              mul2(
                bessel__simp1(
                  q_p_cos,
                  add2(muln_([half, q_d__pctpi, add2(order, half)]), arg),
                ),
                bessel__sum(
                  index => muln_([
                    power(Fix(-1L), index),
                    bessel__simp1(
                      q_mfactorial,
                      addn_([mul2(Fix(2L), index), neg(order), half]),
                    ),
                    power(
                      mul2(Fix(2L), arg),
                      mul2(Fix(-1L), add2(mul2(Fix(2L), index), Fix(1L))),
                    ),
                    inv(
                      bessel__simp1(
                        q_mfactorial,
                        add2(mul2(Fix(2L), index), Fix(1L)),
                      ),
                    ),
                    inv(
                      bessel__simp1(
                        q_mfactorial,
                        addn_([
                          mul2(Fix(-2L), index),
                          neg(order),
                          bessel__rat(-3, 2),
                        ]),
                      ),
                    ),
                  ]),
                  () => bessel__simp1(
                    q_d_floor,
                    div(add2(mul2(Fix(2L), order), Fix(3L)), Fix(-4L)),
                  ),
                ),
              ),
            ),
          ]),
        ]),
      )
    } else {
      Nil
    }
  } else {
    give_up()
  }
}

// ---------------------------------------------------------------------------
// Implementation of Struve L function

///|
/// `(let (($trigexpand t)) (simplify (list '(op) (sub (mul 1/2 %pi %i
/// (add order 1/2)) arg))))`
fn bessel__trig_hyp(op : Value, order : Value, arg : Value) -> Value raise {
  with_special(q_d_trigexpand, t, () => bessel__simp1(
    op,
    sub(
      muln_([
        bessel__rat(1, 2),
        q_d__pctpi,
        q_d__pcti,
        add2(order, bessel__rat(1, 2)),
      ]),
      arg,
    ),
  ))
}

///|
/// The second term of the half-integral expansions of struve_l, with
/// `nu` = abs(order) for a positive and -order for a negative order.
fn bessel__struve_l_term2(
  order : Value,
  arg : Value,
  nu : () -> Value raise,
) -> Value raise {
  let half = bessel__rat(1, 2)
  muln_([
    Fix(-1L),
    power(div(Fix(2L), q_d__pctpi), half),
    inv(power(arg, half)),
    d_exp(div(muln_([q_d__pctpi, q_d__pcti, add2(order, half)]), Fix(2L))),
    add2(
      mul2(
        bessel__trig_hyp(q_p_sinh, order, arg),
        bessel__sum(
          index => muln_([
            bessel__simp1(
              q_mfactorial,
              addn_([mul2(Fix(2L), index), nu(), bessel__rat(-1, 2)]),
            ),
            inv(bessel__simp1(q_mfactorial, mul2(Fix(2L), index))),
            inv(
              bessel__simp1(
                q_mfactorial,
                addn_([nu(), mul2(Fix(-2L), index), bessel__rat(-1, 2)]),
              ),
            ),
            inv(power(mul2(Fix(2L), arg), mul2(Fix(2L), index))),
          ]),
          () => bessel__simp1(
            q_d_floor,
            div(sub(mul2(Fix(2L), nu()), Fix(1L)), Fix(4L)),
          ),
        ),
      ),
      mul2(
        bessel__trig_hyp(q_p_cosh, order, arg),
        bessel__sum(
          index => muln_([
            bessel__simp1(
              q_mfactorial,
              addn_([mul2(Fix(2L), index), nu(), half]),
            ),
            power(mul2(Fix(2L), arg), neg(add2(mul2(Fix(2L), index), Fix(1L)))),
            inv(bessel__simp1(q_mfactorial, add2(mul2(Fix(2L), index), Fix(1L)))),
            inv(
              bessel__simp1(
                q_mfactorial,
                addn_([nu(), mul2(Fix(-2L), index), bessel__rat(-3, 2)]),
              ),
            ),
          ]),
          () => bessel__simp1(
            q_d_floor,
            div(sub(mul2(Fix(2L), nu()), Fix(3L)), Fix(4L)),
          ),
        ),
      ),
    ),
  ])
}

///|
/// (def-simplifier struve_l (order arg) ...)
fn simp__pctstruve_l(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__check_arity(form, q_p_struve_l, [bessel__q_d_order, bessel__q_d_arg])
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_struve_l), list2(order, arg)),
    form,
  )
  let half = bessel__rat(1, 2)
  if zerop1(arg).truthy() {
    // Check for special values
    bessel__struve_zero(order, arg, "struve_l", give_up)
  } else if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    // Check for numerical evaluation
    // http://functions.wolfram.com/03.10.26.0002.01
    with_specials([(q_d_numer, t), (q_d_float, t)], () => d_rectform(
      d_float(
        muln_([
          d_rectform(power(arg, add2(order, Flo(1.0)))),
          d_rectform(inv(power(Flo(2.0), order))),
          inv(power(d_float(q_d__pctpi), Flo(0.5))),
          inv(bessel__simp1(q_p_gamma, add2(order, Flo(1.5)))),
          bessel__struve_hyp(order, div(mul2(arg, arg), Flo(4.0))),
        ]),
      ),
    ))
  } else if complex_bigfloat_numerical_eval_p(list2(order, arg)).truthy() {
    // http://functions.wolfram.com/03.10.26.0002.01
    with_special(q_d_ratprint, Nil, () => d_rectform(
      d_bfloat(
        muln_([
          d_rectform(power(arg, add2(order, Fix(1L)))),
          d_rectform(inv(power(Fix(2L), order))),
          inv(power(d_bfloat(q_d__pctpi), d_bfloat(half))),
          inv(bessel__simp1(q_p_gamma, add2(order, bessel__rat(3, 2)))),
          bessel__struve_hyp(order, div(mul2(arg, arg), Fix(4L))),
        ]),
      ),
    ))
  } else if symval(q_d_besselexpand).truthy() &&
    ratnump(order).truthy() &&
    integerp(mul2(Fix(2L), order)) {
    // Transformations and argument simplifications
    if eq(d_sign(order), q_d_pos) {
      // Expansion of Struve L for a positive half integral order.
      sratsimp(
        add2(
          muln_([
            Fix(-1L),
            power(Fix(2L), sub(Fix(1L), order)),
            power(arg, sub(order, Fix(1L))),
            inv(power(q_d__pctpi, half)),
            inv(bessel__simp1(q_mfactorial, sub(order, half))),
            bessel__sum(
              index => muln_([
                bessel__simp2(q_d_pochhammer, half, index),
                bessel__simp2(q_d_pochhammer, sub(half, order), index),
                power(muln_([arg, arg, inv(Fix(4L))]), mul2(Fix(-1L), index)),
              ]),
              () => sub(order, half),
            ),
          ]),
          bessel__struve_l_term2(order, arg, () => bessel__simp1(q_mabs, order)),
        ),
      )
    } else if eq(d_sign(order), q_d_neg) {
      // Expansion of Struve L for a negative half integral order.
      sratsimp(
        addn_([bessel__struve_l_term2(order, arg, () => neg(order))]),
      )
    } else {
      Nil
    }
  } else {
    give_up()
  }
}

// ---------------------------------------------------------------------------

///|
fn d_gauss(form : Value) -> Value raise {
  format(
    t,
    "NOTE: The gauss function is superseded by random_normal in the `distrib' package.\nPerhaps you meant to enter `~a'.~%",
    [implode(mstring(cons(list1(q_d_random_normal), cdr(form))))],
  )
  |> ignore
  q_d_done
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
fn bessel__bags() -> Value {
  list([q_mlist, q_d_matrix, q_mequal])
}

///|
/// `(defgrad name args derivs...)`
fn bessel__defgrad(
  name : Value,
  args : Array[Value],
  derivs : Array[Value],
) -> Unit {
  push_special(name, q_ear_defgrad_syms) |> ignore
  setf_get(name, q_grad, cons(list(args), list(derivs))) |> ignore
}

///|
fn init_bessel() -> Unit raise {
  // Bessel J
  putprop(q_p_bessel_j, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_bessel_j, [q_d_n, q_d_x], [
    // Derivative wrt to order n. A&S 9.1.64.
    //
    // J[n](x)*log(x/2)
    //       - (x/2)^n*sum((-1)^k*psi(n+k+1)/gamma(n+k+1)*(x^2/4)^k/k!,k,0,inf)
    maxima_lit(
      "$ bessel_j(n,x)*log(x/2)-(x^n*'sum(((-1)^%k*psi[0](n+%k+1)*abs(x)^(2*%k))\n                                  /(4^%k*%k!*gamma(n+%k+1)),%k,0,inf))\n                       /2^n",
    ),
    // Derivative wrt to arg x.
    // A&S 9.1.27; changed from 9.1.30 so that taylor works on Bessel
    // functions
    maxima_lit("$ (bessel_j(n-1,x)-bessel_j(n+1,x))/2"),
  ])
  putprop(
    q_p_bessel_j,
    list([list2(q_v, q_z), Nil, q_bessel_j_integral_2]),
    q_integral,
  )
  |> ignore
  putprop(q_p_bessel_j, q_simplim_pctbessel_j, q_simplim_pctfunction)
  |> ignore

  // Bessel Y
  putprop(q_p_bessel_y, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_bessel_y, [q_d_n, q_d_x], [
    // Derivative wrt order n. A&S 9.1.65.
    //
    // cot(n*%pi)*[diff(bessel_j(n,x),n)-%pi*bessel_y(n,x)]
    //  - csc(n*%pi)*diff(bessel_j(-n,x),n)-%pi*bessel_j(n,x)
    maxima_lit(
      "$ cot(%pi*n)*('diff(bessel_j(n,x),n,1)-%pi*bessel_y(n,x))\n  -'diff(bessel_j(-n,x),n,1)*csc(%pi*n)-%pi*bessel_j(n,x)",
    ),
    // Derivative wrt to arg x. A&S 9.1.27; changed from A&S 9.1.30 to be
    // consistent with bessel_j.
    maxima_lit("$ (bessel_y(n-1,x)-bessel_y(n+1,x))/2"),
  ])
  putprop(
    q_p_bessel_y,
    list([list2(q_n, q_z), Nil, q_bessel_y_integral_2]),
    q_integral,
  )
  |> ignore
  putprop(q_p_bessel_y, q_simplim_pctbessel_y, q_simplim_pctfunction)
  |> ignore

  // Bessel I
  putprop(q_p_bessel_i, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_bessel_i, [q_d_n, q_d_x], [
    // Derivative wrt order n. A&S 9.6.42.
    //
    // I[n](x)*log(x/2)
    //   - (x/2)^n*sum(psi(n+k+1)/gamma(n+k+1)*(x^2/4)^k/k!,k,0,inf)
    maxima_lit(
      "$ bessel_i(n,x)*log(x/2)-(x^n*'sum((psi[0](n+%k+1)*abs(x)^(2*%k))\n                                       /(4^%k*%k!*gamma(n+%k+1)),%k,0,inf))\n  /2^n",
    ),
    // Derivative wrt to x. A&S 9.6.29.
    maxima_lit("$ (bessel_i(n+1,x)+bessel_i(n-1,x))/2"),
  ])
  putprop(
    q_p_bessel_i,
    list([list2(q_v, q_z), Nil, q_bessel_i_integral_2]),
    q_integral,
  )
  |> ignore
  putprop(q_p_bessel_i, q_simplim_pctbessel_i, q_simplim_pctfunction)
  |> ignore

  // Bessel K
  putprop(q_p_bessel_k, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_bessel_k, [q_d_n, q_d_x], [
    // Derivativer wrt order n. A&S 9.6.43.
    //
    // %pi/2*csc(n*%pi)*['diff(bessel_i(-n,x),n)-'diff(bessel_i(n,x),n)]
    //    - %pi*cot(n*%pi)*bessel_k(n,x)
    maxima_lit(
      "$ (%pi*csc(%pi*n)*('diff(bessel_i(-n,x),n,1)-'diff(bessel_i(n,x),n,1)))/2\n  -%pi*bessel_k(n,x)*cot(%pi*n)",
    ),
    // Derivative wrt to x. A&S 9.6.29.
    maxima_lit("$ -((bessel_k(n+1,x)+bessel_k(n-1,x))/2)"),
  ])
  putprop(
    q_p_bessel_k,
    list([list2(q_n, q_z), Nil, q_bessel_k_integral_2]),
    q_integral,
  )
  |> ignore
  putprop(q_p_bessel_k, q_simplim_pctbessel_k, q_simplim_pctfunction)
  |> ignore

  // Put the risplit-function for Bessel J, I, K and Y on the property list
  putprop(q_p_bessel_j, q_risplit_bessel_j_or_i, q_risplit_function) |> ignore
  putprop(q_p_bessel_i, q_risplit_bessel_j_or_i, q_risplit_function) |> ignore
  putprop(q_p_bessel_k, q_risplit_bessel_k_or_y, q_risplit_function) |> ignore
  putprop(q_p_bessel_y, q_risplit_bessel_k_or_y, q_risplit_function) |> ignore

  // Hankel 1 and Hankel 2
  putprop(q_p_hankel_1, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_hankel_1, [q_d_n, q_d_x], [
    // wrt n
    Nil,
    // Derivative wrt arg x. A&S 9.1.27.
    maxima_lit("$ (hankel_1(n-1,x)-hankel_1(n+1,x))/2"),
  ])
  putprop(q_p_hankel_2, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_hankel_2, [q_d_n, q_d_x], [
    // wrt n
    Nil,
    // Derivative wrt arg x. A&S 9.1.27.
    maxima_lit("$ (hankel_2(n-1,x)-hankel_2(n+1,x))/2"),
  ])

  // Struve H and Struve L
  putprop(q_p_struve_h, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_struve_h, [q_d_v, q_d_z], [
    // wrt v
    Nil,
    // Derivative wrt arg z. A&S 12.1.10.
    maxima_lit(
      "$ (z^v/(2^v*sqrt(%pi)*gamma(v+3/2))-struve_h(v+1,z)+struve_h(v-1,z))/2",
    ),
  ])
  putprop(q_p_struve_l, bessel__bags(), q_distribute_u_over) |> ignore
  bessel__defgrad(q_p_struve_l, [q_d_v, q_d_z], [
    // wrt v
    Nil,
    // Derivative wrt arg z. A&S 12.2.5.
    maxima_lit(
      "$ (z^v/(2^v*sqrt(%pi)*gamma(v+3/2))+struve_l(v+1,z)+struve_l(v-1,z))/2",
    ),
  ])
}

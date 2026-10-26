// Port of src/logarc.lisp: logarithmic form of inverse-trig and trig
// functions.

///|
fn d_logarc(exp_ : Value) -> Value raise {
  if atom(exp_) {
    exp_
  } else if arcp(caar(exp_)).truthy() {
    logarc(caar(exp_), d_logarc(cadr(exp_)))
  } else if eq(caar(exp_), q_p_atan2) {
    logarc(q_p_atan2, list2(d_logarc(second(exp_)), d_logarc(third(exp_))))
  } else {
    recur_apply(q_d_logarc, exp_)
  }
}

///|
/// Gives the logarithmic form of arc trig and hyperbolic functions
fn logarc(f : Value, x : Value) -> Value raise {
  let i = q_d__pcti
  let log_ = list1(q_p_log)
  if eq(f, q_p_acos) {
    // -%i * log(x + %i*sqrt(1-x^2))
    muln_([
      Fix(-1L),
      i,
      take(log_, [
        add2(x, mul2(i, root(sub(Fix(1L), power(x, Fix(2L))), Fix(2L)))),
      ]),
    ])
  } else if eq(f, q_p_asin) {
    // -%i * log(sqrt(1-x^2)+%i*x)
    muln_([
      Fix(-1L),
      i,
      take(log_, [
        add2(mul2(i, x), root(sub(Fix(1L), power(x, Fix(2L))), Fix(2L))),
      ]),
    ])
  } else if eq(f, q_p_atan) {
    // (log(1 + %i*x) - log(1 - %i*x)) /(2 %i)
    div(
      sub(
        take(log_, [add2(Fix(1L), mul2(i, x))]),
        take(log_, [sub(Fix(1L), mul2(i, x))]),
      ),
      mul2(Fix(2L), i),
    )
  } else if eq(f, q_p_atan2) {
    // atan2(y,x) = -%i*log((x + %i*y)/sqrt(x^2+y^2))
    let y = car(x)
    let x = cadr(x)
    muln_([
      Fix(-1L),
      i,
      take(log_, [
        div(add2(x, mul2(i, y)), root(add2(mul2(x, x), mul2(y, y)), Fix(2L))),
      ]),
    ])
  } else if eq(f, q_p_asinh) {
    // log(sqrt(x^2+1)+x)
    take(log_, [add2(x, root(add2(Fix(1L), power(x, Fix(2L))), Fix(2L)))])
  } else if eq(f, q_p_acosh) {
    // log(x+sqrt(x-1)*sqrt(x+1))
    take(log_, [
      add2(
        x,
        mul2(
          root(add2(x, Fix(-1L)), Fix(2L)),
          root(add2(x, Fix(1L)), Fix(2L)),
        ),
      ),
    ])
  } else if eq(f, q_p_atanh) {
    // (log(x+1)-log(1-x))/2
    div(
      sub(take(log_, [add2(Fix(1L), x)]), take(log_, [sub(Fix(1L), x)])),
      Fix(2L),
    )
  } else if eq(f, q_p_acot) && zerop1(x).truthy() {
    // acot(0) and acoth(0) are defined, but the forms below would divide
    // by 0.
    div(q_d__pctpi, Fix(2L))
  } else if eq(f, q_p_acoth) && zerop1(x).truthy() {
    div(mul2(i, q_d__pctpi), Fix(-2L))
  } else if memq(
      f,
      list([q_p_asec, q_p_acsc, q_p_acot, q_p_asech, q_p_acsch, q_p_acoth]),
    ).truthy() {
    // asec(x) = acos(1/x), and etc.
    logarc(zl_get(zl_get(get(f, q_d_inverse), q_recip), q_d_inverse), inv(x))
  } else {
    merr("LOGARC: unrecognized argument: ~M", [f])
  }
}

///|
/// Conditionally apply a logarc transformation to operators that have the
/// arcp property but are *not* members of the list `l`. Note: %atan2 is
/// not converted.
fn partial_logarc(e : Value, l : Value) -> Value raise {
  if atom(e) {
    e
  } else if arcp(caar(e)).truthy() && member(caar(e), l) is Nil {
    logarc(caar(e), partial_logarc(cadr(e), l))
  } else {
    recur_apply(
      lfunc("partial-logarc-lambda", args => partial_logarc(arg(args, 0), l)),
      e,
    )
  }
}

///|
/// No top-level forms.
fn init_logarc() -> Unit raise {
  ()
}

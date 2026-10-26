// Port of src/halfangle.lisp: half-angle simplification, called from trigi
// and trigo.

///|
fn halfangle(f : Value, a : Value) -> Value raise {
  if mtimesp(a).truthy() &&
    ratnump(cadr(a)).truthy() &&
    equal(caddr(cadr(a)), Fix(2L)) {
    halfangleaux(f, mul2(Fix(2L), a))
  } else {
    Nil
  }
}

///|
/// f=function; a=twice argument
fn halfangleaux(f : Value, a : Value) -> Value raise {
  let sw = memq(f, list([q_p_cos, q_p_cot, q_p_coth, q_p_cosh]))
  let half = symval(q_n1_sl_sl2)
  if eq(f, q_p_sin) || eq(f, q_p_cos) {
    mul2(
      halfangleaux_factor(f, a),
      power(
        div(add2(Fix(1L), porm(sw, take(list1(q_p_cos), [a]))), Fix(2L)),
        half,
      ),
    )
  } else if eq(f, q_p_tan) || eq(f, q_p_cot) {
    div(
      add2(Fix(1L), porm(sw, take(list1(q_p_cos), [a]))),
      take(list1(q_p_sin), [a]),
    )
  } else if eq(f, q_p_sinh) || eq(f, q_p_cosh) {
    mul2(
      halfangleaux_factor(f, a),
      power(
        div(add2(take(list1(q_p_cosh), [a]), porm(sw, Fix(1L))), Fix(2L)),
        half,
      ),
    )
  } else if eq(f, q_p_tanh) || eq(f, q_p_coth) {
    div(
      add2(take(list1(q_p_cosh), [a]), porm(sw, Fix(1L))),
      take(list1(q_p_sinh), [a]),
    )
  } else if memq(f, list([q_p_sec, q_p_csc, q_p_sech, q_p_csch])).truthy() {
    inv(halfangleaux(get(f, q_recip), a))
  } else {
    Nil
  }
}

///|
fn halfangleaux_factor(f : Value, a : Value) -> Value raise {
  let floor_ = fn(x : Value) -> Value raise {
    simplify(list2(list1(q_d_floor), x))
  }
  let unit_step = fn(x : Value) -> Value raise {
    simplify(list2(list1(q_d_unit_step), x))
  }
  if eq(f, q_p_sin) || eq(f, q_p_cos) {
    let arg = div(
      if eq(f, q_p_sin) {
        d_realpart(a)
      } else {
        add2(d_realpart(a), q_d__pctpi)
      },
      mul2(Fix(2L), q_d__pctpi),
    )
    mul2(
      power(Fix(-1L), floor_(arg)),
      sub(
        Fix(1L),
        mul2(
          add2(
            Fix(1L),
            power(Fix(-1L), add2(floor_(arg), floor_(mul2(Fix(-1L), arg)))),
          ),
          unit_step(mul2(Fix(-1L), d_imagpart(a))),
        ),
      ),
    )
  } else if eq(f, q_p_sinh) || eq(f, q_p_cosh) {
    let arg = div(add2(d_imagpart(a), q_d__pctpi), mul2(Fix(2L), q_d__pctpi))
    let fac = if eq(f, q_p_sinh) {
      div(power(power(a, Fix(2L)), div(Fix(1L), Fix(2L))), a)
    } else {
      Fix(1L)
    }
    muln_([
      fac,
      power(Fix(-1L), floor_(arg)),
      sub(
        Fix(1L),
        mul2(
          add2(
            Fix(1L),
            power(Fix(-1L), add2(floor_(arg), floor_(mul2(Fix(-1L), arg)))),
          ),
          unit_step(d_realpart(a)),
        ),
      ),
    ])
  } else {
    Fix(1L)
  }
}

///|
/// No top-level forms.
fn init_halfangle() -> Unit raise {
  ()
}

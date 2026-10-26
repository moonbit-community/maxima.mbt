// Port of share/numeric/expense.lisp: EXPENSE, the cost of computing an
// expression in terms of scalar floating point additions on the CRAY-1
// (needed by share/simplification/rducon.lisp).

///|
/// The (DECLARE (FIXNUM ...)) of MULTIPLIES-IN-NTH-POWER: SBCL checks the
/// type of each assigned value.
fn expense__fixnum(x : Value) -> Value raise {
  match x {
    Fix(n) if n >= -4611686018427387904L && n <= 4611686018427387903L => x
    _ => raise type_error(x, "FIXNUM")
  }
}

///|
fn multiplies_in_nth_power(nth_ : Value) -> Value raise {
  if num_lt(nth_, Fix(2L)) {
    return Fix(0L)
  }
  let slow = bignump(nth_)
  let cfp = symval(q_d_cost_float_power)
  let mut exin = expense__fixnum(nth_)
  let mut rem : Value = Fix(0L)
  let mut in_cut : Value = Fix(-2L)
  let mut pw2 : Value = Fix(1L)
  while !(zerop(exin) || num_gt(in_cut, cfp)) {
    rem = expense__fixnum(
      if slow {
        num_rem(num_truncate(exin, b=pw2).0, Fix(2L))
      } else {
        num_div(num_truncate(exin, b=pw2).0, Fix(2L))
      },
    )
    let exin1 = num_sub(exin, num_mul(pw2, rem))
    let in_cut1 = num_add(num_add(Fix(1L), in_cut), rem)
    let pw21 = num_add(pw2, pw2)
    exin = expense__fixnum(exin1)
    in_cut = expense__fixnum(in_cut1)
    pw2 = expense__fixnum(pw21)
  }
  if num_lt(in_cut, cfp) {
    in_cut
  } else {
    cfp
  }
}

///|
/// macro EVAL&REDUCE (courtesy of gjc): `(reduce oper (mapcar eval list))`
/// evaluated left to right.
fn eval_ampreduce(oper : Value, eval : Value, list_ : Value) -> Value raise {
  let mut temp = list_
  let mut val = funcall(eval, [car(temp)])
  temp = cdr(temp)
  while temp.truthy() {
    val = funcall(oper, [val, funcall(eval, [car(temp)])])
    temp = cdr(temp)
  }
  val
}

///|
/// `(eval&reduce '+ '$expense l)`
fn expense__sum(l : Value) -> Value raise {
  let mut temp = l
  let mut val = d_expense(car(temp))
  temp = cdr(temp)
  while temp.truthy() {
    val = num_add(val, d_expense(car(temp)))
    temp = cdr(temp)
  }
  val
}

///|
fn d_expense(x : Value) -> Value raise {
  if d_mapatom(x).truthy() {
    return Fix(0L)
  }
  let opr = caar(x)
  if eq(opr, q_mplus) || eq(opr, q_mtimes) {
    let cl = num_add(int(length(x) - 2), expense__sum(cdr(x)))
    if eq(opr, q_mtimes) && equal(Fix(-1L), cadr(x)) {
      num_sub(cl, Fix(1L))
    } else {
      cl
    }
  } else if eq(opr, q_mexpt) {
    let expon = caddr(x)
    num_add(
      d_expense(cadr(x)),
      if integerp(expon) {
        if num_lt(expon, Fix(0L)) {
          num_add(
            symval(q_d_cost_reciprocal),
            multiplies_in_nth_power(num_neg(expon)),
          )
        } else {
          multiplies_in_nth_power(expon)
        }
      } else {
        num_add(
          num_add(d_expense(expon), symval(q_d_cost_exp)),
          if eq(cadr(x), q_d__pcte) {
            Fix(0L)
          } else {
            symval(q_d_cost_sin_cos_log)
          },
        )
      },
    )
  } else if eq(opr, q_mminus) {
    d_expense(cadr(x))
  } else if eq(opr, q_p_sqrt) {
    num_add(symval(q_d_cost_sqrt), d_expense(cadr(x)))
  } else if memq(opr, symval(q_d_merge_ops)).truthy() {
    num_add(
      num_add(num_add(Fix(4L), d_expense(cadr(x))), d_expense(caddr(x))),
      d_expense(cadddr(x)),
    )
  } else if eq(opr, q_mquotient) {
    if eql(cadr(x), Fix(1L)) || eql(cadr(x), Fix(-1L)) {
      num_add(symval(q_d_cost_reciprocal), d_expense(caddr(x)))
    } else {
      num_add(
        num_mul(symval(q_d_cost_divide), int(length(x) - 2)),
        expense__sum(cdr(x)),
      )
    }
  } else if eq(opr, q_p_acos) ||
    eq(opr, q_p_asin) ||
    eq(opr, q_p_atan) ||
    eq(opr, q_p_cosh) ||
    eq(opr, q_p_sinh) ||
    eq(opr, q_p_tan) ||
    eq(opr, q_p_tanh) {
    num_add(symval(q_d_cost_hyper_trig), d_expense(cadr(x)))
  } else if eq(opr, q_p_cos) || eq(opr, q_p_log) || eq(opr, q_p_sin) {
    num_add(symval(q_d_cost_sin_cos_log), d_expense(cadr(x)))
  } else if eq(opr, q_p_atan2) {
    num_add(
      num_add(symval(q_d_cost_hyper_trig), d_expense(cadr(x))),
      d_expense(caddr(x)),
    )
  } else {
    mformat(
      list3(Nil, Str("Beware: ~M is not in function base of EXPENSE~%"), opr),
    )
    |> ignore
    expense__sum(cdr(x))
  }
}

///|
/// Top-level forms of expense.lisp: the DEFMVARs with computed values.
fn init_share_expense() -> Unit raise {
  macsyma_module(sym("expens"), Nil) |> ignore
  if !boundp(q_d_cost_float_power) {
    set(
      q_d_cost_float_power,
      num_add(symval(q_d_cost_exp), symval(q_d_cost_sin_cos_log)),
    )
    |> ignore
  }
  if !boundp(q_d_merge_ops) {
    set(q_d_merge_ops, list3(list2(q_mlist, q_simp), q_d_cvmgp, q_d_cvmgt))
    |> ignore
  }
}

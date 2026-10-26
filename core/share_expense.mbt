// Port of share/numeric/expense.lisp (1984, Regents of the University of
// California): EXPENSE estimates the cost of evaluating an expression in
// terms of scalar floating point additions on the CRAY-1.

///|
/// The fixnum declaration of a DO variable: SBCL checks it on every
/// binding and assignment.
fn share_expense__fixnum(v : Value) -> Value raise {
  match v {
    Fix(n) if n >= -4611686018427387904L && n <= 4611686018427387903L => v
    _ => raise type_error(v, "fixnum")
  }
}

///|
fn multiplies_in_nth_power(nth_ : Value) -> Value raise {
  if num_lt(nth_, int(2)) {
    return int(0)
  }
  let slow = bignump(nth_)
  let cost_float_power = symval(q_d_cost_float_power)
  let mut exin = share_expense__fixnum(nth_)
  let mut rem = share_expense__fixnum(int(0))
  let mut in_cut = share_expense__fixnum(int(-2))
  let mut pw2 = share_expense__fixnum(int(1))
  while !(zerop(exin) || num_gt(in_cut, cost_float_power)) {
    rem = share_expense__fixnum(
      if slow {
        num_rem(truncate1(num_div(exin, pw2)), int(2))
      } else {
        num_div(num_truncate(exin, b=pw2).0, int(2))
      },
    )
    // parallel step of the DO variables
    let exin1 = num_sub(exin, num_mul(pw2, rem))
    let in_cut1 = num_add(num_add(int(1), in_cut), rem)
    let pw21 = num_add(pw2, pw2)
    exin = share_expense__fixnum(exin1)
    in_cut = share_expense__fixnum(in_cut1)
    pw2 = share_expense__fixnum(pw21)
  }
  if num_lt(in_cut, cost_float_power) {
    in_cut
  } else {
    cost_float_power
  }
}

///|
/// The macro EVAL&REDUCE (courtesy of gjc): reduce the list LIST_ with
/// OPER after applying EVAL to each element.
fn eval_ampreduce(oper : Value, eval : Value, list_ : Value) -> Value raise {
  let mut temp = list_
  let mut val = funcall(eval, [car(temp)])
  temp = cdr(temp)
  while temp.truthy() {
    let e = car(temp)
    temp = cdr(temp)
    val = funcall(oper, [val, funcall(eval, [e])])
  }
  val
}

///|
/// (eval&reduce '+ '$expense l)
fn share_expense__sum_expense(l : Value) -> Value raise {
  let mut temp = l
  let mut val = d_expense(car(temp))
  temp = cdr(temp)
  while temp.truthy() {
    let e = car(temp)
    temp = cdr(temp)
    val = num_add(val, d_expense(e))
  }
  val
}

///|
fn d_expense(x : Value) -> Value raise {
  if d_mapatom(x).truthy() {
    return int(0)
  }
  let opr = caar(x)
  if eq(opr, q_mplus) || eq(opr, q_mtimes) {
    let cl = num_add(int(length(x) - 2), share_expense__sum_expense(cdr(x)))
    if eq(opr, q_mtimes) && equal(int(-1), cadr(x)) {
      one_minus(cl)
    } else {
      cl
    }
  } else if eq(opr, q_mexpt) {
    let expon = caddr(x)
    num_add(
      d_expense(cadr(x)),
      if integerp(expon) {
        if num_lt(expon, int(0)) {
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
            int(0)
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
      num_add(num_add(int(4), d_expense(cadr(x))), d_expense(caddr(x))),
      d_expense(cadddr(x)),
    )
  } else if eq(opr, q_mquotient) {
    if member(cadr(x), list([int(1), int(-1)])).truthy() {
      num_add(symval(q_d_cost_reciprocal), d_expense(caddr(x)))
    } else {
      num_add(
        num_mul(symval(q_d_cost_divide), int(length(x) - 2)),
        share_expense__sum_expense(cdr(x)),
      )
    }
  } else if memq(
      opr,
      list([q_p_acos, q_p_asin, q_p_atan, q_p_cosh, q_p_sinh, q_p_tan, q_p_tanh]),
    ).truthy() {
    num_add(symval(q_d_cost_hyper_trig), d_expense(cadr(x)))
  } else if memq(opr, list([q_p_cos, q_p_log, q_p_sin])).truthy() {
    num_add(symval(q_d_cost_sin_cos_log), d_expense(cadr(x)))
  } else if eq(opr, q_p_atan2) {
    num_add(
      num_add(symval(q_d_cost_hyper_trig), d_expense(cadr(x))),
      d_expense(caddr(x)),
    )
  } else {
    mformat(
      list([Nil, Str("Beware: ~M is not in function base of EXPENSE~%"), opr]),
    )
    |> ignore
    share_expense__sum_expense(cdr(x))
  }
}

///|
fn init_share_expense() -> Unit raise {
  defvar_init(
    q_d_cost_float_power,
    num_add(symval(q_d_cost_exp), symval(q_d_cost_sin_cos_log)),
  )
}

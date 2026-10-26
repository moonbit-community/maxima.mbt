// Port of share/simplification/rducon.lisp: REDUCE_CONSTS, which replaces
// constant subexpressions by generated constants (recorded in CONST_EQNS).

///|
/// `(,.l ,x)`: destructively append x to the list l.
fn rducon__snoc(l : Value, x : Value) -> Value raise {
  nconc(l, list1(x))
}

///|
/// macro MINUS-CONSTANTP
fn minus_constantp(x : Value) -> Value raise {
  lbool(
    eq(caar(x), q_mtimes) && length(x) == 3 && equal(cadr(x), Fix(-1L)),
  )
}

///|
fn query_const_table(x : Value) -> Value raise {
  for e in cdr(symval(q_d_const_eqns)).iter() {
    if alike1(caddr(e), x).truthy() {
      return cadr(e)
    }
  }
  Nil
}

///|
fn new_name(default_name : Value) -> Value raise {
  let name = if default_name.truthy() {
    default_name
  } else {
    let n = implode(
      nconc(
        exploden(symval(q_d_const_prefix)),
        exploden(symval(q_d_const_counter)),
      ),
    )
    set(q_d_const_counter, num_add(symval(q_d_const_counter), Fix(1L)))
    |> ignore
    n
  }
  mfuncall(q_d_declare, list2(name, q_d_constant)) |> ignore
  name
}

///|
fn log_const(exp_ : Value, name : Value) -> Value raise {
  let inconst = new_name(name)
  set(
    q_d_const_eqns,
    rducon__snoc(
      symval(q_d_const_eqns),
      list3(list2(q_mequal, q_simp), inconst, exp_),
    ),
  )
  |> ignore
  inconst
}

///|
fn obtain_constant(key : Value, curr_const : Value) -> Value raise {
  let mut inkey = key
  let found = query_const_table(key)
  if found.truthy() {
    return found
  }
  let mut pursue = cdr(symval(q_d_const_eqns))
  let mut pointer : Value = Nil
  let mut hold : Value = Nil
  let mut op = ""
  let mut expense = d_expense(key)
  let negative = mul2(Fix(-1L), key)
  let sum_q = mplusp(key).truthy()
  while pursue.truthy() {
    let rhs = caddar(pursue)
    if alike1(negative, rhs).truthy() {
      return mul2(Fix(-1L), cadar(pursue))
    }
    let mut done = false
    if sum_q && mplusp(rhs).truthy() {
      let trial = sub(key, rhs)
      let trial_2 = sub(negative, rhs)
      let estim = num_add(d_expense(trial), Fix(1L))
      let estim_2 = num_add(d_expense(trial_2), Fix(1L))
      if num_lt(estim, estim_2) {
        if num_lt(estim, expense) {
          pointer = pursue
          op = "sum"
          expense = estim
          hold = trial
          done = hold.truthy()
        }
      } else if num_lt(estim_2, expense) {
        pointer = pursue
        op = "neg"
        expense = estim_2
        hold = trial_2
        done = hold.truthy()
      }
    }
    if !done {
      let trial = div(key, rhs)
      let estim = num_add(d_expense(trial), Fix(1L))
      if num_lt(estim, expense) {
        pointer = pursue
        op = "prod"
        expense = estim
        hold = trial
      }
    }
    pursue = cdr(pursue)
  }
  if pointer.truthy() {
    inkey = match op {
      "sum" => add2(cadar(pointer), hold)
      "neg" => mul2(Fix(-1L), add2(cadar(pointer), hold))
      _ => mul2(cadar(pointer), hold)
    }
    if inkey.truthy() {
      let minkey = mul2(Fix(-1L), inkey)
      for e in cdr(symval(q_d_const_eqns)).iter() {
        let exp = caddr(e)
        let lab = cadr(e)
        if alike1(exp, inkey).truthy() {
          return lab
        } else if alike1(exp, minkey).truthy() {
          return mul2(Fix(-1L), lab)
        }
      }
    }
  }
  log_const(inkey, curr_const)
}

///|
fn find_constant(x : Value) -> Value raise {
  if symbolp(x) && d_constantp(x).truthy() {
    x
  } else if mtimesp(x).truthy() {
    let mut fcon = x
    while cdr(fcon).truthy() {
      let qcon = cadr(fcon)
      if symbolp(qcon) && d_constantp(qcon).truthy() {
        return qcon
      }
      fcon = cdr(fcon)
    }
    Nil
  } else {
    Nil
  }
}

///|
/// The power clause of REDUCE-CONSTANTS: X is a constant power; look for a
/// power of the same base in CONST_EQNS.
fn rducon__reduce_power(x : Value, newconst : Value) -> Value raise {
  let xexpon = caddr(x)
  let xbase = cadr(x)
  let mut p = cdr(symval(q_d_const_eqns))
  let nstate = integerp(xexpon)
  let mut follow = symval(q_d_const_eqns)
  while p.truthy() {
    let obj = caddar(p)
    if mexptp(obj).truthy() && alike1(xbase, cadr(obj)).truthy() {
      let inquir_expon = caddr(obj)
      let both_fix = nstate && integerp(inquir_expon)
      let dif = if both_fix {
        num_sub(xexpon, inquir_expon)
      } else {
        sub(xexpon, inquir_expon)
      }
      let gcd = if both_fix {
        num_gcd(xexpon, inquir_expon)
      } else {
        d_gcd(xexpon, inquir_expon, Nil)
      }
      if integerp(dif) && equal(Fix(1L), dif) {
        let new_exp = mul2(cadar(p), xbase)
        let q = query_const_table(new_exp)
        return if q.truthy() { q } else { log_const(new_exp, newconst) }
      } else if integerp(dif) && equal(Fix(-1L), dif) {
        let inc = new_name(newconst)
        rplaca(cddar(p), mul2(inc, xbase)) |> ignore
        rplacd(follow, append(list1(list3(list2(q_mequal, q_simp), inc, x)), p))
        |> ignore
        return inc
      } else if !(integerp(gcd) && equal(gcd, Fix(1L))) {
        let pw1 = if both_fix {
          num_truncate(xexpon, b=gcd).0
        } else {
          div(xexpon, gcd)
        }
        let pw2 = if both_fix {
          num_truncate(inquir_expon, b=gcd).0
        } else {
          div(inquir_expon, gcd)
        }
        if integerp(pw2) && equal(pw2, Fix(1L)) {
          let new_exp = power(cadar(p), pw1)
          let q = query_const_table(new_exp)
          return if q.truthy() { q } else { log_const(new_exp, newconst) }
        } else if integerp(pw1) && equal(pw1, Fix(1L)) {
          let inc = new_name(newconst)
          rplaca(cddar(p), power(inc, pw2)) |> ignore
          rplacd(
            follow,
            append(list1(list3(list2(q_mequal, q_simp), inc, x)), p),
          )
          |> ignore
          return inc
        } else {
          let inc = new_name(Nil)
          rplaca(cddar(p), power(inc, pw2)) |> ignore
          rplacd(
            follow,
            append(
              list1(list3(list2(q_mequal, q_simp), inc, power(xbase, gcd))),
              p,
            ),
          )
          |> ignore
          return log_const(power(inc, pw1), newconst)
        }
      }
    }
    follow = p
    p = cdr(p)
  }
  Nil
}

///|
fn reduce_constants(x : Value, newconst? : Value = Nil) -> Value raise {
  if d_mapatom(x).truthy() ||
    (
      eq(caar(x), q_mtimes) &&
      equal(cadr(x), Fix(-1L)) &&
      d_mapatom(caddr(x)).truthy() &&
      cdddr(x) is Nil
    ) {
    return x
  }
  let q = query_const_table(x)
  if q.truthy() {
    return q
  }
  if eq(caar(x), q_mexpt) && d_constantp(x).truthy() {
    let r = rducon__reduce_power(x, newconst)
    if r.truthy() {
      return r
    }
  }
  if d_constantp(x).truthy() {
    return obtain_constant(x, newconst)
  }
  let opr = caar(x)
  if eq(opr, q_mtimes) || eq(opr, q_mplus) {
    let product = eq(opr, q_mtimes)
    let negative = product && equal(cadr(x), Fix(-1L))
    if negative && cdddr(x) is Nil {
      let new_q = query_const_table(caddr(x))
      if new_q.truthy() {
        let r = mul2(Fix(-1L), new_q)
        if r.truthy() {
          return r
        }
      }
    }
    let mut next = cdr(x)
    let mut itot = 0
    let mut new : Value = Nil
    let mut non_constants : Value = Nil
    let separate = fn(next : Value) raise {
      let mut seplist = cdr(x)
      while !physical_equal_value(seplist, next) {
        let element = car(seplist)
        if d_constantp(element).truthy() {
          new = rducon__snoc(new, element)
        } else {
          non_constants = rducon__snoc(non_constants, element)
        }
        seplist = cdr(seplist)
      }
    }
    while next.truthy() {
      let exam = car(next)
      let result = reduce_constants(exam)
      if physical_equal_value(exam, result) {
        if d_constantp(exam).truthy() {
          itot = itot + 1
          if new is Nil && (if negative { itot > 2 } else { itot > 1 }) {
            separate(next)
          }
          if new.truthy() {
            new = rducon__snoc(new, exam)
          }
        } else if new.truthy() || non_constants.truthy() {
          non_constants = rducon__snoc(non_constants, exam)
        }
      } else {
        if !(new.truthy() || non_constants.truthy()) {
          separate(next)
        }
        if atom(result) || minus_constantp(result).truthy() {
          new = if atom(result) || !product {
            rducon__snoc(new, result)
          } else {
            let number_q = car(new)
            if d_numberp(number_q).truthy() {
              let new_prod = mul2(number_q, result)
              if mtimesp(new_prod).truthy() {
                nconc(cdr(new_prod), list1(new_prod))
              } else {
                nconc(cdr(new), list1(new_prod))
              }
            } else {
              nconc(cdr(result), new)
            }
          }
        } else {
          non_constants = rducon__snoc(non_constants, result)
        }
      }
      next = cdr(next)
    }
    if product && length(new) == 2 && equal(car(new), Fix(-1L)) {
      muln(nconc(new, non_constants), Nil)
    } else if length(new) > 1 {
      let nc = obtain_constant(
        if product {
          muln(new, Nil)
        } else {
          addn(new, Nil)
        },
        newconst,
      )
      if !product {
        addn(rducon__snoc(non_constants, nc), Nil)
      } else if atom(nc) {
        muln(rducon__snoc(non_constants, nc), Nil)
      } else {
        muln(nconc(cdr(nc), non_constants), Nil)
      }
    } else if new.truthy() || non_constants.truthy() {
      let tot = nconc(new, non_constants)
      if product {
        muln(tot, Nil)
      } else {
        addn(tot, Nil)
      }
    } else {
      x
    }
  } else {
    let mut next = cdr(x)
    let mut new : Value = Nil
    while next.truthy() {
      let exam = car(next)
      let result = reduce_constants(exam)
      if physical_equal_value(exam, result) {
        if new.truthy() {
          new = rducon__snoc(new, exam)
        }
      } else {
        if new is Nil {
          let mut copy = cdr(x)
          while !physical_equal_value(copy, next) {
            new = rducon__snoc(new, car(copy))
            copy = cdr(copy)
          }
        }
        new = rducon__snoc(new, result)
      }
      next = cdr(next)
    }
    if new is Nil {
      x
    } else if !eq(opr, q_mquotient) {
      nconc(list1(car(x)), new)
    } else {
      let cnum = find_constant(car(new))
      let cden = find_constant(cadr(new))
      if cnum.truthy() && cden.truthy() {
        let ratio = obtain_constant(div(cnum, cden), newconst)
        let numerator = if mtimesp(car(new)).truthy() {
          mul2(ratio, remove(cnum, car(new)))
        } else {
          ratio
        }
        if mtimesp(cadr(new)).truthy() {
          div(numerator, muln(remove(cden, cdadr(new)), Nil))
        } else {
          numerator
        }
      } else {
        x
      }
    }
  }
}

///|
fn d_reduce_consts(x : Value, newconstant? : Value = Nil) -> Value raise {
  if atom(x) {
    x
  } else {
    reduce_constants(x, newconst=newconstant)
  }
}

///|
/// Top-level forms of rducon.lisp.
fn init_share_rducon() -> Unit raise {
  macsyma_module(sym("rducon"), Nil) |> ignore
  if get(q_expens, q_version) is Nil {
    d_load(Str("expense")) |> ignore
  }
  if !boundp(q_d_const_eqns) {
    set(q_d_const_eqns, list1(list2(q_mlist, q_simp))) |> ignore
  }
}

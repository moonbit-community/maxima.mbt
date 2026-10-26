// Port of share/calculus/qualsp.lisp (MIT, 1981), used by qual.mac: list
// the facts of the form x > y, x >= y, x = y, x # y known in the database
// about a symbol x.

///|
/// Common loop of $lesses/$leqs/$greaters/$geqs: collect `doutern` of the
/// `pick` side of each fact `((op) a b)` of x's data whose operator is `op`
/// and whose `test` side is x.
fn share_qualsp__scan(
  x : Value,
  op : Value,
  test_second : Bool,
) -> Value raise {
  let x = dinternp(x)
  let mut nl : Value = Nil
  for f in get(x, q_data).iter() {
    let fact = car(f)
    if eq(op, car(fact)) {
      if test_second && eq(x, caddr(fact)) {
        nl = cons(doutern(cadr(fact)), nl)
      } else if (not(test_second)) && eq(x, cadr(fact)) {
        nl = cons(doutern(caddr(fact)), nl)
      }
    }
  }
  cons(list1(q_mlist), nl)
}

///|
fn d_lesses(x : Value) -> Value raise {
  share_qualsp__scan(x, q_mgrp, true)
}

///|
fn d_leqs(x : Value) -> Value raise {
  share_qualsp__scan(x, q_mgqp, true)
}

///|
fn d_greaters(x : Value) -> Value raise {
  share_qualsp__scan(x, q_mgrp, false)
}

///|
fn d_geqs(x : Value) -> Value raise {
  share_qualsp__scan(x, q_mgqp, false)
}

///|
/// $equals/$neqs: the other side of each symmetric fact mentioning x.
fn share_qualsp__scan_sym(x : Value, op : Value) -> Value raise {
  let x = dinternp(x)
  let mut nl : Value = Nil
  for f in get(x, q_data).iter() {
    let fact = car(f)
    if not(eq(op, car(fact))) {
      continue
    } else if eq(x, cadr(fact)) {
      nl = cons(doutern(caddr(fact)), nl)
    } else {
      nl = cons(doutern(cadr(fact)), nl)
    }
  }
  cons(list1(q_mlist), nl)
}

///|
fn d_equals(x : Value) -> Value raise {
  share_qualsp__scan_sym(x, q_meqp)
}

///|
fn d_neqs(x : Value) -> Value raise {
  share_qualsp__scan_sym(x, q_mnqp)
}

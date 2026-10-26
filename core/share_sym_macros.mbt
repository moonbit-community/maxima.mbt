// Port of share/sym/macros.lisp: accessors of partitioned polynomials
// (type 2: each partitioned term has its length in front), plus helpers
// shared by the whole sym package (Franz Lisp compatibility functions and
// the operation functions $mult_sym, $add_sym, ... installed by $operation).

///|
/// longueur de la partition initiale
fn lgi(sym_ : Value) -> Value raise {
  caar(sym_)
}

///|
/// partition initiale
fn moni(p : Value) -> Value raise {
  cddar(p)
}

///|
/// coefficient associe a la partition initiale
fn coei(p : Value) -> Value raise {
  cadar(p)
}

///|
/// terme partitionne initial
fn termi(p : Value) -> Value raise {
  car(p)
}

///|
/// modification physique du coefficient d'un terme
fn chcoeterm(term : Value, coe : Value) -> Value raise {
  rplaca(cdr(term), coe) |> ignore
  term
}

///|
/// liste de termes partitionnes sans le premier
fn termrest(p : Value) -> Value raise {
  cdr(p)
}

///|
/// partition d'un terme partitionne
fn tmon(term : Value) -> Value raise {
  cddr(term)
}

///|
/// coefficient d'un terme partitionne
fn tcoe(term : Value) -> Value raise {
  cadr(term)
}

///|
/// longueur de la partition d'un terme partitionne
fn tlg(term : Value) -> Value raise {
  car(term)
}

///|
fn init_share_macros() -> Unit raise {
  ()
}

// ---------------------------------------------------------------------------
// Helpers shared by the share_sym_* files.

///|
/// Franz Lisp CONCAT: intern the concatenation of the printed arguments
/// (`(format nil "~{~A~}" args)`).
fn share_sym__concat(parts : Array[Value]) -> Value raise {
  let sb = StringBuilder()
  for p in parts {
    match p {
      Sym(_) => sb.write_string(symbol_name(p))
      Str(s) => sb.write_string(s)
      _ => sb.write_string(princ_to_string(p))
    }
  }
  sym(sb.to_string())
}

///|
/// Franz Lisp ATTACH: destructively push NEWELT on the front of OLDLIST.
fn share_sym__attach(newelt : Value, oldlist : Value) -> Value raise {
  rplacd(oldlist, cons(car(oldlist), cdr(oldlist))) |> ignore
  rplaca(oldlist, newelt)
}

///|
/// Franz Lisp NTHCDR: a negative index conses a NIL in front.
fn share_sym__nthcdr(ind : Value, lis : Value) -> Value raise {
  if minusp(ind) {
    cons(Nil, lis)
  } else {
    nthcdr(to_int(ind), lis)
  }
}

///|
/// `(mdefprop name lambda mexpr)` followed by
/// `(add2lnc 'item $functions)`; both given as Lisp text.
fn share_sym__defmexpr(
  name : Value,
  lambda_text : String,
  item_text? : String,
) -> Unit raise {
  mdefprop(name, lread(lambda_text), q_mexpr) |> ignore
  match item_text {
    Some(s) => add2lnc(lread(s), symval(q_d_functions)) |> ignore
    None => ()
  }
}

///|
/// `(meval (list '($is) (list '(mequal) a b)))`, as a Lisp truth value.
fn share_sym__is_equal(a : Value, b : Value) -> Bool raise {
  meval(list([list1(q_d_is), list([list1(q_mequal), a, b])])).truthy()
}

///|
/// The operation functions selected by $operation.
fn share_sym__mult(a : Value, b : Value) -> Value raise {
  funcall(q_d_mult_sym, [a, b])
}

///|
fn share_sym__add(a : Value, b : Value) -> Value raise {
  funcall(q_d_add_sym, [a, b])
}

///|
fn share_sym__moins(a : Value) -> Value raise {
  funcall(q_d_moins_sym, [a])
}

///|
fn share_sym__divi(a : Value, b : Value) -> Value raise {
  funcall(q_d_divi_sym, [a, b])
}

///|
fn share_sym__exp(a : Value, b : Value) -> Value raise {
  funcall(q_d_exp_sym, [a, b])
}

///|
fn share_sym__fadd(l : Value) -> Value raise {
  funcall(q_d_fadd_sym, [l])
}

///|
fn share_sym__fmult(l : Value) -> Value raise {
  funcall(q_d_fmult_sym, [l])
}

///|
/// `(funcall egal a b)` for the equality predicates the sym package passes
/// around by name ('eql, 'equal, ...): the CL predicates have no function
/// cell in the port.
fn share_sym__egal(egal : Value, a : Value, b : Value) -> Bool raise {
  let name = match egal {
    Sym(_) => symbol_name(egal)
    _ => ""
  }
  match name {
    "eq" => eq(a, b)
    "eql" => eql(a, b)
    "equal" => equal(a, b)
    "equalp" => equalp(a, b)
    "=" => num_eq(a, b)
    _ => funcall(egal, [a, b]).truthy()
  }
}

///|
/// CL `(apply '>= l)`: true when L is non-increasing.
fn share_sym__non_increasing(l : Value) -> Bool raise {
  let mut p = l
  while cdr(p) is Cons(_) {
    if num_lt(car(p), cadr(p)) {
      return false
    }
    p = cdr(p)
  }
  true
}

///|
/// CL `(merge 'list l1 l2 pred)`.
fn share_sym__merge(
  l1 : Value,
  l2 : Value,
  pred : (Value, Value) -> Bool raise,
) -> Value raise {
  let c = Collector::new()
  let mut a = l1
  let mut b = l2
  while a is Cons(_) && b is Cons(_) {
    if pred(car(b), car(a)) {
      c.add(car(b))
      b = cdr(b)
    } else {
      c.add(car(a))
      a = cdr(a)
    }
  }
  c.append_list(if a is Cons(_) { a } else { b })
  c.result()
}

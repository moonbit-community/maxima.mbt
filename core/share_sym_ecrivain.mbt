// Port of share/sym/ecrivain.lisp: l'ecrivain de polynomes sous forme
// distribuee.

///|
fn d_distri_ecrit_init(d_distribue : Value, d_lvar : Value) -> Value raise {
  if cdr(d_distribue) is Nil {
    int(0)
  } else if equal(q_mlist, caar(d_distribue)) {
    d_ecrivain_sym(mapcar(x => cdr(x), cdr(d_distribue)), cdr(d_lvar))
  } else {
    d_ecrivain_sym(d_distribue, d_lvar)
  }
}

///|
fn d_ecrivain_sym(ppart : Value, lvar : Value) -> Value raise {
  if ppart is Nil {
    int(0)
  } else if cdr(ppart) is Nil {
    ecrit_mon(cdar(ppart), lvar, caar(ppart))
  } else {
    share_sym__fadd(mapcar(tpart => ecrit_mon(cdr(tpart), lvar, car(tpart)), ppart))
  }
}

///|
fn ecrit_mon(part : Value, lvar : Value, coe : Value) -> Value raise {
  if part is Nil {
    coe
  } else {
    let factors = Collector::new()
    let mut a = lvar
    let mut b = part
    while a is Cons(_) && b is Cons(_) {
      factors.add(share_sym__exp(car(a), car(b)))
      a = cdr(a)
      b = cdr(b)
    }
    share_sym__mult(coe, share_sym__fmult(factors.result()))
  }
}

///|
fn init_share_ecrivain() -> Unit raise {
  share_sym__defmexpr(
    q_d_distri_ecrit,
    "((lambda ()) ((mlist) $distribue $lvar) ((mprog) (($operation)) (($distri_ecrit_init) $distribue $lvar)))",
    item_text="(($distri_ecrit) $distribue $lvar)",
  )
}

// Port of share/sym/tri.lisp (SYM package): ordering of monomials and
// insertion of a monomial in a distributed polynomial
// ((mlist simp) ((mlist simp) coe e1 e2 ... en) ....).

///|
fn d_lexicographique_q(d_a : Value, d_b : Value) -> Value raise {
  n2lexinv_type1(cddr(d_a), cddr(d_b))
}

///|
fn d_longueur_q(d_a : Value, d_b : Value) -> Value raise {
  longueur_q(cddr(d_a), cddr(d_b))
}

///|
fn longueur_q(tt1 : Value, t2 : Value) -> Value raise {
  let l1 = longueur(tt1) // longueur est dans util.lsp
  let l2 = longueur(t2)
  if num_lt(l1, l2) {
    t
  } else if num_eq(l1, l2) {
    d_lex(tt1, t2)
  } else {
    Nil
  }
}

///|
/// The polynomial is ordered but may contain equal monomials: add up their
/// coefficients (destructively).
fn d_simplifie_dist(d_polynome : Value) -> Value raise {
  simplifie_dist(cadr(d_polynome), cdr(d_polynome)) |> ignore
  d_polynome
}

///|
fn simplifie_dist(polynome : Value, d_monome : Value) -> Value raise {
  let mut polynome = polynome
  let mut monome = d_monome
  while true {
    if cddr(polynome) is Nil {
      return Nil
    }
    let mon2 = cadr(polynome)
    if not(equal(cddr(mon2), cddr(monome))) {
      polynome = cdr(polynome)
      monome = mon2
    } else {
      rplaca(cdr(monome), num_add(cadr(monome), cadr(mon2))) |> ignore
      rplacd(polynome, cddr(polynome)) |> ignore
    }
  }
  Nil
}

///|
fn d_insert(d_monome : Value, d_polynome : Value) -> Value raise {
  insert(d_monome, d_polynome) |> ignore
  d_polynome
}

///|
fn insert(d_monome : Value, polynome : Value) -> Value raise {
  if cdr(polynome) is Nil {
    return rplacd(polynome, list1(d_monome))
  }
  let mon2 = cadr(polynome)
  if equal(cddr(mon2), cddr(d_monome)) {
    let coe = num_add(cadr(d_monome), cadr(mon2))
    if num_eq(int(0), coe) {
      rplacd(polynome, cddr(polynome))
    } else {
      rplaca(cdr(mon2), coe)
    }
  } else if d_longueur_q(d_monome, mon2).truthy() {
    insert(d_monome, cdr(polynome))
  } else {
    rplacd(polynome, cons(d_monome, cdr(polynome)))
  }
}

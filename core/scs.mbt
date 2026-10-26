// Port of src/scs.lisp: scsimp, distrib, facout.

///|
fn d_scsimp(expr : Value, rules : Value) -> Value raise {
  scs(expr, mapcar(r => meqhk(r), rules))
}

///|
fn scs(x : Value, zrs : Value) -> Value raise {
  let mut x = x
  let mut flag = true
  let mut sz = conssize(x)
  while flag {
    let mut l = zrs
    while true {
      if l is Nil {
        flag = false
        break
      }
      let nx = subscs(int(0), car(l), x)
      let nsz = conssize(nx)
      if num_lt(nsz, sz) {
        x = nx
        sz = nsz
        break
      }
      l = cdr(l)
    }
  }
  x
}

///|
fn subscs(a : Value, b : Value, c : Value) -> Value raise {
  if atom(b) {
    subsc(a, b, c)
  } else if eq(q_mplus, caar(b)) {
    let mut c = c
    let mut l = cdr(b)
    let mut sz = conssize(c)
    let mut nl : Value = Nil
    while !(l is Nil) {
      let nc = subscs(sub(a, addn(revappend(nl, cdr(l)), t)), car(l), c)
      let nsz = conssize(nc)
      nl = cons(car(l), nl)
      if num_lt(nsz, sz) {
        c = nc
        sz = nsz
      }
      l = cdr(l)
    }
    c
  } else {
    subsc(a, b, c)
  }
}

///|
fn subsc(a : Value, b : Value, c : Value) -> Value raise {
  d_expand(d_ratsubst(a, b, c))
}

///|
fn dstrb(x : Value, l : Value, nl : Value) -> Value raise {
  revappend(mapcar(u => mul2(x, u), l), nl)
}

///|
fn d_distrib(exp_ : Value) -> Value raise {
  if mnump(exp_).truthy() || symbolp(exp_) {
    exp_
  } else if eq(q_mtimes, caar(exp_)) {
    let exp_ = mapcar(x => d_distrib(x), cdr(exp_))
    let mut l = cdr(exp_)
    let mut nl = if mplusp(car(exp_)).truthy() {
      cdar(exp_)
    } else {
      list1(car(exp_))
    }
    while !(l is Nil) {
      if mplusp(car(l)).truthy() {
        let mut m = cdar(l)
        let mut ml : Value = Nil
        while !(m is Nil) {
          ml = dstrb(car(m), nl, ml)
          m = cdr(m)
        }
        nl = ml
      } else {
        nl = dstrb(car(l), nl, Nil)
      }
      l = cdr(l)
    }
    addn(nl, t)
  } else if eq(q_mequal, caar(exp_)) {
    list3(list1(q_mequal), d_distrib(cadr(exp_)), d_distrib(caddr(exp_)))
  } else if eq(q_mrat, caar(exp_)) {
    d_distrib(ratdisrep(exp_))
  } else {
    exp_
  }
}

///|
fn d_facout(x : Value, y : Value) -> Value raise {
  if mplusp(y).truthy() {
    mul2(x, addn(mapcar(l => div(l, x), cdr(y)), t))
  } else {
    y
  }
}

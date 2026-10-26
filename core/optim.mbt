// Port of src/optim.lisp: common subexpression elimination (optimize).

///|
fn optim__fill_subexp() -> Unit raise {
  let v = symval(q_ear_subexp)
  for i in 0..<array_total_size(v) {
    aset1(v, i, Nil) |> ignore
  }
}

///|
fn optim__bucket(n : Int) -> Value raise {
  aref1(symval(q_ear_subexp), n)
}

///|
/// $OPTIMIZE takes a Macsyma expression and returns a BLOCK form which is
/// equivalent, but which uses local variables to store the results of
/// computing common subexpressions.  These subexpressions are found by
/// hashing them.
fn d_optimize(x0 : Value) -> Value raise {
  with_specials(
    [
      (q_d_optimwarn, symval(q_d_optimwarn)),
      (q_ear_setqs, Nil),
      (q_vars, Nil),
      (q_ear_optimcount, int(0)),
      (q_ear_xvars, cdr(d_listofvars(x0))),
    ],
    () => {
      optim__fill_subexp()
      let mut x = collapse(opformat(collapse(x0)))
      if atom(x) {
        return x
      }
      comexp(x) |> ignore
      x = optim(x)
      let result = if symval(q_vars) is Nil {
        x0
      } else {
        if !eq(caar(x), q_mprog) || (d_listp(cadr(x)).truthy() && cdadr(x).truthy()) {
          x = nreverse(cons(x, symval(q_ear_setqs)))
        } else {
          x = nreconc(symval(q_ear_setqs), cddr(x))
        }
        cons(
          list2(q_mprog, q_simp),
          cons(cons(list1(q_mlist), nreverse(symval(q_vars))), x),
        )
      }
      optim__fill_subexp()
      result
    },
  )
}

///|
fn opformat(x : Value) -> Value raise {
  if atom(x) {
    return x
  }
  if specrepp(x).truthy() {
    return opformat(specdisrep(x))
  }
  if symval(q_d_optimwarn).truthy() && mspecfunp(caar(x)).truthy() {
    mtell(
      list1(Str("optimize: encountered a special form; result may be wrong.")),
    )
    |> ignore
    set(q_d_optimwarn, Nil) |> ignore
  }
  if eq(caar(x), q_mexpt) {
    opmexpt(x)
  } else {
    let newargs = mapcar(y => opformat(y), cdr(x))
    if alike(newargs, cdr(x)).truthy() {
      x
    } else {
      cons(car(x), newargs)
    }
  }
}

///|
fn opmexpt(x : Value) -> Value raise {
  let base = opformat(cadr(x))
  let mut exp_ = opformat(caddr(x))
  let negexp = if realp(exp_) && minusp(exp_) {
    num_neg(exp_)
  } else if ratnump(exp_).truthy() && minusp(cadr(exp_)) {
    list3(car(exp_), num_neg(cadr(exp_)), caddr(exp_))
  } else if mtimesp(exp_).truthy() && realp(cadr(exp_)) && minusp(cadr(exp_)) {
    if equal(cadr(exp_), int(-1)) {
      if cdddr(exp_) is Nil {
        caddr(exp_)
      } else {
        cons(car(exp_), cddr(exp_))
      }
    } else {
      cons(car(exp_), cons(num_neg(cadr(exp_)), cddr(exp_)))
    }
  } else if mtimesp(exp_).truthy() &&
    ratnump(cadr(exp_)).truthy() &&
    minusp(cadadr(exp_)) {
    cons(
      car(exp_),
      cons(
        list3(caadr(exp_), num_neg(cadadr(exp_)), caddr(cadr(exp_))),
        cddr(exp_),
      ),
    )
  } else {
    Nil
  }
  let xnew = if negexp.truthy() {
    list3(
      list1(q_mquotient),
      int(1),
      if equal(negexp, int(1)) {
        base
      } else {
        let xn = list3(car(x), base, negexp)
        if ratnump(negexp).truthy() && equal(caddr(negexp), int(2)) {
          opmexpt(xn)
        } else {
          xn
        }
      },
    )
  } else if ratnump(exp_).truthy() && equal(caddr(exp_), int(2)) {
    exp_ = cadr(exp_)
    if equal(exp_, int(1)) {
      list2(list1(q_p_sqrt), base)
    } else {
      list3(list1(q_mexpt), list2(list1(q_p_sqrt), base), exp_)
    }
  } else {
    list3(car(x), base, exp_)
  }
  if alike1(x, xnew).truthy() {
    x
  } else {
    xnew
  }
}

///|
fn d_collapse(x : Value) -> Value raise {
  optim__fill_subexp()
  let r = collapse(x)
  optim__fill_subexp()
  r
}

///|
fn optim__hash_mod(n : Value, u : Value) -> Value raise {
  num_rem(num_add(opt_hash(u), n), int(12553))
}

///|
fn collapse(x : Value) -> Value raise {
  if atom(x) {
    x
  } else if specrepp(x).truthy() {
    collapse(specdisrep(x))
  } else {
    let mut n = opt_hash(caar(x))
    let mut l = cdr(x)
    while !(l is Nil) {
      if !eq(collapse(car(l)), car(l)) {
        rplaca(l, collapse(car(l))) |> ignore
      }
      n = optim__hash_mod(n, car(l))
      l = cdr(l)
    }
    let n = to_int(logand(int(63), n))
    let mut b = optim__bucket(n)
    while !(b is Nil) {
      if alike1(x, caar(b)).truthy() {
        return caar(b)
      }
      b = cdr(b)
    }
    aset1(symval(q_ear_subexp), n, cons(list1(x), optim__bucket(n))) |> ignore
    x
  }
}

///|
fn comexp(x : Value) -> Value raise {
  if !(atom(x) || eq(caar(x), q_rat)) {
    let mut n = opt_hash(caar(x))
    for u in cdr(x).iter() {
      n = optim__hash_mod(n, u)
    }
    let x = assol(x, optim__bucket(to_int(logand(int(63), n))))
    if cdr(x) is Nil {
      rplacd(x, q_seen) |> ignore
      mapc(y => comexp(y) |> ignore, cdar(x))
    } else {
      rplacd(x, q_comexp)
    }
  } else {
    Nil
  }
}

///|
fn optim(x : Value) -> Value raise {
  if atom(x) {
    x
  } else if memq(q_array, cdar(x)).truthy() &&
    !eq(caar(x), q_mqapply) &&
    !mget(caar(x), q_arrayfun_mode).truthy() {
    x
  } else if eq(caar(x), q_rat) {
    x
  } else {
    let mut n = opt_hash(caar(x))
    let mut nx = list1(car(x))
    for u in cdr(x).iter() {
      n = optim__hash_mod(n, u)
      nx = cons(optim(u), nx)
    }
    let x = assol(x, optim__bucket(to_int(logand(int(63), n))))
    nx = nreverse(nx)
    if eq(cdr(x), q_seen) {
      nx
    } else if eq(cdr(x), q_comexp) {
      rplacd(x, getoptimvar()) |> ignore
      push_special(list3(list1(q_msetq), cdr(x), nx), q_ear_setqs) |> ignore
      cdr(x)
    } else {
      cdr(x)
    }
  }
}

///|
/// EXP is in general representation.
fn opt_hash(exp_ : Value) -> Value raise {
  let h = if atom(exp_) {
    // sxhash: a non-negative fixnum
    int(hash_equal(exp_) & 0x3fffffff)
  } else {
    let mut n = opt_hash(caar(exp_))
    let mut args = cdr(exp_)
    while !(args is Nil) {
      n = optim__hash_mod(n, car(args))
      args = cdr(args)
    }
    n
  }
  // a prime number < 2^14 ; = PRIME(1500)
  num_rem(h, int(12553))
}

///|
fn getoptimvar() -> Value raise {
  while true {
    set(q_ear_optimcount, num_add(symval(q_ear_optimcount), int(1))) |> ignore
    let var_ = make_symbol(
      format_to_string("~A~D", [
        symval(q_d_optimprefix),
        symval(q_ear_optimcount),
      ]),
    )
    if memq(var_, symval(q_ear_xvars)) is Nil {
      push_special(var_, q_vars) |> ignore
      return var_
    }
  }
  Nil
}

///|
fn init_optim() -> Unit raise {
  defvar_init(q_ear_subexp, make_array([64], initial=Nil))
  // (defmvar $optimprefix '$% nil :setting-predicate #'symbolp)
  putprop(
    q_d_optimprefix,
    lfunc("optimprefix-assign", args => {
      if !symbolp(arg(args, 1)) {
        mseterr(arg(args, 0), arg(args, 1), reason=Nil) |> ignore
      }
      Nil
    }),
    q_assign,
  )
  |> ignore
}

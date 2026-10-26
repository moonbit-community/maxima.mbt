// Port of share/sym/operations.lisp: the arithmetic operations of the sym
// package (with rat, expand, ratsimp or meval), selected by $oper.

///|
fn share_sym_operations__call(f : Value, e : Value) -> Value raise {
  meval(list2(list1(f), e))
}

// Les operations avec rat

///|
fn d_ratmult(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_rat, list3(list1(q_mtimes), a, b))
}

///|
fn d_ratadd(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_rat, list3(list1(q_mplus), a, b))
}

///|
fn d_ratfmult(ll : Value) -> Value raise {
  share_sym_operations__call(q_d_rat, cons(list1(q_mtimes), ll))
}

///|
fn d_ratfadd(l : Value) -> Value raise {
  share_sym_operations__call(q_d_rat, cons(list1(q_mplus), l))
}

///|
fn d_ratdivi(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_rat, list3(list1(q_mquotient), a, b))
}

///|
fn d_ratexp(x : Value, n : Value) -> Value raise {
  share_sym_operations__call(q_d_rat, list3(list1(q_mexpt), x, n))
}

///|
fn d_ratmoins(a : Value) -> Value raise {
  share_sym_operations__call(q_d_rat, list2(list1(q_mminus), a))
}

// Les operations pour expand

///|
fn d_expandmult(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_expand, list3(list1(q_mtimes), a, b))
}

///|
fn d_expandadd(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_expand, list3(list1(q_mplus), a, b))
}

///|
fn d_expandfmult(ll : Value) -> Value raise {
  share_sym_operations__call(q_d_expand, cons(list1(q_mtimes), ll))
}

///|
fn d_expandfadd(l : Value) -> Value raise {
  share_sym_operations__call(q_d_expand, cons(list1(q_mplus), l))
}

///|
fn d_expanddivi(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_expand, list3(list1(q_mquotient), a, b))
}

///|
fn d_expandexp(x : Value, n : Value) -> Value raise {
  share_sym_operations__call(q_d_expand, list3(list1(q_mexpt), x, n))
}

///|
fn d_expandmoins(a : Value) -> Value raise {
  share_sym_operations__call(q_d_expand, list2(list1(q_mminus), a))
}

// Les operations avec ratsimp

///|
fn d_ratsimpmult(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_ratsimp, list3(list1(q_mtimes), a, b))
}

///|
fn d_ratsimpadd(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_ratsimp, list3(list1(q_mplus), a, b))
}

///|
fn d_ratsimpfmult(ll : Value) -> Value raise {
  share_sym_operations__call(q_d_ratsimp, cons(list1(q_mtimes), ll))
}

///|
fn d_ratsimpfadd(l : Value) -> Value raise {
  share_sym_operations__call(q_d_ratsimp, cons(list1(q_mplus), l))
}

///|
fn d_ratsimpdivi(a : Value, b : Value) -> Value raise {
  share_sym_operations__call(q_d_ratsimp, list3(list1(q_mquotient), a, b))
}

///|
fn d_ratsimpexp(x : Value, n : Value) -> Value raise {
  share_sym_operations__call(q_d_ratsimp, list3(list1(q_mexpt), x, n))
}

///|
fn d_ratsimpmoins(a : Value) -> Value raise {
  share_sym_operations__call(q_d_ratsimp, list2(list1(q_mminus), a))
}

// Les operations avec meval

///|
fn d_mevalmoins(a : Value) -> Value raise {
  meval(list2(list1(q_mminus), a))
}

///|
fn d_mevalmult(a : Value, b : Value) -> Value raise {
  meval(list3(list1(q_mtimes), a, b))
}

///|
fn d_mevaladd(a : Value, b : Value) -> Value raise {
  meval(list3(list1(q_mplus), a, b))
}

///|
fn d_mevalfmult(ll : Value) -> Value raise {
  meval(cons(list1(q_mtimes), ll))
}

///|
fn d_mevalfadd(l : Value) -> Value raise {
  meval(cons(list1(q_mplus), l))
}

///|
fn d_mevaldivi(x : Value, y : Value) -> Value raise {
  meval(list3(list1(q_mquotient), x, y))
}

///|
fn d_mevalexp(x : Value, n : Value) -> Value raise {
  meval(list3(list1(q_mexpt), x, n))
}

///|
/// Change the bodies of the functions $moins_sym $mult_sym ... to those of
/// the operations chosen by $oper (e.g. $mevalmoins $mevalmult ... for
/// $oper = $meval).
fn d_operation() -> Value raise {
  let oper = symval(q_d_oper)
  if equal(oper, symval(q_prefixe)) {
    return t
  }
  let suffixes = ["moins", "mult", "add", "divi", "exp", "fadd", "fmult"]
  let corps : Array[Value] = []
  for suffixe in suffixes {
    corps.push(symbol_function(share_sym__concat([oper, Str(suffixe)])))
  }
  let noms = [
    q_d_moins_sym, q_d_mult_sym, q_d_add_sym, q_d_divi_sym, q_d_exp_sym, q_d_fadd_sym,
    q_d_fmult_sym,
  ]
  for i, nom in noms {
    let f = corps[i]
    defun(nom, args => funcall(f, args))
  }
  set(q_prefixe, oper)
}

///|
fn init_share_operations() -> Unit raise {
  set(q_prefixe, q_depart) |> ignore
}

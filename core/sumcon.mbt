// Port of src/sumcon.lisp: sumcontract, intosum, bashindices, niceindices.

///|
/// e is assumed to be simplified
fn d_sumcontract(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) {
    let mut sums : Value = Nil
    let mut notsums : Value = Nil
    for car_x in cdr(e).iter() {
      if atom(car_x) {
        notsums = cons(car_x, notsums)
      } else if eq(caar(car_x), q_p_sum) {
        sums = cons(cons(d_sumcontract(cadr(car_x)), cddr(car_x)), sums)
      } else {
        notsums = cons(car_x, notsums)
      }
    }
    if sums is Nil {
      subst0(cons(list1(q_mplus), nreverse(notsums)), e)
    } else {
      sums = sumcontract1(sums)
      addn(cons(sums, notsums), t)
    }
  } else {
    recur_apply(q_d_sumcontract, e)
  }
}

///|
/// e is assumed to be simplified
fn d_intosum(e : Value) -> Value raise {
  with_special(q_d_sumexpand, t, fn() raise {
    if atom(e) {
      e
    } else if eq(caar(e), q_mtimes) {
      // puts outside product inside
      let mut sum : Value = Nil
      let mut notsum : Value = Nil
      let mut x = cdr(e)
      while x.truthy() {
        if atom(car(x)) {
          notsum = cons(car(x), notsum)
        } else if eq(caaar(x), q_p_sum) {
          sum = if sum is Nil {
            copy_tree(car(x))
          } else {
            muln(list2(sum, car(x)), t)
          }
        } else {
          notsum = cons(d_sumcontract(car(x)), notsum)
        }
        x = cdr(x)
      }
      if sum is Nil {
        subst0(cons(list1(q_mtimes), nreverse(notsum)), e)
      } else {
        let new_index = if free(cons(Nil, notsum), caddr(sum)).truthy() {
          caddr(sum)
        } else {
          get_free_index(cons(Nil, cons(sum, notsum)))
        }
        sum = subst(new_index, caddr(sum), sum)
        rplaca(cdr(sum), muln(cons(cadr(sum), notsum), t)) |> ignore
        rplacd(car(sum), Nil) |> ignore
        simpsum(sum, Fix(1L), t)
      }
    } else {
      recur_apply(q_d_intosum, e)
    }
  })
}

///|
fn sumcontract1(sums : Value) -> Value raise {
  addn(sumcontract2(Nil, sums), t)
}

///|
fn sumcontract2(result : Value, left : Value) -> Value raise {
  if left is Nil {
    result
  } else {
    let x = sumcombine1(car(left), cdr(left))
    sumcontract2(append(car(x), result), cdr(x))
  }
}

///|
fn sumcombine1(pattern : Value, llist : Value) -> Value raise {
  let mut sum = pattern
  let mut non_sums : Value = Nil
  let mut un_matched_sums : Value = Nil
  for try_this_one in llist.iter() {
    if numberp(sub_star(caddr(sum), caddr(try_this_one))) &&
      numberp(sub_star(cadddr(sum), cadddr(try_this_one))) {
      let x = sumcombine2(try_this_one, sum)
      sum = cdar(x)
      non_sums = cons(cdr(x), non_sums)
    } else {
      un_matched_sums = cons(try_this_one, un_matched_sums)
    }
  }
  cons(cons(simplifya(cons(list1(q_p_sum), sum), Nil), non_sums), un_matched_sums)
}

///|
fn sumcombine2(sum1 : Value, sum2 : Value) -> Value raise {
  let mut e1 = car(sum1)
  let mut e2 = car(sum2)
  let i1 = cadr(sum1)
  let i2 = cadr(sum2)
  let l1 = caddr(sum1)
  let l2 = caddr(sum2)
  let h1 = cadddr(sum1)
  let h2 = cadddr(sum2)
  let newl = simplifya(mk(q_d_max, [l1, l2]), Nil)
  let newh = simplifya(mk(q_d_min, [h1, h2]), Nil)
  let newi = if eq(i1, i2) {
    i1
  } else if free(e1, i2).truthy() {
    i2
  } else if free(e2, i1).truthy() {
    i1
  } else {
    get_free_index(list([Nil, i1, i2, e1, e2, l1, l2, h1, h2]))
  }
  e1 = subst(newi, i1, e1)
  e2 = subst(newi, i2, e2)
  let new_sum = list([list1(q_p_sum), add2(e1, e2), newi, newl, newh])
  let es = [e1, e1, e2, e2]
  let lows = [l1, add2(newh, Fix(1L)), l2, add2(newh, Fix(1L))]
  let highs = [sub_star(newl, Fix(1L)), h1, sub_star(newl, Fix(1L)), h2]
  let terms = Collector::new()
  for k in 0..<4 {
    terms.add(dosum(es[k], newi, lows[k], highs[k], t))
  }
  let extracted = addn(terms.result(), t)
  cons(new_sum, extracted)
}

///|
fn get_free_index(llist : Value, i? : Value = Nil) -> Value raise {
  let pref = symval(q_d_niceindicespref)
  for try_ in cdr(pref).iter() {
    if free(llist, try_).truthy() || eq(i, try_) {
      return try_
    }
  }
  let base = princ_to_string(cadr(pref))
  let mut n = 0
  while true {
    let try_ = sym(base + n.to_string())
    if free(llist, try_).truthy() {
      return try_
    }
    n += 1
  }
  Nil
}

///|
/// e is assumed to be simplified
fn d_bashindices(e : Value) -> Value raise {
  if atom(e) {
    e
  } else {
    // (the LET evaluates the recursion before binding $genindex)
    let e = recur_apply(q_d_bashindices, e)
    with_special(q_d_genindex, q_d_j, fn() raise {
      if atom(e) {
        e
      } else if memq(caar(e), list2(q_p_sum, q_p_product)).truthy() {
        sumconsimp(subst(gensumindex(), caddr(e), e))
      } else {
        e
      }
    })
  }
}

///|
fn d_niceindices(e : Value) -> Value raise {
  if atom(e) {
    e
  } else {
    let e = recur_apply(q_d_niceindices, e)
    if atom(e) {
      e
    } else if memq(caar(e), list2(q_p_sum, q_p_product)).truthy() {
      sumconsimp(subst(get_free_index(e, i=caddr(e)), caddr(e), e))
    } else {
      e
    }
  }
}

///|
fn sumconsimp(e : Value) -> Value raise {
  if !atom(e) && memq(caar(e), list2(q_p_sum, q_p_product)).truthy() {
    list_star([car(e), sumconsimp(cadr(e)), cddr(e)])
  } else {
    resimplify(e)
  }
}

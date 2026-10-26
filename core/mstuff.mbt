// Port of src/mstuff.lisp: sort, makelist, sublist.

///|
fn d_sort(l : Value, f? : Value = q_lessthan) -> Value raise {
  with_special(q_d_prederror, t, () => {
    let mut llist = l
    if !d_listp(llist).truthy() {
      merr("sort: first argument must be a list; found: ~M", [llist]) |> ignore
    }
    llist = copy_list(cdr(llist))
    let bfun = getopr(f)
    let comparfun = mfunction1(bfun)
    if eq(bfun, q_lessthan) || eq(bfun, q_great) {
      llist = mapcar(x => ratdisrep(x), llist)
    }
    simplifya(
      cons(list1(q_mlist), sort_list(llist, (a, b) => funcall(comparfun, [a, b]).truthy())),
      t,
    )
  })
}

///|
fn mfunction1(fun : Value) -> Value raise {
  if functionp(fun) {
    lfunc("mfunction1", args => mevalp(funcall(fun, [arg(args, 0), arg(args, 1)])))
  } else {
    lfunc("mfunction1", args => mevalp(
      list3(
        list1(fun),
        list2(list1(q_mquote), arg(args, 0)),
        list2(list1(q_mquote), arg(args, 1)),
      ),
    ))
  }
}

///|
fn lessthan(a : Value, b : Value) -> Value raise {
  great(b, a)
}

///|
/// `(($ev) ((mquote) form) ...)`
fn mstuff__ev_form(form : Value, extra : Array[Value]) -> Value {
  let args = [list2(list1(q_mquote), form)]
  for e in extra {
    args.push(e)
  }
  cons(list1(q_d_ev), list(args))
}

///|
fn d_makelist(x0 : Value) -> Value raise {
  let x = cdr(x0)
  let res = mstuff__makelist_body(x)
  simplifya(res, t)
}

///|
fn mstuff__makelist_body(x : Value) -> Value raise {
  let n = length(x)
  let mut form : Value = Nil
  let mut arg_ : Value = Nil
  let mut lv : Value = Nil
  if n == 0 {
    return list1(q_mlist)
  } else if n == 1 {
    form = first(x)
    return list2(list1(q_mlist), meval(mstuff__ev_form(form, [])))
  } else if n == 2 {
    form = first(x)
    let b = with_special(q_d_simp, t, () => d_float(meval(second(x))))
    if numberp(b) {
      let ans = Collector::new()
      let mut m = int(1)
      while !num_gt(m, b) {
        ans.add(meval(mstuff__ev_form(form, [])))
        m = num_add(m, int(1))
      }
      return cons(list1(q_mlist), ans.result())
    } else {
      return merr(
        "makelist: second argument must evaluate to a number; found: ~M",
        [b],
      )
    }
  } else if n == 3 {
    form = first(x)
    arg_ = second(x)
    let mut b = meval(third(x))
    if d_listp(b).truthy() {
      lv = mapcar(u => list2(list1(q_mquote), u), cdr(b))
    } else {
      let bb = b
      b = with_special(q_d_simp, t, () => d_float(meval(bb)))
      if d_numberp(b).truthy() {
        let ans = Collector::new()
        let mut m = int(1)
        while !num_gt(m, b) {
          ans.add(
            meval(mstuff__ev_form(form, [mk(q_mequal, [arg_, m])])),
          )
          m = num_add(m, int(1))
        }
        return cons(list1(q_mlist), ans.result())
      } else {
        return merr(
          "makelist: third argument must be a number or a list; found: ~M",
          [b],
        )
      }
    }
  } else if n == 4 {
    form = first(x)
    arg_ = second(x)
    let a = meval(third(x))
    let b = meval(fourth(x))
    let d = with_special(q_d_simp, t, () => d_float(
      meval(mk(q_mplus, [b, mk(q_mtimes, [a, int(-1)])])),
    ))
    if numberp(d) {
      lv = interval2(a, int(1), d)
    } else {
      return merr(
        "makelist: the fourth argument minus the third one must evaluate to a number; found: ~M",
        [d],
      )
    }
  } else if n == 5 {
    form = first(x)
    arg_ = second(x)
    let a = meval(third(x))
    let b = meval(fourth(x))
    let c = meval(fifth(x))
    let d = with_special(q_d_simp, t, () => d_float(
      meval(
        mk(q_mtimes, [
          mk(q_mplus, [b, mk(q_mtimes, [a, int(-1)])]),
          mk(q_mexpt, [c, int(-1)]),
        ]),
      ),
    ))
    if numberp(d) {
      lv = interval2(a, c, d)
    } else {
      return merr(
        "makelist: the fourth argument minus the third one, divided by the fifth one must evaluate to a number; found: ~M",
        [d],
      )
    }
  } else {
    return merr(
      "makelist: maximum 5 arguments allowed; found: ~M.~%To create a list with sublists, use nested makelist commands.",
      [int(n)],
    )
  }
  let ans = Collector::new()
  let mut l = lv
  while !(l is Nil) {
    ans.add(meval(mstuff__ev_form(form, [mk(q_mequal, [arg_, car(l)])])))
    l = cdr(l)
  }
  cons(list1(q_mlist), ans.result())
}

///|
fn interval2(i : Value, s : Value, d : Value) -> Value raise {
  let mut nn = i
  let mut m = int(0)
  let mut ans : Value = Nil
  while !num_gt(m, d) {
    ans = cons(nn, ans)
    let cur = nn
    nn = with_special(q_d_simp, t, () => meval(mk(q_mplus, [s, cur])))
    m = num_add(m, int(1))
  }
  nreverse(ans)
}

///|
fn interval(i : Value, j : Value) -> Value raise {
  let mut nn = i
  let mut m = int(0)
  let k = sub_star(j, i)
  let mut ans : Value = Nil
  while !num_gt(m, k) {
    ans = cons(nn, ans)
    nn = add2(int(1), nn)
    m = num_add(m, int(1))
  }
  nreverse(ans)
}

///|
fn d_sublist(a : Value, f : Value) -> Value raise {
  if !d_listp(a).truthy() {
    merr("sublist: first argument must be a list; found: ~M", [a]) |> ignore
  }
  let mut l = cdr(a)
  let mut x : Value = Nil
  while !(l is Nil) {
    if definitely_so(mfuncall(f, list1(car(l)))).truthy() {
      x = cons(car(l), x)
    }
    l = cdr(l)
  }
  simplifya(cons(list1(q_mlist), nreverse(x)), t)
}

// Port of src/mlisp.lisp, part 2: ev, the mapping functions (map,
// fullmap, outermap, ...), properties (put, declare, remove, ...).

///|
/// One step of the argument loop of $EV: the flags, equations, local
/// definitions etc. given after the expression.
priv struct MlispEvState {
  mut bndvars : Value
  mut bndvals : Value
  mut locvars : Value
  mut exp : Value
  mut subsl : Value
  mut evflg : Int
  mut ratf : Bool
  mut evfunl : Value
  mut funcl : Value
  mut predflg : Bool
}

///|
fn d_ev(l : Value) -> Value raise {
  let l = cdr(l)
  with_specials(
    [
      (q_evp, t),
      (q_ear_nounl, symval(q_ear_nounl)),
      (q_d_float, symval(q_d_float)),
      (q_d_numer, symval(q_d_numer)),
      (q_d_expop, symval(q_d_expop)),
      (q_d_expon, symval(q_d_expon)),
      (q_d_doallmxops, symval(q_d_doallmxops)),
      (q_d_doscmxops, symval(q_d_doscmxops)),
      (q_derivflag, symval(q_derivflag)),
      (q_d_detout, symval(q_d_detout)),
      (q_ear_nounsflag, symval(q_ear_nounsflag)),
      (q_rulefcnl, symval(q_rulefcnl)),
    ],
    () => with_special(q_derivlist, Nil, () => mlisp__ev_body(l)),
  )
}

///|
fn mlisp__ev_body(l0 : Value) -> Value raise {
  let st : MlispEvState = {
    bndvars: Nil,
    bndvals: Nil,
    locvars: Nil,
    exp: car(l0),
    subsl: Nil,
    evflg: 0,
    ratf: false,
    evfunl: Nil,
    funcl: Nil,
    predflg: false,
  }
  let noeval = memq(q_d_noeval, cdr(l0)).truthy()
  let mut l = cdr(l0)
  while l is Cons(_) {
    if !(
        atom(car(l)) ||
        memq(q_array, cdaar(l)).truthy() ||
        memq(
          caaar(l),
          list([
            q_mquote, q_msetq, q_mlist, q_mequal, q_mdefine, q_mset, q_mdefmacro,
            q_d_expand, q_d_local, q_d_derivlist,
          ]),
        ).truthy()
      ) {
      l = cons(meval(car(l)), cdr(l))
    }
    let a = car(l)
    if atom(a) || memq(q_array, cdar(a)).truthy() || eq(caar(a), q_mquote) {
      let handled = if symbolp(a) {
        if eq(a, q_d_eval) {
          st.evflg += 1
          true
        } else if eq(a, q_d_noeval) || eq(a, q_d_rescan) {
          true
        } else if eq(a, q_d_detout) {
          set(q_d_doallmxops, Nil) |> ignore
          set(q_d_doscmxops, Nil) |> ignore
          set(q_d_detout, t) |> ignore
          true
        } else if eq(a, q_d_numer) {
          set(q_d_numer, t) |> ignore
          set(q_d_float, t) |> ignore
          true
        } else if eq(a, q_d_nouns) {
          set(q_ear_nounsflag, t) |> ignore
          true
        } else if eq(a, q_d_pred) {
          st.predflg = true
          true
        } else if eq(a, q_d_expand) {
          set(q_d_expop, symval(q_d_maxposex)) |> ignore
          set(q_d_expon, symval(q_d_maxnegex)).truthy()
        } else if eq(a, q_p_derivative) {
          set(q_derivflag, t) |> ignore
          set(q_derivlist, Nil) |> ignore
          false
        } else if get(a, q_evflag).truthy() {
          st.bndvars = cons(a, st.bndvars)
          st.bndvals = cons(get(a, q_evflag), st.bndvals)
          true
        } else if get(a, q_evfun).truthy() {
          st.exp = evfunmake(a, st.exp)
          st.evfunl = nconc(st.evfunl, list1(a))
          true
        } else {
          false
        }
      } else {
        false
      }
      if !handled {
        let fl = meval(a)
        if symbolp(fl) {
          if eq(fl, q_d_diff) {
            l = list_star([Nil, q_d_del, cdr(l)])
          } else if eq(fl, q_d_risch) {
            l = list_star([Nil, q_d_integrate, cdr(l)])
          }
          set(q_ear_nounl, cons(d_nounify(fl), symval(q_ear_nounl))) |> ignore
        } else if numberp(fl) {
          improper_arg_err(a, q_d_ev) |> ignore
        } else if stringp(fl) {
          improper_arg_err(a, q_d_ev) |> ignore
        } else if eq(caar(fl), q_mlist) {
          l = append(fl, cdr(l))
        } else if memq(
            caar(fl),
            list([q_msetq, q_mequal, q_mdefine, q_mdefmacro, q_mset]),
          ).truthy() {
          l = list_star([Nil, fl, cdr(l)])
        } else {
          improper_arg_err(a, q_d_ev) |> ignore
        }
      }
    } else if !memq(
        caar(a),
        list([
          q_msetq, q_mlist, q_mequal, q_mdefine, q_mdefmacro, q_d_expand, q_d_local,
          q_d_derivlist, q_mset,
        ]),
      ).truthy() {
      improper_arg_err(a, q_d_ev) |> ignore
    } else if eq(caar(a), q_d_expand) {
      if cdr(a) is Nil {
        set(q_d_expop, symval(q_d_maxposex)) |> ignore
        set(q_d_expon, symval(q_d_maxnegex)) |> ignore
      } else if cddr(a) is Nil {
        set(q_d_expop, meval(cadr(a))) |> ignore
        set(q_d_expon, symval(q_d_maxnegex)) |> ignore
      } else {
        set(q_d_expop, meval(cadr(a))) |> ignore
        set(q_d_expon, meval(caddr(a))) |> ignore
      }
    } else if eq(caar(a), q_mdefine) || eq(caar(a), q_mdefmacro) {
      with_special(q_d_use_fast_arrays, Nil, () => {
        let mut fun = cadr(a)
        if eq(caar(fun), q_mqapply) {
          fun = cadr(fun)
        }
        fun = d_verbify(caar(fun))
        st.funcl = nconc(st.funcl, list1(a))
        st.locvars = append(st.locvars, list1(fun))
        if rulechk(fun).truthy() {
          set(q_rulefcnl, cons(fun, symval(q_rulefcnl))) |> ignore
        }
      })
    } else if eq(caar(a), q_d_local) {
      st.locvars = append(st.locvars, cdr(a))
    } else if eq(caar(a), q_d_derivlist) {
      set(q_derivflag, t) |> ignore
      set(q_derivlist, cdr(a)) |> ignore
    } else {
      let mut a = a
      if eq(caar(a), q_mset) {
        l = cons(list3(list1(q_msetq), meval(cadr(a)), caddr(a)), cdr(l))
        a = car(l)
      }
      if eq(caar(a), q_msetq) || eq(caar(a), q_mequal) {
        if msetqp(a).truthy() && msetqp(caddr(a)).truthy() {
          l = nconc(kw_spread(a), cdr(l))
          a = car(l)
        }
        if noeval || !atom(cadr(a)) {
          st.subsl = nconc(st.subsl, list1(cons(caddr(a), cadr(a))))
        }
        if atom(cadr(a)) {
          st.bndvars = cons(cadr(a), st.bndvars)
          st.bndvals = cons(meval(specrepcheck(caddr(a))), st.bndvals)
        }
      } else {
        l = append(a, cdr(l))
      }
    }
    l = cdr(l)
  }
  // Ensure that MUNLOCAL gets called so that we don't leak any local
  // function definitions if we run into an error
  set(q_loclist, cons(Nil, symval(q_loclist))) |> ignore
  defer {
    munlocal() |> ignore
  }
  let bndvars = st.bndvars
  mlisp__mbinding(bndvars, bndvars, Nil, () => {
    with_special(q_mlocp, t, () => meval(cons(list1(q_d_local), st.locvars)))
    |> ignore
    with_special(q_d_translate, Nil, () => {
      for f in st.funcl.iter() {
        meval1(f) |> ignore
      }
    })
    st.exp = with_special(q_d_numer, Nil, () => mevalatoms(st.exp))
    if d_ratp(st.exp).truthy() {
      st.ratf = true
      st.exp = d_ratdisrep(st.exp)
    }
    if specrepp(st.exp).truthy() {
      st.exp = specdisrep(st.exp)
    }
    if st.subsl.truthy() {
      st.exp = simplify(st.exp)
      for item in st.subsl.iter() {
        let a = meval(car(item))
        let b = meval(cdr(item))
        st.exp = maxima_substitute(a, b, st.exp)
      }
    }
    Nil
  })
  |> ignore
  mlisp__mbinding(bndvars, st.bndvals, Nil, () => {
    st.exp = if noeval {
      resimplify(st.exp)
    } else {
      simplify(if st.predflg { mevalp(st.exp) } else { meval1(st.exp).0 })
    }
    if st.evflg > 0 || symval(q_d_infeval).truthy() {
      st.exp = specrepcheck(st.exp)
      while true {
        let mut exp2 = st.exp
        for f in st.evfunl.iter() {
          exp2 = list2(list1(f), exp2)
        }
        let mut exp1 = meval(exp2)
        for item in st.subsl.iter() {
          let a = meval(car(item))
          let b = meval(cdr(item))
          exp1 = maxima_substitute(a, b, exp1)
        }
        let mut done = false
        if !symval(q_d_infeval).truthy() {
          st.evflg -= 1
          done = st.evflg == 0
        }
        let done = if done {
          true
        } else {
          exp1 = specrepcheck(exp1)
          alike1(st.exp, exp1).truthy()
        }
        st.exp = exp1
        if done {
          break
        }
      }
    }
    if st.ratf && !symval(q_d_numer).truthy() && !symval(q_d_float).truthy() {
      st.exp = with_special(q_d_norepeat, Nil, () => ratf(st.exp))
    }
    Nil
  })
  |> ignore
  st.exp
}

///|
fn mevalatoms(exp_ : Value) -> Value raise {
  if atom(exp_) {
    meval1(exp_).0
  } else if memq(q_array, cdar(exp_)).truthy() {
    let exp1 = with_special(q_evarrp, t, () => catch_tag(q_evarrp, () => meval1(
      exp_,
    ).0))
    if eq(exp1, q_notexist) {
      cons(car(exp_), mapcar(x => mevalatoms(x), cdr(exp_)))
    } else {
      exp1
    }
  } else if eq(caar(exp_), q_mquote) {
    cadr(exp_)
  } else if eq(caar(exp_), q_msetq) || eq(caar(exp_), q_d_define) {
    twoargcheck(exp_) |> ignore
    list3(car(exp_), cadr(exp_), mevalatoms(caddr(exp_)))
  } else if (
      eq(caar(exp_), q_d_ev) &&
      cdr(exp_).truthy() &&
      (cddr(exp_) is Nil || equal(cddr(exp_), list1(q_d_eval)))
    ) ||
    eq(caar(exp_), q_mprogn) {
    cons(car(exp_), cons(mevalatoms(cadr(exp_)), cddr(exp_)))
  } else if memq(caar(exp_), list([q_d_sum, q_d_product, q_p_sum, q_p_product])).truthy() {
    arg_count_check(Fix(4L), exp_) |> ignore
    if symval(q_msump).truthy() {
      meval(exp_)
    } else {
      list([
        car(exp_),
        cadr(exp_),
        caddr(exp_),
        mevalatoms(cadddr(exp_)),
        mevalatoms(car(cddddr(exp_))),
      ])
    }
  } else if eq(caar(exp_), q_d__pctth) && fixnump(simplify(cadr(exp_))) {
    meval1(exp_).0
  } else if mlisp__autoldchk_mspecp(caar(exp_)) {
    exp_
  } else if mgetl(caar(exp_), list1(q_mfexprp)).truthy() {
    let mut a = cdadr(mget(caar(exp_), q_mexpr))
    let mut b = cdr(exp_)
    let mut l : Value = Nil
    let mut args : Value = Nil
    while true {
      if !(a.truthy() && b.truthy()) {
        args = nreverse(l)
        break
      }
      if mdeflistp(a).truthy() {
        args = nreconc(
          l,
          if mquotep(cadar(a)).truthy() {
            b
          } else {
            mapcar(x => mevalatoms(x), b)
          },
        )
        break
      } else if mquotep(car(a)).truthy() {
        l = cons(car(b), l)
      } else {
        l = cons(mevalatoms(car(b)), l)
      }
      a = cdr(a)
      b = cdr(b)
    }
    cons(car(exp_), args)
  } else if eq(caar(exp_), q_mmacroexpanded) ||
    (
      symval(q_d_transrun).truthy() &&
      get(caar(exp_), q_translated_mmacro).truthy()
    ) ||
    mget(caar(exp_), q_mmacro).truthy() {
    mevalatoms(mmacroexpand(exp_))
  } else {
    cons(car(exp_), mapcar(x => mevalatoms(x), cdr(exp_)))
  }
}

///|
fn mlisp__autoldchk_mspecp(op : Value) -> Bool raise {
  autoldchk(op) |> ignore
  getl(op, list1(q_mfexpr_star)).truthy() && !get(op, q_evok).truthy()
}

///|
fn evfunmake(fun : Value, exp_ : Value) -> Value raise {
  if msetqp(exp_).truthy() {
    list3(car(exp_), cadr(exp_), evfunmake(fun, caddr(exp_)))
  } else {
    list2(list1(fun), exp_)
  }
}

///|
fn kw_spread(x : Value) -> Value raise {
  let mut y = x
  while msetqp(caddr(y)).truthy() {
    y = caddr(y)
  }
  let val = caddr(y)
  let mut x = x
  let mut l : Value = Nil
  while msetqp(x).truthy() {
    l = cons(list3(car(x), cadr(x), val), l)
    x = caddr(x)
  }
  l
}

///|
fn msetqp(x : Value) -> Value raise {
  lbool(!atom(x) && eq(caar(x), q_msetq))
}

///|
fn mquotep(x : Value) -> Value raise {
  lbool(!atom(x) && eq(caar(x), q_mquote))
}

///|
fn mquote(form : Value) -> Value raise {
  cadr(form)
}

///|
fn d_subvarp(x : Value) -> Value raise {
  lbool(!atom(x) && memq(q_array, cdar(x)).truthy())
}

///|
/// Print a message that the assignment to NAME with the value VAL failed.
/// If REASON is given, print it out as the reason for the failure.
fn mseterr(name : Value, val : Value, reason? : Value = Nil) -> Value raise {
  if symval(q_munbindp).truthy() {
    q_munbindp
  } else if reason.truthy() {
    merr("assignment: cannot assign `~M' to `~:M': ~M.", [val, name, reason])
  } else {
    merr("assignment: cannot assign `~M' to `~:M'.", [val, name])
  }
}

///|
/// When $numer is set, also set $float to the same value.
fn numerset(assign_var : Value, y : Value) -> Value raise {
  ignore(assign_var)
  mset(q_d_float, y)
}

///|
/// Variables that are read-only and should never changed by the user. This
/// is a possible value for the 'assign property.
fn neverset(x : Value, assign_val : Value) -> Value raise {
  if symval(q_munbindp).truthy() {
    q_munbindp
  } else {
    merr("assignment: attempting to assign read-only variable ~:M the value ~M", [
      x, assign_val,
    ])
  }
}

///|
/// Check assignment that the assignment to the variable X is a
/// non-negative integer Y.  If not signal an error.
fn non_negative_integer_set(x : Value, y : Value) -> Value raise {
  if !integerp(y) || !num_ge(y, Fix(0L)) {
    merr("assignment: '~:M must be a non-negative integer. Found: ~:M", [x, y])
  } else {
    Nil
  }
}

///|
fn mmapev(l : Value) -> Value raise {
  if cddr(l) is Nil {
    merr("~:M: expected two or more arguments; found: ~M", [
      caar(l),
      cons(list1(q_mlist), cdr(l)),
    ])
    |> ignore
  }
  let op = getopr(meval(cadr(l)))
  autoldchk(op) |> ignore
  badfunchk(cadr(l), op, Nil) |> ignore
  cons(op, mapcar(x => meval(x), cddr(l)))
}

///|
/// defmspec ($map :properties ((evok t)))
fn mlisp__d_map(l : Value) -> Value raise {
  map1(mmapev(l))
}

///|
fn map1(n : Value) -> Value raise {
  let args = list_to_array(n)
  let n = args.length()
  // MAPLP tells MAP1 that it was invoked by MAPLIST. Capture it and rebind
  // the special to NIL so that a nested MAP inside a function called from
  // MAPLIST does not see MAPLIST's binding.
  let maplistp = symval(q_maplp).truthy()
  with_special(q_maplp, Nil, () => {
    let mut i = n
    args[n - 1] = format1(args[n - 1])
    let mut argi = args[n - 1]
    let op = {
      let m = mapatom(args[n - 1])
      if m.truthy() {
        m
      } else {
        mop(args[n - 1])
      }
    }
    let mut flag = mapatom(args[n - 1])
    let mut argl : Value = Nil
    let mut cdrl : Value = Nil
    while i != 1 {
      let old_argi = argi
      let new_argi = format1(args[i - 2])
      let new_flag = if flag.truthy() {
        flag
      } else {
        flag = mapatom(old_argi)
        if flag.truthy() {
          flag
        } else if !maplistp && !alike1(mop(old_argi), op).truthy() {
          t
        } else {
          Nil
        }
      }
      let new_argl = cons(old_argi, argl)
      let new_cdrl = if flag.truthy() {
        flag
      } else {
        cons(margs(old_argi), cdrl)
      }
      i = i - 1
      argi = new_argi
      flag = new_flag
      argl = new_argl
      cdrl = new_cdrl
    }
    if flag.truthy() {
      if !symval(q_d_maperror).truthy() {
        if symval(q_d_mapprint).truthy() {
          mtell(list1(Str("map: calling 'apply'"))) |> ignore
        }
        funcer(args[0], argl)
      } else if n == 2 && mapatom(args[1]).truthy() {
        improper_arg_err(args[1], q_d_map)
      } else {
        // OP is literally T when the last argument is a mapatom; print the
        // argument itself then. Same for the first argument, on which MOP
        // would signal a Lisp error.
        merr("map: arguments must have same main operator; found: ~M, ~M", [
          if eq(op, t) {
            args[n - 1]
          } else {
            op
          },
          {
            let u = first(argl)
            if mapatom(u).truthy() {
              u
            } else {
              mop(u)
            }
          },
        ])
      }
    } else {
      mcons_op_args(op, mmapcar(cons(args[0], cdrl)))
    }
  })
}

///|
/// defmspec ($maplist :properties ((evok t)))
fn mlisp__d_maplist(l : Value) -> Value raise {
  with_special(q_maplp, t, () => {
    let res = map1(mmapev(l))
    if atom(res) {
      list2(list1(q_mlist), res)
    } else if eq(caar(res), q_mlist) {
      res
    } else {
      cons(list1(q_mlist), margs(res))
    }
  })
}

///|
fn mmapcar(n : Value) -> Value raise {
  let args = list_to_array(n)
  let n = args.length()
  let mut ans : Value = Nil
  let mut argl : Value = Nil
  while true {
    let mut stop = false
    let mut i = n
    while i != 1 {
      if args[i - 1] is Nil {
        let mut others = false
        for j in 2..<n {
          if args[j - 1].truthy() {
            others = true
            break
          }
        }
        if i < n || others {
          if symval(q_d_maperror).truthy() {
            merr("map: arguments must be the same length.", []) |> ignore
          }
          if symval(q_d_mapprint).truthy() {
            mtell(list1(Str("map: truncating one or more arguments."))) |> ignore
          }
        }
        stop = true
        break
      }
      argl = cons(car(args[i - 1]), argl)
      args[i - 1] = cdr(args[i - 1])
      i -= 1
    }
    if stop {
      break
    }
    ans = cons(funcer(args[0], argl), ans)
    argl = Nil
  }
  nreverse(ans)
}

///|
fn mapatom(x : Value) -> Value raise {
  let a = d_atom(x)
  if a.truthy() {
    return a
  }
  let b = mnump(x)
  if b.truthy() {
    return b
  }
  if eq(caar(x), q_mminus) && mnump(cadr(x)).truthy() {
    return t
  }
  let c = d_subvarp(x)
  if c.truthy() {
    return c
  }
  op_equalp(x, list2(q_d_op_at, q_p_op_at))
}

///|
fn d_mapatom(x : Value) -> Value raise {
  if mapatom(specrepcheck(x)).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// defmspec ($fullmap :properties ((evok t)))
fn mlisp__d_fullmap(l : Value) -> Value raise {
  let l = mmapev(l)
  fmap1(car(l), cdr(l), Nil)
}

///|
fn fmap1(fn_ : Value, argl : Value, fmapcaarl : Value) -> Value raise {
  let argl = mapcar(x => format1(x), argl)
  let op = {
    let m = mapatom(car(argl))
    if m.truthy() {
      m
    } else {
      mop(car(argl))
    }
  }
  with_special(q_fmaplvl, num_sub(symval(q_fmaplvl), Fix(1L)), () => {
    let mut cdr1 = argl
    let mut cdrl : Value = Nil
    while cdr1 is Cons(_) {
      let argi = car(cdr1)
      if mapatom(argi).truthy() ||
        !alike1(op, mop(argi)).truthy() ||
        (fmapcaarl.truthy() && !eq(caar(argi), fmapcaarl)) {
        if symval(q_d_maperror).truthy() {
          merr("fullmap: arguments must have same operators.", []) |> ignore
        } else {
          if symval(q_d_mapprint).truthy() {
            mtell(list1(Str("fullmap: calling 'apply'.~%"))) |> ignore
          }
          return funcer(fn_, argl)
        }
      }
      cdrl = cons(margs(car(cdr1)), cdrl)
      cdr1 = cdr(cdr1)
    }
    let mut ans : Value = Nil
    let mut carargl : Value = Nil
    let mut cdrargl : Value = Nil
    let mut bottom : Value = Nil
    let mut done = false
    if memq(Nil, cdrl).truthy() {
      if some(e => e.truthy(), cdrl) {
        if symval(q_d_maperror).truthy() {
          merr("fullmap: arguments must have same formal structure.", [])
          |> ignore
        }
        if symval(q_d_mapprint).truthy() {
          mtell(list1(Str("fullmap: truncating one or more arguments.~%")))
          |> ignore
        }
      }
      done = true
    }
    while !done {
      bottom = lbool(
        zerop(symval(q_fmaplvl)) || mapatom(caar(cdrl)).truthy(),
      )
      let op2 = if bottom.truthy() { bottom } else { mop(caar(cdrl)) }
      let mut eleml = cdrl
      while eleml is Cons(_) {
        let caareleml = caar(eleml)
        if !bottom.truthy() {
          bottom = lbool(
            mapatom(caareleml).truthy() ||
            !alike1(op2, mop(caareleml)).truthy() ||
            (fmapcaarl.truthy() && !eq(caar(caareleml), fmapcaarl)),
          )
        }
        if !done {
          done = cdar(eleml) is Nil
        }
        carargl = nconc(carargl, list1(caareleml))
        cdrargl = nconc(cdrargl, list1(cdar(eleml)))
        eleml = cdr(eleml)
      }
      if done && some(e => e.truthy(), cdrargl) {
        if symval(q_d_maperror).truthy() {
          merr("fullmap: arguments must have same formal structure.", [])
          |> ignore
        }
        if symval(q_d_mapprint).truthy() {
          mtell(list1(Str("fullmap: truncating one or more arguments.~%")))
          |> ignore
        }
      }
      ans = cons(
        if bottom.truthy() {
          funcer(fn_, carargl)
        } else {
          fmap1(fn_, carargl, fmapcaarl)
        },
        ans,
      )
      cdrl = cdrargl
      carargl = Nil
      cdrargl = Nil
      bottom = Nil
    }
    mcons_op_args(op, nreverse(ans))
  })
}

///|
/// defmspec ($matrixmap :properties ((evok t)))
fn mlisp__d_matrixmap(l : Value) -> Value raise {
  with_special(q_fmaplvl, Fix(2L), () => {
    let m = mmapev(l)
    fmapl1(car(m), cdr(m))
  })
}

///|
/// defmspec ($fullmapl :properties ((evok t)))
fn mlisp__d_fullmapl(l : Value) -> Value raise {
  let m = mmapev(l)
  fmapl1(car(m), cdr(m))
}

///|
fn fmapl1(fun : Value, args : Value) -> Value raise {
  let mut header = list1(q_mlist)
  let argl = fmap1(
    fun,
    mapcar(
      z => if !mxorlistp(z).truthy() {
        merr("fullmapl: argument must be a list or matrix; found: ~M", [
          if consp(z) {
            let m = mop(z)
            if m.truthy() {
              m
            } else {
              z
            }
          } else {
            z
          },
        ])
      } else if eq(caar(z), q_d_matrix) {
        header = list1(q_d_matrix)
        cons(list2(q_mlist, q_simp), cdr(z))
      } else {
        z
      },
      args,
    ),
    q_mlist,
  )
  if some(e => !d_listp(e).truthy(), cdr(argl)) {
    argl
  } else {
    cons(header, cdr(argl))
  }
}

///|
fn d_outermap(x : Value, y : Value, z : Value) -> Value raise {
  if z.truthy() {
    outermap1(cons(x, cons(y, z)))
  } else {
    fmapl1(x, list1(y))
  }
}

///|
/// `(listify k)` over a lexpr argument array: the first k arguments for
/// k >= 0, the last -k ones otherwise.
fn mlisp__listify(args : Array[Value], k : Int) -> Value {
  let n = args.length()
  if k >= 0 {
    list_view(args[0:k])
  } else {
    list_view(args[n + k:n])
  }
}

///|
fn outermap1(n : Value) -> Value raise {
  let args = list_to_array(n)
  let n = args.length()
  with_specials([(q_outargs1, Nil), (q_outargs2, Nil)], () => {
    if mxorlistp(args[1]).truthy() {
      set(q_outargs1, list1(args[0])) |> ignore
      set(q_outargs2, mlisp__listify(args, 2 - n)) |> ignore
      fmapl1(q_outermap2, list1(args[1]))
    } else {
      for i in 3..=n {
        if mxorlistp(args[i - 1]).truthy() {
          set(q_outargs1, mlisp__listify(args, i - 1)) |> ignore
          set(
            q_outargs2,
            if i < n {
              mlisp__listify(args, i - n)
            } else {
              Nil
            },
          )
          |> ignore
          return fmapl1(q_outermap2, list1(args[i - 1]))
        }
      }
      funcer(args[0], mlisp__listify(args, 1 - n))
    }
  })
}

///|
fn outermap2(args : Value) -> Value raise {
  if args is Nil {
    Nil
  } else {
    outermap1(
      append(symval(q_outargs1), cons(first(args), symval(q_outargs2))),
    )
  }
}

///|
fn funcer(fn_ : Value, args : Value) -> Value raise {
  if eq(fn_, q_mplus) || eq(fn_, q_mtimes) || eq(fn_, q_mexpt) || eq(fn_, q_mnctimes) {
    simplify(cons(list1(fn_), args))
  } else if eq(fn_, q_outermap2) ||
    eq(fn_, q_constfun) ||
    (
      symval(q_d_transrun).truthy() &&
      symbolp(fn_) &&
      get(fn_, q_translated).truthy() &&
      !mget(fn_, q_local_fun).truthy() &&
      fboundp(fn_)
    ) {
    apply(fn_, mapcar(x => simplify(x), args))
  } else {
    // try to get more info to pass
    mapply1(fn_, mapcar(x => simplify(x), args), fn_, Nil)
  }
}

///|
fn d_qput(l : Value) -> Value raise {
  let l = cdr(l)
  if length(l) != 3 {
    wna_err(q_d_qput) |> ignore
  }
  d_put(car(l), cadr(l), caddr(l))
}

///|
fn d_rem(atom_ : Value, ind : Value) -> Value raise {
  prop1(q_d_rem, atom_, Nil, ind)
}

///|
fn d_put(atom_ : Value, val : Value, ind : Value) -> Value raise {
  let r = prop1(q_d_put, atom_, val, ind)
  add2lnc(atom_, symval(q_d_props)) |> ignore
  r
}

///|
fn prop1(fun : Value, atom_ : Value, val : Value, ind : Value) -> Value raise {
  if !(symbolp(atom_) || stringp(atom_)) {
    merr("~:M: argument must be a symbol or a string; found: ~M", [fun, atom_])
    |> ignore
  }
  if !(symbolp(ind) || stringp(ind)) {
    merr("~:M: indicator must be a symbol or a string; found: ~M", [fun, ind])
    |> ignore
  }
  let mut atom_ = atom_
  let mut ind = ind
  if !symbolp(atom_) {
    if symbolp(getopr(atom_)) {
      atom_ = getopr(atom_)
    } else {
      atom_ = intern(lstring(atom_)).to_value()
    }
  }
  if !symbolp(ind) {
    ind = intern(lstring(ind)).to_value()
  }
  let u = mget(atom_, q_d_props)
  if eq(fun, q_d_get) {
    if u.truthy() {
      getf(cdr(u), ind)
    } else {
      Nil
    }
  } else if eq(fun, q_d_rem) {
    if u.truthy() && zl_remprop(u, ind).truthy() {
      q_d_done
    } else {
      Nil
    }
  } else if !u.truthy() {
    mputprop(atom_, list3(Nil, ind, val), q_d_props) |> ignore
    val
  } else {
    putprop_(u, val, ind)
  }
}

///|
fn d_declare(l : Value) -> Value raise {
  let mut l = cdr(l)
  if oddp(int(length(l))) {
    merr("declare: number of arguments must be a multiple of 2.", []) |> ignore
  }
  let mut vars : Value = Nil
  while l is Cons(_) {
    let mut flag = false
    let prop = cadr(l)
    if d_listp(prop).truthy() {
      for l1 in cdr(prop).iter() {
        meval(list3(list1(q_d_declare), car(l), l1)) |> ignore
      }
      flag = true
    } else if nonsymchk(prop, q_d_declare).truthy() {
      ()
    } else {
      vars = declsetup(car(l), q_d_declare)
    }
    if flag {
      ()
    } else if eq(prop, q_d_evfun) ||
      eq(prop, q_d_evflag) ||
      eq(prop, q_d_nonarray) ||
      eq(prop, q_d_bindtest) {
      declare1(vars, t, stripdollar(prop), Nil) |> ignore
    } else if eq(prop, q_d_noun) {
      for var_ in vars.iter() {
        alias(getopr(var_), d_nounify(var_)) |> ignore
      }
    } else if eq(prop, q_d_nonscalar) || eq(prop, q_d_scalar) || eq(prop, q_d_mainvar) {
      declare1(vars, t, prop, t) |> ignore
    } else if eq(prop, q_d_alphabetic) {
      declare1(vars, t, t, q_d_alphabetic) |> ignore
    } else if memq(prop, symval(q_opers)).truthy() {
      if memq(prop, cdr(symval(q_d_features))).truthy() {
        declare1(vars, t, prop, q_kind) |> ignore
      }
      declare1(mapcar(v => getopr(v), vars), t, prop, q_opers) |> ignore
    } else if memq(prop, cdr(symval(q_d_features))).truthy() {
      declare1(vars, t, prop, q_kind) |> ignore
    } else if eq(prop, q_d_feature) {
      for var_ in vars.iter() {
        nonsymchk(var_, q_d_declare) |> ignore
        add2lnc(var_, symval(q_d_features)) |> ignore
      }
    } else {
      merr("declare: unknown property ~:M", [prop]) |> ignore
    }
    l = cddr(l)
  }
  q_d_done
}

///|
fn declare1(vars : Value, val : Value, prop : Value, mpropp : Value) -> Value raise {
  for var0 in vars.iter() {
    if !(symbolp(var0) || stringp(var0)) {
      merr("declare: argument must be a symbol or a string; found: ~M", [var0])
      |> ignore
    }
    if eq(mpropp, q_d_alphabetic) {
      // Explode var into characters and put each one on the *alphabet*
      // list, which is used by src/nparse.lisp .
      if !stringp(var0) {
        merr("declare: alphabetic declaration requires a string; found: ~M", [
          var0,
        ])
        |> ignore
      }
      for ch in lstring(var0) {
        add2lnc(Char(ch), symval(q_ear_alphabet)) |> ignore
      }
    } else {
      let mut var_ = getopr(var0)
      if eq(mpropp, q_kind) {
        declarekind(var_, prop) |> ignore
      } else if eq(mpropp, q_opers) {
        let lbp = get(var_, q_lbp)
        let rbp = get(var_, q_rbp)
        if lbp.truthy() && rbp.truthy() {
          if eq(prop, q_d_rassociative) && num_ge(lbp, rbp) {
            mtell(
              list([
                Str(
                  "Warning: Declaring ~M right-associative, but its parser binding powers (LBP ~M >= RBP ~M) make it parse left-to-right.",
                ),
                var_,
                lbp,
                rbp,
              ]),
            )
            |> ignore
          } else if eq(prop, q_d_lassociative) && num_lt(lbp, rbp) {
            mtell(
              list([
                Str(
                  "Warning: Declaring ~M left-associative, but its parser binding powers (LBP ~M < RBP ~M) make it parse right-to-left.",
                ),
                var_,
                lbp,
                rbp,
              ]),
            )
            |> ignore
          }
        }
        var_ = linchk(var_)
        putprop_(var_, t, prop) |> ignore
        putprop_(var_, t, q_opers) |> ignore
      } else if mpropp.truthy() {
        if (eq(prop, q_d_scalar) || eq(prop, q_d_nonscalar)) &&
          mget(
            var_,
            if eq(prop, q_d_scalar) {
              q_d_nonscalar
            } else {
              q_d_scalar
            },
          ).truthy() {
          merr("declare: inconsistent declaration ~:M", [
            list3(list1(q_d_declare), var_, prop),
          ])
          |> ignore
        }
        mputprop(var_, val, prop) |> ignore
      } else {
        putprop_(var_, val, prop) |> ignore
      }
      if safe_get(var_, q_op).truthy() && mlisp__operatorp1(var_) {
        var_ = get(var_, q_op)
        if !memq(var_, cdr(symval(q_d_props))).truthy() {
          set(q_ear_mopl, cons(var_, symval(q_ear_mopl))) |> ignore
        }
      }
      add2lnc(getop(var_), symval(q_d_props)) |> ignore
    }
  }
  Nil
}

///|
fn linchk(var_ : Value) -> Value raise {
  if eq(var_, q_d_sum) ||
    eq(var_, q_d_integrate) ||
    eq(var_, q_d_limit) ||
    eq(var_, q_d_diff) ||
    eq(var_, q_d_transpose) {
    d_nounify(var_)
  } else {
    var_
  }
}

///|
fn d_remove(form : Value) -> Value raise {
  with_special(q_ear_fact_protected, Nil, () => {
    i__dolremove(cdr(form)) |> ignore
    if symval(q_ear_fact_protected).truthy() {
      q_d_not_done
    } else {
      q_d_done
    }
  })
}

///|
fn mlisp__memq_list(x : Value, l : Array[Value]) -> Bool {
  for y in l {
    if eq(x, y) {
      return true
    }
  }
  false
}

///|
fn i__dolremove(l : Value) -> Value raise {
  if oddp(int(length(l))) {
    merr("remove: number of arguments must be a multiple of 2.", []) |> ignore
  }
  let mut l = l
  let mut vars : Value = Nil
  while l is Cons(_) {
    let mut flag = false
    let prop = cadr(l)
    if d_listp(prop).truthy() {
      for l1 in cdr(prop).iter() {
        i__dolremove(list2(car(l), l1)) |> ignore
      }
      flag = true
    } else if !(symbolp(prop) || stringp(prop)) {
      merr("remove: argument must be a symbol or a string; found: ~M", [prop])
      |> ignore
    } else {
      vars = declsetup(car(l), q_d_remove)
    }
    if flag {
      ()
    } else if eq(prop, q_d_value) {
      i__dolremvalue(vars) |> ignore
    } else if eq(prop, q_d_function) {
      remove1(
        mapcar(v => d_verbify(v), vars),
        q_mexpr,
        t,
        symval(q_d_functions),
        t,
      )
      |> ignore
    } else if eq(prop, q_d_macro) {
      remove1(mapcar(v => d_verbify(v), vars), q_mmacro, t, symval(q_d_macros), t)
      |> ignore
    } else if eq(prop, q_d_array) {
      meval(cons(list1(q_d_remarray), vars)) |> ignore
    } else if eq(prop, q_d_alias) || eq(prop, q_d_noun) {
      remalias1(vars, lbool(eq(prop, q_d_alias))) |> ignore
    } else if eq(prop, q_d_matchdeclare) {
      remove1(vars, q_matchdeclare, t, t, Nil) |> ignore
    } else if eq(prop, q_d_rule) {
      remrule(
        mapcar(
          v => if stringp(v) {
            d_verbify(v)
          } else {
            v
          },
          vars,
        ),
      )
      |> ignore
    } else if mlisp__memq_list(prop, [
        q_d_evfun, q_d_evflag, q_d_nonarray, q_d_bindtest, q_d_autoload, q_d_assign,
      ]) {
      remove1(vars, stripdollar(prop), Nil, t, Nil) |> ignore
    } else if eq(prop, q_d_mode) || eq(prop, q_d_modedeclare) {
      remove1(vars, q_mode, Nil, q_foo, Nil) |> ignore
    } else if eq(prop, q_d_atvalue) {
      remove1(vars, q_atvalues, t, t, Nil) |> ignore
    } else if mlisp__memq_list(prop, [
        q_d_nonscalar, q_d_scalar, q_d_mainvar, q_d_numer, q_d_atomgrad,
      ]) {
      remove1(vars, prop, t, t, Nil) |> ignore
    } else if memq(prop, symval(q_opers)).truthy() {
      remove1(mapcar(v => linchk(v), vars), prop, Nil, t, Nil) |> ignore
    } else if memq(prop, cdr(symval(q_d_features))).truthy() {
      remove1(vars, prop, Nil, t, Nil) |> ignore
    } else if eq(prop, q_d_feature) {
      for var_ in vars.iter() {
        set(q_d_features, mlisp__delete1_eq(var_, symval(q_d_features))) |> ignore
      }
    } else if eq(prop, q_d_alphabetic) || eq(prop, q_d_transfun) {
      remove1(vars, prop, Nil, t, Nil) |> ignore
    } else if eq(prop, q_d_gradef) || eq(prop, q_d_grad) {
      remove1(vars, q_grad, Nil, symval(q_d_gradefs), t) |> ignore
    } else if mlisp__memq_list(prop, [q_d_dependency, q_d_depend, q_d_depends]) {
      remove1(vars, q_depends, t, symval(q_d_dependencies), t) |> ignore
    } else if eq(prop, q_d_op) || eq(prop, q_d_operator) {
      remove1(vars, q_d_op, Nil, q_foo, Nil) |> ignore
    } else if eq(prop, q_d_deftaylor) || eq(prop, q_d_taylordef) {
      remove1(vars, q_sp2, Nil, t, Nil) |> ignore
    } else {
      merr("remove: unknown property ~:M", [prop]) |> ignore
    }
    l = cddr(l)
  }
  q_d_done
}

///|
fn declsetup(x : Value, fn_ : Value) -> Value raise {
  if atom(x) {
    list1(x)
  } else if eq(caar(x), q_d_nounify) {
    list1(meval(x))
  } else if eq(caar(x), q_mlist) {
    mapcar(
      var_ => if atom(var_) {
        var_
      } else if eq(caar(var_), q_d_nounify) {
        meval(var_)
      } else {
        improper_arg_err(var_, fn_)
      },
      cdr(x),
    )
  } else {
    improper_arg_err(x, fn_)
  }
}

///|
fn remove1(
  vars : Value,
  prop : Value,
  mpropp : Value,
  info : Value,
  funp : Value,
) -> Value raise {
  let mut vars = vars
  let mut info = info
  let mut allflg = false
  while vars is Cons(_) {
    let v0 = car(vars)
    if !(symbolp(v0) || stringp(v0)) {
      merr("remove: argument must be a symbol or a string; found: ~M", [v0])
      |> ignore
    }
    if eq(v0, q_d_all) && !allflg {
      vars = append(
        vars,
        if atom(info) {
          cdr(symval(q_d_props))
        } else if funp.truthy() {
          mapcar(x => caar(x), cdr(info))
        } else {
          cdr(info)
        },
      )
      allflg = true
    } else {
      if stringp(v0) && eq(prop, q_d_op) && getopr0(v0).truthy() {
        kill_operator(getopr0(v0)) |> ignore
      }
      if eq(prop, q_d_alphabetic) && stringp(v0) {
        for ch in lstring(v0) {
          set(q_ear_alphabet, mlisp__delete1_equal(Char(ch), symval(q_ear_alphabet)))
          |> ignore
        }
      } else {
        let var_ = getopr(v0)
        if mpropp.truthy() {
          mremprop(var_, prop) |> ignore
          if eq(prop, q_mexpr) || eq(prop, q_mmacro) {
            mremprop(var_, q_mlexprp) |> ignore
            mremprop(var_, q_mfexprp) |> ignore
            remprop(var_, q_lineinfo) |> ignore
            if mget(var_, q_trace).truthy() {
              macsyma_untrace(var_) |> ignore
            }
          }
        } else if eq(prop, q_d_transfun) {
          remove_transl_fun_props(var_) |> ignore
          remove_transl_array_fun_props(var_) |> ignore
        } else {
          let flag = memq(prop, cdr(symval(q_d_features))).truthy()
          if flag || memq(prop, symval(q_opers)).truthy() {
            if flag {
              unkind(var_, prop) |> ignore
            }
            zl_remprop(var_, prop) |> ignore
            if !getl(var_, mlisp__delete1_eq(prop, copy_list(symval(q_opers)))).truthy() {
              zl_remprop(var_, q_opers) |> ignore
            }
          } else {
            zl_remprop(var_, prop) |> ignore
          }
        }
        if eq(info, t) {
          rempropchk(v0) |> ignore
        } else if eq(info, q_foo) {
          ()
        } else if funp.truthy() {
          mfunction_delete(var_, info) |> ignore
        } else {
          info = mlisp__delete1_eq(var_, info)
        }
      }
    }
    vars = cdr(vars)
  }
  Nil
}

///|
fn remove_transl_fun_props(fun : Value) -> Value raise {
  if mget(fun, q_trace).truthy() {
    macsyma_untrace(fun) |> ignore
  }
  if get(fun, q_translated).truthy() {
    fmakunbound(fun) |> ignore
    let impl_ = get(fun, q_impl_name)
    if fboundp(impl_) {
      fmakunbound(impl_) |> ignore
    }
    zl_remprop(fun, q_impl_name) |> ignore
    zl_remprop(fun, q_arg_list) |> ignore
    zl_remprop(fun, q_translated_mmacro) |> ignore
    zl_remprop(fun, q_function_mode) |> ignore
    if !get(fun, q_a_subr).truthy() {
      zl_remprop(fun, q_once_translated) |> ignore
      zl_remprop(fun, q_translated) |> ignore
    }
  }
  Nil
}

///|
fn remove_transl_array_fun_props(fun : Value) -> Value raise {
  if get(fun, q_translated).truthy() {
    zl_remprop(fun, q_a_subr) |> ignore
    zl_remprop(fun, q_arrayfun_mode) |> ignore
    if !fboundp(fun) {
      zl_remprop(fun, q_translated) |> ignore
    }
  }
  Nil
}

///|
fn rempropchk(var_ : Value) -> Value raise {
  let opr = getopr(var_)
  if (
      !symbolp(opr) ||
      (
        !mgetl(
          opr,
          list([
            q_d_nonscalar, q_d_scalar, q_d_mainvar, q_d_numer, q_matchdeclare, q_d_atomgrad,
            q_atvalues,
          ]),
        ).truthy() &&
        !getl(
          opr,
          list([
            q_evfun, q_evflag, q_translated, q_nonarray, q_bindtest, q_sp2, q_operators,
            q_opers, q_data, q_autoload, q_mode,
          ]),
        ).truthy() &&
        {
          let op = get(opr, q_op)
          op is Nil || member_equal(op, symval(q_ear_mopl)).truthy()
        }
      )
    ) &&
    !member_equal(var_, symval(q_ear_builtin__dolprops)).truthy() {
    mlisp__delete1_equal(var_, symval(q_d_props))
  } else {
    Nil
  }
}

///|
fn d_remfunction(l : Value) -> Value raise {
  let mut l = cdr(l)
  if memq(q_d_all, l).truthy() {
    l = nconc(
      mapcar(x => caar(x), cdr(symval(q_d_functions))),
      mapcar(x => caar(x), cdr(symval(q_d_macros))),
    )
  } else {
    l = mapcar(x => d_verbify(x), l)
    let mut l1 = l
    while l1 is Cons(_) {
      if !(
          assoc_equal(list1(car(l1)), cdr(symval(q_d_functions))).truthy() ||
          assoc_equal(list1(car(l1)), cdr(symval(q_d_macros))).truthy()
        ) {
        rplaca(l1, Nil) |> ignore
      }
      l1 = cdr(l1)
    }
  }
  remove1(l, q_mexpr, t, symval(q_d_functions), t) |> ignore
  remove1(l, q_mmacro, t, symval(q_d_macros), t) |> ignore
  cons(list1(q_mlist), l)
}

///|
fn d_remarray(l : Value) -> Value raise {
  let mut l = cdr(l)
  let mut x : Value = Nil
  while l is Cons(_) {
    if eq(car(l), q_d_all) {
      l = append(l, cdr(symval(q_d_arrays)))
    } else {
      remcompary(car(l)) |> ignore
      let mut pred = mremprop(car(l), q_array)
      pred = mlisp__or(mremprop(car(l), q_hashar), () => pred)
      pred = mlisp__or(mremprop(car(l), q_aexpr), () => pred)
      x = cons(
        if pred.truthy() {
          set(q_d_arrays, mlisp__delete1_eq(car(l), symval(q_d_arrays)))
          |> ignore
          car(l)
        } else {
          Nil
        },
        x,
      )
    }
    l = cdr(l)
  }
  cons(list1(q_mlist), nreverse(x))
}

///|
fn remcompary(x : Value) -> Value raise {
  if eq(x, mget(x, q_array)) {
    zl_remprop(x, q_array_mode) |> ignore
    zl_remprop(x, q_array)
  } else {
    Nil
  }
}

///|
fn d_remvalue(form : Value) -> Value raise {
  i__dolremvalue(cdr(form))
}

///|
fn i__dolremvalue(l : Value) -> Value raise {
  let mut l = l
  let mut x : Value = Nil
  while l is Cons(_) {
    if eq(car(l), q_d_all) {
      l = append(l, cdr(symval(q_d_values)))
    } else {
      x = cons(
        if atom(car(l)) {
          if remvalue(car(l), q_d_remvalue).truthy() {
            car(l)
          } else {
            Nil
          }
        } else {
          let y = mgetl(caaar(l), list2(q_hashar, q_array))
          if y.truthy() {
            remarrelem(y, car(l)) |> ignore
            car(l)
          } else {
            Nil
          }
        },
        x,
      )
    }
    l = cdr(l)
  }
  cons(list1(q_mlist), nreverse(x))
}

///|
fn remarrelem(ary : Value, form : Value) -> Value raise {
  // ARRAY-ELEMENT-TYPE is always T for arrays created by $ARRAY (they are
  // never specialized), so consult the ARRAY-MODE property as well: per
  // the LISTARRAY documentation, unbound elements of FIXNUM/FLONUM arrays
  // read as 0/0.0. For an array with an associated function, store
  // MUNBOUND instead so that the next read recomputes the element rather
  // than finding a made-up 0.
  let mode = safe_get(caar(form), q_array_mode)
  let y = car(arraydims(cadr(ary)))
  arrstore(
    form,
    if arrfunp(caar(form)).truthy() {
      symval(q_munbound)
    } else if eq(y, q_fixnum) || eq(mode, q_d_fixnum) {
      Fix(0L)
    } else if eq(y, q_flonum) || eq(mode, q_d_float) {
      Flo(0.0)
    } else {
      symval(q_munbound)
    },
  )
}

///|
fn remrule(l : Value) -> Value raise {
  let mut l = l
  while l is Cons(_) {
    let r = car(l)
    if eq(r, q_d_all) {
      l = append(l, cdr(symval(q_d_rules)))
    } else if get(r, q_operators).truthy() {
      d_remrule(r, q_d_all) |> ignore
    } else {
      let u = ruleof(r)
      if u.truthy() {
        d_remrule(u, r) |> ignore
      } else if mget(r, q_d_rule).truthy() {
        zl_remprop(r, q_expr) |> ignore
        mremprop(r, q_d_rule) |> ignore
        set(q_d_rules, mlisp__delete1_eq(r, symval(q_d_rules))) |> ignore
      }
    }
    l = cdr(l)
  }
  Nil
}

///|
fn remalias1(l : Value, aliasp : Value) -> Value raise {
  let mut l = l
  while l is Cons(_) {
    let a = car(l)
    if eq(a, q_d_all) {
      l = append(l, cdr(symval(q_d_aliases)))
    } else if aliasp.truthy() || get(a, q_noun).truthy() {
      remalias(a, remp=t) |> ignore
    } else {
      let u = get(a, q_verb)
      if u.truthy() {
        zl_remprop(a, q_verb) |> ignore
        zl_remprop(u, q_noun) |> ignore
      }
    }
    l = cdr(l)
  }
  Nil
}

///|
fn mremprop(atom_ : Value, ind : Value) -> Value raise {
  let props = get(atom_, q_mprops)
  if props.truthy() {
    zl_remprop(props, ind)
  } else {
    Nil
  }
}

///|
fn mgetl(atom_ : Value, inds : Value) -> Value raise {
  let props = get(atom_, q_mprops)
  if props.truthy() {
    getl(props, inds)
  } else {
    Nil
  }
}

///|
fn d_declare_index_properties(form : Value) -> Value raise {
  let a = cdr(form)
  if oddp(int(length(a))) {
    merr(
      "declare_index_properties: number of arguments must be even; found: ~M",
      [cons(list1(q_mlist), a)],
    )
    |> ignore
  }
  let mut l = a
  while l is Cons(_) {
    declare_index_properties_1(first(l), second(l)) |> ignore
    l = cddr(l)
  }
  q_d_done
}

///|
fn declare_index_properties_1(x : Value, l : Value) -> Value raise {
  if !(symbolp(x) || (d_listp(x).truthy() && every(y => symbolp(y), cdr(x)))) {
    merr(
      "declare_index_properties: first argument must be a symbol or a list of symbols; found: ~M",
      [x],
    )
    |> ignore
  }
  if !d_listp(l).truthy() {
    merr("declare_index_properties: second argument must be a list; found: ~M", [
      l,
    ])
    |> ignore
  }
  if !every(
      y => member(y, cdr(symval(q_d_known_index_properties))).truthy(),
      cdr(l),
    ) {
    merr(
      "declare_index_properties: unknown index property; found: ~M~%declare_index_properties: known properties are: ~M",
      [l, symval(q_d_known_index_properties)],
    )
    |> ignore
  }
  if d_listp(x).truthy() {
    mapcar(x1 => mputprop(x1, cdr(l), q_display_indices), cdr(x))
  } else {
    mputprop(x, cdr(l), q_display_indices)
  }
}

///|
fn d_get_index_properties(a : Value) -> Value raise {
  if !symbolp(a) {
    merr("get_index_properties: argument must be a symbol; found: ~M", [a])
    |> ignore
  }
  cons(list1(q_mlist), copy_list(mget(a, q_display_indices)))
}

///|
fn d_remove_index_properties(form : Value) -> Value raise {
  let a = cdr(form)
  if !every(x => symbolp(x), a) {
    merr("remove_index_properties: every argument must be a symbol; found: ~M", [
      a,
    ])
    |> ignore
  }
  for x in a.iter() {
    mremprop(x, q_display_indices) |> ignore
  }
  q_d_done
}

///|
/// OPERATORP1 (defined by DEF-OPERATORP1 in nparse.lisp). Use for truth
/// value only.
fn mlisp__operatorp1(lex : Value) -> Bool raise {
  symbolp(lex) && getl(lex, list([q_lbp, q_rbp, q_nud, q_led])).truthy()
}

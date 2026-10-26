// Port of src/outmis.lisp: miscellaneous out-of-core functions: isolate,
// pickapart, reveal, properties, propvars, printprops, changevar,
// factorsum, combine, factorout.

///|
fn d_isolate(e : Value, n_starxvar : Value) -> Value raise {
  iso1(e, getopr(n_starxvar))
}

///|
fn iso1(e : Value, n_starxvar : Value) -> Value raise {
  let xvar = n_starxvar
  if specrepp(e).truthy() {
    iso1(specdisrep(e), xvar)
  } else if free(e, q_mplus).truthy() &&
    (symval(q_d_isolate_wrt_times) is Nil || free(e, q_mtimes).truthy()) {
    e
  } else if freeof(xvar, e).truthy() {
    mgen2(e)
  } else if alike1(xvar, e).truthy() {
    xvar
  } else if memq(caar(e), list2(q_mplus, q_mtimes)).truthy() {
    iso2(e, xvar)
  } else if eq(caar(e), q_mexpt) {
    if !atom(cadr(e)) {
      list3(car(e), iso1(cadr(e), xvar), caddr(e))
    } else if alike1(cadr(e), xvar).truthy() || symval(q_d_exptisolate) is Nil {
      e
    } else {
      let mut x = d_rat(caddr(e), list1(xvar))
      let mut u = ratdisrep(d_ratnumer(x))
      let mut h : Value = Fix(0L)
      x = ratdisrep(d_ratdenom(x))
      if !equal(x, Fix(1L)) {
        u = d_multthru(list3(list1(q_mexpt), x, Fix(-1L)), e2=u)
      }
      if mplusp(u).truthy() {
        u = d_partition(u, xvar)
        h = cadr(u)
        u = caddr(u)
      }
      u = power_star(cadr(e), iso1(u, xvar))
      if !equal(h, Fix(0L)) {
        mul2_star(mgen2(power_star(cadr(e), h)), u)
      } else {
        u
      }
    }
  } else {
    cons(car(e), mapcar(e1 => iso1(e1, xvar), cdr(e)))
  }
}

///|
fn iso2(e : Value, n_starxvar : Value) -> Value raise {
  let xvar = n_starxvar
  let mut hasit : Value = Nil
  let mut doesnt : Value = Nil
  let op = ncons(caar(e))
  for i in cdr(e).iter() {
    if freeof(xvar, i).truthy() {
      doesnt = cons(i, doesnt)
    } else {
      hasit = cons(iso1(i, xvar), hasit)
    }
  }
  let go_ret = if doesnt is Nil {
    true
  } else if cdr(doesnt) is Nil && atom(car(doesnt)) {
    true
  } else {
    doesnt = simplifya(cons(op, doesnt), Nil)
    if free(doesnt, q_mplus).truthy() &&
      (symval(q_d_isolate_wrt_times) is Nil || free(doesnt, q_mtimes).truthy()) {
      ()
    } else {
      doesnt = mgen2(doesnt)
    }
    false
  }
  if !go_ret {
    doesnt = ncons(doesnt)
  }
  simplifya(cons(op, nconc(hasit, doesnt)), Nil)
}

///|
fn mgen2(h : Value) -> Value raise {
  let m = memsimilarl(
    h,
    cdr(symval(q_d_labels)),
    getlabcharn(symval(q_d_linechar)),
  )
  if m.truthy() {
    return m
  }
  let h = displine(h)
  if symval(q_d_dispflag).truthy() {
    mterpri() |> ignore
  }
  h
}

///|
fn memsimilarl(item : Value, list_ : Value, linechar : Value) -> Value raise {
  let mut l = list_
  while l.truthy() {
    let lab = car(l)
    if eql(getlabcharn(lab), linechar) && boundp(lab) {
      let r = memsimilar(item, lab, symval(lab))
      if r.truthy() {
        return r
      }
    }
    l = cdr(l)
  }
  Nil
}

///|
fn memsimilar(item1 : Value, item2 : Value, item2ev : Value) -> Value raise {
  if equal(item2ev, Fix(0L)) {
    Nil
  } else if alike1(item1, item2ev).truthy() {
    item2
  } else {
    with_special(q_errorsw, t, fn() raise {
      let r = catch_tag(q_errorsw, fn() raise { div(item2ev, item1) })
      if mnump(r).truthy() && zerop1(r) is Nil {
        div(item2, r)
      } else {
        Nil
      }
    })
  }
}

///|
fn d_pickapart(x : Value, lev : Value) -> Value raise {
  let x = format1(x)
  if !fixnump(lev) {
    merror(
      Str("pickapart: second argument must be an integer; found: ~M"),
      list1(lev),
    )
  } else if atom(x) || (eq(caar(x), q_mminus) && atom(cadr(x))) {
    x
  } else if to_int(lev) == 0 {
    mgen2(x)
  } else if atom(cdr(x)) && cdr(x).truthy() {
    x
  } else {
    let lev1 = num_sub(lev, Fix(1L))
    cons(car(x), mapcar(y => d_pickapart(y, lev1), cdr(x)))
  }
}

///|
fn d_reveal(e : Value, lev : Value) -> Value raise {
  let e = format1(e)
  if fixnump(lev) && plusp(lev) {
    reveal(e, Fix(1L), lev)
  } else {
    merror(
      Str("reveal: second argument must be a positive integer; found: ~M"),
      list1(lev),
    )
  }
}

///|
fn simple(x : Value) -> Value raise {
  lbool(atom(x) || memq(caar(x), list2(q_rat, q_bigfloat)).truthy())
}

///|
fn reveal(e : Value, nn : Value, lev : Value) -> Value raise {
  if simple(e).truthy() {
    return e
  }
  if num_eq(nn, lev) {
    let op = caar(e)
    return if eq(op, q_mplus) {
      cons(list2(q_d__cs_um, q_simp), ncons(int(length(cdr(e)))))
    } else if eq(op, q_mtimes) {
      cons(list2(q_d__cp_roduct, q_simp), ncons(int(length(cdr(e)))))
    } else if eq(op, q_mexpt) {
      q_d__ce_xpt
    } else if eq(op, q_mquotient) {
      q_d__cq_uotient
    } else if eq(op, q_mminus) {
      q_d__cn_egterm
    } else if eq(op, q_mlist) {
      cons(list2(q_d__cl_ist, q_simp), ncons(int(length(cdr(e)))))
    } else {
      getop(mop(e))
    }
  }
  let u = if memq(q_simp, cdar(e)).truthy() {
    car(e)
  } else {
    cons(caar(e), cons(q_simp, cdar(e)))
  }
  let nn1 = num_add(nn, Fix(1L))
  let v = mapcar(x => reveal(format1(x), nn1, lev), margs(e))
  if eq(caar(e), q_mqapply) {
    cons(u, cons(cadr(e), v))
  } else if eq(caar(e), q_mplus) {
    cons(u, nreverse(v))
  } else {
    cons(u, v)
  }
}

///|
fn d_properties(x : Value) -> Value raise {
  let x = getopr(fexprcheck(x))
  if !(symbolp(x) || stringp(x)) {
    merror(Str("properties: argument must be a symbol or a string."), Nil)
    |> ignore
  }
  let u = properties(x)
  let v = {
    let n = safe_get(x, q_noun)
    if n.truthy() {
      n
    } else {
      safe_get(x, q_verb)
    }
  }
  if v.truthy() {
    nconc(u, cdr(properties(v)))
  } else {
    u
  }
}

///|
/// Top-level property names and their descriptions.
fn outmis__top_props() -> Value {
  let s = fn(name : String, d : Value) { cons(sym(name), d) }
  list(
    [
      s("bindtest", q_d_bindtest),
      s("sp2", q_d_deftaylor),
      s("sp2subs", q_d_deftaylor),
      s("assign", Str("assign property")),
      s("nonarray", q_d_nonarray),
      s("grad", q_d_gradef),
      s("integral", q_d_integral),
      s("distribute_h_over", Str("distributes over bags")),
      s("simplim%function", Str("limit function")),
      s("conjugate-function", Str("conjugate function")),
      s("commutes-with-conjugate", Str("mirror symmetry")),
      s("risplit-function", Str("complex characteristic")),
      s("noun", q_d_noun),
      s("evfun", q_d_evfun),
      s("evflag", q_d_evflag),
      s("op", q_d_operator),
    ],
  )
}

///|
/// MPROPS property names and their descriptions.
fn outmis__mprops() -> Value {
  let s = fn(name : String, d : Value) { cons(sym(name), d) }
  list(
    [
      s("mexpr", q_d_function),
      s("mmacro", q_d_macro),
      s("hashar", Str("hashed array")),
      s("aexpr", Str("array function")),
      s("atvalues", q_d_atvalue),
      s("$atomgrad", q_d_atomgrad),
      s("$numer", q_d_numer),
      s("depends", q_d_dependency),
      s("$nonscalar", q_d_nonscalar),
      s("$scalar", q_d_scalar),
      s("matchdeclare", q_d_matchdeclare),
      s("mode", q_d_modedeclare),
    ],
  )
}

///|
fn properties(x : Value) -> Value raise {
  if stringp(x) {
    // AT THIS POINT WE MIGHT WANT TO TRY TO TEST ALL CHARS IN STRING ...
    let s = lstring(x)
    return if s.length() > 0 &&
      member(Char(char_at(s, 0)), symval(q_ear_alphabet)).truthy() {
      list2(list1(q_mlist), q_d_alphabetic)
    } else {
      list1(list1(q_mlist))
    }
  }
  let l = cons(
    list2(q_mlist, q_simp),
    if boundp(x) {
      if optionp(x).truthy() {
        ncons(Str("system value"))
      } else {
        ncons(q_d_value)
      }
    } else {
      Nil
    },
  )
  let add = fn(v : Value) { nconc(l, v) |> ignore }
  let top = outmis__top_props()
  let mut y = symbol_plist(x)
  while y.truthy() {
    let ind = car(y)
    // Only process properties with non-NIL values.
    if cadr(y).truthy() {
      // TOP-LEVEL PROPERTIES
      let prop = assq(ind, top)
      if prop.truthy() {
        add(ncons(cdr(prop)))
      } else if memq(ind, symval(q_opers)).truthy() {
        add(list1(ind))
      } else if eq(ind, q_operators) &&
        !(eq(cadr(y), q_simpargs1) || cadr(y) is Nil) {
        add(list1(q_d_rule))
      } else {
        // (these two clauses add an entry and then fall through)
        if memq(ind, list([q_fexpr, q_fsubr, q_mfexpr_stars, q_mfexpr_star])).truthy() {
          add(ncons(Str("special evaluation form")))
        }
        if (get(ind, q_mfexpr_star).truthy() || fboundp(x)) &&
          // Do not add more than one entry to the list.
          memq(q_d_transfun, l) is Nil &&
          memq(q_d_rule, l) is Nil &&
          member_equal(Str("system function"), l) is Nil {
          add(
            list1(
              if get(x, q_translated).truthy() {
                q_d_transfun
              } else if mgetl(x, list2(q_d_rule, q_ruleof)).truthy() {
                q_d_rule
              } else {
                Str("system function")
              },
            ),
          )
        }
        if eq(ind, q_autoload) &&
          member_equal(Str("system function"), l) is Nil {
          add(
            ncons(
              if memq(x, cdr(symval(q_d_props))).truthy() {
                Str("user autoload function")
              } else {
                Str("system function")
              },
            ),
          )
        } else if eq(ind, q_reversealias) &&
          memq(ind, cdr(symval(q_d_aliases))).truthy() {
          add(ncons(q_d_alias))
        } else if eq(ind, q_data) {
          add(cons(Str("database info"), cdr(d_facts(ctxt=x))))
        } else if eq(ind, q_mprops) {
          // PROPS PROPERTIES
          let mprops = outmis__mprops()
          let mut y2 = cdadr(y)
          while y2.truthy() {
            let ind2 = car(y2)
            let prop = assq(ind2, mprops)
            if prop.truthy() {
              add(list1(cdr(prop)))
            } else if eq(ind2, q_array) {
              add(
                list1(
                  if get(x, q_array).truthy() {
                    Str("complete array")
                  } else {
                    Str("declared array")
                  },
                ),
              )
            } else if eq(ind2, q_d_props) && cdadr(y2).truthy() {
              let ul = list2(list1(q_mlist), Str("user properties"))
              let mut y3 = cdadr(y2)
              while y3.truthy() {
                nconc(ul, list1(car(y3))) |> ignore
                y3 = cddr(y3)
              }
              add(list1(ul))
            }
            y2 = cddr(y2)
          }
        }
      }
    }
    y = cddr(y)
  }
  if memq(x, cdr(symval(q_d_features))).truthy() {
    add(ncons(q_d_feature))
  }
  if memq(x, cdr(symval(q_d_contexts))).truthy() {
    add(ncons(q_d_context))
  }
  if memq(x, cdr(symval(q_d_activecontexts))).truthy() {
    add(ncons(q_d_activecontext))
  }
  if symbol_plist(x) is Nil && fboundp(x) {
    add(list1(Str("system function")))
  }
  l
}

///|
fn d_propvars(x : Value) -> Value raise {
  let x = fexprcheck(x)
  let propvars = ncons(list1(q_mlist))
  for item in cdr(symval(q_d_props)).iter() {
    if among(x, meval(list2(list1(q_d_properties), item))).truthy() {
      nconc(propvars, ncons(item)) |> ignore
    }
  }
  propvars
}

///|
fn d_printprops(r : Value) -> Value raise {
  let r = cdr(r)
  if cdr(r) is Nil {
    merror(Str("printprops: requires two arguments."), Nil) |> ignore
  }
  let s = cadr(r)
  let r0 = car(r)
  let r = if atom(r0) {
    if eq(r0, q_d_all) {
      if eq(s, q_d_gradef) {
        mapcar(x => caar(x), cdr(symval(q_d_gradefs)))
      } else {
        cdr(meval(list2(list1(q_d_propvars), s)))
      }
    } else {
      ncons(r0)
    }
  } else {
    cdr(r0)
  }
  if eq(s, q_d_atvalue) {
    dispatvalues(r)
  } else if eq(s, q_d_atomgrad) {
    dispatomgrads(r)
  } else if eq(s, q_d_gradef) {
    dispgradefs(r)
  } else if eq(s, q_d_matchdeclare) {
    dispmatchdeclares(r)
  } else {
    merror(Str("printprops: unknown property ~:M"), list1(s))
  }
}

///|
/// `(mtell-open "~M~%" (list '(mlabel) nil eqn))`
fn outmis__show_eqn(lhs : Value, rhs : Value) -> Unit raise {
  mformat(
    list3(
      Nil,
      Str("~M~%"),
      list3(list1(q_mlabel), Nil, list3(list1(q_mequal), lhs, rhs)),
    ),
  )
  |> ignore
}

///|
fn dispatvalues(l : Value) -> Value raise {
  for f in l.iter() {
    for ll in mget(f, q_atvalues).iter() {
      outmis__show_eqn(atdecode(f, car(ll), cadr(ll)), caddr(ll))
    }
  }
  q_d_done
}

///|
fn atdecode(fun : Value, dl : Value, vl : Value) -> Value raise {
  let vl = copy_list(vl)
  atvarschk(vl) |> ignore
  let atvars = symval(q_atvars)
  let munbound = symval(q_munbound)
  if every(x => zerop(x), dl) {
    let mut v = vl
    let mut varl = atvars
    while v.truthy() {
      if eq(car(v), munbound) {
        rplaca(v, car(varl)) |> ignore
      }
      v = cdr(v)
      varl = cdr(varl)
    }
    cons(list1(fun), vl)
  } else {
    let vars = Collector::new()
    let mut n = length(vl)
    let mut varl = atvars
    while n != 0 {
      vars.add(car(varl))
      varl = cdr(varl)
      n -= 1
    }
    let fun = cons(list1(fun), vars.result())
    let mut eqs : Value = Nil
    let mut v = vl
    varl = atvars
    while v.truthy() {
      if !eq(car(v), munbound) {
        eqs = cons(list3(list1(q_mequal), car(varl), car(v)), eqs)
      }
      v = cdr(v)
      varl = cdr(varl)
    }
    let eqs = cons(list1(q_mlist), nreverse(eqs))
    let mut nvarl : Value = Nil
    let mut d = dl
    varl = atvars
    while d.truthy() {
      if !zerop(car(d)) {
        nvarl = cons(car(d), cons(car(varl), nvarl))
      }
      varl = cdr(varl)
      d = cdr(d)
    }
    let nvarl = nreverse(nvarl)
    list3(list1(q_p_at), cons(list1(q_p_derivative), cons(fun, nvarl)), eqs)
  }
}

///|
fn dispatomgrads(l : Value) -> Value raise {
  for i in l.iter() {
    for j in mget(i, q_d_atomgrad).iter() {
      outmis__show_eqn(
        list4(list1(q_p_derivative), i, car(j), Fix(1L)),
        cdr(j),
      )
    }
  }
  q_d_done
}

///|
fn dispgradefs(l : Value) -> Value raise {
  for i in l.iter() {
    let gl = get(i, q_grad)
    let mut j = car(gl)
    let mut k = cdr(gl)
    let thing = cons(ncons(i), car(gl))
    while !(k is Nil || j is Nil) {
      outmis__show_eqn(
        list4(list1(q_p_derivative), thing, car(j), Fix(1L)),
        car(k),
      )
      j = cdr(j)
      k = cdr(k)
    }
  }
  q_d_done
}

///|
fn dispmatchdeclares(l : Value) -> Value raise {
  let mut ret : Value = Nil
  for i in l.iter() {
    let m = car(mget(i, q_matchdeclare))
    ret = cons(
      append(
        if atom(m) {
          ncons(ncons(m))
        } else if eq(caar(m), q_lambda) {
          list2(list1(q_mqapply), m)
        } else {
          m
        },
        ncons(i),
      ),
      ret,
    )
  }
  cons(list1(q_mlist), reverse(ret))
}

///|
fn d_changevar(expr : Value, trans : Value, nvar : Value, ovar : Value) -> Value raise {
  with_special(q_d_ratfac, Nil, fn() raise {
    if atom(expr) || eq(caar(expr), q_rat) || eq(caar(expr), q_mrat) {
      return expr
    } else if atom(trans) {
      merror(
        Str("changevar: second argument must not be an atom; found: ~M"),
        list1(trans),
      )
      |> ignore
    } else if !atom(nvar) {
      merror(
        Str("changevar: third argument must be an atom; found: ~M"),
        list1(nvar),
      )
      |> ignore
    } else if !atom(ovar) {
      merror(
        Str("changevar: fourth argument must be an atom; found: ~M"),
        list1(ovar),
      )
      |> ignore
    }
    changevar(expr, trans, nvar, ovar)
  })
}

///|
fn solvable(l : Value, var_ : Value, errswitch? : Value = Nil) -> Value raise {
  with_specials([(q_n_starroots, Nil), (q_n_starfailures, Nil)], fn() raise {
    solve(l, var_, Fix(1L)) |> ignore
    let roots = symval(q_n_starroots)
    if roots.truthy() {
      // We arbitrarily pick the first root.  Should we be more careful?
      funcall(q_d_rhs, [car(roots)])
    } else if errswitch.truthy() {
      merror(
        Str("changevar: failed to solve for ~M in ~M"),
        list2(var_, l),
      )
    } else {
      Nil
    }
  })
}

///|
fn changevar(expr : Value, trans : Value, nvar : Value, ovar : Value) -> Value raise {
  if atom(expr) {
    return expr
  }
  if memq(caar(expr), list3(q_p_integrate, q_p_sum, q_p_product)) is Nil ||
    alike1(caddr(expr), ovar) is Nil {
    return recur_apply(
      lfunc("changevar-lambda", args => changevar(arg(args, 0), trans, nvar, ovar)),
      expr,
    )
  }
  // TRANS relates old var and new var: f(ovar, nvar) = 0. Using TRANS, try
  // to solve for ovar so that ovar = tfun(nvar), if possible.
  let trans = meqhk(trans)
  let tfun = solvable(trans, ovar)
  // Compute diff(tfun, nvar) = dovar/dnvar if tfun is available. Otherwise,
  // use implicit differentiation.
  let deriv = if tfun.truthy() {
    sdiff(tfun, nvar)
  } else {
    neg(div(sdiff(trans, nvar), sdiff(trans, ovar)))
  }
  let sum_product_p = memq(caar(expr), list2(q_p_sum, q_p_product)).truthy()
  // For sums and products, we want deriv to be +/-1 so that integers map
  // into integers.
  if sum_product_p && !(equal(deriv, Fix(1L)) || equal(deriv, Fix(-1L))) {
    merror(Str("changevar: illegal change in summation or product"), Nil)
    |> ignore
  }
  let nfun = d_radcan(
    // NIL IF KERNSUBST FAILS
    if tfun.truthy() {
      // Don't multiply by deriv for sums/products because reversing the
      // order of limits doesn't change the sign of the result.
      mul2(
        maxima_substitute(tfun, ovar, cadr(expr)),
        if sum_product_p {
          Fix(1L)
        } else {
          deriv
        },
      )
    } else {
      kernsubst(d_ratsimp(mul2(cadr(expr), deriv), Nil), trans, ovar)
    },
  )
  if nfun is Nil {
    return expr
  }
  if cdddr(expr).truthy() {
    // Handle definite integral, summation, or product. invfun expresses
    // nvar in terms of ovar so that we can compute the new limits.
    let invfun = solvable(trans, nvar, errswitch=t)
    let mut lo_limit = d_limit(list4(invfun, ovar, cadddr(expr), q_d_plus))
    let mut hi_limit = d_limit(
      list4(invfun, ovar, car(cddddr(expr)), q_d_minus),
    )
    // If this is a sum or product and deriv = -1, reverse the limits.
    if sum_product_p && equal(deriv, Fix(-1L)) {
      let tmp = lo_limit
      lo_limit = hi_limit
      hi_limit = tmp
    }
    list([ncons(caar(expr)), nfun, nvar, lo_limit, hi_limit])
  } else {
    // Indefinite integral
    list3(list1(q_p_integrate), nfun, nvar)
  }
}

///|
fn kernsubst(expr : Value, form : Value, ovar : Value) -> Value raise {
  with_specials([(q_varlist, Nil), (q_genvar, Nil)], fn() raise {
    newvar(expr) |> ignore
    let nvarlist = mapcar(
      x => if freeof(ovar, x).truthy() { x } else { solvable(form, x) },
      symval(q_varlist),
    )
    if memq(Nil, nvarlist).truthy() {
      Nil
    } else {
      let expr = ratrep_star(expr)
      set(q_varlist, nvarlist) |> ignore
      rdis(cdr(expr))
    }
  })
}

///|
fn d_factorsum(e : Value) -> Value raise {
  factorsum0(e, q_d_factor)
}

///|
fn d_gfactorsum(e : Value) -> Value raise {
  factorsum0(e, q_d_gfactor)
}

///|
fn factorsum0(e : Value, facfun : Value) -> Value raise {
  // FACFUN is a special variable (declare-top (special facfun)).
  with_special(q_facfun, facfun, fn() raise {
    let e = funcall(symval(q_facfun), [e])
    if mplusp(e).truthy() {
      factorsum1(cdr(e))
    } else {
      factorsum2(e)
    }
  })
}

///|
fn factorsum1(e : Value) -> Value raise {
  let mut e = e
  let mut llv : Value = Nil
  let mut lex : Value = Nil
  let mut cl : Value = Nil
  let mut lt : Value = Nil
  let mut lv : Value = Nil
  // loop: group the terms by shared variables
  while true {
    let f = car(e)
    lv = cdr(d_showratvars(f))
    if lv is Nil {
      cl = cons(f, cl)
    } else {
      let mut q = llv
      let mut r = lex
      while q.truthy() {
        if intersect(car(q), lv).truthy() {
          rplaca(q, union_star(car(q), lv)) |> ignore
          rplaca(r, cons(f, car(r))) |> ignore
          lv = Nil
          break
        }
        q = cdr(q)
        r = cdr(r)
      }
      if lv.truthy() {
        llv = cons(lv, llv)
        lex = cons(ncons(f), lex)
      }
    }
    // skip
    e = cdr(e)
    if e is Nil {
      break
    }
  }
  if cl.truthy() {
    let mut q = llv
    let mut r = lex
    while q.truthy() {
      if cdar(q) is Nil && cdar(r).truthy() {
        rplaca(r, nconc(cl, car(r))) |> ignore
        cl = Nil
        break
      }
      q = cdr(q)
      r = cdr(r)
    }
  }
  // skip2
  llv = Nil
  lv = Nil
  let mut r = lex
  while r.truthy() {
    if cdar(r).truthy() {
      llv = cons(
        factorsum2(
          funcall(symval(q_facfun), [cons(list1(q_mplus), car(r))]),
        ),
        llv,
      )
    } else {
      let mut f = caar(r)
      let c = if mtimesp(f).truthy() { cadr(f) } else { Nil }
      if mtimesp(f) is Nil || mnump(c) is Nil {
        llv = cons(f, llv)
      } else {
        let mut q = lt
        let mut s = lv
        while q.truthy() {
          if alike1(car(s), c).truthy() {
            rplaca(q, cons(dcon(f), car(q))) |> ignore
            f = Nil
            break
          }
          q = cdr(q)
          s = cdr(s)
        }
        if f.truthy() {
          lv = cons(c, lv)
          lt = cons(ncons(dcon(f)), lt)
        }
      }
    }
    r = cdr(r)
  }
  lex = mapcar2(
    fn(s, q) raise {
      simptimes(
        list3(
          list1(q_mtimes),
          s,
          if cdr(q).truthy() {
            cons(list1(q_mplus), q)
          } else {
            car(q)
          },
        ),
        Fix(1L),
        Nil,
      )
    },
    lv,
    lt,
  )
  simplus(cons(list1(q_mplus), nconc_n([cl, lex, llv])), Fix(1L), Nil)
}

///|
fn dcon(mt : Value) -> Value raise {
  if cdddr(mt).truthy() {
    cons(car(mt), cddr(mt))
  } else {
    caddr(mt)
  }
}

///|
fn factorsum2(e : Value) -> Value raise {
  if mtimesp(e) is Nil {
    e
  } else {
    cons(
      list1(q_mtimes),
      mapcar(
        f => if mplusp(f).truthy() { factorsum1(cdr(f)) } else { f },
        cdr(e),
      ),
    )
  }
}

///|
fn d_combine(e : Value) -> Value raise {
  if atom(e) || eq(caar(e), q_rat) {
    e
  } else if eq(caar(e), q_mplus) {
    combine(cdr(e))
  } else {
    recur_apply(q_d_combine, e)
  }
}

///|
fn combine(e : Value) -> Value raise {
  let mut e = e
  let mut r : Value = Nil
  let mut ld : Value = Nil
  let mut ln : Value = Nil
  let mut xl : Value = Nil
  while true {
    // again
    let term = car(e)
    e = cdr(e)
    let mut d : Value = Nil
    let plain = if !(
        ratnump(term).truthy() ||
        mtimesp(term).truthy() ||
        mexptp(term).truthy()
      ) {
      true
    } else {
      d = d_denom(term)
      equal(d, Fix(1L))
    }
    if plain {
      r = cons(term, r)
    } else {
      let nnu = d_num(term)
      if symval(q_d_combineflag).truthy() && integerp(d) {
        xl = cons(term, xl)
      } else {
        let mut sw = false
        let mut q = ld
        let mut p = ln
        while q.truthy() {
          if alike1(car(q), d).truthy() {
            rplaca(p, cons(nnu, car(p))) |> ignore
            sw = true
            break
          }
          q = cdr(q)
          p = cdr(p)
        }
        if !sw {
          ld = cons(d, ld)
          ln = cons(ncons(nnu), ln)
        }
      }
    }
    // end
    if e is Nil {
      break
    }
  }
  if xl.truthy() {
    xl = if cdr(xl).truthy() { d_xthru(addn(xl, t)) } else { car(xl) }
  }
  let mut nus = ln
  let mut des = ld
  while nus.truthy() && des.truthy() {
    r = cons(mul2(addn(car(nus), Nil), power_star(car(des), Fix(-1L))), r)
    nus = cdr(nus)
    des = cdr(des)
  }
  addn(if xl.truthy() { cons(xl, r) } else { r }, Nil)
}

///|
fn d_factorout(e : Value, vl : Value) -> Value raise {
  if vl is Nil {
    merror(Str("factorout: at least two arguments required."), Nil) |> ignore
  }
  if mplusp(e) is Nil {
    return e
  }
  let mut el : Value = Nil
  let mut l : Value = Nil
  let mut e = cdr(e)
  while true {
    // loop
    let mut f = car(e)
    e = cdr(e)
    if mtimesp(f) is Nil {
      f = list3(list1(q_mtimes), Fix(1L), f)
    }
    let mut fl : Value = Nil
    let mut cl : Value = Nil
    for i in cdr(f).iter() {
      if !numberp(i) && d_freeof(append(vl, ncons(i))).truthy() {
        fl = cons(i, fl)
      } else {
        cl = cons(i, cl)
      }
    }
    if fl is Nil {
      el = cons(f, el)
    } else {
      let fl = if cdr(fl).truthy() {
        simptimes(cons(list1(q_mtimes), fl), Fix(1L), Nil)
      } else {
        car(fl)
      }
      let cl : Value = if cl is Nil {
        Fix(1L)
      } else if cdr(cl).truthy() {
        simptimes(cons(list1(q_mtimes), cl), Fix(1L), t)
      } else {
        car(cl)
      }
      let mut x = true
      let mut i = l
      while i.truthy() {
        if alike1(caar(i), fl).truthy() {
          rplacd(car(i), cons(cl, cdar(i))) |> ignore
          x = false
          break
        }
        i = cdr(i)
      }
      if x {
        l = cons(list2(fl, cl), l)
      }
    }
    // end
    if e is Nil {
      break
    }
  }
  for i in l.iter() {
    el = cons(
      simptimes(
        list3(
          list1(q_mtimes),
          car(i),
          d_factorsum(simplus(cons(list1(q_mplus), cdr(i)), Fix(1L), Nil)),
        ),
        Fix(1L),
        Nil,
      ),
      el,
    )
  }
  addn(el, Nil)
}

///|
fn init_outmis() -> Unit raise {
  putprop(q_d_exptisolate, t, q_evflag) |> ignore
  putprop(q_d_isolate_wrt_times, t, q_evflag) |> ignore
}

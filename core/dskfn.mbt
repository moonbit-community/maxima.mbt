// Port of src/dskfn.lisp: save(), which writes Lisp forms that restore
// values, functions, properties and facts when the file is loaded.  The
// forms are printed with the runtime's PRIN1; loading them back goes
// through the restricted Lisp evaluator of suprv1.mbt.

///|
fn infolstchk(x : Value) -> Value raise {
  let iteml = if !(
      x.truthy() &&
      (
        memq(car(x), list([q_d_all, q_d_contexts])).truthy() ||
        memq(car(x), cdr(symval(q_d_infolists))).truthy()
      )
    ) {
    t
  } else if eq(car(x), q_d_all) {
    infolstchk(
      append(
        cdr(symval(q_d_infolists)),
        list([
          q_d_linenum, q_d_ratvars, q_n_starratweights, q_tellratlist, q_ear_alphabet,
          q_d_dontfactor, q_d_features, q_d_contexts,
        ]),
      ),
    )
  } else if eq(car(x), q_d_labels) {
    reverse(cdr(symval(q_d_labels)))
  } else if memq(
      car(x),
      list([q_d_functions, q_d_macros, q_d_gradefs, q_d_dependencies, q_d_structures]),
    ).truthy() {
    mapcar(e => caar(e), cdr(symval(car(x))))
  } else if eq(car(x), q_d_contexts) {
    suprv1__delete1(q_d_global, reverse(cdr(symval(q_d_contexts))))
  } else {
    cdr(symval(car(x)))
  }
  if eq(iteml, t) {
    x
  } else {
    append(if iteml.truthy() { iteml } else { list1(Nil) }, cdr(x))
  }
}

///|
/// WITH-MAXIMA-IO-SYNTAX: print readably, in base 10.
fn dskfn__with_io_syntax(f : () -> Value raise) -> Value raise {
  with_specials(
    [
      (q_ear_print_readably, t),
      (q_ear_print_gensym, Nil),
      (q_ear_print_circle, Nil),
      (q_ear_print_level, Nil),
      (q_ear_print_length, Nil),
      (q_ear_print_base, Fix(10L)),
      (q_ear_print_radix, t),
    ],
    f,
  )
}

///|
/// The macro WITH-MAXIMA-IO-SYNTAX called as a function: FORMS is a list of
/// Maxima forms (or a function value) evaluated with that syntax.
fn with_maxima_io_syntax(forms : Value) -> Value raise {
  dskfn__with_io_syntax(() => match forms {
    Func(_) => funcall(forms, [])
    _ => {
      let mut v : Value = Nil
      for f in forms.iter() {
        v = meval(f)
      }
      v
    }
  })
}

///|
fn d_save(form : Value) -> Value raise {
  if length(rest(form)) == 0 {
    merr("save: no file name specified.", []) |> ignore
  }
  let fname = meval(second(form))
  if !stringp(fname) {
    merr("save: first argument must be a string; found: ~M", [fname]) |> ignore
  }
  // $save stores Lisp expressions.
  dskfn__with_io_syntax(() => dsksetup(cdr(form), q_d_save, fname))
}

///|
fn dsksetup(x : Value, fn_ : Value, fname : Value) -> Value raise {
  with_special(q_errset, symval(q_ear_dsksetup_errset_value), () => {
    let path = lstring(fname)
    let append_ = eq(symval(q_d_file_output_append), q_d_true) ||
      eq(symval(q_d_file_output_append), t)
    let savefile = make_string_output_stream()
    set(q_savefile, savefile) |> ignore
    princ(
      Str(";;; -*- Mode: LISP; package:maxima; syntax:common-lisp; -*- "),
      stream=savefile,
    )
    |> ignore
    terpri(stream=savefile)
    princ(Str("(in-package :maxima)"), stream=savefile) |> ignore
    // Check arguments. First argument was checked above.
    for u in cdr(x).iter() {
      if atom(u) {
        if !symbolp(u) {
          improper_arg_err(u, fn_) |> ignore
        }
      } else if listargp(u).truthy() {
        ()
      } else if !eq(caar(u), q_mequal) || !symbolp(cadr(u)) {
        improper_arg_err(u, fn_) |> ignore
      }
    }
    let list_ = list1(car(x))
    let x = cdr(x)
    let write = () => {
      let old = if append_ && probe_file(path) { read_file(path) } else { "" }
      write_file(path, old + get_output_stream_string(savefile))
    }
    let r = mload__errset(() => dskstore(x, list_)) catch {
      e => {
        write()
        raise e
      }
    }
    ignore(r)
    write()
    Str(suprv1__truename(path))
  })
}

///|
fn dskstore(x : Value, list_ : Value) -> Value raise {
  let mut x = x
  let mut alrdystrd : Value = Nil
  while x is Cons(_) {
    let mut nitemfl : Value = Nil
    let mut val = listargp(car(x))
    if val.truthy() {
      x = nconc(getlabels(car(val), cdr(val), Nil), cdr(x))
    } else {
      val = assq(
        car(x),
        list([
          cons(q_d_inlabels, q_d_inchar),
          cons(q_d_outlabels, q_d_outchar),
          cons(q_d_linelabels, q_d_linechar),
        ]),
      )
      if val.truthy() {
        x = nconc(getlabels_star(symval(cdr(val)), Nil), cdr(x))
      }
    }
    let mut rename : Value = Nil
    let mut item : Value = Nil
    if !atom(car(x)) {
      rename = cadar(x)
      item = getopr(caddar(x))
    } else {
      x = infolstchk(x)
      item = if x.truthy() { getopr(car(x)) } else { Nil }
      rename = item
    }
    if !symbolp(item) {
      nitemfl = item
      let nitem = gensym()
      set(nitem, meval(item)) |> ignore
      item = nitem
    } else if eq(item, q_d_ratweights) {
      item = q_n_starratweights
    } else if eq(item, q_d_tellrats) {
      item = q_tellratlist
    } else if eq(item, q_d_alphabet) {
      item = q_ear_alphabet
    }
    if x is Nil {
      return Nil
    }
    if car(x) is Nil {
      x = cdr(x)
      continue
    }
    val = assq(item, alrdystrd)
    if val.truthy() && eq(rename, cdr(val)) {
      x = cdr(x)
      continue
    }
    alrdystrd = cons(cons(item, rename), alrdystrd)
    if dskfn__nothing_to_store(item) {
      x = cdr(x)
      continue
    }
    if boundp(item) {
      let val = symval(item)
      if eq(item, q_d_context) {
        x = list_star([Nil, val, cdr(x)])
      }
      dskatom(item, rename, val) |> ignore
      if !optionp(rename).truthy() {
        infostore(item, q_value, rename) |> ignore
      }
    }
    let val = if memq(item, cdr(symval(q_d_aliases))).truthy() {
      get(item, q_reversealias)
    } else {
      Nil
    }
    if val.truthy() {
      dskdefprop(rename, val, q_reversealias) |> ignore
      pradd2lnc(rename, q_d_aliases) |> ignore
      dskdefprop(val, rename, q_alias) |> ignore
      if symval(q_greatorder).truthy() && !assq(q_greatorder, alrdystrd).truthy() {
        x = list_star([Nil, q_greatorder, cdr(x)])
      }
      if symval(q_lessorder).truthy() && !assq(q_lessorder, alrdystrd).truthy() {
        x = list_star([Nil, q_lessorder, cdr(x)])
      }
      x = list_star([Nil, val, cdr(x)])
    }
    let noun = get(item, q_noun)
    if noun.truthy() {
      x = list_star([Nil, noun, cdr(x)])
      dskdefprop(rename, noun, q_noun) |> ignore
    } else {
      let verb = get(item, q_verb)
      if verb.truthy() {
        x = list_star([Nil, verb, cdr(x)])
        dskdefprop(rename, verb, q_verb) |> ignore
      }
    }
    if mget(item, q_d_rule).truthy() {
      let r = ruleof(item)
      if r.truthy() {
        x = list_star([Nil, r, cdr(x)])
      }
      pradd2lnc(getop(rename), q_d_rules) |> ignore
    }
    let val = cadr(getl_lm_fcn_prop(item, list1(q_expr)))
    if val.truthy() &&
      (mget(item, q_d_rule).truthy() || get(item, q_translated).truthy()) {
      if mget(item, q_trace).truthy() {
        remprop(item, q_expr) |> ignore
        let val1 = get(item, q_expr)
        if val1.truthy() {
          dskdefprop(rename, val1, q_expr) |> ignore
        }
        set_symbol_plist(item, list_star([q_expr, val, symbol_plist(item)]))
        |> ignore
      } else {
        dskdefprop(rename, val, q_expr) |> ignore
      }
      propschk(item, rename, q_translated) |> ignore
    }
    let ops = get(item, q_operators)
    if ops.truthy() {
      dskdefprop(rename, ops, q_operators) |> ignore
      let rules = get(item, q_rules)
      if rules.truthy() {
        dskdefprop(rename, rules, q_rules) |> ignore
        x = cons(Nil, append(rules, cdr(x)))
      }
      if memq(item, cdr(symval(q_d_props))).truthy() {
        pradd2lnc(rename, q_d_props) |> ignore
      }
      let old = mget(item, q_oldrules)
      if old.truthy() {
        x = cons(Nil, nconc(cdr(reverse(old)), cdr(x)))
      }
    }
    if memq(item, cdr(symval(q_d_features))).truthy() {
      pradd2lnc(rename, q_d_features) |> ignore
    }
    if memq(getop(item), cdr(symval(q_d_props))).truthy() {
      for ind in symval(q_indlist).iter() {
        propschk(item, rename, ind) |> ignore
      }
      for oper in symval(q_opers).iter() {
        propschk(item, rename, oper) |> ignore
      }
    }
    let op = get(item, q_op)
    if op.truthy() && memq(op, cdr(symval(q_d_props))).truthy() {
      dskdefprop(item, op, q_op) |> ignore
      dskdefprop(op, item, q_opr) |> ignore
      pradd2lnc(op, q_d_props) |> ignore
      let m = extopchk(item, op)
      if m.truthy() {
        x = list_star([Nil, m, cdr(x)])
      }
    }
    let grad = get(item, q_grad)
    if grad.truthy() && assoc_equal(list1(item), symval(q_d_gradefs)).truthy() {
      dskdefprop(rename, grad, q_grad) |> ignore
      pradd2lnc(cons(list1(rename), car(grad)), q_d_gradefs) |> ignore
    }
    if get(item, q_data).truthy() && !memq(item, cdr(symval(q_d_contexts))).truthy() {
      let facts = cdr(d_facts(ctxt=item))
      if facts.truthy() {
        fasprin(list([q_restore_facts, list([q_quote, facts])])) |> ignore
        if memq(item, cdr(symval(q_d_props))).truthy() {
          pradd2lnc(item, q_d_props) |> ignore
        }
      }
    }
    if memq(item, cdr(symval(q_d_contexts))).truthy() {
      let facts = with_special(q_context, item, () => cdr(d_facts(ctxt=item)))
      if facts.truthy() {
        fasprint(t, list([q_dsksetq, q_d_context, list([q_quote, item])])) |> ignore
        if memq(item, cdr(symval(q_d_activecontexts))).truthy() {
          fasprint(t, list([q_d_activate, list([q_quote, item])])) |> ignore
        }
        fasprint(t, list([q_restore_facts, list([q_quote, facts])])) |> ignore
      }
    }
    mpropschk(item, rename) |> ignore
    if !get(item, q_verb).truthy() {
      nconc(
        list_,
        list1(
          if nitemfl.truthy() {
            nitemfl
          } else {
            getop(item)
          },
        ),
      )
      |> ignore
    }
    x = cdr(x)
  }
  Nil
}

///|
/// The clause of DSKSTORE recognizing items that have nothing worth saving.
fn dskfn__nothing_to_store(item : Value) -> Bool raise {
  let unset = !boundp(item) ||
    (eq(item, q_d_ratvars) && symval(q_varlist) is Nil) ||
    {
      let val = symval(item)
      (eq(item, q_d_dontfactor) && cdr(val) is Nil) ||
      (
        memq(item, list([q_tellratlist, q_ear_alphabet, q_n_starratweights])).truthy() &&
        val is Nil
      ) ||
      (eq(item, q_d_features) && alike(cdr(val), symval(q_featurel)).truthy()) ||
      (eq(item, q_d_default_let_rule_package) && eq(item, val))
    }
  if !unset {
    return false
  }
  // This clause has been reformulated to cut out a test with dsksavep and
  // unstorep, but to respect the side effects.
  let mprops = safe_get(item, q_mprops)
  if !(mprops is Nil || equal(mprops, list1(Nil))) {
    return false
  }
  if getl(
      item,
      list([q_operators, q_reversealias, q_grad, q_noun, q_verb, q_expr, q_op, q_data]),
    ).truthy() {
    return false
  }
  if memq(item, cdr(symval(q_d_props))).truthy() {
    return false
  }
  !memq(item, cdr(symval(q_d_contexts))).truthy() ||
  !eq(item, q_d_initial) ||
  with_special(q_context, q_d_initial, () => lbool(
    cdr(d_facts(ctxt=q_d_initial)) is Nil,
  )).truthy()
}

///|
fn dskatom(item : Value, rename : Value, val : Value) -> Value raise {
  let q = (v : Value) => list([q_quote, v])
  if eq(item, q_d_ratvars) {
    fasprint(
      t,
      list([q_setq, q_varlist, list([q_append, q_varlist, q(symval(q_varlist))])]),
    )
    |> ignore
    fasprint(
      t,
      list([
        q_setq,
        q_d_ratvars,
        list([q_cons, q(list2(q_mlist, q_simp)), q_varlist]),
      ]),
    )
    |> ignore
    pradd2lnc(q_d_ratvars, q_d_myoptions) |> ignore
  } else if eq(item, q_d_dontfactor) {
    fasprin(list([q_setq, item, list([q_nconc, q(val), list([q_cdr, item])])]))
    |> ignore
    pradd2lnc(item, q_d_myoptions) |> ignore
  } else if eq(item, q_tellratlist) {
    fasprin(list([q_setq, q_tellratlist, list([q_nconc, q(val), q_tellratlist])]))
    |> ignore
    pradd2lnc(q_tellratlist, q_d_myoptions) |> ignore
  } else if eq(item, q_ear_alphabet) {
    fasprin(list([q_setq, q_ear_alphabet, list([q_nconc, q(val), q_ear_alphabet])]))
    |> ignore
  } else if eq(item, q_n_starratweights) {
    fasprin(
      list([q_apply, list([q_function, q_d_ratweight]), q(dot2l(val))]),
    )
    |> ignore
  } else if eq(item, q_d_features) {
    for var_ in cdr(symval(q_d_features)).iter() {
      if !memq(var_, symval(q_featurel)).truthy() {
        pradd2lnc(var_, q_d_features) |> ignore
      }
    }
  } else if eq(item, q_d_linenum) && eq(item, rename) {
    fasprint(t, list([q_setq, q_d_linenum, val])) |> ignore
  } else if d_ratp(val).truthy() {
    fasprint(t, list([q_dsksetq, rename, list([q_dskrat, q(val)])])) |> ignore
  } else if hash_table_p(val) {
    // Hash tables ("fast arrays") aren't printable in all Lisp
    // implementations.
    fasprint(
      t,
      list([
        q_dsksetq,
        rename,
        list([
          q_fill_hash,
          list([q_make_hash_table, q_kw_test, q(q_equal)]),
          q(list_hash_pairs(val)),
        ]),
      ]),
    )
    |> ignore
  } else {
    fasprint(t, list([q_dsksetq, rename, q(val)])) |> ignore
  }
  Nil
}

///|
fn fill_hash(h : Value, kv_list : Value) -> Value raise {
  for kv in kv_list.iter() {
    sethash(first(kv), h, second(kv)) |> ignore
  }
  h
}

///|
fn list_hash_pairs(h : Value) -> Value raise {
  let c = Collector::new()
  maphash((key, value) => c.add(list([key, value])), h)
  c.result()
}

///|
fn mpropschk(item : Value, rename : Value) -> Value raise {
  let props0 = get(item, q_mprops)
  let mut props = cdr(if props0.truthy() { props0 } else { list1(Nil) })
  while props is Cons(_) {
    let ind = car(props)
    let val = cadr(props)
    if memq(ind, list([q_trace, q_trace_type, q_trace_level, q_trace_oldfun])).truthy() ||
      (eq(ind, q_t_mfexpr) && !get(item, q_translated).truthy()) {
      ()
    } else if !memq(ind, list([q_hashar, q_array])).truthy() {
      fasprin(list([q_mdefprop, rename, val, ind])) |> ignore
      if !memq(ind, list([q_mlexprp, q_mfexprp, q_t_mfexpr])).truthy() {
        let r = if memq(ind, list([q_mexpr, q_mmacro])).truthy() {
          let val1 = get(item, q_function_mode)
          if val1.truthy() {
            dskdefprop(rename, val1, q_function_mode) |> ignore
          }
          cons(list1(rename), cdadr(val))
        } else if eq(ind, q_depends) {
          cons(list1(rename), val)
        } else {
          rename
        }
        infostore(item, ind, r) |> ignore
      }
    } else {
      dskary(item, list([q_quote, rename]), val, ind) |> ignore
      infostore(item, ind, rename) |> ignore
    }
    props = cddr(props)
  }
  Nil
}

///|
fn dskary(item : Value, rename : Value, val : Value, ind : Value) -> Value raise {
  // Some small forms ordinarily non-EQ for fasdump must be output in proper
  // sequence with the big mungeables.
  let ary = if eq(ind, q_array) && get(item, q_array).truthy() {
    rename
  } else {
    // This code handles "complete" arrays.
    fasprint(t, list([q_defparameter, q_aaaaa, list1(q_gensym)])) |> ignore
    q_aaaaa
  }
  let dims = arraydims(val)
  if eq(ind, q_hashar) {
    fasprint(t, list([q_remcompary, rename])) |> ignore
  }
  fasprint(
    t,
    list([
      q_mremprop,
      rename,
      list([q_quote, if eq(ind, q_array) { q_hashar } else { q_array }]),
    ]),
  )
  |> ignore
  fasprint(t, list([q_mputprop, rename, ary, list([q_quote, ind])])) |> ignore
  fasprint(
    t,
    list_star([q_n_stararray, ary, list([q_quote, car(dims)]), cdr(dims)]),
  )
  |> ignore
  fasprint(t, list([q_fillarray, ary, list([q_quote, listarray(val)])])) |> ignore
  let val1 = get(item, q_array_mode)
  if val1.truthy() {
    fasprint(t, list([q_defprop, cadr(rename), val1, q_array_mode])) |> ignore
  }
  Nil
}

///|
fn extopchk(item : Value, val : Value) -> Value raise {
  if !(
      get(item, q_nud).truthy() ||
      get(item, q_led).truthy() ||
      get(item, q_lbp).truthy()
    ) {
    return Nil
  }
  fasprin(list([q_define_symbol, list([q_quote, val])])) |> ignore
  if memq(val, symval(q_ear_mopl)).truthy() {
    fasprin(
      list([
        q_setq,
        q_ear_mopl,
        list([q_cons, list([q_quote, val]), q_ear_mopl]),
      ]),
    )
    |> ignore
  }
  let dim = get(item, q_dimension)
  if dim.truthy() {
    dskdefprop(item, dim, q_dimension) |> ignore
    dskdefprop(item, get(item, q_dissym), q_dissym) |> ignore
    dskdefprop(item, get(item, q_grind), q_grind) |> ignore
  }
  for ind in [q_lbp, q_rbp, q_nud, q_led] {
    let v = get(item, ind)
    if v.truthy() {
      dskdefprop(item, v, ind) |> ignore
    }
  }
  let verb = get(item, q_verb)
  if verb.truthy() {
    dskdefprop(verb, get(verb, q_dimension), q_dimension) |> ignore
    dskdefprop(verb, get(verb, q_dissym), q_dissym) |> ignore
  }
  let m = get(item, q_match)
  if m.truthy() {
    dskdefprop(item, m, q_match) |> ignore
    m
  } else {
    Nil
  }
}

///|
fn propschk(item : Value, rename : Value, ind : Value) -> Value raise {
  let val = get(item, ind)
  if val.truthy() {
    dskdefprop(rename, val, ind) |> ignore
    pradd2lnc(getop(rename), q_d_props)
  } else {
    Nil
  }
}

///|
fn fasprin(form : Value) -> Value raise {
  fasprint(Nil, form)
}

///|
fn fasprint(eqfl : Value, form : Value) -> Value raise {
  ignore(eqfl)
  print(form, stream=symval(q_savefile))
}

///|
fn infostore(item : Value, flag : Value, rename : Value) -> Value raise {
  let prop = if eq(flag, q_value) {
    if memq(rename, cdr(symval(q_d_labels))).truthy() {
      q_d_labels
    } else {
      q_d_values
    }
  } else if eq(flag, q_mexpr) {
    q_d_functions
  } else if eq(flag, q_mmacro) {
    q_d_macros
  } else if memq(flag, list([q_array, q_hashar])).truthy() {
    q_d_arrays
  } else if eq(flag, q_depends) {
    q_d_dependencies
  } else {
    q_d_props
  }
  if eq(prop, q_d_labels) {
    fasprin(list([q_addlabel, list([q_quote, rename])])) |> ignore
    if get(item, q_nodisp).truthy() {
      dskdefprop(rename, t, q_nodisp) |> ignore
    }
    Nil
  } else {
    pradd2lnc(rename, prop)
  }
}

///|
fn pradd2lnc(item : Value, prop : Value) -> Value raise {
  if symval(q_d_packagefile) is Nil ||
    !memq(prop, cdr(symval(q_d_infolists))).truthy() ||
    (eq(prop, q_d_props) && getopr0(item).truthy()) {
    fasprin(list([q_add2lnc, list([q_quote, item]), prop]))
  } else {
    Nil
  }
}

///|
fn dskdefprop(name : Value, val : Value, ind : Value) -> Value raise {
  fasprin(
    if memq(ind, list([q_expr, q_fexpr, q_macro])).truthy() &&
      eq(car(val), q_lambda) {
      list_star([
        q_defun,
        name,
        if eq(ind, q_expr) {
          cdr(val)
        } else {
          cons(ind, cdr(val))
        },
      ])
    } else if eq(ind, q_opr) {
      if symbolp(name) {
        list([q_defprop, name, val, ind])
      } else {
        list([
          q_setf,
          list([q_gethash, name, q_ear_opr_table]),
          list([q_quote, val]),
        ])
      }
    } else {
      list([q_defprop, name, val, ind])
    },
  )
}

///|
fn init_dskfn() -> Unit raise {
  defvar_init(
    q_indlist,
    list([
      q_evfun, q_evflag, q_bindtest, q_nonarray, q_sp2, q_sp2subs, q_opers, q_special,
      q_autoload, q_assign, q_mode,
    ]),
  )
}

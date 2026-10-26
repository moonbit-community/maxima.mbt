// Port of share/affine/amacros.lisp: monomial orderings, the remember
// facility, and the structures shared by the affine package.
//
// Structures. The `(:type list) :named` structures are plain lists
// `(name slot1 slot2 ...)`; the others are `make_struct("name", slots)`
// values with the slots in the order of the Lisp defstruct. The slot
// tables below describe both kinds; `amacros__slot_index` maps a slot name
// to its index (counted from 0 after the name for list structures, from 0
// in the slot array otherwise).

///|
/// Slot names of the structures defined in amacros.lisp.
let amacros__struct_slots : Array[(String, String, Bool, Array[String])] = [
  // (struct name, conc-name, list-type?, slots)
  ("s-var", "sv-", true, ["zopens"]),
  ("pre-ldata-sheaves", "pls-", true, ["s-var", "data"]),
  (
    "ldata",
    "ldata-",
    true,
    ["eqns", "inequality", "usedup", "open-inequality", "variables"],
  ),
  ("rmap", "rmap-", true, ["fns", "denom"]),
  ("zopen", "zopen-", true, ["coord", "inv", "inequality", "history"]),
  (
    "variable-correspondence",
    "vc-",
    false,
    ["genvar", "varlist", "add-method"],
  ),
  (
    "ideal",
    "ideal-",
    false,
    ["char-set", "generators", "localization", "variable-correspondence"],
  ),
  (
    "polynomial-vectors",
    "pv-",
    false,
    [
      "length-of-array-of-tables", "rows", "constants-column-number", "relations",
      "type-of-entries", "variables", "verify-conversion", "array-of-polynomials",
      "array-of-tables", "last-column-number", "number-of-independent-terms", "solution-in-macsyma-format",
      "table", "the-sparse-matrix", "type-of-polynomials", "solution-plist",
    ],
  ),
  (
    "poly-data",
    "pd-",
    false,
    ["rows", "sparse-matrix", "segments", "big-monom-list"],
  ),
  ("matrix", "matrix-", true, ["rows"]),
]

///|
/// Index of SLOT in the structure described by the conc-name PREFIX (or by
/// the structure name), or None.
fn amacros__slot_index(prefix : String, slot : String) -> (Bool, Int)? {
  for e in amacros__struct_slots {
    let (name, conc, listp, slots) = e
    if conc == prefix || name == prefix {
      for i, s in slots {
        if s == slot {
          return Some((listp, i))
        }
      }
    }
  }
  None
}

///|
/// The accessor `<conc-name><slot>` applied to STRUCT.
fn amacros__slot_ref(struct_ : Value, prefix : String, slot : String) -> Value raise {
  match amacros__slot_index(prefix, slot) {
    Some((true, i)) => nth(i + 1, struct_)
    Some((false, i)) => struct_ref(struct_, i)
    None => raise LispError::SimpleError("The function " + prefix + slot + " is undefined.")
  }
}

///|
/// `(setf (<conc-name><slot> struct) value)`.
fn amacros__slot_set(
  struct_ : Value,
  prefix : String,
  slot : String,
  value : Value,
) -> Value raise {
  match amacros__slot_index(prefix, slot) {
    Some((true, i)) => setf_car(nthcdr(i + 1, struct_), value)
    Some((false, i)) => struct_set(struct_, i, value)
    None =>
      raise LispError::SimpleError("The function (SETF " + prefix + slot + ") is undefined.")
  }
}

///|
/// `(make-polynomial-vectors)` with the defstruct defaults.
fn amacros__make_polynomial_vectors() -> Value {
  make_struct("polynomial-vectors", [
    Nil,
    Nil,
    Nil,
    Nil,
    q_kw_integer,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
    Nil,
  ])
}

///|
/// `(make-poly-data)`.
fn amacros__make_poly_data() -> Value {
  make_struct("poly-data", [Nil, Nil, Nil, Nil])
}

///|
/// `(make-ldata)` with the defstruct defaults.
fn amacros__make_ldata() -> Value {
  list([q_ldata, Nil, Fix(1L), Fix(0L), Fix(1L), Nil])
}

///|
/// `(make-variable-correspondence)`.
fn amacros__make_variable_correspondence() -> Value {
  make_struct("variable-correspondence", [Nil, Nil, Nil])
}

///|
/// `(make-ideal)`.
fn amacros__make_ideal() -> Value {
  make_struct("ideal", [Nil, Nil, Nil, Nil])
}

///|
fn iassert(expr : Value) -> Value raise {
  if expr is Nil {
    fsignal(list([Str("The expression ~A was not true"), expr]))
  } else {
    Nil
  }
}

///|
fn alphagreatp(x : Value, y : Value) -> Value raise {
  lbool(alphalessp(x, y) is Nil && !equal(x, y))
}

///|
fn d_monomial_alphalessp(x : Value, y : Value) -> Value raise {
  if atom(x) {
    if atom(y) {
      alphalessp(x, y)
    } else if cdr(y) is Nil {
      alphalessp(x, car(y))
    } else if eql(x, cadr(y)) {
      // x<x.z , x< x.*
      t
    } else {
      alphalessp(x, cadr(y))
    }
  } else if atom(y) {
    if cdr(x) is Nil {
      alphalessp(car(x), y)
    } else {
      alphalessp(cadr(x), y)
    }
  } else {
    alphalessp(cdr(x), cdr(y))
  }
}

///|
fn d_monomial_alphagreatp(x : Value, y : Value) -> Value raise {
  lbool(!(equal(x, y) || d_monomial_alphalessp(x, y).truthy()))
}

///|
fn d_power_series_monomial_alphalessp(x : Value, y : Value) -> Value raise {
  if equal(x, y) {
    return Nil
  }
  let x_deg = d_nc_degree(x, type_of_weight=amacros__q_kw_order_weight)
  let y_deg = d_nc_degree(y, type_of_weight=amacros__q_kw_order_weight)
  if eql(x_deg, y_deg) {
    d_monomial_alphalessp(x, y)
  } else if zerop(y_deg) {
    lbool(!zerop(x_deg))
  } else if zerop(x_deg) {
    Nil
  } else if num_gt(x_deg, y_deg) {
    t
  } else {
    Nil
  }
}

///|
fn d_polynomial_monomial_alphalessp(x : Value, y : Value) -> Value raise {
  if equal(x, y) {
    return Nil
  }
  let x_deg = d_nc_degree(x, type_of_weight=amacros__q_kw_order_weight)
  let y_deg = d_nc_degree(y, type_of_weight=amacros__q_kw_order_weight)
  if eql(x_deg, y_deg) {
    d_monomial_alphalessp(x, y)
  } else if zerop(x_deg) {
    lbool(!zerop(y_deg))
  } else if zerop(y_deg) {
    Nil
  } else if num_lt(x_deg, y_deg) {
    t
  } else {
    Nil
  }
}

///|
/// Replaces the &optional / &key part of a lambda list by the variable
/// names (keywords preceding the &key variables).
fn fix_optional(args : Value) -> Value raise {
  let mut args = args
  let tem0 = copy_list(args)
  let mut i = 0
  let mut v = tem0
  while v is Cons(_) {
    if memq(car(v), list2(q_n_ampoptional, q_n_ampkey)) is Cons(_) {
      let opts = Collector::new()
      let mut w = cdr(v)
      while w is Cons(_) {
        if atom(car(w)) && string_search("&", string_upcase(lstring(string(car(w))))) >= 0 {
          break
        }
        let tem = if atom(car(w)) { car(w) } else { caar(w) }
        if eq(car(v), q_n_ampkey) {
          opts.add(kw(string_downcase(lstring(string(tem)))))
        }
        opts.add(tem)
        w = cdr(w)
      }
      args = append(subseq(args, 0, end=i), append(opts.result(), cdr(w)))
      break
    }
    v = cdr(v)
    i += 1
  }
  args
}

///|
fn delete_from__ampaux(list_ : Value) -> Value raise {
  let mut i = 1
  for u in list_.iter() {
    if eq(u, q_n_ampaux) {
      return subseq(list_, 0, end=i - 1)
    }
    i += 1
  }
  list_
}

///|
fn clear_memory_function(f : Value) -> Value raise {
  let tem = get(f, q_kw_memory_table)
  if tem.truthy() {
    clrhash(tem)
  } else {
    Nil
  }
}

///|
/// The expansion of DEFREMEMBER (a macro defining a function that caches
/// its results in an EQUAL hash table on its :memory-table property).
/// Like the macro, it clears the old memory table and returns the DEFUN
/// form.
fn defremember(func_spec : Value, arglist : Value, body : Value) -> Value raise {
  let mut call_arglist = copy_list(arglist)
  if get(func_spec, q_kw_memory_table).truthy() {
    clrhash(get(func_spec, q_kw_memory_table)) |> ignore
  }
  remprop(func_spec, q_kw_dont_remember) |> ignore
  call_arglist = fix_optional(delete_from__ampaux(call_arglist))
  if memq(q_n_ampaux, call_arglist) is Cons(_) {
    format(t, "~%It is inadvisable to use &aux with defremember", []) |> ignore
  }
  let mut hash_args : Value = Nil
  let mut hash_put_args : Value = Nil
  if length(arglist) == 1 {
    hash_args = car(arglist)
    hash_put_args = hash_args
  } else if eq(car(arglist), q_n_amprest) {
    hash_args = second(arglist)
    hash_put_args = list2(q_copy_list, second(arglist))
    call_arglist = second(arglist)
  } else if memq(q_n_amprest, arglist) is Cons(_) {
    hash_args = cons(q_list, delete(q_n_amprest, call_arglist))
    hash_put_args = copy_list(hash_args)
    let n = length(hash_put_args)
    setf_car(
      nthcdr(n - 1, hash_put_args),
      list2(q_copy_list, car(last(hash_put_args))),
    )
    |> ignore
  } else {
    hash_args = cons(q_list, call_arglist)
    hash_put_args = hash_args
  }
  let quoted = list2(q_quote, func_spec)
  let progn_body = cons(q_progn, body)
  let recall = if memq(q_n_amprest, arglist) is Cons(_) {
    list_star([q_apply, quoted, delete(q_n_amprest, copy_list(call_arglist))])
  } else {
    cons(func_spec, call_arglist)
  }
  let remembered = list([
    q_let,
    list2(q_hash_table, q_ans),
    list([
      q_cond,
      list([
        list3(
          q_setq,
          q_hash_table,
          list3(q_get, quoted, q_kw_memory_table),
        ),
        list([
          q_cond,
          list2(
            list3(q_setq, q_ans, list3(q_gethash, hash_args, q_hash_table)),
            q_ans,
          ),
          list([
            t,
            list3(q_setq, q_ans, progn_body),
            list3(
              q_setf,
              list3(q_gethash, hash_put_args, q_hash_table),
              q_ans,
            ),
            q_ans,
          ]),
        ]),
      ]),
      list([
        t,
        list3(
          q_setf,
          list3(q_get, quoted, q_kw_memory_table),
          list3(q_make_hash_table, q_kw_test, list2(q_quote, q_equal)),
        ),
        recall,
      ]),
    ]),
  ])
  list([
    q_defun,
    func_spec,
    arglist,
    list3(
      q_cond,
      list2(list2(q_null, list3(q_get, quoted, q_kw_dont_remember)), remembered),
      list2(t, progn_body),
    ),
  ])
}

///|
fn disable_remember(f : Value) -> Value raise {
  putprop(f, t, q_kw_dont_remember)
}

///|
fn enable_remember(f : Value) -> Value raise {
  remprop(f, q_kw_dont_remember)
}

///|
/// WITH-NO-QUERY rebinds FQUERY around its body; the port has no FQUERY,
/// so it is the body (already evaluated: its last value).
fn with_no_query(body : Value) -> Value raise {
  car(last(body))
}

///|
fn with_no_query_answer_no(body : Value) -> Value raise {
  car(last(body))
}

///|
/// `(user-supply var)`: VAR is the symbol whose value is offered.
fn user_supply(var_ : Value) -> Value raise {
  set(var_, user_supply1(var_, symval(var_)))
}

///|
fn user_supply1(var_ : Value, val : Value) -> Value raise {
  let mut var_ = var_
  with_special(q_ear_print_level, Fix(3L), () => {
    while true {
      format(t, "~%The value of ~A is ~A .", [var_, val]) |> ignore
      format(
        t,
        "~%Supply a form to evaluate to use for ~A or hit return to keep same :",
        [var_],
      )
      |> ignore
      let ch = read_char(stream=symval(q_ear_standard_input))
      match ch {
        Char('\n') => return val
        Char(c) => unread_char(c, stream=symval(q_ear_standard_input))
        _ => ()
      }
      let line = match read_line(stream=symval(q_ear_standard_input)) {
        Some(s) => s
        None => ""
      }
      let new_ = lisp_eval_form(lread(line))
      if eq(new_, q_keep) {
        return var_
      } else {
        format(t, "~%Use ~A?", [new_]) |> ignore
        let answer = match read_line(stream=symval(q_ear_standard_input)) {
          Some(s) => s
          None => ""
        }
        let a = string_trim(" \t", answer)
        if a.has_prefix("y") || a.has_prefix("Y") {
          var_ = new_
          return var_
        }
      }
    }
    var_
  })
}

///|
/// `(tim . body)` is `(time (progn . body))`: the value of the body (already
/// evaluated) with the time report.
fn tim(body : Value) -> Value raise {
  car(last(body))
}

///|
fn amacros__string_append(a : Value, b : String) -> String raise {
  lstring(string(a)) + b
}

///|
/// The expansion of COMPARE-FUNCTIONS.
fn compare_functions(defa : Value, defb : Value, assertions : Value) -> Value raise {
  let assert_ = Collector::new()
  assert_.add(
    list2(q_iassert, list3(q_equal, sym(".ansa."), sym(".ansb."))),
  )
  for v in assertions.iter() {
    assert_.add(list2(q_iassert, v))
  }
  if !eq(car(defa), q_defun) {
    raise LispError::SimpleError("The value of DEFA, " + prin1_to_string(defa) + ", should be a defun")
  }
  let mut defb = defb
  if atom(defb) {
    let l = sym(".l.")
    defb = list([
      q_defun,
      sym(amacros__string_append(defb, "-compare")),
      list2(q_n_amprest, l),
      list3(q_apply, list2(q_quote, defb), l),
    ])
  }
  let fa = Value::Sym(intern(amacros__string_append(second(defa), "-a")))
  let fb = Value::Sym(intern(amacros__string_append(second(defb), "-b")))
  let boda = subst(fa, second(defa), cdddr(defa))
  let bodb = subst(fb, second(defb), cdddr(defb))
  let arglist = Collector::new()
  for v in third(defa).iter() {
    if eq(v, q_n_ampaux) {
      break
    }
    arglist.add(v)
  }
  let l = sym("l")
  let ansa = sym(".ansa.")
  let ansb = sym(".ansb.")
  list([
    q_progn,
    list([q_defun, fa, third(defa), cons(q_tim, boda)]),
    list([q_defun, fb, third(defb), cons(q_tim, bodb)]),
    list([
      q_defun,
      second(defa),
      list2(q_n_amprest, l),
      list2(q_declare, cons(sym("arglist"), arglist.result())),
      list_star([
        q_let,
        list2(ansa, ansb),
        list([
          q_format,
          t,
          Str("~%Comparing the functions ~A and ~A "),
          list2(q_quote, fa),
          list2(q_quote, fb),
        ]),
        list3(
          q_setq,
          ansa,
          list2(
            q_multiple_value_list,
            list3(q_apply, list2(q_quote, fa), list2(q_copy_list, l)),
          ),
        ),
        list3(
          q_setq,
          ansb,
          list2(
            q_multiple_value_list,
            list3(q_apply, list2(q_quote, fb), list2(q_copy_list, l)),
          ),
        ),
        append(
          assert_.result(),
          list1(list3(q_apply, list2(q_quote, q_values), ansa)),
        ),
      ]),
    ]),
  ])
}

///|
/// The expansion of COMPARE-RECURSIVE-FUNCTIONS.
fn compare_recursive_functions(
  fn_a : Value,
  fn_b : Value,
  assertions : Value,
) -> Value raise {
  list([
    q_progn,
    fn_a,
    fn_b,
    list_star([
      q_compare_functions,
      list_star([
        q_defun,
        Value::Sym(intern(amacros__string_append(second(fn_a), "-compare"))),
        cddr(fn_a),
      ]),
      list_star([
        q_defun,
        Value::Sym(intern(amacros__string_append(second(fn_b), "-compare"))),
        cddr(fn_b),
      ]),
      assertions,
    ]),
  ])
}

///|
fn write_object(filename : Value, obj : Value) -> Value raise {
  write_file(lstring(filename), format_to_string("~A", [obj]))
  Nil
}

///|
/// `(set-slots struct conc-prefix slot1 val1 slot2 val2 ...)`: sets the
/// named slots of STRUCT (one of the amacros.lisp structures).
fn set_slots(struct_ : Value, conc_prefix : Value, alt_list : Value) -> Value raise {
  let prefix = lstring(string(conc_prefix))
  let mut v = alt_list
  let mut last_val : Value = Nil
  while v is Cons(_) {
    last_val = amacros__slot_set(
      struct_,
      prefix,
      lstring(string(car(v))),
      second(v),
    )
    v = cddr(v)
  }
  last_val
}

///|
fn zl_copy_structure(
  struct_ : Value,
  conc_prefix : Value,
  alt_list : Value,
) -> Value raise {
  let ans = copy_list(struct_)
  set_slots(ans, conc_prefix, alt_list) |> ignore
  ans
}

///|
fn gshow(form : Value) -> Value raise {
  format(t, "~%The value of ~A is", [form]) |> ignore
  // GRIND-TOP-LEVEL is not defined in Maxima.
  raise LispError::SimpleError("The function GRIND-TOP-LEVEL is undefined.")
}

///|
fn mshow(l : Value) -> Value raise {
  let mut r : Value = Nil
  for v in l.iter() {
    format(t, "~%The value of ~A is.. ", [v]) |> ignore
    r = des(v)
  }
  r
}

///|
fn ncmul_star(factors : Value) -> Value raise {
  if length(factors) == 2 {
    ncmul2_star(car(factors), cadr(factors))
  } else {
    ncmuln(factors, Nil)
  }
}

///|
fn if_verbose(l : Value) -> Value raise {
  if symval(q_ear_verbose_check_overlaps).truthy() {
    car(last(l))
  } else {
    Nil
  }
}

///|
fn init_share_amacros() -> Unit raise {
  ()
}

///|
let amacros__q_kw_order_weight : Value = kw("order-weight")

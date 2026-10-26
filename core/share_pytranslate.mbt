// Port of share/pytranslate/pytranslate.lisp: a translator from Maxima
// expressions to Python source. Maxima forms are first converted to an
// intermediate representation (IR, Lisp lists headed by symbols such as
// SYMBOL, FUNCALL, OP, BODY, ...), which is then printed as Python.

///|
let share_pytranslate__q_plus : Value = sym("+")

///|
let share_pytranslate__q_set : Value = sym("=")

///|
/// `(symbol ,s)`
fn share_pytranslate__sym_ir(s : String) -> Value {
  list2(q_symbol, Str(s))
}

///|
/// `(symbol ,*maxima-variables-dictionary-name*)`
fn share_pytranslate__vars_ir() -> Value {
  list2(q_symbol, symval(q_ear_maxima_variables_dictionary_name))
}

///|
/// `(funcall (symbol ,*python-hierarchial-dict-name*) (dictionary)
///  (symbol ,*maxima-variables-dictionary-name*))`
fn share_pytranslate__new_stack_ir() -> Value {
  list4(
    q_funcall,
    list2(q_symbol, symval(q_ear_python_hierarchial_dict_name)),
    list1(q_dictionary),
    share_pytranslate__vars_ir(),
  )
}

///|
/// `(op-no-bracket = (symbol v) <new stack>)`
fn share_pytranslate__push_stack_ir() -> Value {
  list4(
    q_op_no_bracket,
    share_pytranslate__q_set,
    share_pytranslate__vars_ir(),
    share_pytranslate__new_stack_ir(),
  )
}

///|
/// `(and (consp elm) (consp (car elm)) (eq (caar elm) op))`
fn share_pytranslate__headp(elm : Value, op : Value) -> Bool {
  consp(elm) && consp(car(elm)) && eq(caar(elm), op)
}

///|
/// The IR of the value returned by a block or function body: the last form.
fn share_pytranslate__return_value_ir(elm : Value) -> Value raise {
  if share_pytranslate__headp(elm, q_mcond) {
    mcond_to_ir(elm, is_expr=t)
  } else if share_pytranslate__headp(elm, q_mreturn) {
    maxima_to_ir(cadr(elm))
  } else {
    maxima_to_ir(elm)
  }
}

///|
fn clast(l : Value) -> Value raise {
  car(last(l))
}

///|
/// Check if form is mprogn
fn mprogn_p(form : Value) -> Value raise {
  lbool(
    consp(clast(form)) &&
    consp(car(clast(form))) &&
    eq(caar(clast(form)), q_mprogn),
  )
}

///|
fn symbol_name_to_string(form : Value) -> Value raise {
  maybe_invert_string_case(Str(symbol_name(stripdollar(form))))
}

///|
fn symbol_to_ir(form : Value) -> Value raise {
  list2(q_symbol, symbol_name_to_string(form))
}

///|
fn symbol_to_dictionary_ir(form : Value, dict_name? : Value = Nil) -> Value raise {
  list3(
    q_element_array,
    list2(
      q_symbol,
      if dict_name.truthy() {
        dict_name
      } else {
        symval(q_ear_maxima_variables_dictionary_name)
      },
    ),
    list2(q_string, symbol_name_to_string(form)),
  )
}

///|
fn plot_to_ir(form : Value) -> Value raise {
  list_star([
    q_funcall,
    list3(
      q_element_array,
      symval(q_ear_maxima_function_dictionary_name),
      list2(
        q_string,
        if length(cddr(form)) == 1 {
          Str("plot2d")
        } else {
          Str("plot3d")
        },
      ),
    ),
    maxima_to_ir(cadr(form)),
    mapcar(
      elm => if consp(elm) && consp(car(elm)) && eq(q_mlist, caar(elm)) {
        list_star([
          q_struct_list,
          list2(q_string, symbol_name_to_string(cadr(elm))),
          mapcar(x => maxima_to_ir(x), cddr(elm)),
        ])
      } else {
        maxima_to_ir(elm)
      },
      cddr(form),
    ),
  ])
}

///|
/// `(funcall (element-array (symbol f) (string ,name)) ,@args)`
fn share_pytranslate__fdict_call(name : String, form : Value) -> Value raise {
  list_star([
    q_funcall,
    list3(
      q_element_array,
      list2(q_symbol, symval(q_ear_maxima_function_dictionary_name)),
      list2(q_string, Str(name)),
    ),
    mapcar(x => maxima_to_ir(x), cdr(form)),
  ])
}

///|
fn mfactorial_to_ir(form : Value) -> Value raise {
  share_pytranslate__fdict_call("factorial", form)
}

///|
fn mexpt_to_ir(form : Value) -> Value raise {
  share_pytranslate__fdict_call("pow", form)
}

///|
fn assignment_to_ir(form : Value) -> Value raise {
  if consp(cadr(form)) {
    list_star([
      q_op_no_bracket,
      share_pytranslate__q_set,
      mapcar(x => maxima_to_ir(x), cdr(form)),
    ])
  } else {
    list([
      q_funcall,
      list2(q_symbol, symval(q_ear_assignment_method_name)),
      list2(q_string, symbol_name_to_string(cadr(form))),
      maxima_to_ir(caddr(form)),
      share_pytranslate__vars_ir(),
    ])
  }
}

///|
fn symbol_to_asterisk_ir(form : Value) -> Value raise {
  list2(
    q_symbol,
    Str(
      "*" +
      lstring(maybe_invert_string_case(Str(symbol_name(stripdollar(form))))),
    ),
  )
}

///|
fn endcons_to_ir(form : Value) -> Value raise {
  if consp(clast(form)) {
    maxima_to_ir(append(clast(form), list1(cadr(form))))
  } else {
    list3(
      q_struct_list,
      list2(q_asterisk, maxima_to_ir(clast(form))),
      maxima_to_ir(cadr(form)),
    )
  }
}

///|
/// The statements of a loop body.
fn share_pytranslate__loop_body(form : Value) -> Value raise {
  if mprogn_p(form).truthy() {
    mapcar(x => maxima_to_ir(x), cdr(clast(form)))
  } else {
    list1(maxima_to_ir(clast(form)))
  }
}

///|
fn for_loop_to_ir(form : Value) -> Value raise {
  let thru = caddr(cdddr(form))
  if thru is Nil {
    // Condition Specified
    let init : Value = if cadr(form) is Nil {
      // If variable not given
      Nil
    } else {
      // If variable assigned by "for var:value"
      list1(list3(q_assign, maxima_to_ir(cadr(form)), maxima_to_ir(caddr(form))))
    }
    let unless = clast(butlast(form))
    let cond_ir = if consp(unless) && consp(car(unless)) && eq(q_mnot, caar(unless)) {
      maxima_to_ir(cadr(unless))
    } else {
      list3(q_funcall, share_pytranslate__sym_ir("not"), maxima_to_ir(unless))
    }
    let body = share_pytranslate__loop_body(form)
    let step : Value = if cadddr(form) is Nil {
      Nil
    } else {
      list1(
        list3(
          q_assign,
          maxima_to_ir(cadr(form)),
          list4(
            q_op,
            share_pytranslate__q_plus,
            maxima_to_ir(cadr(form)),
            maxima_to_ir(cadddr(form)),
          ),
        ),
      )
    }
    let del : Value = if cadr(form) is Nil {
      Nil
    } else {
      list1(list2(q_del, maxima_to_ir(cadr(form))))
    }
    append_n([
      list1(q_body),
      init,
      list1(
        list3(q_while_loop, cond_ir, cons(q_body_indented, append(body, step))),
      ),
      del,
    ])
  } else {
    // Limit specified
    let var_ir = maxima_to_ir(cadr(form))
    let from_ir = maxima_to_ir(caddr(form))
    let to_ir = if atom(thru) && !symbolp(thru) {
      maxima_to_ir(one_plus(thru))
    } else {
      list4(
        q_op,
        share_pytranslate__q_plus,
        maxima_to_ir(thru),
        list3(q_num, Fix(1L), Fix(0L)),
      )
    }
    let step : Value = if cadddr(form) is Nil {
      Nil
    } else {
      list1(maxima_to_ir(cadddr(form)))
    }
    list4(
      q_for_list,
      var_ir,
      list_star([q_funcall, share_pytranslate__sym_ir("range"), from_ir, to_ir, step]),
      cons(q_body_indented, share_pytranslate__loop_body(form)),
    )
  }
}

///|
fn for_list_to_ir(form : Value) -> Value raise {
  let v = maxima_to_ir(cadr(form))
  let l = maxima_to_ir(caddr(form))
  list4(q_for_list, v, l, cons(q_body_indented, share_pytranslate__loop_body(form)))
}

///|
fn func_call_arg_to_ir(form : Value) -> Value raise {
  match form {
    Cons(_) =>
      if eq(caar(form), q_mlist) {
        list2(
          q_symbol,
          maybe_invert_string_case(Str(symbol_name(stripdollar(cadr(form))))),
        )
      } else {
        Nil
      }
    _ => maxima_to_ir(form)
  }
}

///|
fn lambda_to_ir(form : Value) -> Value raise {
  let vars = append(
    mapcar(
      x => if consp(x) {
        cadr(x)
      } else {
        x
      },
      cdadr(form),
    ),
    symval(q_ear_symbols_directly_convert),
  )
  with_special(q_ear_symbols_directly_convert, vars, () => if length(cddr(form)) ==
    1 {
    let func_args = mapcar(x => func_arg_to_ir(x), cdadr(form))
    list3(
      q_lambda,
      append(
        func_args,
        // initialize dictionary holding variable bindings
        list1(share_pytranslate__push_stack_ir()),
      ),
      maxima_to_ir(clast(form)),
    )
  } else {
    let func_name = gensym(prefix="$lambda")
    let func_args = mapcar(x => func_arg_to_ir(x), cdadr(form))
    set(
      q_ear_ir_forms_to_append,
      cons(
        func_def_to_ir(
          list3(
            list2(q_mdefine, q_simp),
            cons(list1(func_name), cdadr(form)),
            cons(list1(q_mprogn), cddr(form)),
          ),
        ),
        symval(q_ear_ir_forms_to_append),
      ),
    )
    |> ignore
    list3(
      q_lambda,
      append(
        func_args,
        // initialize dictionary holding variable bindings
        list1(share_pytranslate__push_stack_ir()),
      ),
      append_n([
        list2(q_funcall, symbol_to_ir(func_name)),
        mapcar(x => func_call_arg_to_ir(x), cdadr(form)),
        list1(share_pytranslate__new_stack_ir()),
      ]),
    )
  })
}

///|
fn conditional_auxiliary(forms : Value) -> Value raise {
  let a = maxima_to_ir(car(forms))
  let b = maxima_to_ir(cadr(forms))
  let c = if eq(caddr(forms), t) {
    maxima_to_ir(cadddr(forms))
  } else {
    cons(q_conditional, conditional_auxiliary(cddr(forms)))
  }
  list3(a, b, c)
}

///|
fn conditional_to_ir(form : Value) -> Value raise {
  // (conditional <condition> <res1> <else-res>)
  cons(q_conditional, conditional_auxiliary(cdr(form)))
}

///|
fn if_to_ir(form : Value, case_if? : Value = Nil) -> Value raise {
  let head = if case_if.truthy() { list1(q_body) } else { Nil }
  let cond_ir = list2(
    if case_if.truthy() {
      q_cond_if
    } else {
      q_cond_elif
    },
    maxima_to_ir(cadr(form)),
  )
  let then_ir = list2(q_body_indented, maxima_to_ir(caddr(form)))
  let rest : Value = if eq(cadddr(form), t) {
    let lst : Value = clast(form)
    if lst is Nil || eq(lst, q_d_false) {
      Nil
    } else if share_pytranslate__headp(lst, q_mcond) {
      if_to_ir(lst)
    } else {
      list2(list1(q_cond_else), list2(q_body_indented, maxima_to_ir(lst)))
    }
  } else {
    if_to_ir(cddr(form))
  }
  append_n([head, list2(cond_ir, then_ir), rest])
}

///|
fn mcond_to_ir(form : Value, is_expr? : Value = Nil) -> Value raise {
  if is_expr.truthy() {
    conditional_to_ir(form)
  } else {
    append(if_to_ir(form, case_if=t), Nil)
  }
}

///|
fn mprog_variable_names_list(form : Value) -> Value raise {
  if consp(form) && eq(q_msetq, caar(form)) {
    maxima_to_ir(cadr(form))
  } else {
    maxima_to_ir(form)
  }
}

///|
fn mprog_arg_list(form : Value) -> Value raise {
  if consp(form) && eq(q_msetq, caar(form)) {
    maxima_to_ir(clast(form))
  } else {
    share_pytranslate__sym_ir("None")
  }
}

///|
fn mprog_assign_to_dict(form : Value) -> Value raise {
  mapcar(
    x => if consp(x) {
      list2(list2(q_string, symbol_name_to_string(cadr(x))), maxima_to_ir(caddr(x)))
    } else {
      list2(
        list2(q_string, symbol_name_to_string(x)),
        share_pytranslate__sym_ir("None"),
      )
    },
    cdr(form),
  )
}

///|
fn mlist_p(form : Value) -> Value raise {
  lbool(consp(form) && consp(car(form)) && eq(q_mlist, caar(form)))
}

///|
fn first_list_mprog(form : Value) -> Value raise {
  find_if(x => mlist_p(x).truthy(), cdr(form))
}

///|
fn but_first_mlist(form : Value) -> Value raise {
  let pos = position_if(x => mlist_p(x).truthy(), form)
  let c = Collector::new()
  let mut y = 0
  for x in form.iter() {
    if y != pos {
      c.add(x)
    }
    y = y + 1
  }
  c.result()
}

///|
/// The statements of a block body but the last, a conditional statement
/// being translated by `cond_fn`.
fn share_pytranslate__block_stmts(
  form : Value,
  cond_fn : (Value) -> Value raise,
) -> Value raise {
  mapcar(
    elm => if share_pytranslate__headp(elm, q_mcond) {
      cond_fn(elm)
    } else {
      maxima_to_ir(elm)
    },
    but_first_mlist(butlast(cdr(form))),
  )
}

///|
fn mprog_to_ir(form : Value, context? : Value = Nil) -> Value raise {
  if cdr(form) is Nil {
    return Nil
  }
  if eq(context, q_function) {
    let ins = list4(
      q_obj_funcall,
      share_pytranslate__vars_ir(),
      list2(q_symbol, symval(q_ear_ins_method_name)),
      cons(q_dictionary, mprog_assign_to_dict(first_list_mprog(form))),
    )
    let stmts = share_pytranslate__block_stmts(form, elm => if_to_ir(elm, case_if=t))
    append_n([
      list1(ins),
      stmts,
      list1(
        list3(
          q_funcall,
          share_pytranslate__sym_ir("return"),
          share_pytranslate__return_value_ir(clast(form)),
        ),
      ),
    ])
  } else {
    let func_name = symbol_to_ir(gensym(prefix="$block"))
    let ins = list4(
      q_obj_funcall,
      share_pytranslate__vars_ir(),
      list2(q_symbol, symval(q_ear_ins_method_name)),
      cons(q_dictionary, mprog_assign_to_dict(first_list_mprog(form))),
    )
    let push = share_pytranslate__push_stack_ir()
    let stmts = share_pytranslate__block_stmts(form, elm => mcond_to_ir(elm))
    let ret = list3(
      q_funcall,
      share_pytranslate__sym_ir("return"),
      share_pytranslate__return_value_ir(clast(form)),
    )
    set(
      q_ear_ir_forms_to_append,
      cons(
        list4(
          q_func_def,
          func_name,
          list1(share_pytranslate__vars_ir()),
          append_n([list3(q_body_indented, push, ins), stmts, list1(ret)]),
        ),
        symval(q_ear_ir_forms_to_append),
      ),
    )
    |> ignore
    list3(q_funcall, func_name, share_pytranslate__new_stack_ir())
  }
}

///|
fn mprogn_to_ir(form : Value, func_args? : Value) -> Value raise {
  ignore(func_args)
  let func_name = symbol_to_ir(gensym(prefix="$block"))
  let push = share_pytranslate__push_stack_ir()
  let stmts = share_pytranslate__block_stmts(form, elm => mcond_to_ir(elm))
  let ret = list3(
    q_funcall,
    share_pytranslate__sym_ir("return"),
    share_pytranslate__return_value_ir(clast(form)),
  )
  set(
    q_ear_ir_forms_to_append,
    cons(
      list4(
        q_func_def,
        func_name,
        list1(share_pytranslate__vars_ir()),
        append_n([list2(q_body_indented, push), stmts, list1(ret)]),
      ),
      symval(q_ear_ir_forms_to_append),
    ),
  )
  |> ignore
  list3(q_funcall, func_name, share_pytranslate__vars_ir())
}

///|
/// Recursively generates IR for a multi-dimensional array and fills all
/// cells with Null value
fn array_gen_ir(dimensions : Value) -> Value raise {
  if dimensions is Nil {
    share_pytranslate__sym_ir("None")
  } else {
    list4(
      q_op,
      sym("*"),
      list2(q_struct_list, array_gen_ir(cdr(dimensions))),
      maxima_to_ir(car(dimensions)),
    )
  }
}

///|
/// Helper function for array-def-to-ir which generates the IR for array
/// definition
fn auxillary_array_to_ir(symbol : Value, dimensions : Value) -> Value raise {
  list3(q_assign, symbol, array_gen_ir(dimensions))
}

///|
/// Function to generate IR for array definition using different methods,
/// by using the auxiliary function
fn array_def_to_ir(form : Value) -> Value raise {
  if consp(cadr(form)) {
    cons(
      q_body,
      mapcar(symb => auxillary_array_to_ir(maxima_to_ir(symb), cddr(form)), cdadr(form)),
    )
  } else if !numberp(caddr(form)) {
    auxillary_array_to_ir(maxima_to_ir(cadr(form)), cdddr(form))
  } else {
    auxillary_array_to_ir(maxima_to_ir(cadr(form)), cddr(form))
  }
}

///|
/// Function to convert reference to array elements to IR
fn array_ref_to_ir(symbol : Value, indices : Value) -> Value raise {
  if indices is Nil {
    maxima_to_ir(symbol)
  } else {
    let lst = clast(indices)
    list3(
      q_element_array,
      array_ref_to_ir(symbol, butlast(indices)),
      if atom(lst) && !symbolp(lst) {
        maxima_to_ir(one_minus(lst))
      } else {
        list4(q_op, share_pytranslate__q_plus, maxima_to_ir(lst), Fix(-1L))
      },
    )
  }
}

///|
/// Convert Function args to corresponding IR. Convert the optional list
/// argument into corresponding *args form in python
fn func_arg_to_ir(form : Value) -> Value raise {
  match form {
    Cons(_) =>
      if eq(caar(form), q_mlist) {
        list2(
          q_symbol,
          Str("*" + lstring(symbol_name_to_string(cadr(form)))),
        )
      } else {
        Nil
      }
    _ => symbol_to_ir(form)
  }
}

///|
/// Generates IR for function definition
fn func_def_to_ir(form : Value) -> Value raise {
  // The name of function shouldn't be converted to dictionary element
  set(
    q_ear_symbols_directly_convert,
    cons(caaadr(form), symval(q_ear_symbols_directly_convert)),
  )
  |> ignore
  // Function name
  let fname = maxima_to_ir(caaadr(form))
  // Function arguments, including variable mapping dictionary
  let func_args = mapcar(x => func_arg_to_ir(x), cdadr(form))
  let args = append(
    func_args,
    // initialize dictionary holding variable bindings
    list1(
      list4(
        q_op_no_bracket,
        share_pytranslate__q_set,
        share_pytranslate__vars_ir(),
        share_pytranslate__vars_ir(),
      ),
    ),
  )
  let push = share_pytranslate__push_stack_ir()
  // Map the variables in current context to the Stack
  let ins = list4(
    q_obj_funcall,
    share_pytranslate__vars_ir(),
    list2(q_symbol, symval(q_ear_ins_method_name)),
    cons(
      q_dictionary,
      mapcar(
        x => match x {
          Cons(_) =>
            list2(
              list2(q_string, symbol_name_to_string(cadr(x))),
              list3(q_funcall, share_pytranslate__sym_ir("list"), symbol_to_ir(cadr(x))),
            )
          _ => list2(list2(q_string, symbol_name_to_string(x)), symbol_to_ir(x))
        },
        cdadr(form),
      ),
    ),
  )
  let body = caddr(form)
  let stmts = if consp(body) && consp(car(body)) && eq(caar(body), q_mprog) {
    mprog_to_ir(body, context=q_function)
  } else if consp(body) && consp(car(body)) && eq(caar(body), q_mprogn) {
    let a = mapcar(x => maxima_to_ir(x), butlast(cdr(body)))
    append(
      a,
      list1(
        list3(
          q_funcall,
          share_pytranslate__sym_ir("return"),
          share_pytranslate__return_value_ir(clast(cdr(body))),
        ),
      ),
    )
  } else {
    list1(
      list3(
        q_funcall,
        share_pytranslate__sym_ir("return"),
        share_pytranslate__return_value_ir(body),
      ),
    )
  }
  let def = list4(
    q_func_def,
    fname,
    args,
    append(list3(q_body_indented, push, ins), stmts),
  )
  list3(
    q_body,
    def,
    list4(
      q_op_no_bracket,
      share_pytranslate__q_set,
      symbol_to_dictionary_ir(
        caaadr(form),
        dict_name=symval(q_ear_maxima_function_dictionary_name),
      ),
      symbol_to_ir(caaadr(form)),
    ),
  )
}

///|
/// Generates IR for atomic forms
fn atom_to_ir(form : Value) -> Value raise {
  if form is Nil {
    share_pytranslate__sym_ir("None")
  } else if eq(form, q_d_true) {
    share_pytranslate__sym_ir("True")
  } else if stringp(form) {
    list2(q_string, form)
  } else if !symbolp(form) {
    list3(q_num, form, Fix(0L))
  } else if eq(form, q_d__pcti) {
    // iota complex number
    list3(q_num, Fix(0L), Fix(1L))
  } else if eq(form, q_d__pctpi) {
    // Pi
    list3(q_num, share_pytranslate__sym_ir("math.pi"), Fix(0L))
  } else if eq(form, q_d__pcte) {
    // Euler's Constant
    list3(q_num, share_pytranslate__sym_ir("math.e"), Fix(0L))
  } else if eq(form, q_d_inf) {
    list3(q_num, share_pytranslate__sym_ir("math.inf"), Fix(0L))
  } else if member(form, symval(q_ear_symbols_directly_convert)).truthy() {
    symbol_to_ir(form)
  } else {
    symbol_to_dictionary_ir(form)
  }
}

///|
/// Generates IR for non-atomic forms
fn cons_to_ir(form : Value) -> Value raise {
  if !atom(caar(form)) {
    return Nil
  }
  let type_ = gethash(caar(form), symval(q_ear_maxima_direct_ir_map))
  if type_.truthy() {
    // If the form is present in *maxima-direct-ir-map*
    append(type_, mapcar(x => maxima_to_ir(x), cdr(form)))
  } else {
    let type_ = gethash(caar(form), symval(q_ear_maxima_special_ir_map))
    if type_.truthy() {
      // If the form is to be transformed in a specific way
      funcall(type_, [form])
    } else if memq(q_array, car(form)).truthy() {
      array_ref_to_ir(caar(form), cdr(form))
    } else {
      append(
        list2(
          q_funcall,
          if member(caar(form), symval(q_ear_symbols_directly_convert)).truthy() {
            symbol_to_ir(caar(form))
          } else {
            list3(
              q_element_array,
              symval(q_ear_maxima_function_dictionary_name),
              list2(q_string, symbol_name_to_string(caar(form))),
            )
          },
        ),
        mapcar(x => maxima_to_ir(x), cdr(form)),
      )
    }
  }
}

///|
/// Generates IR for Maxima expression
fn maxima_to_ir(form : Value, is_stmt? : Value = Nil) -> Value raise {
  let ir = if atom(form) {
    atom_to_ir(form)
  } else if consp(form) && consp(car(form)) {
    cons_to_ir(form)
  } else {
    cons(q_no_convert, form)
  }
  if is_stmt.truthy() {
    append_n([list1(q_body), symval(q_ear_ir_forms_to_append), list1(ir)])
  } else {
    ir
  }
}

///|
/// Driver function for the translator, calls the function maxima-to-ir and
/// then ir-to-python
fn d_pytranslate(form : Value, print_ir? : Value = Nil) -> Value raise {
  set(q_ear_ir_forms_to_append, Nil) |> ignore
  let form = nformat(form)
  if print_ir.truthy() {
    ir_to_python(print(maxima_to_ir(form, is_stmt=t)))
  } else {
    ir_to_python(maxima_to_ir(form, is_stmt=t))
  }
}

///|
/// Generates Python source for given IR form
fn ir_to_python(
  form : Value,
  indentation_level? : Value = Fix(0L),
  is_stmt? : Value = Nil,
) -> Value raise {
  let indent = if is_stmt.truthy() {
    // To determine if the form needs to be indented
    format_to_string("~v@{~A~:*~}", [indentation_level, Str("    ")])
  } else {
    ""
  }
  let s = match form {
    Cons(_) => {
      let type_ = gethash(car(form), symval(q_ear_ir_python_direct_templates))
      if type_.truthy() {
        lstring(funcall(type_, [form, indentation_level]))
      } else {
        format_to_string("no-covert : (~a)", [form])
      }
    }
    _ => format_to_string("~a", [form])
  }
  Str(indent + s)
}

// Code below is for functions handling specific IR forms and generating the
// corresponding Python code.

///|
fn dictionary_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "{~{~a~^, ~}}", [
    mapcar(
      elm => ir_to_python(
        list4(
          q_op_no_bracket,
          Char(':'),
          ir_to_python(car(elm)),
          ir_to_python(cadr(elm)),
        ),
        indentation_level~,
      ),
      cdr(form),
    ),
  ])
}

///|
fn obj_funcall_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "~a.~a(~{~a~^, ~})", [
    ir_to_python(cadr(form)),
    ir_to_python(caddr(form)),
    mapcar(elm => ir_to_python(elm, indentation_level~), cdddr(form)),
  ])
}

///|
fn while_loop_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "while ~a:~&~a", [
    ir_to_python(cadr(form), indentation_level~),
    ir_to_python(caddr(form), indentation_level~),
  ])
}

///|
fn for_list_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "for ~a in ~a:~&~a", [
    ir_to_python(cadr(form), indentation_level~),
    ir_to_python(caddr(form), indentation_level~),
    ir_to_python(clast(form), indentation_level~),
  ])
}

///|
fn lambda_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "lambda ~{~a~^, ~}: ~a", [
    mapcar(elm => ir_to_python(elm, indentation_level~), cadr(form)),
    ir_to_python(clast(form), indentation_level~),
  ])
}

///|
fn conditional_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "(~a if ~a else ~a)", [
    ir_to_python(caddr(form), indentation_level~),
    ir_to_python(cadr(form), indentation_level~),
    ir_to_python(cadddr(form), indentation_level~),
  ])
}

///|
fn cond_if_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "if ~a:", [ir_to_python(cadr(form), indentation_level~)])
}

///|
fn cond_else_to_python(form : Value, indentation_level : Value) -> Value raise {
  ignore(form)
  ignore(indentation_level)
  format(Nil, "else:", [])
}

///|
fn cond_elif_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "elif ~a:", [ir_to_python(cadr(form), indentation_level~)])
}

///|
fn element_array_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "~a[~a]", [
    ir_to_python(cadr(form), indentation_level~),
    ir_to_python(clast(form), indentation_level~),
  ])
}

///|
fn func_def_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "def ~a(~{~a~^, ~}):~&~a", [
    ir_to_python(cadr(form)),
    mapcar(elm => ir_to_python(elm, indentation_level~), caddr(form)),
    ir_to_python(clast(form), indentation_level~),
  ])
}

///|
fn struct_list_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "[~{~a~^, ~}]", [
    mapcar(elm => ir_to_python(elm, indentation_level~), cdr(form)),
  ])
}

///|
fn unary_op_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "(~a~a)", [cadr(form), ir_to_python(caddr(form), indentation_level~)])
}

///|
fn del_to_python(form : Value, indentation_level : Value) -> Value raise {
  ignore(indentation_level)
  format(Nil, "del ~a", [ir_to_python(cadr(form))])
}

///|
fn funcall_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "~a(~{~a~^, ~})", [
    ir_to_python(cadr(form)),
    mapcar(elm => ir_to_python(elm, indentation_level~), cddr(form)),
  ])
}

///|
fn string_to_python(form : Value, indentation_level : Value) -> Value raise {
  ignore(indentation_level)
  format(Nil, "~c~a~c", [Char('"'), cadr(form), Char('"')])
}

///|
fn assign_to_python(form : Value, indentation_level : Value) -> Value raise {
  ignore(indentation_level)
  format(Nil, "~a = ~a", [ir_to_python(cadr(form)), ir_to_python(caddr(form))])
}

///|
fn asterisk_to_python(form : Value, indentation_level : Value) -> Value raise {
  ignore(indentation_level)
  format(Nil, "*~a", [ir_to_python(cadr(form))])
}

///|
fn symbol_to_python(form : Value, indentation_level : Value) -> Value raise {
  ignore(indentation_level)
  cadr(form)
}

///|
fn op_no_bracket_template(op : Value) -> Value raise {
  format(Nil, "~@?", [Str("~~{~~#[~~;~~a~~:;~~a ~a ~~]~~}"), op])
}

///|
fn op_no_bracket_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, lstring(op_no_bracket_template(ir_to_python(cadr(form)))), [
    mapcar(elm => ir_to_python(elm, indentation_level~), cddr(form)),
  ])
}

///|
fn op_template(op : Value) -> Value raise {
  format(Nil, "~@?", [Str("(~~{~~#[~~;~~a~~:;~~a ~a ~~]~~})"), op])
}

///|
fn op_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, lstring(op_template(ir_to_python(cadr(form)))), [
    mapcar(elm => ir_to_python(elm, indentation_level~), cddr(form)),
  ])
}

///|
/// "~{~&~a~}" had a problem regarding indentation (the lines of a nested
/// while loop weren't properly indented), hence ~% for new line.
fn body_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "~{~%~a~}", [
    mapcar(elm => ir_to_python(elm, indentation_level~, is_stmt=t), cdr(form)),
  ])
}

///|
fn body_indented_to_python(form : Value, indentation_level : Value) -> Value raise {
  format(Nil, "~{~&~a~}", [
    mapcar(
      elm => ir_to_python(elm, indentation_level=one_plus(indentation_level), is_stmt=t),
      cdr(form),
    ),
  ])
}

///|
fn num_to_python(form : Value, indentation_level : Value) -> Value raise {
  ignore(indentation_level)
  if eql(Fix(0L), clast(form)) {
    ir_to_python(cadr(form))
  } else {
    Str("1j")
  }
}

///|
/// Function to display the internal Maxima form
fn d_show_form(form : Value) -> Value raise {
  print(nformat_check(form))
}

///|
/// Top-level forms: the non-literal DEFVARs (the hash tables mapping Maxima
/// operators and IR heads to their translations).
fn init_share_pytranslate() -> Unit raise {
  if !boundp(q_ear_maxima_direct_ir_map) {
    let ht = make_hash_table()
    let put = (k : Value, v : String) => sethash(k, ht, lread(v))
    put(q_mtimes, "(op *)") |> ignore
    put(q_mplus, "(op +)") |> ignore
    put(q_rat, "(op /)") |> ignore
    put(q_mquotient, "(op /)") |> ignore
    put(q_msetq, "(op-no-bracket =)") |> ignore
    put(q_mlist, "(struct-list)") |> ignore
    put(q_mand, "(boolop (symbol \"and\"))") |> ignore
    put(q_mor, "(boolop (symbol \"or\"))") |> ignore
    put(q_mnot, "(funcall (symbol \"not\"))") |> ignore
    put(q_mminus, "(unary-op -)") |> ignore
    put(q_mgreaterp, "(comp-op >)") |> ignore
    put(q_mequal, "(comp-op ==)") |> ignore
    put(q_mnotequal, "(comp-op !=)") |> ignore
    put(q_mlessp, "(comp-op <)") |> ignore
    put(q_mgeqp, "(comp-op >=)") |> ignore
    put(q_mleqp, "(comp-op <=)") |> ignore
    put(q_d_floor, "(funcall (symbol \"math.floor\"))") |> ignore
    put(q_d_fix, "(funcall (symbol \"math.floor\"))") |> ignore
    put(q_p_fix, "(funcall (symbol \"math.floor\"))") |> ignore
    put(q_p_sqrt, "(funcall (symbol \"math.sqrt\"))") |> ignore
    put(q_mreturn, "(funcall (symbol \"return\"))") |> ignore
    put(q_mabs, "(funcall (symbol \"abs\"))") |> ignore
    set(q_ear_maxima_direct_ir_map, ht) |> ignore
  }
  if !boundp(q_ear_maxima_special_ir_map) {
    let ht = make_hash_table()
    let put = (k : Value, v : Value) => sethash(k, ht, v)
    put(q_mdefine, q_func_def_to_ir) |> ignore
    put(q_p_array, q_array_def_to_ir) |> ignore
    put(q_mprog, q_mprog_to_ir) |> ignore
    put(q_mprogn, q_mprogn_to_ir) |> ignore
    put(q_mcond, q_mcond_to_ir) |> ignore
    put(q_lambda, q_lambda_to_ir) |> ignore
    put(q_mdoin, q_for_list_to_ir) |> ignore
    put(q_mdo, q_for_loop_to_ir) |> ignore
    put(q_p_endcons, q_endcons_to_ir) |> ignore
    put(q_d_endcons, q_endcons_to_ir) |> ignore
    put(q_d_plot3d, q_plot_to_ir) |> ignore
    put(q_d_plot2d, q_plot_to_ir) |> ignore
    put(q_mexpt, q_mexpt_to_ir) |> ignore
    put(q_mfactorial, q_mfactorial_to_ir) |> ignore
    set(q_ear_maxima_special_ir_map, ht) |> ignore
  }
  if !boundp(q_ear_ir_python_direct_templates) {
    let ht = make_hash_table()
    let put = (k : Value, v : Value) => sethash(k, ht, v)
    put(q_num, q_num_to_python) |> ignore
    put(q_asterisk, q_asterisk_to_python) |> ignore
    put(q_body, q_body_to_python) |> ignore
    put(q_body_indented, q_body_indented_to_python) |> ignore
    put(q_op, q_op_to_python) |> ignore
    put(q_op_no_bracket, q_op_no_bracket_to_python) |> ignore
    put(q_comp_op, q_op_to_python) |> ignore
    put(q_boolop, q_op_to_python) |> ignore
    put(q_op, q_op_to_python) |> ignore
    put(q_del, q_del_to_python) |> ignore
    put(q_unary_op, q_unary_op_to_python) |> ignore
    put(q_symbol, q_symbol_to_python) |> ignore
    put(q_assign, q_assign_to_python) |> ignore
    put(q_string, q_string_to_python) |> ignore
    put(q_funcall, q_funcall_to_python) |> ignore
    put(q_struct_list, q_struct_list_to_python) |> ignore
    put(q_func_def, q_func_def_to_python) |> ignore
    put(q_element_array, q_element_array_to_python) |> ignore
    put(q_conditional, q_conditional_to_python) |> ignore
    put(q_cond_if, q_cond_if_to_python) |> ignore
    put(q_cond_else, q_cond_else_to_python) |> ignore
    put(q_cond_elif, q_cond_elif_to_python) |> ignore
    put(q_lambda, q_lambda_to_python) |> ignore
    put(q_for_list, q_for_list_to_python) |> ignore
    put(q_while_loop, q_while_loop_to_python) |> ignore
    put(q_obj_funcall, q_obj_funcall_to_python) |> ignore
    put(q_dictionary, q_dictionary_to_python) |> ignore
    set(q_ear_ir_python_direct_templates, ht) |> ignore
  }
}

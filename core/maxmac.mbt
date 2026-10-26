// Port of src/maxmac.lisp: miscellaneous macros used in Macsyma source
// files.
//
// Body macros are translated at their call sites; the declared macro
// functions below take their bodies as lists of thunks (Lisp functions of
// no arguments, e.g. `list1(lfunc("body", _ => ...))`) and return the
// value of the last one:
//
//   (with-new-context (ctx...) body...)  with_new_context(list([ctx...]), list1(thunk))
//   (mbinding (vars vals fname) body...) mbinding(list([vars, vals, fname]), list1(thunk))
//   (with-default-quotient-dispflags body...)
//       with_specials([(q_d_exptdispflag, t), (q_d_pfeformat, Nil),
//                      (q_d__pctedispflag, Nil)], () => body)

///|
/// Run a list of thunks, returning the value of the last (PROGN).
fn maxmac__progn(forms : Value) -> Value raise {
  let mut v : Value = Nil
  for f in forms.iter() {
    v = funcall0(f)
  }
  v
}

///|
/// Like PUSH, but works at the other end: returns the new value of the
/// place, `(nconc list (ncons object))`, which the caller must store.
fn tuchus(list_ : Value, object_ : Value) -> Value raise {
  nconc(list_, list1(object_))
}

///|
fn load_macsyma_macros_at_runtime(l : Value) -> Value raise {
  mapcar(
    x => {
      if get(x, q_macsyma_module) is Nil {
        raise LispError::SimpleError(
          format_to_string("Missing Maxima macro file -- ~A", [x]),
        )
      }
      Nil
    },
    l,
  )
}

///|
/// `(load-macsyma-macros &rest macro-files)`: a compile-time check that the
/// macro files are loaded.  Returns no values (NIL).
fn load_macsyma_macros(macro_files : Value) -> Value raise {
  load_macsyma_macros_at_runtime(macro_files) |> ignore
  Nil
}

///|
/// `(with-new-context sub-context &rest forms)`: run FORMS (thunks) in a
/// new context created by supcontext, killing it afterwards.
fn with_new_context(sub_context : Value, forms : Value) -> Value raise {
  let my_context = gensym(prefix="$ctxt")
  mfuncall(q_d_supcontext, cons(my_context, sub_context)) |> ignore
  defer (d_killcontext(list1(my_context)) catch { _ => Nil }) |> ignore
  maxmac__progn(forms)
}

///|
/// For creating a macsyma evaluator variable binding context:
/// VARIABLE-SPECIFICATION is (VARIABLES &OPTIONAL VALUES FUNCTION-NAME);
/// BODY is a list of thunks.
fn mbinding(variable_specification : Value, body : Value) -> Value raise {
  let temp = car(variable_specification)
  match length(variable_specification) {
    1 => mbinding_sub(temp, temp, Nil, body)
    2 => mbinding_sub(temp, cadr(variable_specification), Nil, body)
    3 =>
      mbinding_sub(
        temp,
        cadr(variable_specification),
        caddr(variable_specification),
        body,
      )
    _ =>
      maxima_error(
        Str("Bad variable specification: ~a"),
        list1(variable_specification),
      )
  }
}

///|
fn mbinding_sub(
  variables : Value,
  values : Value,
  function_name : Value,
  body : Value,
) -> Value raise {
  let win = Ref::new(false)
  defer (if win.val { (munbind(variables) catch { _ => Nil }) |> ignore })
  mbind(variables, values, function_name) |> ignore
  win.val = true
  maxmac__progn(body)
}

///|
fn matanp(x : Value) -> Value raise {
  lbool(!atom(x) && eq(caar(x), q_p_atan))
}

// Macros used in LIMIT, DEFINT, RESIDU.

///|
fn real_infinityp(x : Value) -> Value raise {
  memq(x, symval(q_ear_real_infinities))
}

///|
fn infinityp(x : Value) -> Value raise {
  if memq(x, symval(q_ear_infinities)).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn real_epsilonp(x : Value) -> Value raise {
  memq(x, symval(q_ear_infinitesimals))
}

///|
fn free_epsilonp(x : Value) -> Value raise {
  lbool(amongl(symval(q_ear_infinitesimals), x) is Nil)
}

///|
fn free_infp(x : Value) -> Value raise {
  lbool(amongl(symval(q_ear_infinities), x) is Nil)
}

///|
fn inf_typep(x : Value) -> Value raise {
  car(amongl(symval(q_ear_infinities), x))
}

///|
fn epsilon_typep(x : Value) -> Value raise {
  car(amongl(symval(q_ear_infinitesimals), x))
}

///|
fn hot_coef(p : Value) -> Value raise {
  pdis(caddr(cadr(rat_no_ratfac(p))))
}

///|
/// `(defmspec name-or-list &rest rest)`: NAME-OR-LIST is either a symbol
/// or `(function :properties plist)`.  In the port REST is a list whose
/// car is the handler, a Lisp function of one argument (the whole
/// unevaluated form); it is installed on the MFEXPR* property and the
/// properties are set.
fn defmspec(name_or_list : Value, rest_ : Value) -> Value raise {
  let (function, properties) : (Value, Value) = if symbolp(name_or_list) {
    (name_or_list, Nil)
  } else {
    (car(name_or_list), getf(cdr(name_or_list), kw("properties")))
  }
  putprop(function, car(rest_), q_mfexpr_star) |> ignore
  for p in properties.iter() {
    putprop_(function, cadr(p), car(p)) |> ignore
  }
  function
}

// Setf hacking.

///|
fn mget(atom_ : Value, ind : Value) -> Value raise {
  let props = if symbolp(atom_) { get(atom_, q_mprops) } else { Nil }
  if props.truthy() {
    getf(cdr(props), ind)
  } else {
    Nil
  }
}

///|
fn old_get(plist : Value, tag : Value) -> Value raise {
  getf(cdr(plist), tag)
}

///|
fn d_get(atom_ : Value, ind : Value) -> Value raise {
  prop1(q_d_get, atom_, Nil, ind)
}

///|
fn mdefprop(sym_ : Value, val : Value, indicator : Value) -> Value raise {
  mputprop(sym_, val, indicator)
}

///|
fn mputprop(atom_ : Value, val : Value, ind : Value) -> Value raise {
  let mut props = get(atom_, q_mprops)
  if props is Nil {
    props = list1(Nil)
    putprop_(atom_, props, q_mprops) |> ignore
  }
  putprop_(props, val, ind)
}

///|
fn init_maxmac() -> Unit raise {
  macsyma_module(sym("maxmac"), list1(q_macro)) |> ignore
}

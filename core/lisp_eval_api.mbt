// Lisp evaluator: entry points and initialization.

///|
let le__initialized : Ref[Bool] = Ref(false)

///|
/// Install the reader hooks (#. and #$) that need the evaluator.
fn le__init_reader_hooks() -> Unit {
  @lisp.read_eval_hook.val = form => lisp_eval_form(form)
  @lisp.read_maxima_hook.val = text => with_special(
    q_ear_mread_prompt,
    Str(""),
    () => macsyma_read_string(Str(text)),
  )
}

///|
/// Set up the evaluator on first use: the CL functions, *FEATURES*, the
/// reader hooks and the Lisp definitions of Maxima's macros.
fn le__init() -> Unit raise {
  if le__initialized.val {
    return
  }
  le__initialized.val = true
  le__register_cl_lists()
  le__register_cl_sequences()
  le__register_cl_numbers()
  le__register_cl_strings()
  le__register_cl_hash()
  le__register_conditions()
  le__register_structs()
  le__register_arrays()
  le__register_symbols()
  le__register_streams()
  le__register_eval()
  le__register_maxima_support()
  let feats = sym("*features*")
  if !boundp(feats) {
    set(
      feats,
      list(
        [
          ":has-distinct-double-float", ":lisp-unicode-capable", ":cl", ":cltl2",
          ":64-bit", ":ansi-cl", ":common-lisp", ":ieee-floating-point", ":unix",
        ].map(sym),
      ),
    )
    |> ignore
  }
  for name in [
    "*load-pathname*", "*load-truename*", "*compile-file-pathname*", "*load-verbose*",
    "*load-print*", "*compile-verbose*", "*compile-print*",
  ] {
    if !boundp(sym(name)) {
      set(sym(name), Nil) |> ignore
    }
  }
  if !boundp(sym("*package*")) {
    set(sym("*package*"), Str("MAXIMA")) |> ignore
  }
  if !boundp(sym("*print-case*")) {
    set(sym("*print-case*"), sym(":upcase")) |> ignore
  }
  for name in ["*print-pretty*", "*print-circle*", "*print-readably*", "*print-level*", "*print-length*", "*read-suppress*", "*break-on-signals*"] {
    if !boundp(sym(name)) {
      set(sym(name), Nil) |> ignore
    }
  }
  for name in ["*print-escape*", "*print-gensym*", "*print-array*", "*read-eval*"] {
    if !boundp(sym(name)) {
      set(sym(name), t) |> ignore
    }
  }
  for c in [
    ("internal-time-units-per-second", Value::Fix(1000000L)),
    ("pi", Flo(@math.PI)),
    ("char-code-limit", Fix(1114112L)),
    ("array-dimension-limit", Fix(4611686018427387901L)),
    ("array-total-size-limit", Fix(4611686018427387901L)),
    ("call-arguments-limit", Fix(4611686018427387903L)),
    ("lambda-parameters-limit", Fix(4611686018427387903L)),
    ("multiple-values-limit", Fix(1073741824L)),
    ("boole-and", Fix(1L)),
    ("boole-xor", Fix(6L)),
    ("boole-ior", Fix(7L)),
    ("single-float-epsilon", Flo(1.1102230246251568e-16)),
    ("most-positive-single-float", Flo(1.7976931348623157e308)),
    ("most-negative-single-float", Flo(-1.7976931348623157e308)),
  ] {
    if !boundp(sym(c.0)) {
      set(sym(c.0), c.1) |> ignore
    }
  }
  le__init_reader_hooks()
  le__wrap_mv_functions()
  // the function cells of the operations compiled inline
  for name in [
    "+", "-", "*", "<", ">", "<=", ">=", "=", "eq", "eql", "equal", "cons", "1+",
    "1-", "car", "cdr", "cadr", "cddr", "caar", "cdar", "null", "not", "atom",
    "consp",
  ] {
    match intern(name) {
      { func: Some(lf), id, .. } => le__inline_cells[id] = lf
      _ => ()
    }
  }
  // Maxima's macros written in Lisp
  let saved = @lisp.reader_package.val
  @lisp.reader_package.val = "maxima"
  defer {
    @lisp.reader_package.val = saved
  }
  @lisp.lread_source_all(le__prelude, f => le__eval_file_form(f) |> ignore)
}

///|
/// The multiple-valued wrappers installed by `le__wrap_mv_functions`.
let le__mv_wrapped : Map[Int, LFunc] = Map::new()

///|
/// Symbols whose function was defined by interpreted code (not to be
/// replaced by a wrapper).
let le__interpreted_defuns : Set[Int] = Set::new()

///|
/// Replace the function cells of the ported multiple-valued functions
/// (which return their primary value) by wrappers that also set the values
/// register. Run at initialization and after a share package is loaded.
fn le__wrap_mv_functions() -> Unit {
  for p in le__mv_wrappers() {
    match p.0 {
      Sym({ func: Some(lf), .. } as s) => {
        if le__mv_wrapped.get(s.id) is Some(w) && physical_equal(w, lf) {
          continue
        }
        if le__interpreted_defuns.contains(s.id) {
          continue
        }
        let f = p.1
        let w : LFunc = { name: s.name, call: args => le__values(f(args)) }
        s.func = Some(w)
        le__mv_wrapped[s.id] = w
      }
      _ => ()
    }
  }
}

///|
/// Called after a share package's functions have been registered.
fn lisp_eval_after_share_load() -> Unit {
  if le__initialized.val {
    le__wrap_mv_functions()
  }
}

///|
/// Evaluate a Lisp form in the null lexical environment.
fn lisp_eval_form(form : Value) -> Value raise {
  le__init()
  le__eval_toplevel(form)
}

///|
/// Evaluate a Lisp form and return all its values.
fn lisp_eval_form_values(form : Value) -> Array[Value] raise {
  le__init()
  le__mv.val = None
  let v = le__eval_toplevel(form)
  le__values_of(v)
}

///|
/// Load a Lisp source file: read and evaluate each top-level form.
fn lisp_load_file(path : String) -> Unit raise {
  le__init()
  let text = read_file(path)
  let saved = @lisp.reader_package.val
  @lisp.reader_package.val = "maxima"
  defer {
    @lisp.reader_package.val = saved
  }
  with_specials(
    [
      (sym("*load-pathname*"), Str(path)),
      (sym("*load-truename*"), Str(suprv1__truename(path))),
      (sym("*package*"), symval(sym("*package*"))),
    ],
    () => {
      @lisp.lread_source_all(text, f => le__eval_file_form(f) |> ignore)
      Value::Nil
    },
  )
  |> ignore
}

///|
/// CL (read stream nil eof): one datum from an input stream, or `eof`.
fn lisp_read(stream : Value, eof : Value) -> Value raise {
  le__init()
  @lisp.lread_stream(stream, eof_error=false, eof_value=eof)
}

///|
/// Read all forms of a string of Lisp source and evaluate them; returns the
/// value of the last one.
fn lisp_eval_string(text : String) -> Value raise {
  le__init()
  let mut v : Value = Nil
  @lisp.lread_source_all(text, f => v = le__eval_file_form(f))
  v
}

///|
/// Names of the macros the prelude defines (before it has been loaded).
let le__prelude_macro_names : Ref[Set[String]?] = Ref(None)

///|
fn le__prelude_macros() -> Set[String] {
  match le__prelude_macro_names.val {
    Some(s) => s
    None => {
      let s : Set[String] = Set::new()
      for line in le__prelude.split("\n") {
        let l = line.to_string()
        if l.has_prefix("(defmacro ") {
          let rest = l.substring(start=10)
          let name = match rest.find(" ") {
            Some(i) => rest.substring(end=i)
            None => rest
          }
          s.add(name)
        }
      }
      le__prelude_macro_names.val = Some(s)
      s
    }
  }
}

///|
/// (coerce lambda-expression 'function)
fn lisp_function_of_lambda(lform : Value) -> Value raise {
  le__init()
  le__closure_of_lambda(lform, Top, None)
}

///|
/// Is the symbol the name of a Lisp macro? (CL MACRO-FUNCTION as a test)
fn lisp_macro_p(s : Value) -> Bool raise {
  match s {
    Sym(sy) => {
      get(s, le__q_macro_function).truthy() ||
      le__builtin_macros().contains(sy.name) ||
      (!le__initialized.val && le__prelude_macros().contains(sy.name)) ||
      (sy.func is None && le__maxima_macro_sources.contains(sy.name))
    }
    _ => false
  }
}

///|
/// The macro expander of a symbol (CL MACRO-FUNCTION), or nil.
fn lisp_macro_function(s : Value) -> Value raise {
  match s {
    Sym(sy) => {
      let p = get(s, le__q_macro_function)
      if p.truthy() {
        return p
      }
      if le__builtin_macros().get(sy.name) is Some(exp) {
        return lfunc(sy.name, args => exp(arg(args, 0), Top))
      }
      if !le__initialized.val && le__prelude_macros().contains(sy.name) {
        le__init()
        return get(s, le__q_macro_function)
      }
      if sy.func is None && le__maxima_macro_sources.contains(sy.name) {
        le__init()
        if le__define_library_macro(sy) {
          return get(s, le__q_macro_function)
        }
      }
      Nil
    }
    _ => Nil
  }
}

// The Maxima-to-Lisp translator (transl*.lisp) is not ported: the port has
// no Lisp compiler. `translate` and `compile` keep their user-visible
// contract -- they check that each function exists, mark it translated and
// return the list of names, as transs.lisp's $TRANSLATE does -- while the
// function keeps running in the interpreter, which computes the same
// results.

///|
/// TRANSLATE-FUNCTION: succeed for an existing function (signalling
/// fundef's "no such function" otherwise) and return its name.
fn translate_compat__function(name : Value) -> Value raise {
  // tr-mfun fetches the definition the same way FUNDEF does
  consfundef(name, Nil, Nil) |> ignore
  putprop(name, t, q_translated) |> ignore
  name
}

///|
/// `$translate` (transs.lisp)
fn translate_compat__translate(form : Value) -> Value raise {
  let mut functs = cdr(form)
  if functs.truthy() && stringp(car(functs)) {
    return merr(
      "translate: call 'translate_file' to translate a file; found: ~M",
      [car(functs)],
    )
  }
  if memq(q_d_functions, functs).truthy() || memq(q_d_all, functs).truthy() {
    functs = mapcar(x => caar(x), cdr(symval(q_d_functions)))
  }
  let v = Collector::new()
  for f in functs.iter() {
    if atom(f) {
      let it = translate_compat__function(d_verbify(f))
      if it.truthy() {
        v.add(it)
      }
    } else {
      mformat(
        list([
          Nil,
          Str("error: 'translate' argument must be an atom; found: ~M~%"),
          f,
        ]),
      )
      |> ignore
    }
  }
  cons(list1(q_mlist), v.result())
}

///|
/// `$compile` (transs.lisp): translate, then (no-op) compile.
fn translate_compat__compile(form : Value) -> Value raise {
  translate_compat__translate(form)
}

///|
fn init_translate_compat() -> Unit {
  register_mspec(sym("$translate"), translate_compat__translate)
  register_mspec(sym("$compile"), translate_compat__compile)
}

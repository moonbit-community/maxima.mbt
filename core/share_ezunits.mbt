// Port of share/ezunits/ezunits.lisp (Robert Dodier, 2008): TeX and MathML
// output for the ezunits backtick operator, and the helpers $odds/$evens.

///|
/// Process tex(a`b): throw away the backtick, texify a, and texify b with
/// all symbols in b output as mathrm.
fn tex_ezunits(x : Value, l : Value, r : Value) -> Value raise {
  let l = tex(cadr(x), l, list1(Str("\\;")), symval(q_lop), caar(x))
  tex(mathrm_ify(caddr(x)), l, r, caar(x), symval(q_rop))
}

///|
/// If a symbol has a texword property, preserve it. Otherwise replace each
/// symbol with a gensym which has a mathrm texword property.
fn mathrm_ify(e : Value) -> Value raise {
  let v = reverse(cdr(d_listofvars(e)))
  let l = mapcar(
    s => if get(s, q_texword).truthy() {
      s
    } else {
      let g = gensym()
      putprop(
        g,
        Str(
          "\\mathrm{" +
          lstring(maybe_invert_string_case(Str(symbol_name(stripdollar(s))))) +
          "}",
        ),
        q_texword,
      )
      |> ignore
      g
    },
    v,
  )
  let eqs = Collector::new()
  let mut pa = v
  let mut pb = l
  while pa is Cons(_) && pb is Cons(_) {
    eqs.add(mk(q_mequal, [car(pa), car(pb)]))
    pa = cdr(pa)
    pb = cdr(pb)
  }
  d_substitute(cons(list1(q_mlist), eqs.result()), e)
}

///|
fn d_odds(a : Value) -> Value raise {
  cons(list1(q_mlist), odds(cdr(a), Fix(1L)))
}

///|
fn d_evens(a : Value) -> Value raise {
  cons(list1(q_mlist), odds(cdr(a), Fix(0L)))
}

///|
/// Display an ezunits expression in MathML; only called after the MathML
/// presentation library has been loaded.
fn mathml_presentation_ezunits(mexpress : Value) -> Value raise {
  funcall(q_mpr_engine, [
    mk(q_mtimes, [cadr(mexpress), caddr(mexpress)]),
    q_mparen,
    q_mparen,
  ])
}

///|
/// Installed into *MATHML-PRESENTATION-HOOK*: an idempotent setup function
/// registering the MathML output for ezunits expressions.
fn ezunits_setup_mathml() -> Value raise {
  funcall(q_setup, [
    list2(q_d_op_bq, list2(q_mprprocess, q_mathml_presentation_ezunits)),
  ])
}

///|
fn init_share_ezunits() -> Unit raise {
  putprop(q_d_op_bq_bq, q_tex_infix, q_tex) |> ignore
  putprop(q_d_op_bq, q_tex_ezunits, q_tex) |> ignore
  // Register a hook so we set up properly if the MathML code hasn't yet
  // been loaded.
  set(
    q_ear_mathml_presentation_hook,
    cons(
      q_ezunits_setup_mathml,
      remove(
        q_ezunits_setup_mathml,
        if boundp(q_ear_mathml_presentation_hook) {
          symval(q_ear_mathml_presentation_hook)
        } else {
          Nil
        },
      ),
    ),
  )
  |> ignore
  // But make sure we do the right thing if it's been loaded already.
  if fboundp(q_mpr_engine) {
    ezunits_setup_mathml() |> ignore
  }
}

// Port of share/contrib/diffequations/odeutils.lisp (Barton Willis, 2004):
// utilities for odelin. The algorithms are shared with the port of
// odelin.lisp (core/share_odelin.mbt), which loads these files itself.

///|
/// Map the function f onto a mbag and simplify the result. When the bag is
/// an equality, list, or matrix, simplification isn't needed; however, new
/// types of bags (say sets) may need simplification after the mapping.
///
/// If the arguments of bag are in CRE form, margs changes them to general
/// form---and mbag-map may return an expression in general form.
fn mbag_map(f : Value, bag : Value) -> Value raise {
  share_odelin__mbag_map(x => funcall(f, [x]), bag)
}

///|
fn number_of_unks(p : Value, unks : Value) -> Value raise {
  share_odelin__number_of_unks(p, unks)
}

///|
/// Evaluate the top-level forms of the diffequations data files (kummer,
/// gauss, extrabessel, spherodialwave, ...): `($put 'a v 'i)` and
/// `(putprop 'a 'v 'i)` with quoted or self-evaluating arguments.
fn share_odeutils__eval_put_forms(text : String) -> Unit raise {
  let arg_value = (x : Value) => if consp(x) && eq(car(x), q_quote) {
    cadr(x)
  } else {
    x
  }
  for form in lread_all(text) {
    let args = cdr(form)
    let a = arg_value(car(args))
    let v = arg_value(cadr(args))
    let i = arg_value(caddr(args))
    match symbol_name(car(form)) {
      "$put" => d_put(a, v, i) |> ignore
      "putprop" => putprop(a, v, i) |> ignore
      _ =>
        raise LispError::SimpleError(
          "unexpected top-level form " + prin1_to_string(form),
        )
    }
  }
}

///|
fn init_share_odeutils() -> Unit raise {
  d_put(sym("$odeutils"), int(1), q_d_version) |> ignore
}

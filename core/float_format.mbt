// Port of src/float-format.lisp: the mapping from Maxima's 'flonum float
// type to a CL float type.  The port always uses the default
// double-float flonum (no :flonum-long / :flonum-double-double), so the
// FLONUM type is `Flo(Double)` and the constants below are the double
// constants of the runtime:
//
//   +most-positive-flonum+               most_positive_double_float
//   +most-negative-flonum+               -most_positive_double_float
//   +least-positive-flonum+              least_positive_double_float
//   +least-negative-flonum+              -least_positive_double_float
//   +flonum-epsilon+                     double_float_epsilon
//   +least-positive-normalized-flonum+   least_positive_normalized_double_float
//   +least-negative-normalized-flonum+   -least_positive_normalized_double_float
//   +flonum-exponent-marker+             #\D (set by gen_vars.mbt)
//
// Translated code should use the runtime constants directly; the symbol
// values are also set here for code that reads them with `symval`.

///|
fn init_float_format() -> Unit raise {
  set(q_n_plusmost_positive_flonum_plus, Flo(most_positive_double_float))
  |> ignore
  set(q_n_plusmost_negative_flonum_plus, Flo(-most_positive_double_float))
  |> ignore
  set(q_n_plusleast_positive_flonum_plus, Flo(least_positive_double_float))
  |> ignore
  set(q_n_plusleast_negative_flonum_plus, Flo(-least_positive_double_float))
  |> ignore
  set(q_n_plusflonum_epsilon_plus, Flo(double_float_epsilon)) |> ignore
  set(
    q_n_plusleast_positive_normalized_flonum_plus,
    Flo(least_positive_normalized_double_float),
  )
  |> ignore
  set(
    q_n_plusleast_negative_normalized_flonum_plus,
    Flo(-least_positive_normalized_double_float),
  )
  |> ignore
}

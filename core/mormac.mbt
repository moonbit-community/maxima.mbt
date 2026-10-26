// Port of src/mormac.lisp: the MACSYMA-MODULE macro.

///|
/// `(macsyma-module module &rest options)`: record OPTIONS on the
/// MACSYMA-MODULE property of MODULE (RUNTIME when no options are given).
/// The macro also sets *macro-file* (used by DECLARE-TOP at compile time)
/// to whether MACRO is among the options.
fn macsyma_module(module_ : Value, options : Value) -> Value raise {
  set(q_ear_macro_file, memq(q_macro, options)) |> ignore
  let opts = if options is Nil { list1(q_runtime) } else { options }
  defprop(module_, opts, q_macsyma_module)
}

///|
fn init_mormac() -> Unit raise {
  macsyma_module(sym("mormac"), list1(q_macro)) |> ignore
}

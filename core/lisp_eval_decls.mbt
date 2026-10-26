// Interface of the Lisp evaluator (core/lisp_eval*.mbt): evaluation of
// Lisp forms for `:lisp`, loading Lisp source files, and running the code
// that the translator (transl*.lisp) produces.

///|
/// Evaluate a Lisp form in the null lexical environment.
declare fn lisp_eval_form(form : Value) -> Value raise

///|
/// Load a Lisp source file: read and evaluate each top-level form.
declare fn lisp_load_file(path : String) -> Unit raise

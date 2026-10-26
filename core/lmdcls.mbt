// Port of src/lmdcls.lisp: DECLARE-TOP and MAKE-UNSPECIAL.
//
// `(declare-top (special a b) (unspecial c))` only proclaims variables
// special (or removes the special proclamation) at compile time.  In the
// port every variable named in a DECLARE-TOP SPECIAL is listed in
// docs/index/specials.txt and accessed with symval/set/bind, so uses of
// the macro need no translation: drop them.  UNSPECIAL declarations mean
// the variable is an ordinary lexical variable in that file.

///|
/// The port has no global special proclamations to clear; returns SYMBOL
/// like the Lisp version.
fn make_unspecial(symbol : Value) -> Value raise {
  symbol
}

///|
/// `(declare-top &rest decl-specs)`: compile-time declarations only;
/// nothing to do at run time.
fn declare_top(decl_specs : Value) -> Value raise {
  ignore(decl_specs)
  Nil
}

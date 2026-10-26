// Port of src/compat.lisp: Maclisp compatibility definitions.

///|
/// Make a symbol out of the printed representations of all args.
fn symbolconc(args : Value) -> Value raise {
  let sb = StringBuilder::new()
  for s in args.iter() {
    match s {
      Fix(_) | Big(_) => sb.write_string(format_to_string("~d", [s]))
      Nil | Sym(_) => sb.write_string(symbol_name(s))
      Str(str) => sb.write_string(str)
      _ => sb.write_string(format_to_string("~a", [s]))
    }
  }
  sym(sb.to_string())
}

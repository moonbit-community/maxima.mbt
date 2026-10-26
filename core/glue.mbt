// Hand-written glue between the generated contract and the Lisp runtime.

///|
/// Positional argument `i` from a Lisp-call argument array (nil if absent).
fn arg(args : Array[Value], i : Int) -> Value {
  if i < args.length() {
    args[i]
  } else {
    Nil
  }
}

///|
/// The `&rest` list starting at index `n`.
fn rest_args(args : Array[Value], n : Int) -> Value {
  if n >= args.length() {
    Nil
  } else {
    list_view(args[n:])
  }
}

///|
/// Value of keyword argument `:name` in `args[start:]`, if supplied.
fn key_arg(args : Array[Value], start : Int, name : String) -> Value? {
  let k = sym(name)
  let mut i = start
  while i + 1 < args.length() {
    if eq(args[i], k) {
      return Some(args[i + 1])
    }
    i += 2
  }
  None
}

///|
/// Raise Maxima's wrong-number-of-arguments error unless
/// `min <= args.length() <= max` (max < 0 means unbounded).
fn check_arity_range(
  name : String,
  args : Array[Value],
  min : Int,
  max : Int,
) -> Unit raise {
  let n = args.length()
  if n < min || (max >= 0 && n > max) {
    arity_error(name, args, min, max) |> ignore
  }
}

///|
/// Raise the "expected exactly N arguments" error for a fixed arity.
fn check_arity(name : String, args : Array[Value], n : Int) -> Unit raise {
  check_arity_range(name, args, n, n)
}

///|
fn arity_error(
  name : String,
  args : Array[Value],
  min : Int,
  max : Int,
) -> Value raise {
  let fname = if name.has_prefix("$") || name.has_prefix("%") {
    name.substring(start=1)
  } else {
    name
  }
  let given = args.length()
  let what = if min == max {
    "expected exactly \{min} arguments"
  } else if max < 0 {
    "expected at least \{min} arguments"
  } else if given < min {
    "expected at least \{min} arguments"
  } else {
    "expected at most \{max} arguments"
  }
  merror(
    Str("~M: " + what + " but got ~M: ~M"),
    list([sym("$" + fname), int(given), cons(list1(q_mlist), list(args))]),
  )
}

///|
/// Install a `defmspec` handler on the `mfexpr*` property.
fn register_mspec(s : Value, f : (Value) -> Value raise) -> Unit {
  let name = symbol_name(s) catch { _ => "?" }
  putprop(s, lfunc(name, args => f(arg(args, 0))), q_mfexpr_star) |> ignore
}

///|
/// Install a simplifier function on a symbol's function cell.
fn register_simplifier(s : Value, f : (Array[Value]) -> Value raise) -> Unit {
  defun(s, f)
}

///|
/// Initial value of a special variable.
fn defvar_init(s : Value, v : Value) -> Unit {
  if !boundp(s) {
    set(s, v) |> ignore
  }
}

///|
/// `(gettext s)` — no translation catalogs in the port.
fn gettext(s : String) -> String {
  s
}

// ---------------------------------------------------------------------------
// Expression-building helpers corresponding to mopers.lisp macros.

///|
/// `(take '(op) args...)`: `head` is the operator header list, e.g.
/// `list1(q_p_sin)`; arguments are already simplified.
fn take(head : Value, args : Array[Value]) -> Value raise {
  simplifya(cons(head, list(args)), t)
}

///|
/// `(take* '(op) args...)`: arguments not yet simplified.
fn take_star(head : Value, args : Array[Value]) -> Value raise {
  simplifya(cons(head, list(args)), Nil)
}

///|
/// `(ftake 'op args...)`
fn ftake(op : Value, args : Array[Value]) -> Value raise {
  simplifya(cons(list1(op), list(args)), t)
}

///|
/// `(ftake* 'op args...)`
fn ftake_star(op : Value, args : Array[Value]) -> Value raise {
  simplifya(cons(list1(op), list(args)), Nil)
}

///|
/// `(fapply 'op arglist)`
fn fapply(op : Value, arglist : Value) -> Value raise {
  simplifya(cons(list1(op), arglist), t)
}

///|
/// `(fapply* 'op arglist)`
fn fapply_star(op : Value, arglist : Value) -> Value raise {
  simplifya(cons(list1(op), arglist), Nil)
}

///|
/// `(add a b ...)` on simplified terms.
fn addn_(terms : Array[Value]) -> Value raise {
  if terms.length() == 2 {
    add2(terms[0], terms[1])
  } else {
    addn(list(terms), t)
  }
}

///|
/// `(add* a b ...)` on unsimplified terms.
fn addn_star(terms : Array[Value]) -> Value raise {
  if terms.length() == 2 {
    add2_star(terms[0], terms[1])
  } else {
    addn(list(terms), Nil)
  }
}

///|
/// `(mul a b ...)` on simplified factors.
fn muln_(factors : Array[Value]) -> Value raise {
  match factors.length() {
    2 => mul2(factors[0], factors[1])
    3 => mul3(factors[0], factors[1], factors[2])
    _ => muln(list(factors), t)
  }
}

///|
/// `(mul* a b ...)` on unsimplified factors.
fn muln_star(factors : Array[Value]) -> Value raise {
  if factors.length() == 2 {
    mul2_star(factors[0], factors[1])
  } else {
    muln(list(factors), Nil)
  }
}

///|
/// `(inv x)` = x^-1
fn inv(x : Value) -> Value raise {
  power(x, Fix(-1L))
}

///|
/// `(inv* x)`
fn inv_star(x : Value) -> Value raise {
  power_star(x, Fix(-1L))
}

///|
/// `(ncmul a b ...)`
fn ncmul_(factors : Array[Value]) -> Value raise {
  if factors.length() == 2 {
    ncmul2(factors[0], factors[1])
  } else {
    ncmuln(list(factors), t)
  }
}

///|
/// `(=0 x)`
fn eq0(x : Value) -> Bool {
  equal(x, Fix(0L))
}

///|
/// `(=1 x)`
fn eq1(x : Value) -> Bool {
  equal(x, Fix(1L))
}

///|
/// Build `((op) args...)` without simplifying (a fresh header).
fn mk(op : Value, args : Array[Value]) -> Value {
  cons(list1(op), list(args))
}

///|
/// Build `((op simp) args...)` (only for results known to be simplified).
fn mk_simp(op : Value, args : Array[Value]) -> Value {
  cons(list2(op, q_simp), list(args))
}

///|
/// `(caar x)` as the operator of a Maxima expression; nil for atoms.
fn op_of(x : Value) -> Value {
  match x {
    Cons({ car: Cons({ car: op, .. }), .. }) => op
    _ => Nil
  }
}

///|
/// Is `x` an expression with operator `op`?  (`(and (consp x) (eq (caar x) op))`)
fn is_op(x : Value, op : Value) -> Bool {
  match x {
    Cons({ car: Cons({ car: o, .. }), .. }) => eq(o, op)
    _ => false
  }
}

///|
/// Convenience: `(merror fmt args...)` from MoonBit strings.
fn merr(fmt : String, args : Array[Value]) -> Value raise {
  merror(Str(fmt), list(args))
}

///|
/// Run `f`, restoring the listed specials afterwards (Lisp `let` of
/// specials whose new values are assigned inside `f`).
fn[T] save_specials(syms : Array[Value], f : () -> T raise) -> T raise {
  let saved = syms.map(s => (s, symval(s), boundp(s)))
  defer {
    for e in saved {
      if e.2 {
        set(e.0, e.1) |> ignore
      } else {
        makunbound(e.0) |> ignore
      }
    }
  }
  f()
}

///|
/// CL `catch`: run f; if a `throw` to `tag` happens, return its value.
fn catch_tag(tag : Value, f : () -> Value raise) -> Value raise {
  f() catch {
    LispError::Throw(tg, v) if eq(tg, tag) => v
    e => raise e
  }
}

///|
/// CL `throw`.
fn throw_tag(tag : Value, v : Value) -> Value raise {
  raise LispError::Throw(tag, v)
}

///|
/// Is this error a Maxima-level error (merror) condition?
fn is_maxima_error(e : Error) -> Bool {
  match e {
    LispError::Condition(s, _, _) => s.name == "maxima-$error"
    _ => false
  }
}

///|
/// Lisp `(errset form)` / Maxima `errcatch`: Some(value) on success, None
/// if a Maxima error or Lisp error was signalled. Non-error control
/// transfers (throw, return-from, go) propagate.
fn errset(f : () -> Value raise) -> Value? raise {
  f() catch {
    LispError::Throw(_, _) as e => raise e
    LispError::ReturnFrom(_, _) as e => raise e
    LispError::Go(_) as e => raise e
    _ => None
  } noraise {
    v => Some(v)
  }
}

///|
/// `#$expr$`: parse Maxima syntax once (cached) and return the expression.
/// Implemented by the port of nparse.lisp.
declare fn maxima_lit(s : String) -> Value raise

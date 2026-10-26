// Lisp evaluator: Common Lisp functions -- arrays, symbols, types,
// conditions, structures, streams and files, evaluation.

// ---------------------------------------------------------------------------
// Types

///|
/// Parents of condition types (CL's hierarchy plus DEFINE-CONDITION).
let le__condition_parents : Map[String, Array[String]] = {
  "condition": [],
  "serious-condition": ["condition"],
  "error": ["serious-condition"],
  "warning": ["condition"],
  "simple-condition": ["condition"],
  "simple-error": ["simple-condition", "error"],
  "simple-warning": ["simple-condition", "warning"],
  "style-warning": ["warning"],
  "type-error": ["error"],
  "simple-type-error": ["simple-condition", "type-error"],
  "program-error": ["error"],
  "control-error": ["error"],
  "cell-error": ["error"],
  "unbound-variable": ["cell-error"],
  "undefined-function": ["cell-error"],
  "unbound-slot": ["cell-error"],
  "arithmetic-error": ["error"],
  "division-by-zero": ["arithmetic-error"],
  "floating-point-overflow": ["arithmetic-error"],
  "floating-point-underflow": ["arithmetic-error"],
  "floating-point-inexact": ["arithmetic-error"],
  "floating-point-invalid-operation": ["arithmetic-error"],
  "file-error": ["error"],
  "stream-error": ["error"],
  "end-of-file": ["stream-error"],
  "parse-error": ["error"],
  "reader-error": ["parse-error", "stream-error"],
  "package-error": ["error"],
  "print-not-readable": ["error"],
  "storage-condition": ["serious-condition"],
  "maxima-$error": ["error"],
}

///|
/// :report functions of condition types.
let le__condition_reports : Map[String, Value] = Map::new()

///|
/// Slot names of DEFINE-CONDITION types (with their initargs).
let le__condition_slots : Map[String, Array[(Value, Value)]] = Map::new()

///|
fn le__subtype_name(t1 : String, t2 : String) -> Bool {
  if t1 == t2 || t2 == "t" {
    return true
  }
  match le__condition_parents.get(t1) {
    Some(ps) => ps.iter().any(p => le__subtype_name(p, t2))
    None =>
      match le__struct_parents.get(t1) {
        Some(p) => le__subtype_name(p, t2)
        None => false
      }
  }
}

///|
fn le__type_name(ty : Value) -> String {
  match ty {
    Sym(s) => s.name
    Nil => "nil"
    _ => ""
  }
}

///|
fn le__range_ok(x : Value, lo : Value, hi : Value) -> Bool raise {
  let lo_ok = match lo {
    Sym({ name: "*", .. }) | Nil => true
    Cons({ car: l, .. }) => num_gt(x, l)
    l => num_ge(x, l)
  }
  let hi_ok = match hi {
    Sym({ name: "*", .. }) | Nil => true
    Cons({ car: h, .. }) => num_lt(x, h)
    h => num_le(x, h)
  }
  lo_ok && hi_ok
}

///|
fn le__typep(x : Value, ty : Value) -> Bool raise {
  match ty {
    Cons({ car: Sym(h), cdr: args }) =>
      match h.name {
        "or" => args.iter().any(t => le__typep(x, t) catch { _ => false })
        "and" => args.iter().all(t => le__typep(x, t) catch { _ => false })
        "not" => !le__typep(x, car(args))
        "member" => member_eql(x, args)
        "eql" => eql(x, car(args))
        "satisfies" => le__call1(car(args), x).truthy()
        "integer" => integerp(x) && le__range_ok(x, car(args), cadr(args))
        "float" | "double-float" | "single-float" | "real" | "rational" | "short-float" | "long-float" =>
          le__typep(x, Sym(h)) && le__range_ok(x, car(args), cadr(args))
        "mod" => integerp(x) && !minusp(x) && num_lt(x, car(args))
        "unsigned-byte" =>
          integerp(x) &&
          !minusp(x) &&
          (match car(args) {
            Fix(n) => integer_length(x) <= n.to_int()
            _ => true
          })
        "signed-byte" =>
          integerp(x) &&
          (match car(args) {
            Fix(n) => integer_length(x) < n.to_int()
            _ => true
          })
        "cons" =>
          match x {
            Cons({ car: a, cdr: d }) =>
              (car(args) is Nil || le__type_name(car(args)) == "*" ||
              le__typep(a, car(args))) &&
              (cadr(args) is Nil || le__type_name(cadr(args)) == "*" ||
              le__typep(d, cadr(args)))
            _ => false
          }
        "complex" => complexp(x)
        "string" | "simple-string" | "base-string" => stringp(x)
        "vector" | "simple-vector" | "array" | "simple-array" => arrayp(x) || stringp(x)
        "function" => functionp(x)
        _ => le__typep(x, Sym(h))
      }
    Nil => false
    Sym(s) =>
      match s.name {
        "t" => true
        "null" => x is Nil
        "list" => x is (Nil | Cons(_))
        "cons" => x is Cons(_)
        "atom" => !(x is Cons(_))
        "symbol" => x is (Nil | Sym(_))
        "keyword" => keywordp(x)
        "boolean" => x is Nil || eq(x, t)
        "number" => numberp(x)
        "real" => realp(x)
        "rational" => rationalp(x)
        "integer" => integerp(x)
        "fixnum" => fixnump(x)
        "bignum" => bignump(x)
        "bit" => x is Fix(0L | 1L)
        "unsigned-byte" => integerp(x) && !minusp(x)
        "signed-byte" => integerp(x)
        "ratio" => ratiop(x)
        "float" | "double-float" | "single-float" | "short-float" | "long-float" | "flonum" =>
          floatp(x)
        "complex" => complexp(x)
        "character" | "base-char" | "standard-char" => characterp(x)
        "string" | "simple-string" | "base-string" => stringp(x)
        "vector" | "simple-vector" | "array" | "simple-array" => arrayp(x) || stringp(x)
        "bit-vector" | "simple-bit-vector" => vectorp(x)
        "sequence" => x is (Nil | Cons(_) | Vec(_) | Str(_))
        "hash-table" => hash_table_p(x)
        "function" | "compiled-function" => functionp(x)
        "stream" => streamp(x)
        "package" => stringp(x)
        "pathname" => stringp(x)
        "random-state" => false
        "structure" | "structure-object" => x is Struct(_)
        name =>
          match x {
            Struct(st) => le__subtype_name(st.stype.name, name)
            _ => false
          }
      }
    _ => false
  }
}

///|
fn member_eql(x : Value, l : Value) -> Bool {
  for y in l.iter() {
    if eql(x, y) {
      return true
    }
  }
  false
}

///|
fn le__type_of(x : Value) -> Value {
  match x {
    Nil => sym("null")
    Sym(s) => if s.name.has_prefix(":") { sym("keyword") } else { sym("symbol") }
    Cons(_) => sym("cons")
    Fix(_) => sym("fixnum")
    Big(_) => sym("bignum")
    Ratio(_, _) => sym("ratio")
    Flo(_) => sym("double-float")
    Cplx(_, _) => sym("complex")
    Str(_) => sym("simple-string")
    Char(_) => sym("character")
    Vec(_) => sym("simple-vector")
    Hash(_) => sym("hash-table")
    Func(_) => sym("function")
    Struct(st) =>
      if st.stype.name == "si::condition" {
        match st.slots[0] {
          Sym(_) as ty => ty
          _ => sym("condition")
        }
      } else {
        Sym(st.stype)
      }
    Stream(_) => sym("stream")
    Box(_) => sym("t")
  }
}

// ---------------------------------------------------------------------------
// Conditions

///|
/// A condition object: #S(si::condition type message payload initargs).
fn le__make_condition(
  ty : String,
  msg : String,
  payload : Value,
  initargs : Value,
) -> Value {
  make_struct("si::condition", [sym(ty), Str(msg), payload, initargs])
}

///|
fn le__condition_p(x : Value) -> Bool {
  match x {
    Struct(st) => st.stype.name == "si::condition"
    _ => false
  }
}

///|
fn le__condition_type(c : Value) -> String {
  match c {
    Struct(st) if st.stype.name == "si::condition" =>
      match st.slots[0] {
        Sym(s) => s.name
        _ => "condition"
      }
    _ => "condition"
  }
}

///|
fn le__condition_message(c : Value) -> String {
  match c {
    Struct(st) if st.stype.name == "si::condition" => lstring(st.slots[1])
    _ => ""
  }
}

///|
/// The condition object for a MoonBit error, or None for non-local exits.
fn le__condition_of_error(e : Error) -> Value? {
  match e {
    LispError::Throw(_, _) | LispError::ReturnFrom(_, _) | LispError::Go(_) =>
      None
    LispError::SimpleError(msg) =>
      Some(le__make_condition("simple-error", msg, Nil, Nil))
    LispError::Condition(s, msg, payload) =>
      if le__condition_p(payload) {
        Some(payload)
      } else {
        Some(le__make_condition(s.name, msg, payload, Nil))
      }
    _ => Some(le__make_condition("simple-error", e.to_string(), Nil, Nil))
  }
}

///|
/// The MoonBit error that signals a condition object.
fn le__error_of_condition(c : Value) -> LispError {
  let ty = le__condition_type(c)
  match c {
    Struct(st) if ty == "simple-error" && st.slots[3] is Nil && st.slots[2] is Nil =>
      LispError::SimpleError(le__condition_message(c))
    Struct(st) if ty == "maxima-$error" => LispError::Condition(intern(ty), le__condition_message(c), st.slots[2])
    _ => LispError::Condition(intern(ty), le__condition_message(c), c)
  }
}

///|
/// Does the condition match the type specifier of a handler?
fn le__condition_matches(c : Value, ty : Value) -> Bool {
  match ty {
    Sym(s) => le__subtype_name(le__condition_type(c), s.name)
    Cons({ car: Sym({ name: "or", .. }), cdr: tys }) =>
      tys.iter().any(t => le__condition_matches(c, t))
    Cons({ car: Sym({ name: "and", .. }), cdr: tys }) =>
      tys.iter().all(t => le__condition_matches(c, t))
    Cons({ car: Sym({ name: "not", .. }), cdr: tys }) =>
      !le__condition_matches(c, car(tys))
    _ => false
  }
}

///|
/// Active handlers (HANDLER-CASE and HANDLER-BIND), innermost last.
priv enum LeHandler {
  HCase(Value, Value) // types, tag
  HBind(Value, Value) // types, handler functions
}

///|
let le__handlers : Array[LeHandler] = []

///|
/// Signal a condition object: run the applicable HANDLER-BIND handlers and
/// transfer to the innermost applicable HANDLER-CASE. Returns normally if
/// no handler took a non-local exit.
fn le__signal(c : Value) -> Unit raise {
  let mut i = le__handlers.length() - 1
  while i >= 0 {
    match le__handlers[i] {
      HCase(types, tag) => {
        let mut k = 0
        for ty in types.iter() {
          if le__condition_matches(c, ty) {
            raise LispError::Throw(tag, cons(int(k), c))
          }
          k += 1
        }
      }
      HBind(types, fns) => {
        let tys = list_to_array(types)
        let fs = list_to_array(fns)
        for k, ty in tys {
          if le__condition_matches(c, ty) {
            // run the handler with the handlers below this one active
            let saved = le__handlers.copy()
            le__handlers.truncate(i)
            defer {
              le__handlers.clear()
              for h in saved {
                le__handlers.push(h)
              }
            }
            le__funcall(fs[k], [c]) |> ignore
          }
        }
      }
    }
    i -= 1
  }
}

///|
/// Build a condition object from ERROR/SIGNAL/WARN arguments.
fn le__coerce_condition(
  a : Array[Value],
  default_type : String,
) -> Value raise {
  let d = le__arg(a, 0)
  match d {
    Str(fmt) => {
      let args = a[1:].to_array()
      let msg = format_to_string(fmt, args)
      make_struct("si::condition", [
        sym(default_type),
        Str(msg),
        Nil,
        list([sym(":format-control"), d, sym(":format-arguments"), list(args)]),
      ])
    }
    Sym(s) => {
      let initargs = list(a[1:].to_array())
      let msg = match getf(initargs, sym(":format-control")) {
        Str(fmt) =>
          format_to_string(
            fmt,
            list_to_array(getf(initargs, sym(":format-arguments"))),
          )
        _ => ""
      }
      let c = make_struct("si::condition", [d, Str(msg), Nil, initargs])
      // a :report function computes the message
      let rep = le__find_report(s.name)
      match rep {
        Some(r) => {
          let text = match r {
            Str(_) => lstring(r)
            _ =>
              with_output_to_string(st => le__funcall(r, [c, st]) |> ignore)
          }
          match c {
            Struct(st) => st.slots[1] = Str(text)
            _ => ()
          }
        }
        None =>
          if msg == "" {
            match c {
              Struct(st) =>
                st.slots[1] = Str(
                  "Condition of type " + string_upcase(s.name) + " was signalled.",
                )
              _ => ()
            }
          }
      }
      c
    }
    _ =>
      if le__condition_p(d) {
        d
      } else {
        le__make_condition(default_type, prin1_to_string(d), Nil, Nil)
      }
  }
}

///|
fn le__find_report(ty : String) -> Value? {
  match le__condition_reports.get(ty) {
    Some(r) => Some(r)
    None =>
      match le__condition_parents.get(ty) {
        Some(ps) => {
          for p in ps {
            match le__find_report(p) {
              Some(r) => return Some(r)
              None => ()
            }
          }
          None
        }
        None => None
      }
  }
}

///|
fn le__handler_case_fn(a : Array[Value]) -> Value raise {
  let thunk = le__arg(a, 0)
  let types = le__arg(a, 1)
  let handlers = list_to_array(le__arg(a, 2))
  let tag = cons(Nil, Nil)
  le__handlers.push(HCase(types, tag))
  let depth = le__handlers.length()
  let r = le__funcall(thunk, []) catch {
    LispError::Throw(tg, payload) if physical_equal_value(tg, tag) => {
      le__handlers.truncate(depth - 1)
      let k = to_int(car(payload))
      return le__funcall(handlers[k], [cdr(payload)])
    }
    e => {
      le__handlers.truncate(depth - 1)
      match le__condition_of_error(e) {
        Some(c) => {
          let mut k = 0
          for ty in types.iter() {
            if le__condition_matches(c, ty) {
              return le__funcall(handlers[k], [c])
            }
            k += 1
          }
          raise e
        }
        None => raise e
      }
    }
  }
  le__handlers.truncate(depth - 1)
  r
}

///|
fn le__handler_bind_fn(a : Array[Value]) -> Value raise {
  let thunk = le__arg(a, 0)
  let types = le__arg(a, 1)
  let fns = le__arg(a, 2)
  le__handlers.push(HBind(types, fns))
  let depth = le__handlers.length()
  let r = le__funcall(thunk, []) catch {
    e => {
      le__handlers.truncate(depth - 1)
      // an error from ported code (it did not go through SIGNAL): run the
      // handlers now; they may exit non-locally
      if !(e is LispError::Throw(_, _)) {
        match le__condition_of_error(e) {
          Some(c) => {
            let tys = list_to_array(types)
            let fs = list_to_array(fns)
            for k, ty in tys {
              if le__condition_matches(c, ty) && !le__signalled(c) {
                le__funcall(fs[k], [c]) |> ignore
              }
            }
          }
          None => ()
        }
      }
      raise e
    }
  }
  le__handlers.truncate(depth - 1)
  r
}

///|
/// Conditions already offered to the handlers by SIGNAL (so HANDLER-BIND
/// does not run its handler twice).
let le__signalled_conditions : Array[Value] = []

///|
fn le__signalled(c : Value) -> Bool {
  le__signalled_conditions.iter().any(x => physical_equal_value(x, c))
}

///|
fn le__lisp_error(a : Array[Value]) -> Value raise {
  let c = le__coerce_condition(a, "simple-error")
  le__signalled_conditions.push(c)
  if le__signalled_conditions.length() > 16 {
    le__signalled_conditions.remove(0) |> ignore
  }
  le__signal(c)
  raise le__error_of_condition(c)
}

///|
let le__muffle_tag : Value = cons(sym("si::muffle-warning"), Nil)

///|
fn le__warn(a : Array[Value]) -> Value raise {
  let c = le__coerce_condition(a, "simple-warning")
  let muffled = try {
    le__signal(c)
    false
  } catch {
    LispError::Throw(tg, _) if physical_equal_value(tg, le__muffle_tag) => true
    e => raise e
  }
  if !muffled {
    let out = symval(error_output)
    fresh_line(stream=out) |> ignore
    write_string("WARNING: " + le__condition_message(c) + "\n", stream=out)
  }
  Nil
}

///|
fn le__register_conditions() -> Unit {
  le__def("error", a => le__lisp_error(a))
  le__def("cerror", a => le__lisp_error(a[1:].to_array()))
  le__def("warn", a => le__warn(a))
  le__def("signal", a => {
    let c = le__coerce_condition(a, "simple-condition")
    le__signal(c)
    Nil
  })
  le__def("muffle-warning", _ => raise LispError::Throw(le__muffle_tag, Nil))
  le__def("make-condition", a => le__coerce_condition(a, "simple-condition"))
  le__def("si::handler-case-fn", a => le__handler_case_fn(a))
  le__def("si::handler-bind-fn", a => le__handler_bind_fn(a))
  le__def("simple-condition-format-control", a => match le__arg(a, 0) {
    Struct(st) => getf(st.slots[3], sym(":format-control"))
    _ => Nil
  })
  le__def("simple-condition-format-arguments", a => match le__arg(a, 0) {
    Struct(st) => getf(st.slots[3], sym(":format-arguments"))
    _ => Nil
  })
  le__def("type-error-datum", a => match le__arg(a, 0) {
    Struct(st) => st.slots[2]
    _ => Nil
  })
  le__def("cell-error-name", a => match le__arg(a, 0) {
    Struct(st) => st.slots[2]
    _ => Nil
  })
  le__def("invoke-debugger", a => raise le__error_of_condition(le__arg(a, 0)))
  le__def("si::define-condition", a => {
    let name = le__type_name(le__arg(a, 0))
    let parents = list_to_array(le__arg(a, 1)).map(p => le__type_name(p))
    le__condition_parents[name] = if parents.length() == 0 {
      ["condition"]
    } else {
      parents
    }
    let slots = []
    for sl in le__arg(a, 2).iter() {
      let sname = car(sl)
      let initarg = cadr(sl)
      slots.push((sname, initarg))
      for reader in caddr(sl).iter() {
        let ia = initarg
        defun(reader, args => match le__arg(args, 0) {
          Struct(st) => getf(st.slots[3], ia)
          _ => Nil
        })
      }
    }
    le__condition_slots[name] = slots
    match le__arg(a, 3) {
      Nil => ()
      r => le__condition_reports[name] = r
    }
    le__arg(a, 0)
  })
  struct_print_functions["si::condition"] = lfunc("print-condition", a => {
    write_string(le__condition_message(le__arg(a, 0)), stream=le__arg(a, 1))
    Nil
  })
}

// ---------------------------------------------------------------------------
// Structures

///|
let le__struct_parents : Map[String, String] = Map::new()

///|
/// Slots (name, default form) of DEFSTRUCT types, by name.
let le__struct_slots : Map[String, Array[(Value, Value)]] = Map::new()

///|
fn le__struct_option(opts : Value, name : String) -> Value? {
  for o in opts.iter() {
    match o {
      Sym(s) if s.name == name => return Some(Nil)
      Cons({ car: Sym(s), cdr: rest }) if s.name == name => return Some(rest)
      _ => ()
    }
  }
  None
}

///|
fn le__m_defstruct(form : Value, _env : LeEnv) -> Value raise {
  let spec = cadr(form)
  let (name, opts) = match spec {
    Cons({ car: n, cdr: o }) => (n, o)
    _ => (spec, Nil)
  }
  let sname = le__type_name(name)
  let mut body = cddr(form)
  if body is Cons({ car: Str(_), cdr: rest }) {
    body = rest
  }
  let conc = match le__struct_option(opts, ":conc-name") {
    Some(Nil) => ""
    Some(Cons({ car: Nil, .. })) => ""
    Some(Cons({ car: c, .. })) => le__str(c)
    _ => sname + "-"
  }
  // :type list/vector
  let rep_type = match le__struct_option(opts, ":type") {
    Some(Cons({ car: Sym(s), .. })) => s.name
    _ => ""
  }
  let named = le__struct_option(opts, ":named") is Some(_)
  let parent = match le__struct_option(opts, ":include") {
    Some(Cons({ car: p, .. })) => Some(le__type_name(p))
    _ => None
  }
  let slots : Array[(Value, Value)] = []
  match parent {
    Some(p) =>
      match le__struct_slots.get(p) {
        Some(ps) =>
          for x in ps {
            slots.push(x)
          }
        None => le__error("defstruct: unknown included structure " + p) |> ignore
      }
    None => ()
  }
  for sl in body.iter() {
    match sl {
      Cons({ car: n, cdr: rest }) => slots.push((n, car(rest)))
      _ => slots.push((sl, Nil))
    }
  }
  le__struct_slots[sname] = slots
  match parent {
    Some(p) => le__struct_parents[sname] = p
    None => ()
  }
  let offset = if rep_type != "" && named { 1 } else { 0 }
  let forms = Collector::new()
  forms.add(sym("progn"))
  forms.add(
    list([
      sym("si::defstruct-register"),
      le__quote(name),
      le__quote(list(slots.map(s => cons(s.0, s.1)))),
      match parent {
        Some(p) => le__quote(sym(p))
        None => Nil
      },
    ]),
  )
  // constructor(s)
  let ctor_specs = []
  for o in opts.iter() {
    match o {
      Cons({ car: Sym({ name: ":constructor", .. }), cdr: rest }) =>
        ctor_specs.push(rest)
      _ => ()
    }
  }
  if ctor_specs.length() == 0 {
    ctor_specs.push(Nil)
  }
  let build = (vals : Value) => {
    match rep_type {
      "list" => cons(sym("list"), if named { cons(le__quote(name), vals) } else { vals })
      "vector" => cons(sym("vector"), if named { cons(le__quote(name), vals) } else { vals })
      _ => list3(sym("si::make-struct"), le__quote(name), cons(sym("list"), vals))
    }
  }
  for cs in ctor_specs {
    match cs {
      Cons({ car: Nil, .. }) => ()
      Cons({ car: cname, cdr: Cons({ car: boa, .. }) }) => {
        // BOA constructor
        let vars = []
        le__loop_pattern_vars(boa, vars)
        let ll = Collector::new()
        let mut mode = ""
        for x in boa.iter() {
          if le__is_amp(x) {
            mode = le__type_name(x)
            ll.add(x)
          } else {
            match x {
              Sym(_) if mode == "&optional" || mode == "&key" => {
                let d = slots.iter().find_first(s => eq(s.0, x))
                ll.add(list2(x, match d {
                  Some(s) => s.1
                  None => Nil
                }))
              }
              _ => ll.add(x)
            }
          }
        }
        let vals = list(slots.map(s => if vars.iter().any(v => eq(v, s.0)) {
          s.0
        } else {
          s.1
        }))
        forms.add(list4(sym("defun"), cname, ll.result(), build(vals)))
      }
      _ => {
        let cname = match cs {
          Cons({ car: c, .. }) => c
          _ => sym("make-" + sname)
        }
        let ll = cons(sym("&key"), list(slots.map(s => list2(s.0, s.1))))
        forms.add(list4(sym("defun"), cname, ll, build(list(slots.map(s => s.0)))))
      }
    }
  }
  // predicate, copier
  if rep_type == "" {
    match le__struct_option(opts, ":predicate") {
      Some(Cons({ car: Nil, .. })) => ()
      other => {
        let pname = match other {
          Some(Cons({ car: p, .. })) => p
          _ => sym(sname + "-p")
        }
        forms.add(
          list4(
            sym("defun"),
            pname,
            list1(sym("si::x")),
            list3(sym("typep"), sym("si::x"), le__quote(name)),
          ),
        )
      }
    }
    match le__struct_option(opts, ":copier") {
      Some(Cons({ car: Nil, .. })) => ()
      other => {
        let cname = match other {
          Some(Cons({ car: p, .. })) => p
          _ => sym("copy-" + sname)
        }
        forms.add(
          list4(
            sym("defun"),
            cname,
            list1(sym("si::x")),
            list2(sym("si::copy-struct"), sym("si::x")),
          ),
        )
      }
    }
  }
  // accessors
  for i, s in slots {
    let aname = conc + le__type_name(s.0)
    let acc = sym(aname)
    let idx = i + offset
    let getter = match rep_type {
      "list" => list3(sym("nth"), Fix(idx.to_int64()), sym("si::x"))
      "vector" => list3(sym("aref"), sym("si::x"), Fix(idx.to_int64()))
      _ => list3(sym("si::struct-ref"), sym("si::x"), Fix(idx.to_int64()))
    }
    forms.add(list4(sym("defun"), acc, list1(sym("si::x")), getter))
    match rep_type {
      "list" => le__defsetf_short.remove(aname)
      _ => ()
    }
    if rep_type == "" {
      le__struct_accessors[aname] = idx
    } else {
      // (setf (acc x) v) through the list/vector element
      le__defsetf_long[aname] = lfunc("defstruct-setf", args => {
        let x = car(le__arg(args, 0))
        let v = le__arg(args, 1)
        if rep_type == "list" {
          list3(
            sym("si::setcar"),
            list3(sym("nthcdr"), Fix(idx.to_int64()), x),
            v,
          )
        } else {
          list4(sym("si::setaref"), x, Fix(idx.to_int64()), v)
        }
      })
    }
  }
  // printing
  match le__struct_option(opts, ":print-function") {
    Some(Cons({ car: f, .. })) =>
      forms.add(
        list3(
          sym("si::set-struct-printer"),
          le__quote(name),
          le__struct_fn_form(f),
        ),
      )
    _ => ()
  }
  match le__struct_option(opts, ":print-object") {
    Some(Cons({ car: f, .. })) =>
      forms.add(
        list4(
          sym("si::set-struct-printer"),
          le__quote(name),
          le__struct_fn_form(f),
          t,
        ),
      )
    _ => ()
  }
  forms.add(le__quote(name))
  forms.result()
}

///|
fn le__struct_fn_form(f : Value) -> Value {
  match f {
    Sym(_) => list2(sym("function"), f)
    Cons({ car: Sym({ name: "lambda", .. }), .. }) => list2(sym("function"), f)
    _ => f
  }
}

///|
fn le__register_structs() -> Unit {
  le__def("si::defstruct-register", a => {
    let name = le__type_name(le__arg(a, 0))
    let slots = list_to_array(le__arg(a, 1)).map(p => (car(p), cdr(p)))
    le__struct_slots[name] = slots
    match le__arg(a, 2) {
      Nil => ()
      p => le__struct_parents[name] = le__type_name(p)
    }
    le__arg(a, 0)
  })
  le__def("si::make-struct", a => make_struct(
    le__type_name(le__arg(a, 0)),
    list_to_array(le__arg(a, 1)),
  ))
  le__def("si::struct-ref", a => struct_ref(le__arg(a, 0), le__int(le__arg(a, 1))))
  le__def("si::setslot", a => struct_set(
    le__arg(a, 0),
    le__int(le__arg(a, 1)),
    le__arg(a, 2),
  ))
  le__def("si::copy-struct", a => match le__arg(a, 0) {
    Struct(st) => Struct({ stype: st.stype, slots: st.slots.copy() })
    x => x
  })
  le__def("copy-structure", a => funcall(sym("si::copy-struct"), a))
  le__def("si::set-struct-printer", a => {
    let name = le__type_name(le__arg(a, 0))
    let f = le__arg(a, 1)
    let obj_style = le__arg(a, 2).truthy()
    struct_print_functions[name] = if obj_style {
      lfunc("print-object", args => le__funcall(f, [le__arg(args, 0), le__arg(args, 1)]))
    } else {
      f
    }
    Nil
  })
}

// ---------------------------------------------------------------------------
// Arrays

///|
fn le__dims_of(v : Value) -> Array[Int] raise {
  match v {
    Nil => []
    Cons(_) => list_to_array(v).map(x => to_int(x))
    _ => [to_int(v)]
  }
}

///|
fn le__elt_type_name(ty : Value) -> String {
  match ty {
    Sym(s) =>
      match s.name {
        "character" | "base-char" | "standard-char" => "character"
        "fixnum" => "fixnum"
        "bit" => "bit"
        "double-float" | "flonum" | "float" | "single-float" => "double-float"
        _ => "t"
      }
    Cons({ car: Sym({ name: "unsigned-byte" | "signed-byte" | "integer" | "mod", .. }), .. }) =>
      "fixnum"
    _ => "t"
  }
}

///|
fn le__register_arrays() -> Unit {
  le__def("make-array", a => {
    let dims = le__dims_of(le__arg(a, 0))
    let elt = le__elt_type_name(le__kwarg_or(a, 1, ":element-type", t))
    let fill = match le__kwarg(a, 1, ":fill-pointer") {
      Some(Nil) | None => None
      Some(Fix(n)) => Some(n.to_int())
      Some(_) => Some(if dims.length() > 0 { dims[0] } else { 0 })
    }
    let init = le__kwarg_or(a, 1, ":initial-element", Nil)
    let arr = make_array(dims, initial=init, elt~, fill?)
    match le__kwarg(a, 1, ":initial-contents") {
      Some(contents) =>
        match arr {
          Vec(v) => {
            let data : Array[Value] = []
            fn flat(x : Value, k : Int) -> Unit raise {
              if k == dims.length() {
                data.push(x)
              } else {
                for e in le__seq_elems(x) {
                  flat(e, k + 1)
                }
              }
            }

            flat(contents, 0)
            for i, x in data {
              if i < v.data.length() {
                v.data[i] = x
              }
            }
          }
          _ => ()
        }
      None => ()
    }
    arr
  })
  le__def("aref", a => {
    let x = le__arg(a, 0)
    match x {
      Str(s) => Char(char_at(s, le__int(le__arg(a, 1))))
      _ => aref(x, a[1:].to_array().map(i => to_int(i) catch { _ => 0 }))
    }
  })
  le__def("svref", a => aref1(le__arg(a, 0), le__int(le__arg(a, 1))))
  le__def("row-major-aref", a => match le__arg(a, 0) {
    Vec(v) => v.data[le__int(le__arg(a, 1))]
    _ => Nil
  })
  le__def("si::setaref", a => {
    let x = le__arg(a, 0)
    let v = a[a.length() - 1]
    let idx = a[1:a.length() - 1].to_array().map(i => to_int(i) catch { _ => 0 })
    aset(x, idx, v) |> ignore
    v
  })
  le__def("array-dimensions", a => array_dimensions(le__arg(a, 0)))
  le__def("array-dimension", a => int(
    array_dimension(le__arg(a, 0), le__int(le__arg(a, 1))),
  ))
  le__def("array-rank", a => int(array_rank(le__arg(a, 0))))
  le__def("array-total-size", a => int(array_total_size(le__arg(a, 0))))
  le__def("array-element-type", a => match le__arg(a, 0) {
    Vec(v) => sym(v.elt)
    Str(_) => sym("character")
    _ => t
  })
  le__def("adjustable-array-p", a => le__bool(vectorp(le__arg(a, 0))))
  le__def("array-has-fill-pointer-p", a => match le__arg(a, 0) {
    Vec({ fill: Some(_), .. }) => t
    _ => Nil
  })
  le__def("fill-pointer", a => int(fill_pointer(le__arg(a, 0))))
  le__def("si::setfillptr", a => {
    set_fill_pointer(le__arg(a, 0), le__int(le__arg(a, 1)))
    le__arg(a, 1)
  })
  le__def("vector-push", a => {
    match le__arg(a, 1) {
      Vec({ fill: Some(f), data, .. } as v) =>
        if f < data.length() {
          data[f] = le__arg(a, 0)
          v.fill = Some(f + 1)
          int(f)
        } else {
          Nil
        }
      _ => Nil
    }
  })
  le__def("vector-push-extend", a => int(
    vector_push_extend(le__arg(a, 1), le__arg(a, 0)),
  ))
  le__def("vector-pop", a => vector_pop(le__arg(a, 0)))
  le__def("adjust-array", a => {
    let x = le__arg(a, 0)
    let r = adjust_array(
      x,
      le__dims_of(le__arg(a, 1)),
      initial=le__kwarg_or(a, 2, ":initial-element", Nil),
    )
    match (r, le__kwarg(a, 2, ":fill-pointer")) {
      (Vec(v), Some(Fix(n))) => v.fill = Some(n.to_int())
      _ => ()
    }
    r
  })
  le__def("vectorp", a => le__bool(vectorp(le__arg(a, 0)) || stringp(le__arg(a, 0))))
  le__def("simple-vector-p", a => le__bool(vectorp(le__arg(a, 0))))
  le__def("arrayp", a => le__bool(arrayp(le__arg(a, 0)) || stringp(le__arg(a, 0))))
  le__def("vector", a => vector(a))
  le__def("si::string-append-fill", a => {
    let target = le__arg(a, 0)
    for c in string_chars(le__str(le__arg(a, 1))) {
      vector_push_extend(target, Char(c)) |> ignore
    }
    Nil
  })
  le__def("si::sequence-list", a => list(le__seq_elems(le__arg(a, 0))))
}

// ---------------------------------------------------------------------------
// Symbols and packages

///|
fn le__register_symbols() -> Unit {
  le__def("si::setget", a => {
    // (si::setget sym ind [default] value)
    let v = a[a.length() - 1]
    putprop(le__arg(a, 0), v, le__arg(a, 1)) |> ignore
    v
  })
  le__def("si::setsymfn", a => {
    let v = le__arg(a, 1)
    match (le__arg(a, 0), v) {
      (Sym(s), Func(lf)) => s.func = Some(lf)
      (Sym(s), Nil) => s.func = None
      (n, _) => le__install_function(n, v)
    }
    v
  })
  le__def("si::setplist", a => set_symbol_plist(le__arg(a, 0), le__arg(a, 1)))
  le__def("si::setmget", a => {
    mputprop(le__arg(a, 0), le__arg(a, 2), le__arg(a, 1)) |> ignore
    le__arg(a, 2)
  })
  le__def("si::setmacfn", a => {
    putprop(le__arg(a, 0), le__arg(a, 1), le__q_macro_function) |> ignore
    le__arg(a, 1)
  })
  le__def("si::proclaim-special", a => {
    le__proclaim_special(le__arg(a, 0))
    le__arg(a, 0)
  })
  le__def("proclaim", a => {
    le__proclaim(le__arg(a, 0))
    Nil
  })
  le__def("si::defsetf-short", a => {
    le__defsetf_short[le__type_name(le__arg(a, 0))] = le__arg(a, 1)
    le__arg(a, 0)
  })
  le__def("si::defsetf-long", a => {
    le__defsetf_long[le__type_name(le__arg(a, 0))] = le__arg(a, 1)
    le__arg(a, 0)
  })
  le__def("si::in-package", a => {
    let p = string_downcase(le__str(le__arg(a, 0)))
    @lisp.reader_package.val = if p == "cl-user" || p == "common-lisp-user" || p == "user" {
      "maxima"
    } else {
      p
    }
    Str(string_upcase(@lisp.reader_package.val))
  })
  le__def("find-package", a => {
    match le__arg(a, 0) {
      Nil => Nil
      x => Str(string_upcase(le__str(x)))
    }
  })
  le__def("make-package", a => Str(string_upcase(le__str(le__arg(a, 0)))))
  le__def("package-name", a => le__arg(a, 0))
  le__def("symbol-package", a => {
    match le__arg(a, 0) {
      Sym(s) =>
        if s.name.has_prefix(":") {
          Str("KEYWORD")
        } else if s.interned {
          Str("MAXIMA")
        } else {
          Nil
        }
      Nil => Str("COMMON-LISP")
      _ => Nil
    }
  })
  for name in ["use-package", "export", "import", "shadow", "shadowing-import", "unexport", "unuse-package"] {
    le__def(name, _ => t)
  }
  le__def("intern", a => {
    let name = le__str(le__arg(a, 0))
    let pname = match le__arg(a, 1) {
      Nil => ""
      p => string_downcase(le__str(p))
    }
    let full = if pname == "keyword" { ":" + name } else { name }
    let existed = find_symbol(full) is Sym(_)
    let s = sym(full)
    le__values([s, if existed { sym(":internal") } else { Nil }])
  })
  le__def("find-symbol", a => {
    let name = le__str(le__arg(a, 0))
    match find_symbol(name) {
      Sym(_) as s => le__values([s, sym(":internal")])
      _ => if name == "nil" { le__values([Nil, sym(":internal")]) } else { le__values([Nil, Nil]) }
    }
  })
  le__def("unintern", _ => t)
  le__def("make-symbol", a => make_symbol(le__str(le__arg(a, 0))))
  le__def("gensym", a => {
    match le__arg(a, 0) {
      Str(p) => gensym(prefix=p)
      _ => gensym()
    }
  })
  le__def("gentemp", a => {
    let prefix = match le__arg(a, 0) {
      Str(p) => p
      _ => "t"
    }
    let mut i = 1
    while find_symbol(prefix + i.to_string()) is Sym(_) {
      i += 1
    }
    sym(prefix + i.to_string())
  })
  le__def("copy-symbol", a => make_symbol(le__str(le__arg(a, 0))))
  le__def("keywordp", a => le__bool(keywordp(le__arg(a, 0))))
  le__def("symbolp", a => le__bool(symbolp(le__arg(a, 0))))
  le__def("fmakunbound", a => fmakunbound(le__arg(a, 0)))
  le__def("si::all-symbols", _ => list(all_symbols().map(s => Sym(s))))
  le__def("symbol-function", a => {
    let x = le__arg(a, 0)
    match x {
      Sym({ func: Some(lf), .. }) => Func(lf)
      _ => le__undefined_function(x)
    }
  })
  le__def("fdefinition", a => funcall(sym("symbol-function"), a))
  le__def("symbol-value", a => {
    let x = le__arg(a, 0)
    if boundp(x) {
      symval(x)
    } else {
      le__unbound(x)
    }
  })
}

// ---------------------------------------------------------------------------
// Streams and files

///|
/// Output file streams opened by OPEN: written to disk on CLOSE.
let le__open_files : Array[(LStream, String, StringBuilder, String)] = []

///|
fn le__stream_arg(a : Array[Value], i : Int) -> Value {
  if i < a.length() {
    a[i]
  } else {
    Nil
  }
}

///|
fn le__in_stream(v : Value) -> Value {
  match v {
    Nil => symval(standard_input)
    Sym(_) => symval(standard_input)
    _ => v
  }
}

///|
fn le__open(a : Array[Value]) -> Value raise {
  let path = le__str(le__arg(a, 0))
  let dir = le__kwarg_or(a, 1, ":direction", sym(":input"))
  match dir {
    Sym({ name: ":output" | ":io", .. }) => {
      let if_exists = le__kwarg_or(a, 1, ":if-exists", Nil)
      let prefix = if if_exists is Sym({ name: ":append", .. }) && probe_file(path) {
        read_file(path)
      } else {
        ""
      }
      if if_exists is Sym({ name: ":error", .. }) && probe_file(path) {
        raise LispError::Condition(
          intern("file-error"),
          "file " + path + " already exists",
          Str(path),
        )
      }
      let buf = StringBuilder::new()
      buf.write_string(prefix)
      let st : LStream = {
        input: "",
        pos: 0,
        unread: [],
        out: None,
        name: path,
        sink: Some(s => buf.write_string(s)),
        column: 0,
        line: 1,
        is_input: false,
        eof: false,
      }
      write_file(path, prefix)
      le__open_files.push((st, path, buf, "open"))
      Stream(st)
    }
    Sym({ name: ":probe", .. }) => if probe_file(path) { Str(path) } else { Nil }
    _ =>
      if probe_file(path) {
        open_input_file(path)
      } else {
        match le__kwarg_or(a, 1, ":if-does-not-exist", sym(":error")) {
          Nil => Nil
          _ =>
            raise LispError::Condition(
              intern("file-error"),
              "The file " + path + " does not exist.",
              Str(path),
            )
        }
      }
  }
}

///|
fn le__close(s : Value) -> Value raise {
  match s {
    Stream(st) => {
      for i, f in le__open_files {
        if physical_equal(f.0, st) {
          write_file(f.1, f.2.to_string())
          le__open_files.remove(i) |> ignore
          return t
        }
      }
      st.eof = true
      t
    }
    _ => Nil
  }
}

///|
fn le__path_parts(p : String) -> (String, String, String) {
  // (directory with trailing /, name, type)
  let (dir, base) = match p.rev_find("/") {
    Some(i) => (p.substring(end=i + 1), p.substring(start=i + 1))
    None => ("", p)
  }
  match base.rev_find(".") {
    Some(i) if i > 0 => (dir, base.substring(end=i), base.substring(start=i + 1))
    _ => (dir, base, "")
  }
}

///|
fn le__register_streams() -> Unit {
  le__def("print", a => print(le__arg(a, 0), stream=le__stream_arg(a, 1)))
  le__def("prin1", a => prin1(le__arg(a, 0), stream=le__stream_arg(a, 1)))
  le__def("princ", a => princ(le__arg(a, 0), stream=le__stream_arg(a, 1)))
  le__def("pprint", a => {
    write_string("\n" + prin1_to_string(le__arg(a, 0)), stream=le__stream_arg(a, 1))
    le__values([])
  })
  le__def("write", a => {
    let st = le__kwarg_or(a, 1, ":stream", Nil)
    let esc = match le__kwarg(a, 1, ":escape") {
      Some(v) => v.truthy()
      None => true
    }
    if esc {
      prin1(le__arg(a, 0), stream=st)
    } else {
      princ(le__arg(a, 0), stream=st)
    }
  })
  le__def("terpri", a => {
    terpri(stream=le__stream_arg(a, 0))
    Nil
  })
  le__def("fresh-line", a => le__bool(fresh_line(stream=le__stream_arg(a, 0))))
  le__def("write-string", a => {
    let s = le__str(le__arg(a, 0))
    let cs = string_chars(s)
    let (st, en) = le__start_end(a, 2, cs.length())
    write_string(chars_to_string(cs[st:en].to_array()), stream=le__stream_arg(a, 1))
    le__arg(a, 0)
  })
  le__def("write-line", a => {
    write_string(le__str(le__arg(a, 0)) + "\n", stream=le__stream_arg(a, 1))
    le__arg(a, 0)
  })
  le__def("write-char", a => {
    write_char(le__char(le__arg(a, 0)), stream=le__stream_arg(a, 1))
    le__arg(a, 0)
  })
  le__def("finish-output", a => {
    finish_output(stream=le__stream_arg(a, 0))
    Nil
  })
  le__def("force-output", a => {
    finish_output(stream=le__stream_arg(a, 0))
    Nil
  })
  le__def("clear-output", _ => Nil)
  le__def("clear-input", _ => Nil)
  le__def("read-char", a => {
    let st = le__in_stream(le__arg(a, 0))
    let eof_error = if a.length() > 1 { a[1].truthy() } else { true }
    let eofv = cons(Nil, Nil)
    let c = read_char(stream=st, eof_value=eofv)
    if physical_equal_value(c, eofv) {
      if eof_error {
        raise LispError::Condition(intern("end-of-file"), "end of file", st)
      }
      le__arg(a, 2)
    } else {
      c
    }
  })
  le__def("read-char-no-hang", a => funcall(sym("read-char"), a))
  le__def("peek-char", a => {
    // (peek-char peek-type stream eof-error-p eof-value)
    let st = le__in_stream(le__arg(a, 1))
    let eof_error = if a.length() > 2 { a[2].truthy() } else { true }
    let eofv = cons(Nil, Nil)
    if le__arg(a, 0).truthy() {
      // skip whitespace
      while true {
        let c = peek_char(stream=st, eof_value=eofv)
        match c {
          Char(ch) if is_space_char(ch) => read_char(stream=st) |> ignore
          _ => break
        }
      }
    }
    let c = peek_char(stream=st, eof_value=eofv)
    if physical_equal_value(c, eofv) {
      if eof_error {
        raise LispError::Condition(intern("end-of-file"), "end of file", st)
      }
      le__arg(a, 3)
    } else {
      c
    }
  })
  le__def("unread-char", a => {
    unread_char(le__char(le__arg(a, 0)), stream=le__in_stream(le__arg(a, 1)))
    Nil
  })
  le__def("read-line", a => {
    let st = le__in_stream(le__arg(a, 0))
    let eof_error = if a.length() > 1 { a[1].truthy() } else { true }
    match read_line(stream=st) {
      Some(l) => le__values([Str(l), Nil])
      None =>
        if eof_error {
          raise LispError::Condition(intern("end-of-file"), "end of file", st)
        } else {
          le__values([le__arg(a, 2), t])
        }
    }
  })
  le__def("read", a => {
    let st = le__in_stream(le__arg(a, 0))
    let eof_error = if a.length() > 1 { a[1].truthy() } else { true }
    le__init_reader_hooks()
    @lisp.lread_stream(st, eof_error~, eof_value=le__arg(a, 2))
  })
  le__def("read-preserving-whitespace", a => funcall(sym("read"), a))
  le__def("read-from-string", a => {
    let s = le__str(le__arg(a, 0))
    let eof_error = if a.length() > 1 { a[1].truthy() } else { true }
    let start = to_int(le__kwarg_or(a, 3, ":start", Fix(0L)))
    le__init_reader_hooks()
    let (v, pos) = @lisp.lread_from_string(s, start~, eof_error~, eof_value=le__arg(a, 2))
    le__values([v, int(pos)])
  })
  le__def("make-string-output-stream", _ => make_string_output_stream())
  le__def("get-output-stream-string", a => Str(
    get_output_stream_string(le__arg(a, 0)),
  ))
  le__def("make-string-input-stream", a => {
    let s = le__str(le__arg(a, 0))
    let cs = string_chars(s)
    let st = if a.length() > 1 { le__int(a[1]) } else { 0 }
    let en = if a.length() > 2 && a[2].truthy() { le__int(a[2]) } else { cs.length() }
    make_string_input_stream(chars_to_string(cs[st:en].to_array()))
  })
  le__def("streamp", a => le__bool(streamp(le__arg(a, 0))))
  le__def("input-stream-p", a => match le__arg(a, 0) {
    Stream(st) => le__bool(st.is_input)
    _ => Nil
  })
  le__def("output-stream-p", a => match le__arg(a, 0) {
    Stream(st) => le__bool(!st.is_input)
    _ => Nil
  })
  le__def("open-stream-p", a => match le__arg(a, 0) {
    Stream(st) => le__bool(!st.eof)
    _ => Nil
  })
  le__def("interactive-stream-p", _ => Nil)
  le__def("open", a => le__open(a))
  le__def("close", a => le__close(le__arg(a, 0)))
  le__def("file-length", a => match le__arg(a, 0) {
    Stream(st) => int(string_length(st.input))
    _ => Nil
  })
  le__def("file-position", a => match le__arg(a, 0) {
    Stream(st) => int(st.pos)
    _ => Nil
  })
  le__def("princ-to-string", a => Str(princ_to_string(le__arg(a, 0))))
  le__def("prin1-to-string", a => Str(prin1_to_string(le__arg(a, 0))))
  le__def("write-to-string", a => {
    let esc = match le__kwarg(a, 1, ":escape") {
      Some(v) => v.truthy()
      None => true
    }
    Str(if esc { prin1_to_string(le__arg(a, 0)) } else { princ_to_string(le__arg(a, 0)) })
  })
  le__def("format", a => {
    let dest = le__arg(a, 0)
    let ctl = le__arg(a, 1)
    match ctl {
      Func(_) => {
        le__funcall(ctl, [if dest is Nil { make_string_output_stream() } else { dest }] + a[2:].to_array())
        |> ignore
        Nil
      }
      _ => format(dest, le__str(ctl), a[2:].to_array())
    }
  })
  le__def("probe-file", a => {
    let p = le__str(le__arg(a, 0))
    if probe_file(p) {
      Str(p)
    } else {
      Nil
    }
  })
  le__def("truename", a => Str(suprv1__truename(le__str(le__arg(a, 0)))))
  le__def("pathname", a => Str(le__str(le__arg(a, 0))))
  le__def("pathnamep", a => le__bool(stringp(le__arg(a, 0))))
  le__def("namestring", a => Str(le__str(le__arg(a, 0))))
  le__def("file-namestring", a => {
    let (_, n, ty) = le__path_parts(le__str(le__arg(a, 0)))
    Str(if ty == "" { n } else { n + "." + ty })
  })
  le__def("directory-namestring", a => Str(le__path_parts(le__str(le__arg(a, 0))).0))
  le__def("pathname-name", a => Str(le__path_parts(le__str(le__arg(a, 0))).1))
  le__def("pathname-type", a => {
    let ty = le__path_parts(le__str(le__arg(a, 0))).2
    if ty == "" {
      Nil
    } else {
      Str(ty)
    }
  })
  le__def("pathname-directory", a => {
    let d = le__path_parts(le__str(le__arg(a, 0))).0
    if d == "" {
      return Nil
    }
    let parts = d.split("/").to_array().map(x => x.to_string()).filter(x => x != "")
    cons(
      sym(if d.has_prefix("/") { ":absolute" } else { ":relative" }),
      list(parts.map(p => Str(p))),
    )
  })
  le__def("make-pathname", a => {
    let defaults = match le__kwarg(a, 0, ":defaults") {
      Some(Nil) | None => ("", "", "")
      Some(d) => le__path_parts(le__str(d))
    }
    let dir = match le__kwarg(a, 0, ":directory") {
      Some(Cons({ car: kind, cdr: parts })) => {
        let sb = StringBuilder::new()
        if kind is Sym({ name: ":absolute", .. }) {
          sb.write_string("/")
        }
        for p in parts.iter() {
          sb.write_string(lstring(p))
          sb.write_string("/")
        }
        sb.to_string()
      }
      Some(Str(s)) => if s.has_suffix("/") { s } else { s + "/" }
      _ => defaults.0
    }
    let name = match le__kwarg(a, 0, ":name") {
      Some(Nil) | None => defaults.1
      Some(n) => lstring(n)
    }
    let ty = match le__kwarg(a, 0, ":type") {
      Some(Nil) | None => defaults.2
      Some(n) => lstring(n)
    }
    Str(dir + name + (if ty == "" { "" } else { "." + ty }))
  })
  le__def("merge-pathnames", a => {
    let p = le__str(le__arg(a, 0))
    let d = match le__arg(a, 1) {
      Nil => ""
      x => le__str(x)
    }
    let (pd, pn, pt) = le__path_parts(p)
    let (dd, dn, dt) = le__path_parts(d)
    let dir = if pd.has_prefix("/") { pd } else { dd + pd }
    let name = if pn == "" { dn } else { pn }
    let ty = if pt == "" { dt } else { pt }
    Str(dir + name + (if ty == "" { "" } else { "." + ty }))
  })
  le__def("user-homedir-pathname", _ => match getenv("HOME") {
    Some(h) => Str(if h.has_suffix("/") { h } else { h + "/" })
    None => Str("/")
  })
  le__def("ensure-directories-exist", a => le__arg(a, 0))
  le__def("directory", a => {
    let p = le__str(le__arg(a, 0))
    let (d, _, _) = le__path_parts(p)
    let dir = if d == "" { "." } else { d }
    list(list_directory(dir).map(f => Str(d + f)))
  })
  le__def("file-write-date", a => if probe_file(le__str(le__arg(a, 0))) {
    Fix(0L)
  } else {
    Nil
  })
}

// ---------------------------------------------------------------------------
// Evaluation and miscellany

///|
fn le__register_eval() -> Unit {
  le__def("eval", a => le__eval_toplevel(le__arg(a, 0)))
  le__def("funcall", a => le__funcall(le__arg(a, 0), a[1:].to_array()))
  le__def("apply", a => {
    if a.length() == 0 {
      return le__error("apply: too few arguments")
    }
    let spread = list_to_array(a[a.length() - 1])
    let lead = if a.length() > 2 { a[1:a.length() - 1].to_array() } else { [] }
    le__funcall(le__arg(a, 0), lead + spread)
  })
  le__def("values", a => le__values(a))
  le__def("values-list", a => le__values(list_to_array(le__arg(a, 0))))
  le__def("identity", a => le__arg(a, 0))
  le__def("constantly", a => {
    let v = le__arg(a, 0)
    lfunc("constantly", _ => v)
  })
  le__def("complement", a => {
    let f = le__arg(a, 0)
    lfunc("complement", args => le__bool(!le__funcall(f, args).truthy()))
  })
  le__def("not", a => le__bool(le__arg(a, 0) is Nil))
  le__def("null", a => le__bool(le__arg(a, 0) is Nil))
  le__def("macroexpand-1", a => {
    let (f, ex) = le__macroexpand_1(le__arg(a, 0), le__cur_env.val)
    le__values([f, le__bool(ex)])
  })
  le__def("macroexpand", a => {
    let (f, ex) = le__macroexpand(le__arg(a, 0), le__cur_env.val)
    le__values([f, le__bool(ex)])
  })
  le__def("macro-function", a => match le__arg(a, 0) {
    Sym(s) =>
      match le__global_macro(s) {
        Some(m) => m
        None =>
          match le__builtin_macros().get(s.name) {
            Some(exp) => lfunc(s.name, args => exp(le__arg(args, 0), Top))
            None => Nil
          }
      }
    _ => Nil
  })
  le__def("special-operator-p", a => match le__arg(a, 0) {
    Sym(s) => le__bool(le__special_forms().contains(s.name))
    _ => Nil
  })
  le__def("constantp", a => match le__arg(a, 0) {
    Sym(s) => le__bool(s.constant || s.name == "t" || s.name.has_prefix(":"))
    Cons({ car: Sym({ name: "quote", .. }), .. }) => t
    Cons(_) => Nil
    _ => t
  })
  le__def("compile", a => {
    // the evaluator compiles on definition: return the function
    match (le__arg(a, 0), le__arg(a, 1)) {
      (Nil, def) =>
        match def {
          Cons(_) => le__closure_of_lambda(def, Top, None)
          _ => def
        }
      (name, Nil) => name
      (name, def) => {
        let fv = match def {
          Cons(_) => le__closure_of_lambda(def, Top, None)
          _ => def
        }
        le__install_function(name, fv)
        name
      }
    }
  })
  le__def("function-lambda-expression", _ => le__values([Nil, t, Nil]))
  le__def("compiled-function-p", a => le__bool(functionp(le__arg(a, 0))))
  le__def("typep", a => le__bool(le__typep(le__arg(a, 0), le__arg(a, 1))))
  le__def("type-of", a => le__type_of(le__arg(a, 0)))
  le__def("subtypep", a => {
    let t1 = le__type_name(le__arg(a, 0))
    let t2 = le__type_name(le__arg(a, 1))
    le__values([le__bool(le__subtype_name(t1, t2)), t])
  })
  le__def("documentation", _ => Nil)
  le__def("require", _ => t)
  le__def("provide", _ => t)
  le__def("sleep", _ => Nil)
  le__def("room", _ => Nil)
  le__def("gc", _ => Nil)
  le__def("get-universal-time", _ => {
    let ms = wall_time_ms()
    int64((ms / 1000UL).reinterpret_as_int64() + 2208988800L)
  })
  le__def("get-internal-real-time", _ => int64(
    wall_time_ms().reinterpret_as_int64() * 1000L,
  ))
  le__def("get-internal-run-time", _ => int64((cpu_time() * 1000000.0).to_int64()))
  le__def("machine-type", _ => Str("unknown"))
  le__def("machine-instance", _ => Str("unknown"))
  le__def("machine-version", _ => Str("unknown"))
  le__def("software-type", _ => Str("unknown"))
  le__def("software-version", _ => Str("unknown"))
  le__def("si::ensure-generic", a => le__arg(a, 0))
  le__def("si::add-method", a => le__add_method(a))
  le__def("load", a => {
    lisp_load_file(le__str(le__arg(a, 0)))
    t
  })
}

///|
/// Methods of generic functions: name -> list of (specializers, function).
let le__methods : Map[String, Array[(Array[Value], Value)]] = Map::new()

///|
fn le__specializer_ok(x : Value, spec : Value) -> Bool raise {
  match spec {
    Cons({ car: Sym({ name: "eql", .. }), cdr: Cons({ car: v, .. }) }) =>
      eql(x, le__eval_toplevel(v))
    _ => le__typep(x, spec)
  }
}

///|
fn le__add_method(a : Array[Value]) -> Value raise {
  let name = le__arg(a, 0)
  let specs = list_to_array(le__arg(a, 1))
  let fn_ = le__arg(a, 2)
  let key = le__type_name(name)
  let ms = match le__methods.get(key) {
    Some(m) => m
    None => {
      let m = []
      le__methods[key] = m
      m
    }
  }
  // replace a method with the same specializers
  let mut replaced = false
  for i, m in ms {
    if m.0.length() == specs.length() &&
      m.0.iter().zip(specs.iter()).all(p => equal(p.0, p.1)) {
      ms[i] = (specs, fn_)
      replaced = true
    }
  }
  if !replaced {
    ms.push((specs, fn_))
  }
  // the generic function: the first applicable method, most specific
  // (fewest T specializers) first
  defun(name, args => {
    let mut best : Value? = None
    let mut best_score = -1
    for m in ms {
      let mut ok = true
      let mut score = 0
      for i, sp in m.0 {
        if i >= args.length() || !le__specializer_ok(args[i], sp) {
          ok = false
          break
        }
        if !eq(sp, t) {
          score += 1
        }
      }
      if ok && score > best_score {
        best = Some(m.1)
        best_score = score
      }
    }
    match best {
      Some(f) => le__funcall(f, args)
      None =>
        le__error(
          "no applicable method for " + prin1_to_string(name) + " on " +
          prin1_to_string(list(args)),
        )
    }
  })
  name
}

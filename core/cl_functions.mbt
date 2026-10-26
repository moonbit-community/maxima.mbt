// Common Lisp functions installed in their symbols' function cells, so that
// Maxima code can call them as `?name(...)` (and Lisp code can funcall them
// by symbol), as in CL Maxima.

///|
fn cl__arith(
  args : Array[Value],
  init : Value,
  f : (Value, Value) -> Value raise,
) -> Value raise {
  let mut acc = init
  for a in args {
    acc = f(acc, a)
  }
  acc
}

///|
fn cl__chain(
  args : Array[Value],
  f : (Value, Value) -> Bool raise,
) -> Value raise {
  for i in 0..<(args.length() - 1) {
    if !f(args[i], args[i + 1]) {
      return Nil
    }
  }
  t
}

///|
fn cl__def(name : String, f : (Array[Value]) -> Value raise) -> Unit {
  let s = sym(name)
  if !fboundp(s) {
    defun(s, f)
  }
}

///|
fn register_cl_functions() -> Unit {
  cl__def("car", a => car(arg(a, 0)))
  cl__def("cdr", a => cdr(arg(a, 0)))
  cl__def("caar", a => caar(arg(a, 0)))
  cl__def("cadr", a => cadr(arg(a, 0)))
  cl__def("cdar", a => cdar(arg(a, 0)))
  cl__def("cddr", a => cddr(arg(a, 0)))
  cl__def("caddr", a => caddr(arg(a, 0)))
  cl__def("first", a => car(arg(a, 0)))
  cl__def("second", a => cadr(arg(a, 0)))
  cl__def("third", a => caddr(arg(a, 0)))
  cl__def("rest", a => cdr(arg(a, 0)))
  cl__def("cons", a => cons(arg(a, 0), arg(a, 1)))
  cl__def("list", a => list(a))
  cl__def("list*", a => list_star(a))
  cl__def("length", a => llength(arg(a, 0)))
  cl__def("reverse", a => reverse(arg(a, 0)))
  cl__def("append", a => append_n(a))
  cl__def("nth", a => nth(to_int(arg(a, 0)), arg(a, 1)))
  cl__def("nthcdr", a => nthcdr(to_int(arg(a, 0)), arg(a, 1)))
  cl__def("last", a => last(arg(a, 0)))
  cl__def("member", a => member(arg(a, 0), arg(a, 1)))
  cl__def("position", a => {
    let i = position(arg(a, 0), arg(a, 1))
    if i < 0 {
      Nil
    } else {
      int(i)
    }
  })
  cl__def("assoc", a => assoc(arg(a, 0), arg(a, 1)))
  cl__def("copy-list", a => copy_list(arg(a, 0)))
  cl__def("copy-tree", a => copy_tree(arg(a, 0)))
  cl__def("copy-seq", a => copy_seq(arg(a, 0)))
  cl__def("null", a => lbool(arg(a, 0) is Nil))
  cl__def("not", a => lbool(arg(a, 0) is Nil))
  cl__def("atom", a => lbool(atom(arg(a, 0))))
  cl__def("consp", a => lbool(consp(arg(a, 0))))
  cl__def("listp", a => lbool(listp(arg(a, 0))))
  cl__def("symbolp", a => lbool(symbolp(arg(a, 0))))
  cl__def("numberp", a => lbool(numberp(arg(a, 0))))
  cl__def("integerp", a => lbool(integerp(arg(a, 0))))
  cl__def("rationalp", a => lbool(rationalp(arg(a, 0))))
  cl__def("floatp", a => lbool(floatp(arg(a, 0))))
  cl__def("realp", a => lbool(realp(arg(a, 0))))
  cl__def("complexp", a => lbool(complexp(arg(a, 0))))
  cl__def("stringp", a => lbool(stringp(arg(a, 0))))
  cl__def("characterp", a => lbool(characterp(arg(a, 0))))
  cl__def("functionp", a => lbool(functionp(arg(a, 0))))
  cl__def("hash-table-p", a => lbool(hash_table_p(arg(a, 0))))
  cl__def("arrayp", a => lbool(arrayp(arg(a, 0))))
  cl__def("vectorp", a => lbool(vectorp(arg(a, 0))))
  cl__def("zerop", a => lbool(zerop(arg(a, 0))))
  cl__def("plusp", a => lbool(plusp(arg(a, 0))))
  cl__def("minusp", a => lbool(minusp(arg(a, 0))))
  cl__def("oddp", a => lbool(oddp(arg(a, 0))))
  cl__def("evenp", a => lbool(evenp(arg(a, 0))))
  cl__def("eq", a => lbool(eq(arg(a, 0), arg(a, 1))))
  cl__def("eql", a => lbool(eql(arg(a, 0), arg(a, 1))))
  cl__def("equal", a => lbool(equal(arg(a, 0), arg(a, 1))))
  cl__def("equalp", a => lbool(equalp(arg(a, 0), arg(a, 1))))
  cl__def("+", a => cl__arith(a, Fix(0L), (x, y) => num_add(x, y)))
  cl__def("*", a => cl__arith(a, Fix(1L), (x, y) => num_mul(x, y)))
  cl__def("-", a => if a.length() == 1 {
    num_neg(a[0])
  } else {
    cl__arith(a[1:].to_array(), a[0], (x, y) => num_sub(x, y))
  })
  cl__def("/", a => if a.length() == 1 {
    num_inv(a[0])
  } else {
    cl__arith(a[1:].to_array(), a[0], (x, y) => num_div(x, y))
  })
  cl__def("1+", a => one_plus(arg(a, 0)))
  cl__def("1-", a => one_minus(arg(a, 0)))
  cl__def("=", a => cl__chain(a, (x, y) => num_eq(x, y)))
  cl__def("<", a => cl__chain(a, (x, y) => num_lt(x, y)))
  cl__def(">", a => cl__chain(a, (x, y) => num_gt(x, y)))
  cl__def("<=", a => cl__chain(a, (x, y) => num_le(x, y)))
  cl__def(">=", a => cl__chain(a, (x, y) => num_ge(x, y)))
  cl__def("max", a => cl__arith(a[1:].to_array(), a[0], (x, y) => num_max(x, y)))
  cl__def("min", a => cl__arith(a[1:].to_array(), a[0], (x, y) => num_min(x, y)))
  cl__def("abs", a => num_abs(arg(a, 0)))
  cl__def("mod", a => num_mod(arg(a, 0), arg(a, 1)))
  cl__def("rem", a => num_rem(arg(a, 0), arg(a, 1)))
  cl__def("gcd", a => cl__arith(a, Fix(0L), (x, y) => num_gcd(x, y)))
  cl__def("expt", a => expt(arg(a, 0), arg(a, 1)))
  cl__def("isqrt", a => isqrt(arg(a, 0)))
  cl__def("floor", a => num_floor(arg(a, 0), b=a.get(1).unwrap_or(Fix(1L))).0)
  cl__def("ceiling", a => num_ceiling(arg(a, 0), b=a.get(1).unwrap_or(Fix(1L))).0)
  cl__def("truncate", a => num_truncate(arg(a, 0), b=a.get(1).unwrap_or(Fix(1L))).0)
  cl__def("round", a => num_round(arg(a, 0), b=a.get(1).unwrap_or(Fix(1L))).0)
  cl__def("float", a => lfloat(arg(a, 0)))
  cl__def("rational", a => rational(arg(a, 0)))
  cl__def("rationalize", a => rationalize(arg(a, 0)))
  cl__def("numerator", a => numerator(arg(a, 0)))
  cl__def("denominator", a => denominator(arg(a, 0)))
  cl__def("sqrt", a => lsqrt(arg(a, 0)))
  cl__def("exp", a => lexp(arg(a, 0)))
  cl__def("log", a => if a.length() > 1 {
    llog2(a[0], a[1])
  } else {
    llog(arg(a, 0))
  })
  cl__def("sin", a => lsin(arg(a, 0)))
  cl__def("cos", a => lcos(arg(a, 0)))
  cl__def("tan", a => ltan(arg(a, 0)))
  cl__def("atan", a => latan(arg(a, 0), x?=a.get(1)))
  cl__def("realpart", a => realpart(arg(a, 0)))
  cl__def("imagpart", a => imagpart(arg(a, 0)))
  cl__def("complex", a => complex(arg(a, 0), i=a.get(1).unwrap_or(Fix(0L))))
  cl__def("ash", a => ash(arg(a, 0), to_int(arg(a, 1))))
  cl__def("logand", a => cl__arith(a, Fix(-1L), (x, y) => logand(x, y)))
  cl__def("logior", a => cl__arith(a, Fix(0L), (x, y) => logior(x, y)))
  cl__def("logxor", a => cl__arith(a, Fix(0L), (x, y) => logxor(x, y)))
  cl__def("integer-length", a => int(integer_length(arg(a, 0))))
  cl__def("get", a => get(arg(a, 0), arg(a, 1)))
  cl__def("putprop", a => putprop(arg(a, 0), arg(a, 1), arg(a, 2)))
  cl__def("remprop", a => remprop(arg(a, 0), arg(a, 1)))
  cl__def("symbol-plist", a => symbol_plist(arg(a, 0)))
  cl__def("symbol-name", a => Str(symbol_name(arg(a, 0))))
  cl__def("symbol-value", a => symbol_value(arg(a, 0)))
  cl__def("symbol-function", a => symbol_function(arg(a, 0)))
  cl__def("boundp", a => lbool(boundp(arg(a, 0))))
  cl__def("fboundp", a => lbool(fboundp(arg(a, 0))))
  cl__def("makunbound", a => makunbound(arg(a, 0)))
  cl__def("set", a => set(arg(a, 0), arg(a, 1)))
  cl__def("intern", a => sym(lstring(arg(a, 0))))
  cl__def("make-symbol", a => make_symbol(lstring(arg(a, 0))))
  cl__def("gensym", a => gensym())
  cl__def("funcall", a => funcall(arg(a, 0), a[1:].to_array()))
  // (apply f a1 ... list): the last argument is a list of further args
  cl__def("apply", a => {
    let spread = list_to_array(arg(a, a.length() - 1))
    let lead = if a.length() > 2 { a[1:a.length() - 1].to_array() } else { [] }
    funcall(arg(a, 0), lead + spread)
  })
  cl__def("identity", a => arg(a, 0))
  cl__def("values", a => arg(a, 0))
  cl__def("print", a => print(arg(a, 0)))
  cl__def("princ", a => princ(arg(a, 0)))
  cl__def("prin1", a => prin1(arg(a, 0)))
  cl__def("terpri", _ => {
    terpri()
    Nil
  })
  cl__def("format", a => format(arg(a, 0), lstring(arg(a, 1)), a[2:].to_array()))
  cl__def("string", a => string(arg(a, 0)))
  cl__def("string-upcase", a => Str(string_upcase(lstring(arg(a, 0)))))
  cl__def("string-downcase", a => Str(string_downcase(lstring(arg(a, 0)))))
  cl__def("char", a => aref1(arg(a, 0), to_int(arg(a, 1))))
  cl__def("aref", a => aref(arg(a, 0), a[1:].to_array().map(x => to_int(x) catch {
    _ => 0
  })))
  cl__def("make-hash-table", _ => make_hash_table(kind=Equal))
  cl__def("gethash", a => gethash(arg(a, 0), arg(a, 1)))
  cl__def("hash-table-count", a => int(hash_table_count(arg(a, 0))))
  cl__def("vector", a => vector(a))
  cl__def("make-array", a => make_array([to_int(arg(a, 0))]))
  cl__def("coerce", a => {
    let x = arg(a, 0)
    match arg(a, 1) {
      Sym({ name: "list", .. }) => vector_to_list(x)
      Sym({ name: "string", .. }) => Str(char_list_to_string(x))
      Sym({ name: "float" | "double-float" | "flonum", .. }) => lfloat(x)
      _ => x
    }
  })
  cl__def("sort", a => {
    let lt = (x : Value, y : Value) => funcall(arg(a, 1), [x, y]).truthy()
    match arg(a, 0) {
      // a vector is sorted in place
      Vec(v) as seq => {
        let n = match v.fill {
          Some(f) => f
          None => v.data.length()
        }
        let sorted = sort_array(v.data[0:n].to_array(), lt)
        for i in 0..<n {
          v.data[i] = sorted[i]
        }
        seq
      }
      seq => sort_list(seq, lt)
    }
  })
  cl__def("copy-seq", a => copy_seq(arg(a, 0)))
  // (mapcar f l1 l2 ...): stops at the shortest list
  cl__def("mapcar", a => {
    let ls = a[1:].to_array().map(list_to_array)
    let n = ls.fold(init=if ls.is_empty() { 0 } else { ls[0].length() }, (m, l) => m.min(l.length()))
    let out = []
    for i in 0..<n {
      out.push(funcall(arg(a, 0), ls.map(l => l[i])))
    }
    list(out)
  })
  cl__def("remove", a => remove(arg(a, 0), arg(a, 1)))
  cl__def("delete", a => delete(arg(a, 0), arg(a, 1)))
  cl__def("subst", a => subst(arg(a, 0), arg(a, 1), arg(a, 2)))
  cl__def("subseq", a => if a.length() > 2 && arg(a, 2).truthy() {
    subseq(arg(a, 0), to_int(arg(a, 1)), end=to_int(arg(a, 2)))
  } else {
    subseq(arg(a, 0), to_int(arg(a, 1)))
  })
  cl__def("search", a => {
    let i = string_search(lstring(arg(a, 0)), lstring(arg(a, 1)))
    if i < 0 {
      Nil
    } else {
      int(i)
    }
  })
  cl__def("delete-file", a => {
    let path = lstring(arg(a, 0))
    @fs.remove_file(path) catch {
      _ =>
        raise LispError::Condition(
          intern("file-error"),
          "cannot delete file \{path}",
          Str(path),
        )
    }
    t
  })
  // RENAME-FILE (primary value: the new name). moonbitlang/x/fs has no
  // rename, so the file is copied and the original deleted.
  cl__def("rename-file", a => {
    let from = lstring(arg(a, 0))
    let to = lstring(arg(a, 1))
    let bytes = read_file_bytes(from)
    @fs.write_bytes_to_file(to, bytes) catch {
      _ =>
        raise LispError::Condition(
          intern("file-error"),
          "cannot rename file \{from} to \{to}",
          Str(from),
        )
    }
    @fs.remove_file(from) catch {
      _ =>
        raise LispError::Condition(
          intern("file-error"),
          "cannot rename file \{from} to \{to}",
          Str(from),
        )
    }
    Str(to)
  })
  cl__def("logbitp", a => lbool(logbitp(to_int(arg(a, 0)), arg(a, 1))))
  cl__def("array-dimension", a => int(array_dimension(arg(a, 0), to_int(arg(a, 1)))))
  cl__def("getf", a => getf(arg(a, 0), arg(a, 1), default=arg(a, 2)))
  cl__def("namestring", a => string(arg(a, 0)))
  cl__def("pathname-name", a => {
    let p = lstring(arg(a, 0))
    let base = match p.rev_find("/") {
      Some(i) => p.substring(start=i + 1)
      None => p
    }
    match base.rev_find(".") {
      Some(i) if i > 0 => Str(base.substring(end=i))
      _ => Str(base)
    }
  })
  cl__def("pathname-type", a => {
    let p = lstring(arg(a, 0))
    let base = match p.rev_find("/") {
      Some(i) => p.substring(start=i + 1)
      None => p
    }
    match base.rev_find(".") {
      Some(i) if i > 0 => Str(base.substring(start=i + 1))
      _ => Nil
    }
  })
  cl__def("pathname-version", _ => Nil)
  cl__def("getenv", a => match getenv(lstring(arg(a, 0))) {
    Some(v) => Str(v)
    None => Nil
  })
  cl__def("lisp-implementation-type", _ => Str("MoonBit"))
  cl__def("lisp-implementation-version", _ => Str("0.1"))
}

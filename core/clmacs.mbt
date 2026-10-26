// Port of src/clmacs.lisp: Common Lisp versions of Maclisp utilities.

///|
let clmacs__q_macro_function : Value = sym("macro-function")

///|
/// Native implementations of the operators used with DEF-OP (the runtime
/// does not define the CL arithmetic functions as Lisp functions).
fn clmacs__native_op(op : Value) -> ((Array[Value]) -> Value raise)? {
  let name = match op {
    Sym(s) => s.name
    _ => return None
  }
  match name {
    "+" =>
      Some(args => {
        let mut s : Value = Fix(0L)
        for a in args {
          s = num_add(s, a)
        }
        s
      })
    "*" =>
      Some(args => {
        let mut s : Value = Fix(1L)
        for a in args {
          s = num_mul(s, a)
        }
        s
      })
    "-" =>
      Some(args => {
        if args.length() == 1 {
          num_neg(args[0])
        } else {
          let mut s = args[0]
          for i in 1..<args.length() {
            s = num_sub(s, args[i])
          }
          s
        }
      })
    "1-" => Some(args => one_minus(arg(args, 0)))
    "1+" => Some(args => one_plus(arg(args, 0)))
    "quot" => Some(args => quot(arg(args, 0), arg(args, 1)))
    _ => None
  }
}

///|
/// Make a macro expander for an operator that declares the type and
/// result of numerical operations: `(name a b)` expands to
/// `(the return (op (the type a) (the type b)))`.  The expander is a Lisp
/// function of (form env) returning the expansion.
fn make_operation(
  n_dottype : Value,
  n_dotop : Value,
  n_dotreturn : Value,
) -> Value raise {
  let ret = if n_dotreturn.truthy() { n_dotreturn } else { n_dottype }
  lfunc("make-operation", args => {
    let bod = arg(args, 0)
    let body = mapcar(
      v => if eq(t, n_dottype) { v } else { list3(q_the, n_dottype, v) },
      cdr(bod),
    )
    let body = cons(n_dotop, body)
    if eq(t, ret) {
      body
    } else {
      list3(q_the, ret, body)
    }
  })
}

///|
/// `(def-op name arg-type op &optional return-type)`: in the port NAME
/// becomes a function applying OP (the type declarations have no run-time
/// effect); the expander from MAKE-OPERATION is kept on the
/// MACRO-FUNCTION property.
fn def_op(
  name : Value,
  arg_type : Value,
  op : Value,
  return_type~ : Value = Nil,
) -> Value raise {
  putprop(
    name,
    make_operation(arg_type, op, return_type),
    clmacs__q_macro_function,
  )
  |> ignore
  match clmacs__native_op(op) {
    Some(f) => defun(name, f)
    None => defun(name, args => funcall(op, args))
  }
  name
}

///|
/// This is essentially what the quotient is supposed to do.
fn quot(a : Value, b : Value) -> Value raise {
  if integerp(a) && integerp(b) {
    num_truncate(a, b~).0
  } else {
    num_div(a, b)
  }
}

///|
/// `(status option &optional item)`: `(status feature x)` tests *features*
/// for the keyword X; `(status gctime)` is 0.
fn status(option : Value, item~ : Value = Nil) -> Value raise {
  if symbol_name(option) == "feature" {
    let k = kw(lstring(string(item)))
    if boundp(q_ear_features) {
      member(k, symval(q_ear_features))
    } else {
      Nil
    }
  } else if eq(option, q_gctime) {
    Fix(0L)
  } else {
    Nil
  }
}

///|
/// CL STRING< : the index of the first mismatch when STR1 is less than
/// STR2, otherwise NIL.
fn clmacs__string_lt(s1 : String, s2 : String) -> Value {
  let a = string_chars(s1)
  let b = string_chars(s2)
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i in 0..<n {
    if a[i] != b[i] {
      return if a[i] < b[i] { int(i) } else { Nil }
    }
  }
  if a.length() < b.length() {
    int(a.length())
  } else {
    Nil
  }
}

///|
fn string_lt_dol(str1 : Value, str2 : Value) -> Value raise {
  clmacs__string_lt(lstring(str1), lstring(str2))
}

///|
/// Returns the character C with inverted case.
fn char_invert_case(c : Value) -> Value raise {
  match c {
    Char(ch) => {
      let downcased = char_downcase(ch)
      if downcased == ch {
        Char(char_upcase(ch))
      } else {
        Char(downcased)
      }
    }
    _ => raise type_error(c, "character")
  }
}

///|
/// numbers<strings<symbols<lists<?
///
/// For symbols, the CL version compares names with the case of uniform-case
/// names inverted, which is exactly a plain comparison of the port's
/// (user-visible) names.
fn alphalessp(x : Value, y : Value) -> Value raise {
  if numberp(x) {
    if numberp(y) {
      lbool(num_lt(x, y))
    } else {
      t
    }
  } else if stringp(x) {
    if numberp(y) {
      Nil
    } else if stringp(y) {
      clmacs__string_lt(lstring(x), lstring(y))
    } else {
      t
    }
  } else if symbolp(x) {
    if numberp(y) || stringp(y) {
      Nil
    } else if symbolp(y) {
      let nx = string_chars(symbol_name(x))
      let ny = string_chars(symbol_name(y))
      let n = if nx.length() < ny.length() { nx.length() } else { ny.length() }
      for i in 0..<n {
        if nx[i] != ny[i] {
          return lbool(nx[i] < ny[i])
        }
      }
      // Same length means same symbol name: the (same) package decides,
      // and string< of equal package names is NIL.  Otherwise the symbol
      // with the shorter name is "less".
      lbool(nx.length() < ny.length())
    } else if consp(y) {
      t
    } else {
      Nil
    }
  } else if listp(x) {
    if numberp(y) || stringp(y) || symbolp(y) {
      Nil
    } else if listp(y) {
      let r = alphalessp(car(x), car(y))
      if r.truthy() {
        r
      } else if equal(car(x), car(y)) {
        alphalessp(cdr(x), cdr(y))
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else if numberp(y) || stringp(y) || symbolp(y) || consp(y) {
    Nil
  } else {
    // neither is of known type:
    alphalessp(Str(prin1_to_string(x)), Str(prin1_to_string(y)))
  }
}

///|
/// `(symbol-array sym)` = `(get sym 'array)`
fn symbol_array(sym_ : Value) -> Value raise {
  get(sym_, q_array)
}

///|
/// CL ARRAY-ELEMENT-TYPE of a runtime array.
fn clmacs__array_element_type(ar : Value) -> Value raise {
  match ar {
    Str(_) => sym("character")
    _ => {
      let a = as_array(ar)
      match a.elt {
        "t" | "" => t
        "flonum" => sym("double-float")
        e => sym(e)
      }
    }
  }
}

///|
fn arraydims(ar : Value) -> Value raise {
  let ar = if symbolp(ar) { symbol_array(ar) } else { ar }
  cons(clmacs__array_element_type(ar), array_dimensions(ar))
}

///|
fn fixnump_(n : Value) -> Value raise {
  lbool(fixnump(n))
}

///|
fn bignump_(x : Value) -> Value raise {
  lbool(bignump(x))
}

///|
fn posint(x : Value) -> Value raise {
  lbool(integerp(x) && num_gt(x, Fix(0L)))
}

///|
fn negint(x : Value) -> Value raise {
  lbool(integerp(x) && num_lt(x, Fix(0L)))
}

///|
/// If x is in the list, return the sublist with element, else nil.
fn memq_(x : Value, lis : Value) -> Value raise {
  memq(x, lis)
}

///|
fn firstn(n : Value, lis : Value) -> Value raise {
  subseq(lis, 0, end=to_int(n))
}

///|
/// `(defprop sym val indic)`; with INDIC EXPR the function cell is set.
fn defprop(sym_ : Value, val : Value, indic : Value) -> Value raise {
  if eq(indic, q_expr) {
    fset(sym_, symbol_function(val))
  } else {
    setf_get(sym_, indic, val)
  }
}

///|
/// Find the N most significant or least significant bits of the absolute
/// value of X.  If N is positive, take the most significant; otherwise,
/// the least significant.
fn haipart(x : Value, n : Value) -> Value raise {
  let x = num_abs(x)
  let n = to_int(n)
  if n < 0 {
    // If the desired number of bits is larger than the actual number, just
    // return the number.  (Prevents gratuitously generating a huge bignum
    // if n is very large, as can happen with bigfloats.)
    if integer_length(x) < -n {
      x
    } else {
      logand(x, one_minus(ash(Fix(1L), -n)))
    }
  } else {
    let s = n - integer_length(x)
    ash(x, if s < 0 { s } else { 0 })
  }
}

///|
/// `(setf (symbol-function sym) val)`
fn fset(sym_ : Value, val : Value) -> Value raise {
  match val {
    Func(f) => defun(sym_, f.call, name=f.name)
    Sym(_) => {
      let f = symbol_function(val)
      match f {
        Func(g) => defun(sym_, g.call, name=g.name)
        _ => raise type_error(f, "function")
      }
    }
    _ => raise type_error(val, "function")
  }
  val
}

///|
fn zl_get(sym_ : Value, tag : Value) -> Value raise {
  if symbolp(sym_) {
    get(sym_, tag)
  } else if consp(sym_) {
    getf(cdr(sym_), tag)
  } else {
    Nil
  }
}

///|
fn zl_remprop(sym_ : Value, indicator : Value) -> Value raise {
  if symbolp(sym_) {
    remprop(sym_, indicator)
  } else if atom(sym_) {
    Nil
  } else {
    // (remf (cdr sym) indicator)
    let mut prev = sym_
    let mut l = cdr(sym_)
    while consp(l) {
      if eq(car(l), indicator) {
        rplacd(prev, cddr(l)) |> ignore
        return t
      }
      prev = cdr(l)
      l = cddr(l)
    }
    Nil
  }
}

///|
fn getl(plist : Value, indicator_list : Value) -> Value raise {
  let plist = if symbolp(plist) {
    symbol_plist(plist)
  } else if consp(plist) {
    cdr(plist)
  } else {
    return Nil
  }
  if indicator_list is Nil {
    Nil
  } else if cdr(indicator_list) is Nil {
    // Fast path for the common case of a single-element INDICATOR-LIST:
    let indicator = car(indicator_list)
    let mut tail = plist
    while consp(tail) {
      if cadr(tail).truthy() && eq(car(tail), indicator) {
        return tail
      }
      tail = cddr(tail)
    }
    Nil
  } else {
    let mut tail = plist
    while consp(tail) {
      if cadr(tail).truthy() && memq(car(tail), indicator_list).truthy() {
        return tail
      }
      tail = cddr(tail)
    }
    Nil
  }
}

///|
fn safe_get(sym_ : Value, prop : Value) -> Value raise {
  if symbolp(sym_) {
    get(sym_, prop)
  } else {
    Nil
  }
}

///|
fn safe_getl(sym_ : Value, prop : Value) -> Value raise {
  if symbolp(sym_) {
    getl(sym_, prop)
  } else {
    Nil
  }
}

///|
fn ncons(x : Value) -> Value raise {
  cons(x, Nil)
}

// Format of *acursor*.
// 0                 1  2  3  4  5    6  7  8  9  10
// dim               i1 i2 i3 i4 i5   d1 d2 d3 d4 d5
// array dimension   current index    maximal index

///|
fn clmacs__cursor_ref(i : Int32) -> Int32 raise {
  to_int(aref1(symval(q_ear_acursor), i))
}

///|
fn clmacs__cursor_set(i : Int32, v : Int32) -> Unit raise {
  aset1(symval(q_ear_acursor), i, int(v)) |> ignore
}

///|
fn set_up_cursor(ar : Value) -> Value raise {
  let lis = array_dimensions(ar)
  clmacs__cursor_set(0, length(lis))
  let mut i = 6
  for v in lis.iter() {
    clmacs__cursor_set(i, to_int(v) - 1)
    i += 1
  }
  for j in 1..<=length(lis) {
    clmacs__cursor_set(j, 0)
  }
  Nil
}

///|
fn aset_by_cursor(ar : Value, val : Value) -> Value raise {
  let n = clmacs__cursor_ref(0)
  let idx : Array[Int32] = []
  match n {
    1 | 2 | 3 | 4 | 5 =>
      for j in 1..<=n {
        idx.push(clmacs__cursor_ref(j))
      }
    _ =>
      raise LispError::SimpleError(
        format_to_string(
          "~S fell through ECASE expression. Wanted one of (1 2 3 4 5).",
          [int(n)],
        ),
      )
  }
  aset(ar, idx, val) |> ignore
  // set the index (`cursor') for the next call to ASET-BY-CURSOR
  let mut j = n
  while true {
    if clmacs__cursor_ref(j) < clmacs__cursor_ref(5 + j) {
      clmacs__cursor_set(j, clmacs__cursor_ref(j) + 1)
      return t
    } else {
      clmacs__cursor_set(j, 0)
    }
    if j == 0 {
      return Nil
    }
    j -= 1
  }
  Nil
}

///|
fn fillarray(ar : Value, x : Value) -> Value raise {
  let mut ar = if symbolp(ar) { get(ar, q_array) } else { ar }
  if array_rank(ar) != 1 {
    // (make-array (array-total-size ar) :displaced-to ar): a 1-d view
    // sharing the storage.
    let a = as_array(ar)
    ar = Vec({ data: a.data, dims: [a.data.length()], fill: None, elt: a.elt, })
  }
  let mut x = if x is Nil {
    match lstring(string(clmacs__array_element_type(ar))) {
      "fixnum" => list1(Fix(0L))
      // CL: FLOAT; the port's float arrays are double-float.
      "float" | "double-float" => list1(Flo(0.0))
      "t" => list1(Nil)
      _ =>
        raise LispError::SimpleError(
          format_to_string(
            "~S fell through ECASE expression. Wanted one of (FIXNUM FLOAT T).",
            [clmacs__array_element_type(ar)],
          ),
        )
    }
  } else if arrayp(x) {
    listarray(x)
  } else if atom(x) {
    list1(x)
  } else {
    x
  }
  let len = match as_array(ar).fill {
    Some(f) => f
    None => as_array(ar).data.length()
  }
  if len > 0 {
    set_up_cursor(ar) |> ignore
    while aset_by_cursor(ar, car(x)).truthy() {
      if cdr(x).truthy() {
        x = cdr(x)
      }
    }
  }
  Nil
}

///|
fn listarray(x : Value) -> Value raise {
  let x = if symbolp(x) { get(x, q_array) } else { x }
  if array_rank(x) == 1 {
    vector_to_list(x)
  } else {
    list(as_array(x).data)
  }
}

///|
/// `(check-arg place pred &rest res)`: assert that PRED holds for PLACE.
/// PRED is a function designator called on PLACE (or, if not a function,
/// a truth value); RES are the ASSERT format control and arguments.
fn check_arg(place : Value, pred : Value, res : Value) -> Value raise {
  let ok = match pred {
    Func(_) => funcall(pred, [place])
    Sym(_) if fboundp(pred) => funcall(pred, [place])
    _ => pred
  }
  if ok is Nil {
    let msg = if stringp(car(res)) {
      format_to_string(lstring(car(res)), list_to_array(cdr(res)))
    } else {
      format_to_string("The assertion ~S failed.", [list2(pred, place)])
    }
    raise LispError::SimpleError(msg)
  }
  Nil
}

///|
/// `(deff fun val)` = `(setf (symbol-function 'fun) val)`
fn deff(fun : Value, val : Value) -> Value raise {
  fset(fun, val)
}

///|
fn xcons(x : Value, y : Value) -> Value raise {
  cons(y, x)
}

///|
fn make_equal_hash_table(not_dim1 : Value) -> Value raise {
  let table = make_hash_table(kind=Equal)
  if not_dim1 is Nil {
    sethash(q_dim1, table, t) |> ignore
  }
  table
}

///|
/// `(float x &optional (y 1e0))` = `(cl:float x y)`; flonums are doubles.
fn float(x : Value, y~ : Value = Flo(1.0)) -> Value raise {
  ignore(y)
  if floatp(x) {
    x
  } else {
    Flo(to_double(x))
  }
}

///|
/// Like do-merge-asym, but calls onefun if an element appears in one but
/// not the other list, regardless of which list it appears in.
fn do_merge_symm(
  list1 : Value,
  list2 : Value,
  eqfun : Value,
  lessfun : Value,
  bothfun : Value,
  onefun : Value,
) -> Value raise {
  do_merge_asym(list1, list2, eqfun, lessfun, bothfun, onefun, onefun)
}

///|
/// Takes two lists.  The element equality function is eqfun, and they must
/// be sorted by lessfun.  Calls bothfun on each element that is shared by
/// the two lists; calls only1fun on each element that appears only in the
/// first list; calls only2fun on each element that appears only in the
/// second list.  If both/only1/only2 fun are nil, treat as no-op.
fn do_merge_asym(
  list1 : Value,
  list2 : Value,
  eqfun : Value,
  lessfun : Value,
  bothfun : Value,
  only1fun : Value,
  only2fun : Value,
) -> Value raise {
  let mut l1 = list1
  let mut l2 = list2
  while true {
    if l1 is Nil {
      if only2fun.truthy() {
        while l2.truthy() {
          funcall(only2fun, [car(l2)]) |> ignore
          l2 = cdr(l2)
        }
      }
      break
    } else if l2 is Nil {
      if only1fun.truthy() {
        while l1.truthy() {
          funcall(only1fun, [car(l1)]) |> ignore
          l1 = cdr(l1)
        }
      }
      break
    } else if funcall(eqfun, [car(l1), car(l2)]).truthy() {
      if bothfun.truthy() {
        funcall(bothfun, [car(l1)]) |> ignore
      }
      l1 = cdr(l1)
      l2 = cdr(l2)
    } else if funcall(lessfun, [car(l1), car(l2)]).truthy() {
      if only1fun.truthy() {
        funcall(only1fun, [car(l1)]) |> ignore
      }
      l1 = cdr(l1)
    } else {
      if only2fun.truthy() {
        funcall(only2fun, [car(l2)]) |> ignore
      }
      l2 = cdr(l2)
    }
  }
  Nil
}

///|
fn init_clmacs() -> Unit raise {
  def_op(sym("f+"), q_fixnum, q_op_plus) |> ignore
  def_op(sym("f*"), q_fixnum, sym("*")) |> ignore
  def_op(q_f_, q_fixnum, sym("-")) |> ignore
  def_op(sym("f1-"), q_fixnum, sym("1-")) |> ignore
  def_op(sym("f1+"), q_fixnum, sym("1+")) |> ignore
  def_op(q_quotient, t, q_quot) |> ignore
  defvar_init(q_ear_acursor, make_array([11], elt="fixnum", initial=Fix(0L)))
  // exp is shadowed to save trouble for other packages--its declared
  // special
  defun(q_exp, args => lexp(arg(args, 0)))
}

// macdes.lisp is excluded from the port (help system), but it also defines
// the list utility $create_list, which is ported here.

///|
let macdes__q_d_create_list : Value = sym("$create_list")

///|
/// `(defmspec $create_list (l) ...)`
fn macdes__d_create_list(l : Value) -> Value raise {
  cons(list1(q_mlist), macdes__create_list1(cadr(l), cddr(l)))
}

///|
/// `(defun create-list1 (form &rest l) ...)`
fn macdes__create_list1(form : Value, l : Value) -> Value raise {
  if l is Nil {
    return list1(meval(form))
  }
  let var1 = first(l)
  let mut lis = second(l)
  let mut l = cddr(l)
  if !symbolp(var1) {
    merr("create_list: expected a symbol; found: ~A", [var1]) |> ignore
  }
  lis = meval(lis)
  let vars = list1(var1)
  mlisp__mbinding(vars, vars, Nil, fn() {
    if numberp(lis) {
      let top = meval(car(l))
      l = cdr(l)
      if numberp(top) {
        // (loop for i from lis to top do (mset var1 i) append ...)
        let acc = Collector::new()
        let mut i = lis
        while num_le(i, top) {
          mset(var1, i) |> ignore
          acc.append_list(macdes__create_list1(form, l))
          i = num_add(i, Fix(1L))
        }
        return acc.result()
      }
    }
    if d_listp(lis).truthy() {
      let acc = Collector::new()
      for v in cdr(lis).iter() {
        mset(var1, v) |> ignore
        acc.append_list(macdes__create_list1(form, l))
      }
      acc.result()
    } else {
      merr("create_list: unexpected arguments.", [])
    }
  })
}

///|
fn init_macdes() -> Unit raise {
  register_mspec(macdes__q_d_create_list, macdes__d_create_list)
  register_mspec(macdes__q_d_apropos, macdes__d_apropos)
}

///|
let macdes__q_d_apropos : Value = sym("$apropos")

///|
/// CL `(apropos-list s :maxima)`: every symbol whose name contains `s`,
/// compared with CHAR-EQUAL (as SBCL does).
fn macdes__apropos_list(s : String) -> Array[Value] {
  let needle = s.to_lower()
  let acc : Array[Value] = []
  for sy in all_symbols() {
    if sy.name.to_lower().contains(needle) {
      acc.push(Sym(sy))
    }
  }
  acc
}

///|
/// `(defmspec $apropos (s) ...)`: the Maxima user symbols (names starting
/// with $ or %) whose names contain the string or symbol name S.
fn macdes__d_apropos(form : Value) -> Value raise {
  let s0 = car(margs(form))
  let s = match s0 {
    Str(str) => str
    Sym(_) => symbol_name(stripdollar(s0))
    _ =>
      return merr("apropos: argument must be a string or symbol; found: ~M", [
        s0,
      ])
  }
  // DELETE-IF-NOT keeps the symbols themselves; REMOVE-DUPLICATES keeps
  // the last occurrence of each.
  let kept : Array[Value] = []
  for x in macdes__apropos_list(s) {
    let name = symbol_name(x)
    if name != "" && (name.has_prefix("$") || name.has_prefix("%")) {
      kept.push(x)
    }
  }
  let res = Collector::new()
  for i, x in kept {
    let mut later = false
    for j in (i + 1)..<kept.length() {
      if eq(kept[j], x) {
        later = true
        break
      }
    }
    if !later {
      res.add(x)
    }
  }
  cons(list1(q_mlist), res.result())
}

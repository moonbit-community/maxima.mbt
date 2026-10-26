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
}

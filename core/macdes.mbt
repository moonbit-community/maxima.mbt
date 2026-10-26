// The list-creation utility of src/macdes.lisp (the rest of that file is the
// help system, which is not ported). Registered from init_mlisp.

///|
/// `(defmspec $create_list (l) ...)`
fn macdes__d_create_list(l : Value) -> Value raise {
  cons(list1(q_mlist), macdes__create_list1(cadr(l), cddr(l)))
}

///|
/// `(defun create-list1 (form &rest l &aux lis var1 top) ...)`
fn macdes__create_list1(form : Value, l : Value) -> Value raise {
  if l is Nil {
    return list1(meval(form))
  }
  let var1 = car(l)
  let mut lis = cadr(l)
  let mut l = cddr(l)
  if !symbolp(var1) {
    merr("create_list: expected a symbol; found: ~A", [var1]) |> ignore
  }
  lis = meval(lis)
  // (mbinding ((list var1)) ...): bind VAR1 to itself, unbind on exit.
  let vars = list1(var1)
  let mut win = false
  defer (if win { munbind(vars) |> ignore })
  mbind(vars, vars, Nil) |> ignore
  win = true
  let numeric = if numberp(lis) {
    let top0 = car(l)
    l = cdr(l)
    let top = meval(top0)
    if numberp(top) {
      Some(top)
    } else {
      None
    }
  } else {
    None
  }
  match numeric {
    Some(top) => {
      let out = Collector::new()
      let mut i = lis
      while num_le(i, top) {
        mset(var1, i) |> ignore
        out.append_list(macdes__create_list1(form, l))
        i = num_add(i, Fix(1L))
      }
      out.result()
    }
    None =>
      if d_listp(lis).truthy() {
        let out = Collector::new()
        for v in cdr(lis).iter() {
          mset(var1, v) |> ignore
          out.append_list(macdes__create_list1(form, l))
        }
        out.result()
      } else {
        merr("create_list: unexpected arguments.", [])
      }
  }
}

///|
let macdes__q_d_create_list : Value = sym("$create_list")

///|
fn init_macdes_create_list() -> Unit raise {
  register_mspec(macdes__q_d_create_list, macdes__d_create_list)
}

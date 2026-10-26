// Port of src/opr-util.lisp: op and opr properties.

///|
fn getopr0(x : Value) -> Value raise {
  if symbolp(x) {
    let v = get(x, q_opr)
    if v.truthy() {
      return v
    }
  }
  if stringp(x) {
    gethash(x, symval(q_ear_opr_table))
  } else {
    Nil
  }
}

///|
fn getopr(x : Value) -> Value raise {
  let v = getopr0(x)
  if v.truthy() {
    v
  } else {
    x
  }
}

///|
fn putopr(x : Value, y : Value) -> Value raise {
  if symbolp(x) {
    let v = setf_get(x, q_opr, y)
    if v.truthy() {
      return v
    }
  }
  if stringp(x) {
    sethash(x, symval(q_ear_opr_table), y)
  } else {
    Nil
  }
}

///|
fn remopr(x : Value) -> Value raise {
  if symbolp(x) {
    let v = remprop(x, q_opr)
    if v.truthy() {
      return v
    }
  }
  if stringp(x) {
    lbool(remhash(x, symval(q_ear_opr_table)))
  } else {
    Nil
  }
}

///|
fn init_opr_util() -> Unit raise {
  defvar_init(q_ear_opr_table, make_hash_table(kind=Equal))
}

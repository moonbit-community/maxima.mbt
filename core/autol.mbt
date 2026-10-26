// Port of src/autol.lisp: helper functions for autoloading. The actual
// autoloading data is in max_ext.mbt.
//
// AALOAD of a Lisp file runs the ported share file if there is one, else
// loads the source with the Lisp evaluator (`autol__load_lisp_hook`), while
// Maxima (.mac) files are loaded with BATCHLOAD as in the Lisp source.

///|
/// Loader for Lisp source files found by AALOAD (receives the path).
let autol__load_lisp_hook : Ref[(String) -> Value raise] = Ref(path => {
  lisp_load_file(path)
  t
})

///|
/// CL `|_l|` (the rest-argument name in autoload stubs), as a port symbol.
let autol__q_l : Value = sym(invert_case("_l"))

///|
fn aload(file : Value) -> Value raise {
  // *load-verbose* has no counterpart in the port.
  let tem = with_special(q_d_system, list1(list1(q_mlist)), () => d_file_search1(
    file,
    list3(list1(q_mlist), q_d_file_search_lisp, q_d_system),
  ))
  if tem.truthy() {
    let path = match tem {
      Str(s) => s
      _ => princ_to_string(tem)
    }
    with_special(q_ear_read_base, Fix(10L), () => if share_try_load(path) {
      t
    } else {
      (autol__load_lisp_hook.val)(path)
    })
  } else {
    Nil
  }
}

///|
fn d_aload_mac(file : Value) -> Value raise {
  let tem = d_file_search1(file, list2(list1(q_mlist), q_d_file_search_maxima))
  if tem.truthy() {
    let path = match tem {
      Str(s) => s
      _ => princ_to_string(tem)
    }
    let in_stream = open_input_file(path)
    batchload_stream(in_stream, autoloading_p=t)
  } else {
    Nil
  }
}

///|
/// for defun, defmfun
fn autof(fun : Value, file : Value) -> Value raise {
  if !fboundp(fun) {
    defun(fun, l => {
      aload(file) |> ignore
      apply(fun, list(l))
    })
  }
  Nil
}

///|
/// for defmacro. The port has no macro functions; the stub is installed in
/// the function cell like AUTOF's.
fn autom(fun : Value, file : Value) -> Value raise {
  if !fboundp(fun) {
    defun(fun, l => {
      aload(file) |> ignore
      apply(fun, list(l))
    })
  }
  Nil
}

///|
/// for defmspec
fn auto_mspec(fun : Value, file : Value) -> Value raise {
  if get(fun, q_mfexpr_star) is Nil {
    let stub = lfunc(
      (symbol_name(fun) catch { _ => "auto-mspec" }),
      args => {
        aload(file) |> ignore
        funcall(get(fun, q_mfexpr_star), [arg(args, 0)])
      },
    )
    setf_get(fun, q_mfexpr_star, stub)
  } else {
    Nil
  }
}

///|
/// Build `((lambda) ((mlist) ((mlist) _l)) ((mprogn) ((loader) ((mquote)
/// file)) (($apply) ((mquote) fun) _l)))`.
fn autol__stub(fun : Value, file : Value, loader : Value) -> Value {
  list3(
    list1(q_lambda),
    list2(list1(q_mlist), list2(list1(q_mlist), autol__q_l)),
    list3(
      list1(q_mprogn),
      list2(list1(loader), list2(list1(q_mquote), file)),
      list3(list1(q_d_apply), list2(list1(q_mquote), fun), autol__q_l),
    ),
  )
}

///|
/// foo(x,y):=..
fn auto_mexpr(fun : Value, file : Value) -> Value raise {
  if mget(fun, q_mexpr) is Nil {
    mputprop(fun, autol__stub(fun, file, q_aload), q_mexpr)
  } else {
    Nil
  }
}

///|
/// foo(x,y):=..
fn d_auto_mexpr(fun : Value, file : Value) -> Value raise {
  if mget(fun, q_mexpr) is Nil {
    mputprop(fun, autol__stub(fun, file, q_d_aload_mac), q_mexpr)
  } else {
    Nil
  }
}

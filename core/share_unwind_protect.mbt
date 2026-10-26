// Port of share/contrib/unwind_protect.lisp.

///|
fn d_unwind_protect(e : Value) -> Value raise {
  let e = margs(e)
  let v = meval(first(e)) catch {
    err => {
      mapcar(x => meval(x), rest(e)) |> ignore
      raise err
    }
  }
  mapcar(x => meval(x), rest(e)) |> ignore
  v
}

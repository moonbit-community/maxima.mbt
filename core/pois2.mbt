// Port of src/pois2.lisp: poisson series limits.

///|
fn poislim1(uu : Value, n : Value) -> Value raise {
  ignore(uu)
  if !fixnump(n) {
    merr("poislim: argument must be an integer; found: ~M", [n]) |> ignore
  }
  set(q_poisvals, Nil) |> ignore
  set(q_poists, ash(int(1), to_int(n))) |> ignore
  for j in 0..<6 {
    push_special(expt(symval(q_poists), int(j)), q_poisvals) |> ignore
  }
  set(q_poissiz, n) |> ignore
  set(q_poistsm, expt(int(2), num_sub(n, int(1)))) |> ignore
  let mut sum = int(0)
  for i in 0..<6 {
    sum = num_add(sum, num_mul(symval(q_poistsm), expt(symval(q_poists), int(i))))
  }
  set(q_poishift, sum) |> ignore
  set(q_d_poisz, list3(list2(q_mpois, q_simp), Nil, Nil)) |> ignore
  set(
    q_d_pois1,
    list3(list2(q_mpois, q_simp), Nil, list2(symval(q_poishift), int(1))),
  )
  |> ignore
  n
}

///|
fn nonperiod(p : Value) -> Value raise {
  lbool(
    cadr(p) is Nil &&
    eql(car(caddr(p)), symval(q_poishift)) &&
    cddr(caddr(p)) is Nil,
  )
}

///|
fn init_pois2() -> Unit raise {
  poislim1(Nil, int(5)) |> ignore
}

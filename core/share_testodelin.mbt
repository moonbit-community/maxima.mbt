// Port of share/contrib/diffequations/testodelin.lisp (Barton Willis,
// 2004): run odelin on each equation of a file and report the solved and
// unsolved equations and the run times.

///|
fn init_share_testodelin() -> Unit raise {
  d_put(sym("$testodelin"), int(1), q_d_version) |> ignore
}

///|
fn d_testodelin(fn_ : Value) -> Value raise {
  let mut acc : Value = Nil
  let mut i = 0
  let mut times : Value = Nil
  let mut solved_des : Value = Nil
  let mut unsolved_des : Value = Nil
  let mut total_time : Value = int(0)
  let mut longest_time : Value = int(0)
  // (string fn), (make-pathname :name fn)
  let fname = match fn_ {
    Str(s) => s
    _ => invert_case(symbol_name(fn_))
  }
  d_load(Str("odelin")) |> ignore
  let strm = open_input_file(fname)
  let eof = q_eof
  while true {
    let de = mread(list2(strm, eof))
    if eq(eof, de) {
      break
    }
    acc = cons(nth(2, de), acc)
  }
  acc = reverse(acc)
  let itups = 1000000.0 // internal-time-units-per-second
  let q_de = sym("de")
  for de in acc.iter() {
    i = i + 1
    meval(list2(list1(q_d_kill), q_d_all)) |> ignore // sigh....
    format(t, "~%-- ~A ------------------------------------~%", [int(i)])
    |> ignore
    let start = acall__get_internal_run_time()
    displa(list([list1(q_mequal), q_de, de])) |> ignore
    let gork = list2(
      list1(q_d_errcatch),
      list([list1(q_d_odelin), de, sym("$Y"), sym("$X")]),
    )
    let mut sol = meval(gork)
    let t1 = num_sub(acall__get_internal_run_time(), start)
    times = cons(t1, times)
    longest_time = num_max(longest_time, t1)
    let t1f : Value = Flo(to_double(t1) / itups)
    total_time = num_add(total_time, t1f)
    let t1m = mul2(t1f, q_d_sec)
    if !like(sol, list1(list1(q_mlist))).truthy() &&
      !like(d_first(sol), Nil).truthy() {
      solved_des = cons(de, solved_des)
      sol = d_first(sol)
      displa(list([list1(q_mequal), sym("sol"), sol])) |> ignore
      displa(list([list1(q_mequal), sym("time"), t1m])) |> ignore
    } else {
      unsolved_des = cons(de, unsolved_des)
      displa(list([list1(q_mequal), sym("time"), t1m])) |> ignore
      displa(list([list1(q_mequal), sym("notsolved"), de])) |> ignore
    }
  }
  let longest_time : Value = Flo(to_double(longest_time) / itups)
  let total_time = mul2(total_time, q_d_sec)
  displa(list([list1(q_mequal), sym("totaltime"), total_time])) |> ignore
  displa(list([list1(q_mequal), sym("longest_time"), longest_time])) |> ignore
  displa(
    list([list1(q_mequal), sym("number_of_solved_des"), int(length(solved_des))]),
  )
  |> ignore
  displa(
    list([
      list1(q_mequal),
      sym("number_of_unsolved_des"),
      int(length(unsolved_des)),
    ]),
  )
  |> ignore
  times = sort_list(times, (a, b) => num_lt(a, b))
  times = cons(list1(q_mlist), times)
  displa(list([list1(q_mequal), sym("times"), times])) |> ignore
  let mut last : Value = Nil
  for de in unsolved_des.iter() {
    last = displa(de)
  }
  ignore(last)
  Nil
}

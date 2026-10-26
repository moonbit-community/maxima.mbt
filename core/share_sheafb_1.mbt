// Port of share/affine/sheafb.lisp (part 1): blowups of pre-ldata-sheaves,
// rational maps applied to ldata, normalization of open sets, open
// refinements, simplification of the ldata of an s-variety and the
// translation of components between opens.
//
// Notes:
// - The structures (ldata, zopen, rmap, pre-ldata-sheaves, s-var) are the
//   list structures handled by the `sheafa__` helpers.
// - Several functions call functions that are not defined in Maxima
//   (`process-sleep`, `mem`, `push-new`, `string-append`, and LIST-VARIABLES
//   with a wrong argument count).  As in the reference, those calls signal
//   an error (`sheafb__undefined`).
// - `~/maxima::tilde-q-fsh/` format directives are emulated by printing the
//   surrounding text with `format` and the argument with FSH.
// - The Maclisp `multiple-value` form is translated as
//   `multiple-value-setq`.

// ---------------------------------------------------------------------------
// Symbols without generated constants

///|
let sheafb__q_check_the_worst : Value = sym("check-the-worst")

///|
let sheafb__q_opens_not_to_try : Value = sym("opens-not-to-try")

///|
let sheafb__q_opens_to_try : Value = sym("opens-to-try")

///|
let sheafb__q_a_red_pls : Value = sym("a-red-pls")

///|
let sheafb__q_an_open_number : Value = sym("an-open-number")

///|
let sheafb__q_component_number : Value = sym("component-number")

// ---------------------------------------------------------------------------
// Helpers

///|
/// A call of a function that is not defined in Maxima.
fn sheafb__undefined(name : String) -> Value raise {
  raise LispError::SimpleError(
    "The function MAXIMA::" + name + " is undefined.",
  )
}

///|
/// `(format t "...~/maxima::tilde-q-fsh/...")`: `x` printed with FSH on
/// *standard-output*.
fn sheafb__fsh(x : Value) -> Unit raise {
  fsh(x, stream=symval(standard_output)) |> ignore
}

///|
/// `(iassert form)` (amacros.lisp).
fn sheafb__iassert(ok : Bool, form : String) -> Unit raise {
  if !ok {
    fsignal(list([Str("The expression ~A was not true"), Str(form)]))
    |> ignore
  }
}

///|
/// `(check-arg place pred "msg")` when the predicate fails.
fn sheafb__check_arg(ok : Bool, msg : String) -> Unit raise {
  if !ok {
    raise LispError::SimpleError(msg)
  }
}

///|
/// `(setf (nth n l) v)`
fn sheafb__setf_nth(n : Int, l : Value, v : Value) -> Value raise {
  let cell = nthcdr(n, l)
  if cell is Nil {
    raise LispError::SimpleError(
      format_to_string("~A is too large an index for SETF of NTH.", [int(n)]),
    )
  }
  setf_car(cell, v) |> ignore
  v
}

///|
/// CL `read` from *standard-input*: one form per line.
fn sheafb__read() -> Value raise {
  match read_line(stream=symval(standard_input)) {
    Some(s) => lread(s)
    None => raise LispError::SimpleError("end of file on *standard-input*")
  }
}

///|
/// CL `yes-or-no-p` / `y-or-n-p` with a format control.
fn sheafb__ask(prompt : String, args : Array[Value], long : Bool) -> Bool raise {
  while true {
    format(t, "~&", []) |> ignore
    format(t, prompt, args) |> ignore
    format(t, if long { " (yes or no) " } else { " (y or n) " }, []) |> ignore
    finish_output(stream=symval(standard_output))
    match read_line(stream=symval(standard_input)) {
      None => raise LispError::SimpleError("end of file on *standard-input*")
      Some(s) => {
        let a = string_upcase(s.trim(chars=" \t\r\n").to_owned())
        if long {
          if a == "YES" {
            return true
          }
          if a == "NO" {
            return false
          }
          format(t, "~&Please type \"yes\" for yes or \"no\" for no.", [])
          |> ignore
        } else {
          if a == "Y" || a == "YES" {
            return true
          }
          if a == "N" || a == "NO" {
            return false
          }
          format(t, "~&Please type \"y\" for yes or \"n\" for no.", [])
          |> ignore
        }
      }
    }
  }
  false
}

///|
/// `(member x l :test #'equal)` as a Bool.
fn sheafb__member_equal(x : Value, l : Value) -> Bool {
  member_equal(x, l).truthy()
}

///|
/// Destructive tail append of `x` to the list `l` (LOOP `collect into`,
/// whose variable shares structure with later collections).
fn sheafb__collect(l : Value, x : Value) -> Value {
  if l is Nil {
    list1(x)
  } else {
    nconc(l, list1(x))
  }
}

// ---------------------------------------------------------------------------
// Blowups

///|
/// Returns the I'th open of the blowup of the FIRSTK coord of ZOPEN.
fn iblowup(zopen : Value, i : Value, firstk : Value) -> Value raise {
  let ich = ichart(i, firstk, zopen_dim(zopen))
  let pss = sheafa__compose_rmap(
    sheafa__zopen_coord(ich),
    sheafa__zopen_coord(zopen),
  )
  let qss = sheafa__compose_rmap(
    sheafa__zopen_inv(zopen),
    sheafa__zopen_inv(ich),
  )
  let ineq = function_numerator(
    apply_rmap(sheafa__zopen_inv(ich), sheafa__zopen_inequality(zopen)),
  )
  let answ = copy_list(zopen)
  sheafa__set_zopen_coord(answ, pss) |> ignore
  sheafa__set_zopen_inv(answ, qss) |> ignore
  sheafa__set_zopen_inequality(answ, ineq) |> ignore
  answ
}

///|
fn s_blow(
  simp_pls : Value,
  open_number : Value,
  component_number : Value,
) -> Value raise {
  let (pls, empty_opens, codim) = normalize_pls(
    simp_pls, open_number, component_number,
  )
  sheafa__show("EMPTY-OPENS", empty_opens)
  sheafa__show("CODIM", codim)
  simplify_svar_ldata(blowup_sheaf(pls, codim, opens_not_to_blowup=empty_opens))
}

///|
fn high_dimensional_component(pls : Value) -> (Value, Value) raise {
  let mut ld_num : Value = Nil
  let mut min_open_number = 0
  let mut prev_min = 100
  let mut open_number = 0
  for lis_dat in sheafa__pls_data(pls).iter() {
    let mut ld_number = 0
    for v in lis_dat.iter() {
      let tem = length(sheafa__ldata_eqns(v))
      if tem < prev_min {
        min_open_number = open_number
        ld_num = int(ld_number)
        prev_min = tem
      }
      ld_number += 1
    }
    open_number += 1
  }
  (list2(int(min_open_number), ld_num), int(prev_min))
}

///|
/// `(vformat ...)`: the expansion `(cond (*verbose* (format t ...)) (t nil))`.
fn vformat(l : Value) -> Value raise {
  list3(
    q_cond,
    list2(q_ear_verbose, cons(q_format, cons(t, l))),
    list2(t, Nil),
  )
}

///|
/// `(vdes ...)`: the expansion `(cond (*verbose* (des ...)) (t nil))`.
fn vdes(l : Value) -> Value raise {
  list3(q_cond, list2(q_ear_verbose, cons(q_des, l)), list2(t, Nil))
}

///|
/// `(vformat t ctl args...)` inlined.
fn sheafb__vformat(ctl : String, args : Array[Value]) -> Unit raise {
  if symval(q_ear_verbose).truthy() {
    format(t, ctl, args) |> ignore
  }
}

///|
/// `(vdes x)` inlined.
fn sheafb__vdes(x : Value) -> Unit raise {
  if symval(q_ear_verbose).truthy() {
    des(x) |> ignore
  }
}

///|
fn blowup_pls_using_high_dimensional_components(
  pls : Value,
  n : Value,
  one_open? : Value = t,
  already_blown_up? : Value = Nil,
) -> Value raise {
  let mut current_pls = pls
  let mut i = n
  let mut new_pls = current_pls
  let mut red_pls = current_pls
  let mut first_time = true
  let blew_up : Array[Value] = []
  while true {
    if sheafa__pls_data(current_pls) is Nil {
      return list2(append(already_blown_up, list(blew_up)), i)
    }
    if !first_time {
      sheafb__vformat("reduced  pls:", [])
      sheafb__vdes(red_pls)
      sheafb__vformat("homogeneous simplified pls:", [])
      // If keeping more than one open the current-pls will be simplified
      // inside blowup since that way we only simplify opens blown up.
      if one_open.truthy() {
        current_pls = simplify_svar_homogeneous(current_pls)
      }
      sheafb__vdes(current_pls)
      if sheafa__pls_data(red_pls) is Nil {
        return list2(list(blew_up), i)
      }
      let (op, codim) = high_dimensional_component(red_pls)
      sheafa__show("OP", op)
      sheafa__show("CODIM", codim)
      format(
        t,
        "~%The ~A blowup: the ~A component of the ~A open of codimension ~A.",
        [i, second(op), car(op), codim],
      )
      |> ignore
      new_pls = blowup_pls(
        current_pls,
        nth(to_int(car(op)), pls_opens(red_pls)),
        sheafa__ldata_eqns(
          nth(to_int(second(op)), nth(to_int(car(op)), sheafa__pls_data(red_pls))),
        ),
        simplify_homogeneous=lbool(one_open is Nil),
      )
      blew_up.push(
        list2(
          format(
            Nil,
            "Before the ~A blowup the homogeneous equations on one of the nontrivial opens looked like :",
            [i],
          ),
          current_pls,
        ),
      )
      blew_up.push(
        list2(
          format(
            Nil,
            "~%The ~A blowup was by the ~A ldata  of the following open:",
            [i, second(op)],
          ),
          open_sub_scheme(red_pls, car(op)),
        ),
      )
    }
    first_time = false
    let mut ii = 0
    let mut found = false
    for _ope in pls_opens(new_pls).iter() {
      red_pls = simplify_svar_ldata(open_sub_scheme(new_pls, int(ii)))
      sheafa__show("II", int(ii))
      sheafa__show(
        "(LENGTH (PLS-DATA RED-PLS))",
        int(length(sheafa__pls_data(red_pls))),
      )
      format(t, "Open history: ~A", [
        sheafa__zopen_history(car(pls_opens(current_pls))),
      ])
      |> ignore
      if sheafa__pls_data(red_pls).truthy() {
        if one_open.truthy() {
          current_pls = open_sub_scheme(new_pls, int(ii))
        } else {
          current_pls = new_pls
        }
        format(t, "~%Taking the ~A open with history ", [int(ii)]) |> ignore
        found = true
        break
      } else {
        format(t, "~%The ~A open is empty", [int(ii)]) |> ignore
      }
      ii += 1
    }
    if !found {
      return append(already_blown_up, list(blew_up))
    }
    i = num_add(i, Fix(1L))
  }
  Nil
}

///|
fn eliminate_empty_and_larger_opens(pls : Value) -> Value raise {
  let paired : Array[Value] = []
  let mut dl = sheafa__pls_data(pls)
  for v in pls_opens(pls).iter() {
    if dl is Nil {
      break
    }
    let lis_dat = car(dl)
    dl = cdr(dl)
    if lis_dat.truthy() {
      paired.push(cons(v, lis_dat))
    }
  }
  let paired_dat = list(paired)
  construct_pre_ldata_sheaves(
    opens=mapcar(x => car(x), paired_dat),
    data=mapcar(x => cdr(x), paired_dat),
  )
}

///|
fn blowup_pls_using_choices(
  pls : Value,
  n : Value,
  query_user? : Value = t,
  one_open? : Value = t,
  already_blown_up? : Value = Nil,
  number_to_reduce? : Value = Fix(3L),
) -> Value raise {
  let mut current_pls = pls
  let mut choice : Value = Nil
  let mut current_op_number : Value = Nil
  let mut choices : Value = Nil
  set(q_ear_query_user, query_user) |> ignore
  let mut i = n
  let mut new_pls = current_pls
  let mut first_time = true
  let mut blew_up : Value = Nil
  while true {
    if sheafa__pls_data(current_pls) is Nil {
      return append(already_blown_up, blew_up)
    }
    if !first_time {
      if query_user is Nil {
        sheafb__vformat("Going to blowup wrt to reduced  pls:", [])
        sheafb__vformat("homogeneous simplified pls:", [])
      }
      sheafb__vdes(current_pls)
      let mut vch = choices
      let mut done = false
      while vch is Cons(_) {
        choice = car(vch)
        new_pls = Nil
        if query_user is Nil {
          format(t, "~%The ~A blowup: The coordinates and the equations", [i])
          |> ignore
          des(second(choice)) |> ignore
          des(third(choice)) |> ignore
        }
        let c = choice
        let cp = current_pls
        catch_tag(q_new_choice, () => {
          new_pls = blowup_pls(
            cp,
            second(c),
            sheafa__ldata_eqns(third(c)),
            simplify_homogeneous=t,
          )
          new_pls
        })
        |> ignore
        if new_pls.truthy() {
          new_pls = eliminate_empty_and_larger_opens(new_pls)
          done = true
          break
        }
        vch = cdr(vch)
      }
      if !done {
        fsignal(list1(Str("Ran out of choices"))) |> ignore
      }
      blew_up = sheafb__collect(
        blew_up,
        list3(
          format(
            Nil,
            "~%The ~A blowup was by equations on the ~A open :",
            [i, current_op_number],
          ),
          second(choice),
          third(choice),
        ),
      )
      blew_up = sheafb__collect(
        blew_up,
        list2(
          format(
            Nil,
            "After the ~A blowup the homogeneous equations on one of the nontrivial opens looked like :",
            [i],
          ),
          new_pls,
        ),
      )
      set(q_ear_blew_up, blew_up) |> ignore
    }
    set(
      q_ear_previous_blowups,
      cons(symval(q_ear_blew_up), symval(q_ear_previous_blowups)),
    )
    |> ignore
    set(q_ear_blew_up, blew_up) |> ignore
    first_time = false
    choices = provide_some_choices_to_blowup(
      new_pls,
      query_user~,
      number_to_reduce~,
    )
    if choices is Nil {
      return append(already_blown_up, blew_up)
    }
    choice = car(choices)
    let mut op_num = 0
    for op in pls_opens(new_pls).iter() {
      current_op_number = int(op_num)
      if zopen_special_subset(second(choice), op).truthy() {
        break
      }
      op_num += 1
    }
    if one_open.truthy() {
      current_pls = open_sub_scheme(new_pls, current_op_number)
    } else {
      current_pls = new_pls
    }
    i = num_add(i, Fix(1L))
  }
  Nil
}

///|
fn restart_blowup(
  part? : Value = Nil,
  use_blewup? : Value = Nil,
  one_open? : Value = Nil,
  query_user? : Value = Nil,
  after? : Value = Fix(0L),
  number_to_reduce? : Value = Fix(3L),
) -> Value raise {
  if part.truthy() {
    let pls = second(part)
    blowup_pls_using_choices(
      pls,
      after,
      query_user~,
      one_open~,
      already_blown_up=list1(part),
      number_to_reduce~,
    )
  } else if use_blewup.truthy() {
    let blew = symval(q_ear_blew_up)
    let las = nth(length(blew) - 1, blew)
    let blas = nth(length(blew) - 2, blew)
    let n = int(length(blew) / 2)
    let pls = if string_upcase(lstring(car(las))).contains("AFTER") {
      second(las)
    } else {
      set(q_ear_blew_up, butlast(symval(q_ear_blew_up))) |> ignore
      second(blas)
    }
    blowup_pls_using_choices(
      pls,
      n,
      query_user~,
      one_open~,
      number_to_reduce~,
      already_blown_up=symval(q_ear_blew_up),
    )
  } else {
    Nil
  }
}

///|
fn gen_pcomplexity(lis : Value) -> Value raise {
  if lis is Nil {
    Fix(0L)
  } else if affine_polynomialp(lis).truthy() {
    pcomplexity(lis)
  } else if rational_functionp(lis).truthy() {
    num_add(pcomplexity(car(lis)), pcomplexity(cdr(lis)))
  } else if listp(lis) {
    let mut sum : Value = Fix(0L)
    for v in lis.iter() {
      sum = num_add(sum, gen_pcomplexity(v))
    }
    sum
  } else {
    merr("don't know how complex", [])
  }
}

///|
/// Returns an ordered list of choices..
fn provide_some_choices_to_blowup(
  new_pls : Value,
  query_user? : Value = t,
  number_to_reduce? : Value = Fix(3L),
) -> Value raise {
  let mut choices : Value = Nil
  let mut check_the_worst = t
  let mut opens_not_to_try : Value = Nil
  let mut opens_to_try : Value = Nil
  if query_user is Nil ||
    sheafb__ask(" Simplify and provide choices of open and equation ", [], true) {
    let tem : Array[Value] = []
    let tem1 : Array[Value] = []
    let mut the_min1 : Value = Fix(0L)
    let mut the_max1 : Value = Fix(0L)
    let mut min_pcomp1 : Value = Fix(0L)
    let mut max_pcomp1 : Value = Fix(0L)
    let mut first = true
    for lis_ld in sheafa__pls_data(new_pls).iter() {
      if lis_ld.truthy() {
        let len = int(length(sheafa__ldata_eqns(car(lis_ld))))
        tem.push(len)
        let pcomp = gen_pcomplexity(sheafa__ldata_eqns(car(lis_ld)))
        tem1.push(pcomp)
        if first {
          the_min1 = len
          the_max1 = len
          min_pcomp1 = pcomp
          max_pcomp1 = pcomp
          first = false
        } else {
          if num_lt(len, the_min1) {
            the_min1 = len
          }
          if num_gt(len, the_max1) {
            the_max1 = len
          }
          if num_lt(pcomp, min_pcomp1) {
            min_pcomp1 = pcomp
          }
          if num_gt(pcomp, max_pcomp1) {
            max_pcomp1 = pcomp
          }
        }
      } else {
        tem.push(Fix(0L))
        tem1.push(Fix(0L))
      }
    }
    let the_min = the_min1
    let number_eqns = list(tem)
    let comp_eqns = list(tem1)
    let the_max = the_max1
    let min_comp : Value = Nil
    ignore(min_pcomp1)
    let _where_complex = find_position_in_list(max_pcomp1, comp_eqns)
    sheafb__vformat(
      "%The number of equations are ~A and their complexity is ~A",
      [number_eqns, comp_eqns],
    )
    let where_the_max = find_position_in_list(the_max, number_eqns)
    {
      let mut ws = comp_eqns
      let mut lds = sheafa__pls_data(new_pls)
      let mut ops = pls_opens(new_pls)
      let mut i = 0
      for v in number_eqns.iter() {
        if ws is Nil || lds is Nil || ops is Nil {
          break
        }
        let w = car(ws)
        let lis_ld = car(lds)
        let op = car(ops)
        if !zerop(v) {
          format(
            t,
            "~%On open ~A there are ~A equations of complexity ~A .",
            [int(i), v, w],
          )
          |> ignore
        }
        if equal(v, the_min) {
          choices = cons(
            list3(format(Nil, "Least homogeneous equations", []), op, car(lis_ld)),
            choices,
          )
        }
        if eql(w, min_comp) {
          choices = cons(
            list3(format(Nil, "Least complex equations", []), op, car(lis_ld)),
            choices,
          )
        }
        ws = cdr(ws)
        lds = cdr(lds)
        ops = cdr(ops)
        i += 1
      }
    }
    if query_user.truthy() {
      check_the_worst = user_supply1(sheafb__q_check_the_worst, check_the_worst)
    }
    if query_user.truthy() {
      opens_not_to_try = user_supply1(
        sheafb__q_opens_not_to_try, opens_not_to_try,
      )
      opens_to_try = user_supply1(sheafb__q_opens_to_try, opens_to_try)
    }
    let mut some_red : Value = Nil
    let some_red_pls = {
      let mut ii = 0
      for op in pls_opens(new_pls).iter() {
        let iiv = int(ii)
        if !sheafb__member_equal(iiv, opens_not_to_try) &&
          (
            num_lt(int(length(some_red)), number_to_reduce) ||
            sheafb__member_equal(iiv, opens_to_try)
          ) {
          opens_not_to_try = cons(iiv, opens_not_to_try)
          format(t, "~%Reducing the ~A open", [iiv]) |> ignore
          sheafa__show("II", iiv)
          sheafa__show("OPENS-NOT-TO-TRY", opens_not_to_try)
          sheafa__show(
            "(MEMBER II OPENS-NOT-TO-TRY :TEST #'EQUAL)",
            member_equal(iiv, opens_not_to_try),
          )
          sheafa__show(
            "(NULL (MEMBER II OPENS-NOT-TO-TRY :TEST #'EQUAL))",
            lbool(member_equal(iiv, opens_not_to_try) is Nil),
          )
          let red_pls = simplify_svar_ldata(open_sub_scheme(new_pls, iiv))
          sheafa__set_zopen_history(
            op,
            cons(car(make_component_history(red_pls)), sheafa__zopen_history(op)),
          )
          |> ignore
          if sheafa__pls_data(red_pls) is Nil {
            sheafb__setf_nth(ii, sheafa__pls_data(new_pls), Nil) |> ignore
          } else {
            some_red = sheafb__collect(some_red, red_pls)
          }
        }
        ii += 1
      }
      sheafa__show("THE-MAX", the_max)
      sheafa__show("OPENS-NOT-TO-TRY", opens_not_to_try)
      sheafa__show("WHERE-THE-MAX", where_the_max)
      if check_the_worst.truthy() {
        // (mem where-the-max opens-not-to-try :test #'eq): MEM is undefined.
        sheafb__undefined("MEM") |> ignore
        cons(
          simplify_svar_ldata(open_sub_scheme(new_pls, where_the_max)),
          some_red,
        )
      } else {
        some_red
      }
    }
    let red_choices : Array[Value] = []
    for red_pls in some_red_pls.iter() {
      let mut ops = pls_opens(red_pls)
      for lis_ld in sheafa__pls_data(red_pls).iter() {
        if ops is Nil {
          break
        }
        let op = car(ops)
        ops = cdr(ops)
        for ld in lis_ld.iter() {
          red_choices.push(list3(Str("Reduced ld"), op, ld))
        }
      }
    }
    let red_choices = sort_list(list(red_choices), (u, v) => {
      order_ldata(third(u), third(v)).truthy()
    })
    choices = append(red_choices, choices)
    set(
      q_ear_reduced_history,
      cons(some_red_pls, symval(q_ear_reduced_history)),
    )
    |> ignore
    if query_user.truthy() {
      while sheafb__ask("Show the reduced pls's?", [], true) {
        des(some_red_pls) |> ignore
      }
    }
    if query_user.truthy() {
      let mut i = 0
      for v in choices.iter() {
        if !sheafb__ask("show next?", [], false) {
          break
        }
        format(t, "~3% Number**** ~A :", [int(i)]) |> ignore
        sheafa__show("(LENGTH V)", int(length(v)))
        for ww in v.iter() {
          des(ww) |> ignore
        }
        i += 1
      }
      while true {
        format(t, "~%Type the number of the  one do you want:", []) |> ignore
        let n = sheafb__read()
        if !(numberp(n) && num_lt(n, int(length(choices)))) {
          ()
        } else {
          des(nth(to_int(n), choices)) |> ignore
          if sheafb__ask("~%Choosing this one?", [], true) {
            return cons(nth(to_int(n), choices), delete_nth(n, choices))
          }
        }
      }
      Nil
    } else {
      choices
    }
  } else {
    let mut a_red_pls : Value = Nil
    let mut an_open_number : Value = Nil
    let mut component_number : Value = Nil
    while true {
      format(
        t,
        "enter a form to evaluate giving (list nil open ldata-to-blowup) or T to enter pls and component numbers: ",
        [],
      )
      |> ignore
      let mut answ = lisp_eval_form(sheafb__read())
      if atom(answ) {
        a_red_pls = user_supply1(sheafb__q_a_red_pls, a_red_pls)
        an_open_number = user_supply1(sheafb__q_an_open_number, an_open_number)
        component_number = user_supply1(
          sheafb__q_component_number, component_number,
        )
        answ = list3(
          Nil,
          nth(to_int(an_open_number), pls_opens(a_red_pls)),
          nth(
            to_int(component_number),
            nth(to_int(an_open_number), sheafa__pls_data(a_red_pls)),
          ),
        )
      }
      sheafb__iassert(
        eq(car(second(answ)), q_zopen),
        "(AND (EQ (CAR (SECOND ANSW)) 'ZOPEN))",
      )
      sheafb__iassert(
        eq(car(third(answ)), q_ldata),
        "(AND (EQ (CAR (THIRD ANSW)) 'LDATA))",
      )
      des(answ) |> ignore
      if sheafb__ask("Use it?", [], false) {
        return list1(answ)
      }
    }
    Nil
  }
}

///|
fn sort_the_reduced_history(some_red_pls : Value) -> Value raise {
  let red_choices : Array[Value] = []
  for red_pls in some_red_pls.iter() {
    let mut ops = pls_opens(red_pls)
    for lis_ld in sheafa__pls_data(red_pls).iter() {
      if ops is Nil {
        break
      }
      let op = car(ops)
      ops = cdr(ops)
      for ld in lis_ld.iter() {
        red_choices.push(list3(Str("Reduced ld"), op, ld))
      }
    }
  }
  sort_list(list(red_choices), (u, v) => order_ldata(third(u), third(v)).truthy())
}

///|
fn order_ldata(u : Value, v : Value) -> Value raise {
  let lu = length(sheafa__ldata_eqns(u))
  let lv = length(sheafa__ldata_eqns(v))
  if lu < lv {
    t
  } else if lu == lv {
    lbool(
      num_lt(
        gen_pcomplexity(sheafa__ldata_eqns(u)),
        gen_pcomplexity(sheafa__ldata_eqns(v)),
      ),
    )
  } else {
    Nil
  }
}

///|
/// Performs the transform of an ldata into new equations on the ITH blowup
/// of the FIRSTK coordinates of AMBIENT-DIM space.
fn proper_transform(
  ld : Value,
  ith : Value,
  firstk : Value,
  ambient_dim : Value,
) -> Value raise {
  let ich = ichart(ith, firstk, ambient_dim)
  let ld = copy_list(ld)
  let trans = apply_rmap(sheafa__zopen_inv(ich), ld)
  format(t, "~%Exceptional divisor is ", []) |> ignore
  sheafb__fsh(xxx(ith))
  format(t, ".", []) |> ignore
  let answ = cdr(
    eliminate_common_factors(
      cons(pexpt(xxx(ith), Fix(10L)), sheafa__ldata_eqns(trans)),
    ),
  )
  sheafa__set_ldata_eqns(trans, answ) |> ignore
  trans
}

///|
fn blowup_sheaf(
  pls : Value,
  firstk : Value,
  opens_not_to_blowup? : Value = Nil,
  opens_to_blowup? : Value = Nil,
  simplify_homogeneous? : Value = Nil,
  add_exceptional_divisor_ldata? : Value = Nil,
  keep_history? : Value = t,
) -> Value raise {
  let pls = copy_list_structure(pls)
  let svar = sheafa__pls_s_var(pls)
  let data = sheafa__pls_data(pls)
  let opens = sheafa__sv_zopens(svar)
  let dim = zopen_dim(car(pls_opens(pls)))
  let paired : Array[Value] = []
  let mut dls = data
  let mut ii = 0
  for op in opens.iter() {
    if dls is Nil {
      break
    }
    let mut dl = car(dls)
    dls = cdr(dls)
    des(dl) |> ignore
    let iiv = int(ii)
    if (opens_to_blowup is Nil && member(iiv, opens_not_to_blowup) is Nil) ||
      member(iiv, opens_to_blowup).truthy() {
      format(t, "~%Blowing up open number ~A ", [iiv]) |> ignore
      let k = to_int(firstk)
      for i in 1..=k {
        let iv = int(i)
        let tem = iblowup(op, iv, firstk)
        let pts : Array[Value] = []
        for ldat in dl.iter() {
          sheafb__iassert(ldatap(ldat).truthy(), "(LDATAP LDAT)")
          pts.push(proper_transform(ldat, iv, firstk, dim))
        }
        let mut pt = list(pts)
        sheafb__iassert(eq(car(tem), q_zopen), "(EQ (CAR TEM) 'ZOPEN)")
        sheafa__set_zopen_history(
          tem,
          cons(xxx(iv), sheafa__zopen_history(tem)),
        )
        |> ignore
        if simplify_homogeneous.truthy() {
          let acc : Array[Value] = []
          for v in pt.iter() {
            for x in ldata_simplify_homogeneous(
                v,
                may_invert=sheafa__zopen_inequality(tem),
              ).iter() {
              acc.push(x)
            }
          }
          pt = list(acc)
        }
        if add_exceptional_divisor_ldata.truthy() {
          pt = append(pt, list1(sheafa__make_ldata(eqns=list1(xxx(iv)))))
        }
        paired.push(cons(tem, pt))
      }
    } else {
      if add_exceptional_divisor_ldata.truthy() {
        dl = append(dl, list1(sheafa__make_ldata(eqns=list1(Fix(1L)))))
      }
      paired.push(cons(op, dl))
    }
    ii += 1
  }
  let paired_data = list(paired)
  let answ = sheafa__make_pls(
    s_var=sheafa__make_s_var(zopens=mapcar(x => car(x), paired_data)),
    data=mapcar(x => cdr(x), paired_data),
  )
  if keep_history.truthy() {
    add_pls_zopen_history(answ) |> ignore
  }
  answ
}

///|
fn linear_poly_solve(poly : Value, var_ : Value) -> Value raise {
  ratreduce(
    pminus(pcoeff(poly, Fix(1L), variables_to_exclude_from_cof=list1(var_))),
    pcoeff(poly, list3(var_, Fix(1L), Fix(1L))),
  )
}

///|
fn unused_variables(n : Value, strin? : Value = Nil) -> Value raise {
  // The CL name of the new variable is "$<strin>NEW<i>" with STRIN in CL
  // case; the port name is its case inversion.
  let cl_strin = if strin.truthy() {
    let s = match strin {
      Str(s) => s
      Sym(_) => invert_case(symbol_name(strin))
      _ => lstring(string(strin))
    }
    s + "NEW"
  } else {
    "NEW"
  }
  let res : Array[Value] = []
  let k = to_int(n)
  for i in 1..=k {
    let cl_name = "$" + cl_strin + i.to_string()
    res.push(add_newvar(Sym(intern(invert_case(cl_name)))).0)
  }
  list(res)
}

///|
/// Argument may be list of polys, or rat'l fns, result is always rat'l.
fn apply_rmap(
  rmap : Value,
  fns : Value,
  coords_for_fn? : Value,
  subs? : Value = Nil,
) -> Value raise {
  let coords_for_fn = match coords_for_fn {
    Some(c) => c
    None => symval(q_ear_xxx)
  }
  let mut rmap = rmap
  // (new-rmap rmap)
  if new_rmap_p(rmap) is Nil {
    format(t, "~%Converting an rmap", []) |> ignore
    rmap = convert_rmap_to_new(rmap)
  }
  let subs = if subs.truthy() {
    subs
  } else {
    subs_for_simple_rat_sublis(coords_for_fn, sheafa__rmap_fns(rmap))
  }
  if affine_polynomialp(fns).truthy() || rational_functionp(fns).truthy() {
    let answ = simple_rat_sublis(subs, fns)
    // (process-sleep 5): PROCESS-SLEEP is undefined.
    sheafb__undefined("PROCESS-SLEEP") |> ignore
    answ
  } else if eq(car(fns), q_ldata) {
    let eqns = mapcar(
      v => function_numerator(apply_rmap(rmap, v, coords_for_fn~, subs~)),
      sheafa__ldata_eqns(fns),
    )
    let ineq = function_numerator(
      apply_rmap(rmap, sheafa__ldata_inequality(fns), coords_for_fn~, subs~),
    )
    sheafa__make_ldata(eqns~, inequality=ineq)
  } else if affine_polynomialp(car(fns)).truthy() ||
    rational_functionp(car(fns)).truthy() ||
    ldatap(car(fns)).truthy() {
    mapcar(v => apply_rmap(rmap, v, coords_for_fn~, subs~), fns)
  } else {
    merr("fns should be a polynomial, rat'l fn,ldata or list of such", [])
  }
}

///|
fn ldatap(obj : Value) -> Value raise {
  lbool(consp(obj) && eq(car(obj), q_ldata))
}

///|
/// Takes as arguments a list of polys or rat'l fns and tries to make these
/// into the first coordinates.  It tries to find the inverse, and checks
/// whether it has found the inverse.
fn make_normal_zopen(eqns : Value, dim : Value, gg : Value) -> Value raise {
  let check_inverse = true
  let newvar = unused_variables(dim)
  let dif : Array[Value] = []
  {
    let mut us = newvar
    for v in eqns.iter() {
      if us is Nil {
        break
      }
      dif.push(function_numerator(n__(v, list3(car(us), Fix(1L), Fix(1L)))))
      us = cdr(us)
    }
  }
  let dif_eqns = list(dif)
  let mut variables = linear_ldatap(
    sheafa__make_ldata(eqns~),
    open_g=gg,
  )
  if variables is Nil {
    let vs : Array[Value] = []
    for v in dif_eqns.iter() {
      let tem = any_linearp(v, gg, variables_to_exclude=newvar)
      vs.push(tem)
      if tem is Nil {
        merr("this equation contains no linear ~M", [v]) |> ignore
      }
    }
    variables = list(vs)
  }
  let others : Array[Value] = []
  {
    let mut i = 0
    let d = to_int(dim)
    for v in symval(q_ear_xxx).iter() {
      if i >= d {
        break
      }
      if memq(v, variables) is Nil {
        others.push(v)
      }
      i += 1
    }
  }
  let other_variables = list(others)
  let all_variables = append(variables, other_variables)
  let other_monoms = mapcar(v => list3(v, Fix(1L), Fix(1L)), other_variables)
  let coords = append(eqns, other_monoms)
  let ce : Array[Value] = []
  {
    let mut us = newvar
    for v in coords.iter() {
      if us is Nil {
        break
      }
      ce.push(function_numerator(n__(v, list3(car(us), Fix(1L), Fix(1L)))))
      us = cdr(us)
    }
  }
  let coord_eqns = list(ce)
  let mut solu = solve_simple_system(
    mapcar(x => function_numerator(x), coord_eqns),
    all_variables,
    invertible=gg,
  )
  solu = gen_psublis(newvar, symval(q_ear_xxx), solu)
  let fs : Array[Value] = []
  {
    let mut fl = solu
    for v in all_variables.iter() {
      if fl is Nil {
        break
      }
      fs.push(
        nth(to_int(find_position_in_list(v, symval(q_ear_xxx))), solu),
      )
      fl = cdr(fl)
    }
  }
  let fns = list(fs)
  {
    let mut fl = solu
    for v in all_variables.iter() {
      if fl is Nil {
        break
      }
      let f = car(fl)
      fl = cdr(fl)
      sheafb__setf_nth(
        to_int(find_position_in_list(v, symval(q_ear_xxx))),
        fns,
        f,
      )
      |> ignore
    }
  }
  let answ = sheafa__make_zopen(
    coord=construct_rmap(coords),
    inv=construct_rmap(fns),
    inequality=gg,
  )
  if check_inverse {
    check_zopen_inv(answ) |> ignore
  }
  answ
}

///|
fn check_zopen_inv(zopen : Value) -> Value raise {
  let ma = sheafa__compose_rmap(
    sheafa__zopen_inv(zopen),
    sheafa__zopen_coord(zopen),
  )
  let mut us = symval(q_ear_xxx)
  for v in sheafa__rmap_fns(ma).iter() {
    if us is Nil {
      break
    }
    if !eql(car(car(v)), car(us)) {
      return merr("not the inverse", [])
    }
    us = cdr(us)
  }
  q_ok
}

///|
fn solve_simple_system(
  eqns : Value,
  variables : Value,
  invertible? : Value = Fix(1L),
) -> Value raise {
  let mut used_up : Value = Nil
  let mut all = copy_list(eqns)
  while all.truthy() {
    let v = car(all)
    let tem = any_linearp(v, invertible, among_variables=variables)
    if tem.truthy() {
      all = replace_functions(all, v, tem, invertible_g=invertible)
      used_up = cons(
        v,
        replace_functions(used_up, v, tem, invertible_g=invertible),
      )
    }
  }
  let simpl_eqns = append(used_up, all)
  mapcar(
    v => {
      for w in simpl_eqns.iter() {
        if eql(pdegree(w, v), Fix(1L)) {
          return linear_poly_solve(w, v)
        }
      }
      Nil
    },
    variables,
  )
}

///|
fn normalize_zopen(
  zopen : Value,
  eqns : Value,
  inequality? : Value = Nil,
  data? : Value = Nil,
) -> (Value, Value) raise {
  let inequality = if inequality is Nil {
    sheafa__zopen_inequality(zopen)
  } else {
    inequality
  }
  let op = make_normal_zopen(eqns, zopen_dim(zopen), inequality)
  let answ = copy_list(zopen)
  sheafa__set_zopen_coord(
    answ,
    sheafa__compose_rmap(sheafa__zopen_coord(op), sheafa__zopen_coord(zopen)),
  )
  |> ignore
  sheafa__set_zopen_inv(
    answ,
    sheafa__compose_rmap(sheafa__zopen_inv(zopen), sheafa__zopen_inv(op)),
  )
  |> ignore
  sheafa__set_zopen_inequality(
    answ,
    function_numerator(apply_rmap(sheafa__zopen_inv(op), inequality)),
  )
  |> ignore
  let data = if data.truthy() {
    apply_rmap(sheafa__zopen_inv(op), data)
  } else {
    data
  }
  (answ, data)
}

///|
fn normalize_zopen_in_pls(
  pls : Value,
  zopen_number : Value,
  eqns : Value,
  copy_? : Value = Nil,
) -> Value raise {
  let pls = if copy_.truthy() {
    copy_tree(pls)
  } else {
    copy_list_structure(pls)
  }
  let opens = pls_opens(pls)
  let k = to_int(zopen_number)
  let open_ = nth(k, opens)
  let lis_dat = nth(k, sheafa__pls_data(pls))
  let new_open = normalize_zopen(open_, eqns).0
  let mapl = find_ring_map(open_, new_open)
  sheafb__setf_nth(k, opens, new_open) |> ignore
  sheafb__setf_nth(k, sheafa__pls_data(pls), apply_rmap(mapl, lis_dat))
  |> ignore
  pls
}

///|
fn copy_list_structure(expr : Value) -> Value raise {
  if atom(expr) {
    expr
  } else {
    let h = car(expr)
    if eq(h, q_zopens) ||
      eq(h, q_pre_ldata_sheaves) ||
      eq(h, q_rmap) ||
      eq(h, q_s_var) ||
      eq(h, q_ldata) {
      copy_list(expr)
    } else {
      // (loop for v on expr do (setf (car v) ...)) returns NIL.
      let mut v = expr
      while v is Cons(_) {
        setf_car(v, copy_list_structure(car(v))) |> ignore
        v = cdr(v)
      }
      Nil
    }
  }
}

///|
/// Should return an open cover such that the functions are all linear.
fn best_open_cover(list_fns : Value, open_g : Value) -> Value raise {
  if all_linearp(list_fns, inequal=open_g).truthy() {
    list1(open_g)
  } else {
    let pf : Array[Value] = []
    for v in list_fns.iter() {
      if gm_prepared(v, inequal=open_g).truthy() {
        pf.push(v)
      }
    }
    let prep_fns = list(pf)
    if length(prep_fns) == 1 {
      best_open_cover1(prep_fns, open_g)
    } else {
      let possible : Array[Value] = []
      let mut min = 0
      let mut first = true
      for v in prep_fns.iter() {
        sheafa__show("V", v)
        let tem = best_open_cover1(list1(v), open_g)
        let acc : Array[Value] = []
        for gg in tem.iter() {
          for x in best_open_cover(
              remove_equal(v, copy_list(prep_fns)),
              sftimes(open_g, gg),
            ).iter() {
            acc.push(x)
          }
        }
        let mut inv_list = list(acc)
        sheafa__show("INV-LIST", inv_list)
        inv_list = eliminate_multiples(inv_list)
        possible.push(inv_list)
        let l = length(inv_list)
        if first || l < min {
          min = l
        }
        first = false
        sheafa__show("MIN", int(min))
      }
      for v in possible {
        if length(v) == min {
          return v
        }
      }
      Nil
    }
  }
}

///|
fn eliminate_multiples(list_fns : Value, square_free? : Value = t) -> Value raise {
  let fs : Array[Value] = []
  for v in list_fns.iter() {
    let tem = non_constant_factors(v)
    fs.push(tem)
    if square_free.truthy() {
      let mut w = tem
      while w is Cons(_) {
        setf_car(cdr(w), Fix(1L)) |> ignore
        w = cddr(w)
      }
    }
  }
  mapcar(
    x => multiply_out_factorization(x),
    eliminate_larger(list(fs), test_=q_a_factor),
  )
}

///|
/// This works for a list of one function..
fn best_open_cover1(list_fns : Value, open_g : Value) -> Value raise {
  let pf : Array[Value] = []
  for f in list_fns.iter() {
    if any_linearp(f, open_g).truthy() {
      ()
    } else {
      pf.push(f)
    }
  }
  let prep_fns = list(pf)
  let the_prep_fns = prep_fns
  let lis_prep_var = mapcar(
    f => subst(Nil, q_ok, gm_all_prepared(f, inequal=open_g)),
    prep_fns,
  )
  let lpc : Array[Value] = []
  {
    let mut lises = lis_prep_var
    for f in prep_fns.iter() {
      if lises is Nil {
        break
      }
      let lis = car(lises)
      lises = cdr(lises)
      lpc.push(
        mapcar(
          varl => mapcar(
            v => {
              let tem = non_constant_factors(
                pcoeff(f, list3(v, Fix(1L), Fix(1L))),
              )
              let mut w = tem
              while w is Cons(_) {
                setf_car(cdr(w), Fix(1L)) |> ignore
                w = cddr(w)
              }
              tem
            },
            varl,
          ),
          lis,
        ),
      )
    }
  }
  let lis_prep_cofs = list(lpc)
  let possible_refs = all_perms(lis_prep_cofs)
  let mut answ : Value = Nil
  let facts_a : Array[Value] = []
  let mut tem : Value = Nil
  let mut min = 0
  let mut first = true
  for v in possible_refs.iter() {
    tem = eliminate_larger(v, test_=q_a_factor)
    facts_a.push(tem)
    let l = length(tem)
    if first || l < min {
      min = l
    }
    first = false
  }
  let facts = list(facts_a)
  let mut compl_tem : Value = Nil
  let mut min_compl : Value = Fix(0L)
  let mut first_c = true
  let mut i = 0
  for v in facts.iter() {
    if length(v) == min {
      compl_tem = cons(int(i), gen_pcomplexity(tem))
      if first_c || num_lt(cdr(compl_tem), min_compl) {
        min_compl = cdr(compl_tem)
      }
      first_c = false
    }
    i += 1
  }
  // (loop for v in compl-tem ...): COMPL-TEM is a dotted pair, so the loop
  // either returns at its first element or fails on the non-list cdr.
  if compl_tem is Cons(_) {
    if eq(cdr(compl_tem), min_compl) {
      answ = nth(to_int(car(compl_tem)), facts)
    } else {
      raise LispError::SimpleError(
        format_to_string("The value ~S is not of type LIST", [cdr(compl_tem)]),
      )
    }
  }
  mapcar(
    w => nplcm(open_g, w),
    append(the_prep_fns, mapcar(x => multiply_out_factorization(x), answ)),
  )
}

///|
fn all_perms(list_lists : Value) -> Value raise {
  if length(list_lists) == 1 {
    car(list_lists)
  } else {
    let acc : Array[Value] = []
    for v in car(list_lists).iter() {
      for w in all_perms(cdr(list_lists)).iter() {
        acc.push(append(v, w))
      }
    }
    list(acc)
  }
}

///|
/// Will return m+1 opens covering the zopen.  It is gm-prepared wrt the
/// inequality g of zopen.
fn open_refinement(zopen : Value, gmprep_poly : Value, m : Value) -> Value raise {
  let gg = sheafa__zopen_inequality(zopen)
  let vari = gm_prepared(gmprep_poly, m~, inequal=gg)
  sheafb__check_arg(eq(car(zopen), q_zopen), "a zopen")
  sheafb__check_arg(affine_polynomialp(gmprep_poly).truthy(), "poly")
  let cofs = mapcar(v => pcoeff(gmprep_poly, list3(v, Fix(1L), Fix(1L))), vari)
  let mzopens = mapcar(
    cof => {
      let ans = copy_list(zopen)
      sheafa__set_zopen_inequality(ans, nplcm(cof, gg)) |> ignore
      sheafa__set_zopen_coord(ans, sheafa__zopen_coord(zopen)) |> ignore
      sheafa__set_zopen_inv(ans, sheafa__zopen_inv(zopen)) |> ignore
      ans
    },
    cofs,
  )
  let next_open = copy_list(zopen)
  sheafa__set_zopen_inequality(next_open, nplcm(gg, gmprep_poly)) |> ignore
  cons(next_open, mzopens)
}

///|
/// Will return m ldata covering the ldata.  The open-gs can be used as the
/// open number for the simplification.
fn ldata_refinement(
  ldata : Value,
  gmprep_poly : Value,
  m : Value,
  inequality? : Value = Fix(1L),
) -> (Value, Value) raise {
  let vari = gm_prepared(gmprep_poly, m~, inequal=inequality)
  sheafb__check_arg(affine_polynomialp(gmprep_poly).truthy(), "poly")
  let mut cofs = mapcar(
    v => pcoeff(gmprep_poly, list3(v, Fix(1L), Fix(1L))),
    vari,
  )
  eliminate_multiples(cofs) |> ignore
  cofs = mapcar(x => square_free(x), cofs)
  let all_ldata = mapcar(
    cof => {
      let ans = copy_list(ldata)
      sheafa__set_ldata_inequality(
        ans,
        nplcm(cof, sheafa__ldata_inequality(ldata)),
      )
      |> ignore
      ans
    },
    cofs,
  )
  (all_ldata, cofs)
}

///|
/// Takes a pre-ldata-sheaves and simplifies it.  This may involve adding
/// more opens if we meet m-prepared's in the ldata; it returns a
/// pre-ldata-sheaves.
fn simplify_svar_ldata(
  pls : Value,
  keep_opens_with_empty_ldata? : Value = Nil,
  check_containment? : Value = t,
  set_ldata_inequalities_to_one? : Value = t,
  refine_opens? : Value = t,
  keep_history? : Value = t,
  opens_not_to_simplify? : Value = Nil,
) -> Value raise {
  let b = bind(q_ear_refine_opens, refine_opens)
  defer unbind(b)
  let pls = copy_list_structure(pls)
  let opens_not_to_simplify = mapcar(
    i => nth(to_int(i), pls_opens(pls)),
    opens_not_to_simplify,
  )
  let svar = sheafa__pls_s_var(pls)
  let data = sheafa__pls_data(pls)
  let answ = with_special(q_ear_inside_simplify_svar_ldata, t, () => {
    let al : Array[Value] = []
    {
      let mut dls = data
      for op in sheafa__sv_zopens(svar).iter() {
        if dls is Nil {
          break
        }
        al.push(cons(op, car(dls)))
        dls = cdr(dls)
      }
    }
    let a_list = list(al)
    let mut simped_ld : Value = Nil
    let opens : Array[Value] = []
    let ldata_list : Array[Value] = []
    let mut v = a_list
    while v is Cons(_) {
      let w = car(v)
      format(t, "~%Open Number : ~A", [
        find_position_in_list(car(w), pls_opens(pls)),
      ])
      |> ignore
      let gg = sheafa__zopen_inequality(car(w))
      set(q_ear_stop_simplify, Nil) |> ignore
      if !sheafb__member_equal(car(w), opens_not_to_simplify) {
        let mut tem : Value = Nil
        let mut stopped = false
        let mut ld = cdr(w)
        while ld is Cons(_) {
          let some_ld = ldata_simplifications(car(ld), open_g=gg)
          tem = append(tem, copy_list(some_ld))
          if symval(q_ear_stop_simplify).truthy() {
            let stop = symval(q_ear_stop_simplify)
            sheafa__show("*STOP-SIMPLIFY*", stop)
            // Set v so that (cdr v) will be the rest of the pairs
            // (zopen . (list ldata1 ldata2..)).
            let refs = open_refinement(car(w), car(stop), second(stop))
            format(
              t,
              "~%Refining open number ~D into ~D opens with inequalities ",
              [find_position_in_list(car(w), pls_opens(pls)), int(length(refs))],
            )
            |> ignore
            sheafb__fsh(mapcar(r => sheafa__zopen_inequality(r), refs))
            sheafb__iassert(
              symval(q_ear_refine_opens).truthy(),
              "(NOT (NULL *REFINE-OPENS*))",
            )
            for vv in tem.iter() {
              sheafb__check_arg(eq(car(vv), q_ldata), "an ldata")
            }
            let rest = cdr(ld)
            let t2 = tem
            v = cons(
              Nil,
              append(
                mapcar(
                  open_ => cons(open_, copy_tree(append(t2, rest))),
                  refs,
                ),
                cdr(v),
              ),
            )
            stopped = true
            break
          }
          ld = cdr(ld)
        }
        if !stopped {
          simped_ld = delete_redundant_ldata(
            tem,
            ignore_ldata_inequalities=t,
            gg=sheafa__zopen_inequality(car(w)),
          )
        }
        sheafa__show("(LENGTH V)", int(length(v)))
      } else {
        simped_ld = cdr(w)
      }
      if symval(q_ear_stop_simplify) is Nil &&
        (
          sheafb__member_equal(car(w), opens_not_to_simplify) ||
          keep_opens_with_empty_ldata.truthy() ||
          simped_ld.truthy()
        ) {
        if simped_ld.truthy() {
          simped_ld = delete_redundant_ldata(
            simped_ld,
            gg=sheafa__zopen_inequality(car(w)),
          )
          if check_containment.truthy() {
            check_component_containment(
              cdr(w),
              simped_ld,
              open_g=sheafa__zopen_inequality(car(w)),
            )
            |> ignore
          }
        }
        opens.push(car(w))
        ldata_list.push(simped_ld)
      }
      v = cdr(v)
    }
    sheafa__make_pls(
      s_var=sheafa__make_s_var(zopens=list(opens)),
      data=list(ldata_list),
    )
  })
  if set_ldata_inequalities_to_one.truthy() {
    set_inequalities_to_one(answ) |> ignore
  }
  if keep_history.truthy() {
    add_pls_zopen_history(answ) |> ignore
  }
  answ
}

///|
/// `(desn x)`: the expansion `(let (*give-coordinates*) (des x))`.
fn desn(x : Value) -> Value raise {
  list3(q_let, list1(q_ear_give_coordinates), list2(q_des, x))
}

///|
fn set_inequalities_to_one(form : Value) -> Value raise {
  if form is Nil {
    Nil
  } else if atom(form) {
    form
  } else if eq(car(form), q_ldata) {
    sheafa__set_ldata_inequality(form, Fix(1L)) |> ignore
    form
  } else {
    let mut r = form
    while r is Cons(_) {
      setf_car(r, set_inequalities_to_one(car(r))) |> ignore
      r = cdr(r)
    }
    form
  }
}

///|
fn check_component_containment(
  orig_ldata_list : Value,
  list_ldat : Value,
  open_g? : Value = Fix(1L),
) -> Value raise {
  let mut bad_components : Value = Nil
  let use_ldata_inverse = true
  let open_g : Value = if open_g is Nil { Fix(1L) } else { open_g }
  let orig_ldata_list = if ldatap(orig_ldata_list).truthy() {
    list1(orig_ldata_list)
  } else {
    orig_ldata_list
  }
  let mut i = 0
  for v in list_ldat.iter() {
    let mut verified = false
    for ld in orig_ldata_list.iter() {
      let gg = if use_ldata_inverse {
        plcm(open_g, sheafa__ldata_inequality(v))
      } else {
        open_g
      }
      let (answ, unit) = grobner_subset(
        sheafa__ldata_eqns(ld),
        sheafa__ldata_eqns(v),
        may_invert=gg,
      )
      if unit.truthy() {
        format(t, "~%**The component is   empty***", []) |> ignore
      }
      if unit.truthy() || answ.truthy() {
        format(t, "~%    Component ~D verified:", [int(i)]) |> ignore
        des(v) |> ignore
        verified = true
        break
      }
    }
    if !verified {
      bad_components = cons(int(i), bad_components)
      format(t, "**The component ", []) |> ignore
      sheafb__fsh(v)
      format(t, " ~%does not contain the original data***** ", []) |> ignore
      if symval(q_ear_signal_component_error).truthy() {
        fsignal(list2(Str("not contained"), v)) |> ignore
      }
    }
    i += 1
  }
  bad_components
}

///|
fn check_components_contain_original(
  ldata : Value,
  list_ldat : Value,
) -> Value raise {
  let bad_components : Value = Nil
  let mut i = 0
  for v in list_ldat.iter() {
    catch_tag(q_took_too_long, () => grobner_remember(sheafa__ldata_eqns(v)))
    |> ignore
    for u in sheafa__ldata_eqns(ldata).iter() {
      if d_zerop(polysimp(u).0) is Nil {
        sheafa__mshow("U", u)
        sheafa__mshow("(POLYSIMP U)", polysimp(u).0)
        format(t, "**The ideal: ", []) |> ignore
        sheafb__fsh(v)
        format(t, " ~%does not contain the original one *** : ", []) |> ignore
        sheafb__fsh(ldata)
        // (push-new i bad-components): PUSH-NEW is undefined.
        sheafb__undefined("PUSH-NEW") |> ignore
        break
      }
    }
    format(t, "~%    Component ~D verified:", [int(i)]) |> ignore
    des(v) |> ignore
    i += 1
  }
  if bad_components.truthy() {
    format(t, "~%All but components ~A contained the originals.", [
      bad_components,
    ])
    |> ignore
  }
  bad_components
}

///|
fn variable_doesnt_occur(var_ : Value, lists_fns : Value) -> Value raise {
  ignore(var_)
  for _v in lists_fns.iter() {
    // (list-variables v :test #'eq): LIST-VARIABLES takes one argument.
    raise LispError::SimpleError("invalid number of arguments: 3")
  }
  t
}

///|
/// The following is for converting back things which have been dumped to
/// file, or after we have reset the genvar.
fn replace_rmaps_by_new_ones(form : Value) -> Value raise {
  if form is Nil {
    Nil
  } else if atom(form) {
    form
  } else if eq(car(form), q_rmap) {
    convert_rmap_to_new(form)
  } else {
    let mut r = form
    while r is Cons(_) {
      setf_car(r, replace_rmaps_by_new_ones(car(r))) |> ignore
      r = cdr(r)
    }
    form
  }
}

///|
fn rerat(form : Value) -> Value raise {
  if form is Nil {
    Nil
  } else if symbolp(form) &&
    !(
      eq(form, q_ldata) ||
      eq(form, q_s_var) ||
      eq(form, q_zopens) ||
      eq(form, q_rmap) ||
      eq(form, q_zopen) ||
      eq(form, q_pre_ldata_sheaves) ||
      eq(form, q_quote) ||
      eq(form, q_inequality) ||
      eq(form, q_eqns)
    ) {
    // (add-newvar (intern (string-append "$" (string form)))):
    // STRING-APPEND is undefined.
    sheafb__undefined("STRING-APPEND")
  } else {
    let mut r = form
    while r is Cons(_) {
      setf_car(r, rerat(car(r))) |> ignore
      r = cdr(r)
    }
    form
  }
}

///|
fn affine_svar(
  dim? : Value = Nil,
  eqns? : Value = Nil,
  inequality? : Value = Fix(1L),
  ld_inequality? : Value = Fix(1L),
  list_ldata? : Value = Nil,
) -> Value raise {
  let list_ldata = if list_ldata is Nil {
    list1(sheafa__make_ldata(eqns~, inequality=ld_inequality))
  } else {
    list_ldata
  }
  construct_pre_ldata_sheaves(
    s_var=sheafa__make_s_var(
      zopens=list1(
        affine_open(
          subseq(symval(q_ear_xxx), 0, end=to_int(dim)),
          inequal=inequality,
        ),
      ),
    ),
    data=list1(list_ldata),
  )
}

///|
fn affine_ldata(n : Value, eqns : Value, inequality : Value) -> Value raise {
  construct_pre_ldata_sheaves(
    s_var=sheafa__make_s_var(
      zopens=list1(
        affine_open(
          subseq(symval(q_ear_xxx), 0, end=to_int(n)),
          inequal=inequality,
        ),
      ),
    ),
    data=list1(list1(sheafa__make_ldata(eqns~, inequality~))),
  )
}

///|
/// `(desn-editor expr)`: the macro prints EXPR's value (with
/// `(for-editor (desn ...))`) and the form `(setq expr (rerat '<value>))`
/// at expansion time; its expansion is NIL.
fn desn_editor(expr : Value) -> Value raise {
  let me = list3(
    q_setq,
    expr,
    list2(q_rerat, list2(q_quote, symval(expr))),
  )
  // (for-editor ...): (let ((linel 75) $display2d) ...); LINEL is lexical.
  with_special(q_d_display2d, Nil, () => {
    with_special(q_ear_give_coordinates, Nil, () => des(symval(expr)))
  })
  |> ignore
  format(t, "~A", [me]) |> ignore
  Nil
}

///|
fn change_strings_to_symbols(tree : Value) -> Value raise {
  match tree {
    Str(s) => make_symbol(s)
    _ =>
      if atom(tree) {
        tree
      } else {
        let mut v = tree
        while v is Cons(_) {
          setf_car(v, change_strings_to_symbols(car(v))) |> ignore
          v = cdr(v)
        }
        tree
      }
  }
}

///|
fn des_file(expr : Value, file_name : Value) -> Value raise {
  let name = match file_name {
    Str(s) => s
    _ => lstring(string(file_name))
  }
  let mut res : Value = Nil
  let text = with_output_to_string(st => {
    res = with_specials([(standard_output, st), (q_d_display2d, Nil)], () => {
      des(expr)
    })
  })
  write_file(name, text)
  res
}

///|
fn sh_comp(com : Value) -> Value raise {
  for v in car(com).iter() {
    format(t, "~%~A", [v]) |> ignore
  }
  Nil
}

///|
fn find_ring_map(from_open : Value, to_open : Value) -> Value raise {
  sheafa__compose_rmap(
    sheafa__zopen_coord(from_open),
    sheafa__zopen_inv(to_open),
  )
}

///|
fn translate_component(
  from_open : Value,
  to_open : Value,
  ldata : Value,
  pls? : Value = Nil,
) -> Value raise {
  let mut from_open = from_open
  let mut to_open = to_open
  let mut ldata = ldata
  if pls.truthy() {
    to_open = nth(to_int(to_open), pls_opens(pls))
    ldata = nth(to_int(ldata), nth(to_int(from_open), sheafa__pls_data(pls)))
    from_open = nth(to_int(from_open), pls_opens(pls))
  }
  sheafa__show("(CAR LDATA)", car(ldata))
  if equal(from_open, to_open) {
    ldata
  } else {
    let mapl = find_ring_map(from_open, to_open)
    sheafa__show("(LENGTH (LDATA-EQNS LDATA))", int(length(sheafa__ldata_eqns(ldata))))
    apply_rmap(mapl, ldata)
  }
}

///|
fn sftimes(f : Value, g : Value) -> Value raise {
  square_free(ptimes(f, g))
}

///|
fn apply_rmap_to_square_free_factors(mapl : Value, pol : Value) -> Value raise {
  let facts = non_constant_factors(pol)
  if facts is Nil {
    cons(pol, Fix(1L))
  } else {
    let tem : Array[Value] = []
    let mut f = facts
    while f is Cons(_) {
      tem.push(car(f))
      f = cddr(f)
    }
    let answ = apply_rmap(mapl, list(tem))
    let mut answer = cons(Fix(1L), Fix(1L))
    for v in answ.iter() {
      answer = rattimes(answer, v, t)
    }
    answer
  }
}

///|
/// Did not need to compute the translated ldata except on the intersection.
fn translate_component_and_reduce(
  from_open : Value,
  to_open : Value,
  ldata : Value,
  use_inverse_inequal? : Value = t,
) -> (Value, Value) raise {
  let b = bind(q_ear_refine_opens, Nil)
  defer unbind(b)
  let mapl = find_ring_map(from_open, to_open)
  // (process-sleep 20): PROCESS-SLEEP is undefined.
  sheafb__undefined("PROCESS-SLEEP") |> ignore
  let gg = sheafa__zopen_inequality(to_open)
  let mut hh = if use_inverse_inequal.truthy() {
    let inv = find_ring_map(to_open, from_open)
    let inv_denom = function_numerator(
      apply_rmap_to_square_free_factors(mapl, sheafa__rmap_denom(inv)),
    )
    let hh = sftimes(gg, inv_denom)
    sheafb__undefined("PROCESS-SLEEP") |> ignore
    hh
  } else {
    gg
  }
  let transl = apply_rmap(mapl, ldata)
  hh = sftimes(sheafa__rmap_denom(mapl), hh)
  hh = sftimes(
    function_numerator(apply_rmap(mapl, sheafa__zopen_inequality(from_open))),
    hh,
  )
  // Calculate on open intersection (possibly using the inv-denom !!).
  let red_transl = ldata_simplifications(transl, open_g=hh)
  sheafa__show("RED-TRANSL", red_transl)
  let tem : Array[Value] = []
  for v in red_transl.iter() {
    if unit_idealp(sheafa__ldata_eqns(v), may_invert=hh) is Nil {
      tem.push(v)
    }
  }
  let answ = if tem.length() > 1 {
    format(t, "~%The image had two components meet the intersection.", [])
    |> ignore
    des(list(tem)) |> ignore
    fsignal(list1(q_two_components))
  } else if tem.length() == 1 {
    tem[0]
  } else {
    Nil
  }
  (answ, hh)
}

///|
fn init_share_sheafb() -> Unit raise {

}

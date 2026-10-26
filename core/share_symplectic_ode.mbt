// Port of share/contrib/symplectic_ode/symplectic_ode.lisp (Barton Willis,
// 2017): symplectic integration of time independent separable hamiltonian
// systems.
//
// EXPR-TO-COMPILED-FUN defines a Maxima function and compiles it with
// $COMPILE (the Maxima-to-Lisp translator, transs.lisp); $SYMPLECTIC_ODE
// therefore needs the translator ($COMPILE and $MODEDECLARE).

///|
/// A Maxima coerce function: either convert x to type ntype or signal an
/// error. The allowable values of ntype are float, bfloat, fixnum, rational,
/// and any (no coercion).
fn mcoerce(x : Value, ntype : Value) -> Value raise {
  let mut xx = x
  let type_test : (Value) -> Bool raise = if eql(ntype, q_d_float) {
    xx = d_float(x)
    v => d_floatnump(v).truthy()
  } else if eql(ntype, q_d_bfloat) {
    xx = d_bfloat(x)
    v => d_bfloatp(v).truthy()
  } else if eql(ntype, q_fixnum) {
    // (coerce x 'fixnum)
    xx = match x {
      Fix(n) if n >= -4611686018427387904L && n <= 4611686018427387903L => x
      _ =>
        raise LispError::SimpleError(
          prin1_to_string(x) + " can't be converted to type FIXNUM.",
        )
    }
    v => fixnump(v)
  } else if eql(ntype, q_d_rational) {
    xx = d_rationalize(x)
    v => d_ratnump(v).truthy()
  } else if eql(ntype, q_d_any) {
    _ => true
  } else {
    merror(Str("Unknown type ~M"), list1(ntype)) |> ignore
    _ => true
  }
  if type_test(xx) {
    xx
  } else {
    merror(Str("Unable to convert ~M to type ~M"), list([x, ntype]))
  }
}

///|
/// Return a compiled CL function args |--> e where the args are
/// modedeclared to be type ntype. When ntype isn't one of the types
/// accepted by modedeclare, the type is changed to the type any. The
/// argument args must be a CL list. Return the identifier for the function.
fn expr_to_compiled_fun(e : Value, ntype : Value, args : Value) -> Value raise {
  let mut ntype = ntype
  if !member(
      ntype,
      list([q_d_any, q_d_boolean, q_d_fixnum, q_d_number, q_d_rational, q_d_float]),
    ).truthy() {
    mtell(
      list([
        Str("Type ~M is unknown to the compiler; changing to type any."),
        ntype,
      ]),
    )
    |> ignore
    ntype = q_d_any
  }
  let f = gensym()
  meval(
    list([
      list1(q_mdefine),
      cons(list1(f), args),
      list([
        list1(q_mprogn),
        list([list1(q_d_modedeclare), cons(list1(q_mlist), args), ntype]),
        e,
      ]),
    ]),
  )
  |> ignore
  // compile returns a Maxima list of function identifiers.
  second(mfuncall(q_d_compile, list1(f)))
}

///|
/// (apply fk args) on a function compiled by EXPR-TO-COMPILED-FUN. The
/// port's $COMPILE (translate_compat.mbt) leaves the function in the
/// interpreter, so a function without a Lisp definition is applied as a
/// Maxima function.
fn share_symplectic_ode__call(fk : Value, args : Value) -> Value raise {
  if fboundp(fk) {
    apply(fk, args)
  } else {
    mapply1(fk, args, fk, Nil)
  }
}

///|
/// The Poisson bracket {f,g} for the canonical coordinates p & q. Either
/// both p & q must be equal length Maxima lists or both must be mapatoms.
fn d_poisson_bracket(f : Value, g : Value, p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  if d_listp(p).truthy() && d_listp(q).truthy() {
    p = rest(p)
    q = rest(q)
  } else if d_mapatom(p).truthy() && d_mapatom(q).truthy() {
    p = list1(p)
    q = list1(q)
  } else {
    merror(
      Str(
        "Either the third and fourth arguments to poisson_bracket must (i) both be lists or (ii) both be mapatoms",
      ),
      Nil,
    )
    |> ignore
  }
  let terms = mapcar2(
    (pk, qk) => sub(
      mul2(d_diff(list([f, qk])), d_diff(list([g, pk]))),
      mul2(d_diff(list([f, pk])), d_diff(list([g, qk]))),
    ),
    p,
    q,
  )
  // (reduce #'add terms)
  match terms {
    Nil => addn_([])
    _ => {
      let mut acc = car(terms)
      for x in cdr(terms).iter() {
        acc = add2(acc, x)
      }
      acc
    }
  }
}

///|
/// symplectic ode solver: Usage: (non scalar or scalar version)
///     symplectic_ode(ham, [p1,..., pn], [q1, ... , qn], [p01, ... p0n],
///           [q01, ... q0n], dt, N, [method], [ntype])
///     symplectic_ode(ham, p, q, po, qo, dt, [method],[ntype])
/// The method is
///   for k = 1 ... n
///     q <-  q + c(k)*diff(ham,p)*dt
///     p <-  p - d(k)*diff(ham,q)*dt ;use updated position q
fn d_symplectic_ode(
  ham : Value,
  p : Value,
  q : Value,
  po : Value,
  qo : Value,
  dt : Value,
  nn : Value,
  sym_method? : Value = q_d_symplectic_euler,
  ntype? : Value = q_d_float,
) -> Value raise {
  let mut p = p
  let mut q = q
  let mut po = po
  let mut qo = qo
  let ddt = gensym()
  let xmlist = get(q_mlist, q_msimpind)
  let mut scalar_case = false
  let mut n = to_int64(mcoerce(nn, q_fixnum))
  if every(x => d_listp(x).truthy(), list([p, q, po, qo])) {
    // Maxima to CL list conversion
    scalar_case = false
    po = list1(mapcar(x => mcoerce(x, ntype), rest(po)))
    qo = list1(mapcar(x => mcoerce(x, ntype), rest(qo)))
    p = rest(p)
    q = rest(q)
  } else if every(s => !d_listp(s).truthy(), list([p, q, po, qo])) {
    scalar_case = true
    po = list1(list1(mcoerce(po, ntype)))
    qo = list1(list1(mcoerce(qo, ntype)))
    p = list1(p)
    q = list1(q)
  } else {
    merror(
      Str(
        "Either the second through fifth arguments must all be lists or all must be nonlists.",
      ),
      Nil,
    )
    |> ignore
  }
  if some(s => !d_symbolp(s).truthy(), p) ||
    some(s => !d_symbolp(s).truthy(), q) {
    merror(
      Str(
        "The second and third arguments must be either be symbols or lists of symbols.",
      ),
      Nil,
    )
    |> ignore
  }
  let mut args = append(p, append(q, list1(ddt)))
  let update_p = mapcar2(
    (pk, qk) => expr_to_compiled_fun(
      sub(pk, mult(ddt, d_diff(list([ham, qk])))),
      ntype,
      args,
    ),
    p,
    q,
  )
  let update_q = mapcar2(
    (pk, qk) => expr_to_compiled_fun(
      add2(qk, mult(ddt, d_diff(list([ham, pk])))),
      ntype,
      args,
    ),
    p,
    q,
  )
  let mut cfs = gethash(sym_method, symval(q_ear_symplectic_method_coefficients))
  if !cfs.truthy() {
    // build a list of all methods
    let mut all_methods : Value = Nil
    maphash(
      (a, _b) => all_methods = cons(a, all_methods),
      symval(q_ear_symplectic_method_coefficients),
    )
    all_methods = cons(xmlist, all_methods)
    merror(
      Str("The method must be a member of ~M, but found ~M"),
      list([all_methods, sym_method]),
    )
    |> ignore
  }
  cfs = mapcar(
    x => cons(
      mcoerce(mul2(dt, car(x)), ntype),
      mcoerce(mul2(dt, cdr(x)), ntype),
    ),
    cfs,
  )
  let mut poo = car(po)
  let mut qoo = car(qo)
  while n > 0L {
    n = n - 1L
    for cx in cfs.iter() {
      args = append(poo, append(qoo, list1(car(cx))))
      let a1 = args
      poo = mapcar(fk => share_symplectic_ode__call(fk, a1), update_p)
      args = append(poo, append(qoo, list1(cdr(cx))))
      let a2 = args
      qoo = mapcar(fk => share_symplectic_ode__call(fk, a2), update_q)
    }
    po = cons(poo, po)
    qo = cons(qoo, qo)
  }
  if scalar_case {
    po = mapcar(x => car(x), reverse(po))
    qo = mapcar(x => car(x), reverse(qo))
  } else {
    po = mapcar(x => cons(xmlist, x), reverse(po))
    qo = mapcar(x => cons(xmlist, x), reverse(qo))
  }
  // The functions update-p and update-q are no longer needed.
  mapc(f => fmakunbound(f) |> ignore, update_p) |> ignore
  mapc(f => fmakunbound(f) |> ignore, update_q) |> ignore
  // Convert po & qo from CL lists to Maxima lists.
  po = cons(xmlist, po)
  qo = cons(xmlist, qo)
  list([xmlist, po, qo])
}

///|
fn share_symplectic_ode__big(s : String) -> Value raise {
  lread(s)
}

///|
fn init_share_symplectic_ode() -> Unit raise {
  // Let's have version numbers 1,2,3, ...
  d_put(Str("symplectic_ode"), int(1), q_d_version) |> ignore
  // Define a mlist msimpind. This definition should be somewhere else.
  setf_get(q_mlist, q_msimpind, list([q_mlist, q_simp])) |> ignore
  // Hash table for coefficients of symplectic methods; each value is a
  // list of the form ((c1 . d1) (c2 . d2) ...)
  defvar_init(q_ear_symplectic_method_coefficients, make_hash_table(kind=Eql))
  defvar_init(q_ear_symplectic_method_digits, make_hash_table(kind=Eql))
  let coeffs = symval(q_ear_symplectic_method_coefficients)
  let digits = symval(q_ear_symplectic_method_digits)
  sethash(q_d_symplectic_euler, coeffs, list1(cons(int(1), int(1)))) |> ignore
  sethash(q_d_symplectic_euler, digits, q_d_inf) |> ignore
  sethash(
    q_d_verlet,
    coeffs,
    list([
      cons(int(0), div(int(1), int(2))),
      cons(int(1), div(int(1), int(2))),
    ]),
  )
  |> ignore
  sethash(q_d_verlet, digits, q_d_inf) |> ignore
  sethash(
    q_d_symplectic_third_order,
    coeffs,
    list([
      cons(int(1), div(int(-1), int(24))),
      cons(div(int(-2), int(3)), div(int(3), int(4))),
      cons(div(int(2), int(3)), div(int(7), int(24))),
    ]),
  )
  |> ignore
  sethash(q_d_symplectic_third_order, digits, q_d_inf) |> ignore
  let k = div(int(1), sub(int(2), power(int(2), div(int(1), int(3)))))
  let c4 = list([
    cons(div(k, int(2)), k),
    cons(
      div(mul2(sub(int(1), power(int(2), div(int(1), int(3)))), k), int(2)),
      mul2(mul2(int(-1), power(int(2), div(int(1), int(3)))), k),
    ),
    cons(
      div(mul2(sub(int(1), power(int(2), div(int(1), int(3)))), k), int(2)),
      k,
    ),
    cons(div(k, int(2)), int(0)),
  ])
  sethash(q_d_symplectic_fourth_order, coeffs, c4) |> ignore
  sethash(q_d_symplectic_fourth_order, digits, q_d_inf) |> ignore
  // see Kostas Tselios and T. E. Simos, ``Optimized fifth order symplectic
  // integrators for orbital problems,'' Revista Mexicana de Astronomia y
  // Astrofisica, 49, 11-24 (2013); the coefficients are taken to be good
  // to 40 digits.
  let b = share_symplectic_ode__big
  let cs = list([
    div(
      b("5652885872144153264930671803559342469576954521714583915513"),
      b("50216813883093446110686315385661331328818843555712276103168"),
    ),
    div(
      b("362426134418756238993387367402013039958979964654753376945"),
      b("392318858461667547739736838950479151006397215279002157056"),
    ),
    div(
      b("-4274909969574666030908365902533105271208568565239518523207"),
      b("3138550867693340381917894711603833208051177722232017256448"),
    ),
    div(
      b("3078687817773247970859746019343925292770783479419914796411"),
      b("3138550867693340381917894711603833208051177722232017256448"),
    ),
    div(
      b("629221334757054438917474234802547577988423100782937501865"),
      b("1569275433846670190958947355801916604025588861116008628224"),
    ),
    div(
      b("4341517001601166158290432120166041572705763778637534302909"),
      b("12554203470773361527671578846415332832204710888928069025792"),
    ),
    div(
      b("-5047053371114805865785231327168622346738894852075304064687"),
      b("12554203470773361527671578846415332832204710888928069025792"),
    ),
  ])
  let ds = list([
    div(
      b("2319601814552342659136359435206712577059674598536966859091"),
      b("6277101735386680763835789423207666416102355444464034512896"),
    ),
    div(
      b("-3225928552003184381834780354143261178475501353749927450079"),
      b("100433627766186892221372630771322662657637687111424552206336"),
    ),
    div(
      b("-4812257597683015175999923204116192762946117963505537572213"),
      b("401734511064747568885490523085290650630550748445698208825344"),
    ),
    div(
      b("402235246967237878148042461203282093231351221007491081787"),
      b("784637716923335095479473677900958302012794430558004314112"),
    ),
    div(
      b("-4205009085731718839023168486933272699269839833464512439795"),
      b("12554203470773361527671578846415332832204710888928069025792"),
    ),
    div(
      b("274392137557984949615301132056520558869905595208602668291"),
      b("12554203470773361527671578846415332832204710888928069025792"),
    ),
    div(
      b("5963476957294596320417393096022684997935176483307435518905"),
      b("12554203470773361527671578846415332832204710888928069025792"),
    ),
  ])
  sethash(
    q_d_symplectic_fifth_order,
    coeffs,
    mapcar2((a, d) => cons(a, d), cs, ds),
  )
  |> ignore
  sethash(q_d_symplectic_fifth_order, digits, int(40)) |> ignore
}

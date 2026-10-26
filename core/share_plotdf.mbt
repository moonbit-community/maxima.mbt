// Port of share/dynamics/plotdf.lisp: plotdf, which draws a direction field
// for an ordinary 1st order differential equation, or for a system of two
// autonomous 1st order equations, and ploteq, which plots equipotential
// curves (Jaime E. Villate).

///|
/// parses a plotdf option into a command-line option for tcl scripts
fn plotdf_option_to_tcl(value : Value, s1 : Value, s2 : Value) -> Value raise {
  let mut value = value
  let name = second(value)
  if !(d_listp(value).truthy() && symbolp(name)) {
    merr(
      "plotdf-option-to-tcl: Expecting a symbol for the option name, found: \"~M\"",
      [value],
    )
    |> ignore
  }
  let realp_ = plot__pred("realp", v => realp(v))
  let naturalp_ = plot__pred("naturalp", v => naturalp(v).truthy())
  let stringp_ = plot__pred("stringp", v => stringp(v))
  let nm = match name {
    Sym(s) => s.name
    _ => ""
  }
  match nm {
    "$xradius" | "$yradius" | "$xcenter" | "$ycenter" | "$tinitial" | "$tstep" => {
      let v = check_option(cdr(value), realp_, Str("a real number"), count=Fix(1L))
      value = list3(list1(q_mlist), name, v)
    }
    "$width" | "$height" | "$nsteps" | "$versus_t" => {
      let v = check_option(
        cdr(value),
        naturalp_,
        Str("a natural number"),
        count=Fix(1L),
      )
      value = list3(list1(q_mlist), name, v)
    }
    "$trajectory_at" => {
      let v = check_option(cdr(value), realp_, Str("a real number"), count=Fix(2L))
      value = cons(list1(q_mlist), cons(name, v))
    }
    "$bbox" => {
      let v = check_option(cdr(value), realp_, Str("a real number"), count=Fix(4L))
      value = cons(list1(q_mlist), cons(name, v))
    }
    "$xfun"
    | "$parameters"
    | "$sliders"
    | "$vectors"
    | "$fieldlines"
    | "$curves"
    | "$windowtitle"
    | "$xaxislabel" | "$yaxislabel" | "$psfile" => {
      let v = check_option(cdr(value), stringp_, Str("a string"), count=Fix(1L))
      value = list3(list1(q_mlist), name, v)
    }
    "$axes" => {
      let a = third(value)
      value = if !a.truthy() {
        list3(list1(q_mlist), q_d_axes, Fix(0L))
      } else if eq(a, q_d_x) {
        list3(list1(q_mlist), q_d_axes, Str("x"))
      } else if eq(a, q_d_y) {
        list3(list1(q_mlist), q_d_axes, Str("y"))
      } else {
        list3(list1(q_mlist), q_d_axes, Str("xy"))
      }
    }
    "mbox" =>
      value = if !third(value).truthy() {
        list3(list1(q_mlist), q_d_nobox, Fix(1L))
      } else {
        list3(list1(q_mlist), q_d_nobox, Fix(0L))
      }
    "$direction" =>
      if !member_equal(
          ensure_string(third(value)),
          list3(Str("forward"), Str("backward"), Str("both")),
        ).truthy() {
        merr(
          "plotdf-option-to-tcl: direction should be forward, backward or both.",
          [],
        )
        |> ignore
      }
    _ =>
      if eql(name, s1) {
        value = cons(list1(q_mlist), cons(q_d_x, cddr(check_range(value))))
      } else if eql(name, s2) {
        value = cons(list1(q_mlist), cons(q_d_y, cddr(check_range(value))))
      } else {
        merr("plotdf-option-to-tcl: unknown option ~M", [name]) |> ignore
      }
  }
  let vv = mapcar(a => if symbolp(a) { ensure_string(a) } else { a }, cdr(value))
  let st = make_string_output_stream()
  if equal(first(vv), Str("x")) || equal(first(vv), Str("y")) {
    format(st, "-~(~a~)center ", [first(vv)]) |> ignore
    format(st, "{~a} ", [num_div(num_add(third(vv), second(vv)), Fix(2L))])
    |> ignore
    format(st, "-~(~a~)radius ", [first(vv)]) |> ignore
    format(st, "{~a}", [num_div(num_sub(third(vv), second(vv)), Fix(2L))])
    |> ignore
  } else {
    format(st, "-~(~a~) ", [first(vv)]) |> ignore
    format(st, "{~{~a~^ ~}}", [cdr(vv)]) |> ignore
  }
  Str(get_output_stream_string(st))
}

///|
/// applies float(ev(expression, numer)) to an expression, and returns a
/// string (a list of characters, as MSTRING returns it)
fn expr_to_str(fun : Value) -> Value raise {
  mstring(mfuncall(q_d_float, list1(mfuncall(q_d_ev, list2(fun, q_d_numer)))))
}

///|
/// (concatenate 'string ...) of strings and lists of characters.
fn plotdf__concat(parts : Array[Value]) -> String {
  let sb = StringBuilder::new()
  for p in parts {
    match p {
      Str(s) => sb.write_string(s)
      _ => sb.write_string(char_list_to_string(p))
    }
  }
  sb.to_string()
}

///|
/// The variable names given right after the expression(s), if any: (s1 s2
/// remaining-options).
fn plotdf__vars(options : Value) -> (Value, Value, Value) raise {
  let o = car(options)
  if listp(o) &&
    length(o) == 3 &&
    (symbolp(cadar(options)) || d_subvarp(cadar(options)).truthy()) &&
    (symbolp(caddar(options)) || d_subvarp(caddar(options)).truthy()) {
    (cadar(options), caddar(options), cdr(options))
  } else {
    (q_d_x, q_d_y, options)
  }
}

///|
/// substitute s1 by $x and s2 by $y (the SUBXY function plotdf defines)
fn plotdf__subxy(expr : Value, s1 : Value, s2 : Value) -> Value raise {
  if listp(expr) {
    mapcar(e => plotdf__subxy(e, s1, s2), expr)
  } else if eq(expr, s1) {
    q_d_x
  } else if eq(expr, s2) {
    q_d_y
  } else {
    expr
  }
}

///|
/// Outputs the data, either into a file to be passed to Xmaxima or sent
/// directly to Xmaxima if Maxima is being run from Xmaxima.
fn plotdf__output(cmd : String, opts : String) -> Value raise {
  let data = format(Nil, "plotdf ~a ~a~%", [Str(cmd), Str(opts)])
  let file = plot_file_path(format(Nil, "~a.xmaxima", [random_name(Fix(16L))]))
  if symval(q_d_show_openplot).truthy() {
    write_file(lstring(file), lstring(data))
    d_system(
      list2(
        symval(q_d_xmaxima_plot_command),
        format(Nil, lstring(symval(q_d_gnuplot_file_args)), [file]),
      ),
    )
    |> ignore
  } else {
    princ(format(Nil, "{~a}", [data])) |> ignore
  }
  list2(list1(q_mlist), file)
}

///|
/// plots the direction field for an ODE  dy/dx = f(x,y), or for an
/// autonomous system of 2 equations dx/dt = f(x,y), dy/dt = g(x,y)
fn d_plotdf(ode : Value, options : Value) -> Value raise {
  let mut ode = if d_listp(ode).truthy() { ode } else { list2(list1(q_mlist), ode) }
  // if the variables are not x and y, their names must be given right after
  // the expression for the ode's
  let (s1, s2, options) = plotdf__vars(options)
  // parse options and copy them to string opts
  let mut opts = " "
  for v in options.iter() {
    opts = opts + " " + lstring(plotdf_option_to_tcl(v, s1, s2))
  }
  if !opts.contains("-xaxislabel ") {
    opts = opts + " -xaxislabel " + lstring(ensure_string(s1))
  }
  if !opts.contains("-yaxislabel ") {
    opts = opts + " -yaxislabel " + lstring(ensure_string(s2))
  }
  // check that the expressions given contain only the axis variables
  let vars = cdr(mfuncall(q_d_listofvars, list1(ode)))
  if !opts.contains("-parameters ") {
    for var_ in vars.iter() {
      if !(eq(var_, s1) || eq(var_, s2)) {
        merr(
          "plotdf: expression(s) given can only depend on ~M and ~M~%Found extra variable ~M",
          [s1, s2, var_],
        )
        |> ignore
      }
    }
  }
  // substitute $x by s1 and $y by s2
  ode = mapcar(e => plotdf__subxy(e, s1, s2), ode)
  // parse the differential equation expressions
  let cmd = match length(ode) {
    3 =>
      plotdf__concat([
        Str(" -dxdt \""),
        expr_to_str(second(ode)),
        Str("\" -dydt \""),
        expr_to_str(third(ode)),
        Str("\""),
      ])
    2 => plotdf__concat([Str(" -dydx \""), expr_to_str(second(ode)), Str("\"")])
    _ => {
      merr(
        "plotdf: first argument must be either an expression or a list with two expressions.",
        [],
      )
      |> ignore
      ""
    }
  }
  plotdf__output(cmd, opts)
}

///|
/// plot equipotential curves for a scalar field f(x,y)
fn d_ploteq(fun : Value, options : Value) -> Value raise {
  let mut mfun = list3(list1(q_mtimes), Fix(-1L), fun)
  // if the variables are not x and y, their names must be given right after
  // the expression for the ode's
  let (s1, s2, options) = plotdf__vars(options)
  mfun = mapcar(e => plotdf__subxy(e, s1, s2), mfun)
  let cmd = plotdf__concat([
    Str(" -dxdt \""),
    expr_to_str(mfuncall(q_d_diff, list2(mfun, q_d_x))),
    Str("\" -dydt \""),
    expr_to_str(mfuncall(q_d_diff, list2(mfun, q_d_y))),
    Str("\" "),
  ])
  // parse options and copy them to string opts
  let mut opts = " "
  for v in options.iter() {
    opts = opts + " " + lstring(plotdf_option_to_tcl(v, s1, s2))
  }
  if !opts.contains("-vectors ") {
    opts = opts + " -vectors {}"
  }
  if !opts.contains("-fieldlines ") {
    opts = opts + " -fieldlines {}"
  }
  if !opts.contains("-curves ") {
    opts = opts + " -curves {red}"
  }
  if !opts.contains("-windowtitle ") {
    opts = opts + " -windowtitle {Ploteq}"
  }
  if !opts.contains("-xaxislabel ") {
    opts = opts + " -xaxislabel " + lstring(ensure_string(s1))
  }
  if !opts.contains("-yaxislabel ") {
    opts = opts + " -yaxislabel " + lstring(ensure_string(s2))
  }
  plotdf__output(cmd, opts)
}

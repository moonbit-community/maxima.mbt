// Port of src/plot.lisp (part 3): plot2d, contour_plot and plot3d.

///|
/// The plot object for the plot_format in OPTIONS ($plot2d's and $plot3d's
/// CASE on the format); WHO names the caller in the error message.
fn plot__make_plot(options : Value, who : String, geomview : Bool) -> PlotObj raise {
  let fmt = getf(options, q_d_plot_format)
  if eq(fmt, q_d_xmaxima) {
    plot__make_instance(XmaximaPlot)
  } else if eq(fmt, q_d_gnuplot) {
    plot__make_instance(GnuplotPlot)
  } else if eq(fmt, q_d_gnuplot_pipes) {
    let plot = plot__make_instance(GnuplotPlot)
    plot.pipe = true
    plot
  } else if geomview && eq(fmt, q_d_geomview) {
    plot__make_instance(GeomviewPlot)
  } else {
    merr(who + ": plot format ~M not supported", [fmt]) |> ignore
    plot__make_instance(GnuplotPlot)
  }
}

///|
/// plot2d
/// Examples:
///
/// plot2d (sec(x), [x, -2, 2], [y, -20, 20]);
///
/// plot2d (exp(3*s), [s, -2, 2], logy);
///
/// plot2d ([parametric, cos(t), sin(t), [t, -%pi, %pi]], same_xy);
///
/// xy:[[10,.6], [20,.9], [30,1.1], [40,1.3], [50,1.4]]$
/// plot2d ( [ [discrete, xy], 2*%pi*sqrt(l/980) ], [l, 0, 50],
/// [style, points, lines], [color, red, blue], [point_type, box],
/// [legend, "experiment", "theory"],
/// [xlabel, "pendulum's length (cm)"], [ylabel, "period (s)"]);
///
/// plot2d ( x^2-1, [x, -3, 3], [y, -2, 10], nobox, [color, red],
/// [ylabel, "x^2-1"], [plot_format, xmaxima]);
///
/// plot2d ( x^2+y^2 = 1, [x, -2, 2], [y, -2 ,2]);
fn d_plot2d(fun : Value, xrange? : Value = Nil, extra_options : Value) -> Value raise {
  with_specials(
    [
      (q_d_display2d, Nil),
      (q_ear_plot_realpart, symval(q_ear_plot_realpart)),
    ],
    () => plot__plot2d(fun, xrange, extra_options),
  )
}

///|
fn plot__plot2d(fun0 : Value, xrange0 : Value, extra_options0 : Value) -> Value raise {
  let mut fun = fun0
  let mut xrange = xrange0
  let mut extra_options = extra_options0
  let mut options = copy_tree(symval(q_ear_plot_options))
  let mut yrange : Value = Nil
  let put = (k : Value, v : Value) => options = plot__putf(options, k, v)
  // fun must be a maxima list with several objects: expressions (simple
  // functions), maxima lists (parametric or discrete cases).  A single
  // parametric or discrete plot is placed inside a maxima list.
  put(q_d_type, Str("plot2d"))
  if fun is Cons(_) &&
    (
      eq(second(fun), q_d_parametric) ||
      eq(second(fun), q_d_contour) ||
      eq(second(fun), q_d_discrete)
    ) {
    fun = list2(list1(q_mlist), fun)
  }
  // If by now fun is not a maxima list, it is then a single expression
  if !d_listp(fun).truthy() {
    fun = list2(list1(q_mlist), fun)
  }
  // 2- Get names for the two axis and values for xmin and xmax if needed.
  // If any of the objects in the fun list is a simple function, the xrange
  // option is mandatory and will provide the name of the horizontal axis
  // and the values of xmin and xmax.
  let mut xrange_required = false
  let mut bounds_required = false
  let mut yrange_required = false
  let small = num_neg(num_div(Flo(1.7976931348623157e308), Fix(1024L)))
  let huge = num_div(Flo(1.7976931348623157e308), Fix(1024L))
  put(q_d_ybounds, list2(small, huge))
  for f in cdr(fun).iter() {
    if d_listp(f).truthy() {
      let kind = d_first(f)
      if eq(kind, q_d_parametric) {
        if !bounds_required {
          bounds_required = true
          // Default X and Y bound large so parametric plots don't get
          // prematurely clipped. Don't use most-positive-flonum because
          // draw2d will overflow.
          put(q_d_xbounds, list2(small, huge))
        }
        check_range(funcall(q_d_fourth, [f])) |> ignore
      } else if eq(kind, q_d_contour) {
        xrange = check_range(xrange)
        xrange_required = true
        if !yrange_required {
          yrange_required = true
          if extra_options is Nil {
            merr(
              "plot2d: contour plots require intervals for the variables in the two axes; only one interval was given.",
              [],
            )
            |> ignore
          } else {
            yrange = car(extra_options)
            extra_options = cdr(extra_options)
            yrange = check_range(yrange)
            put(q_d_xvar, d_first(xrange))
            put(q_d_yvar, d_first(yrange))
            put(q_d_x, cddr(xrange))
            put(q_d_y, cddr(yrange))
          }
        }
      } else if eq(kind, q_d_discrete) {
        ()
      } else {
        merr("plot2d: a keyword 'parametric' or 'discrete' missing in ~M", [f])
        |> ignore
      }
    } else {
      // The expression represents a function, explicit or implicit
      if !xrange_required {
        xrange_required = true
        xrange = check_range(xrange)
        xrange_required = true
        if !getf(options, q_d_xlabel).truthy() {
          put(q_d_xlabel, ensure_string(second(xrange)))
        }
        put(q_d_xvar, cadr(xrange))
        put(q_d_x, cddr(xrange))
      }
      if listp(f) && eq(q_mequal, caar(f)) {
        // Implicit function
        if !yrange_required {
          yrange_required = true
          if extra_options is Nil {
            merr(
              "plot2d: implicit function plots require intervals for the variables in the two axes; only one interval was given.",
              [],
            )
            |> ignore
          } else {
            yrange = car(extra_options)
            extra_options = cdr(extra_options)
            yrange = check_range(yrange)
            put(q_d_yvar, d_first(yrange))
            put(q_d_y, cddr(yrange))
          }
        }
      }
    }
  }
  if !xrange_required {
    // Make the default ranges on X nd Y large so parametric plots don't get
    // prematurely clipped. Don't use most-positive-flonum because draw2d
    // will overflow.
    put(q_d_xbounds, list2(small, huge))
    if xrange.truthy() {
      // second argument was really a plot option, not an xrange
      extra_options = cons(xrange, extra_options)
    }
  }
  // If no global options xlabel or ylabel have been given, choose a default
  // value for them: the expressions given, converted to Maxima strings, if
  // their length is less than 50 characters, or the default "x" and "y"
  // otherwise.
  if length(fun) == 2 {
    let v = second(fun)
    let (xlabel, ylabel) : (Value, Value) = if atom(v) {
      (Str("x"), d_sconcat(list1(v)))
    } else if eq(second(v), q_d_parametric) {
      (d_sconcat(list1(third(v))), d_sconcat(list1(fourth(v))))
    } else if eq(second(v), q_d_discrete) {
      (Str("x"), Str("y"))
    } else if eq(second(v), q_d_contour) {
      (
        ensure_string(getf(options, q_d_xvar)),
        ensure_string(getf(options, q_d_yvar)),
      )
    } else {
      (Str("x"), d_sconcat(list1(v)))
    }
    if !getf(options, q_d_xlabel).truthy() {
      if length(xlabel) < 50 {
        put(q_d_xlabel, xlabel)
      }
    }
    if !getf(options, q_d_ylabel).truthy() {
      if length(ylabel) < 50 {
        put(q_d_ylabel, ylabel)
      }
    }
  }
  // For explicit functions, default ylabel is the name of the 2nd variable
  if getf(options, q_d_yvar).truthy() {
    put(q_d_ylabel, d_sconcat(list1(getf(options, q_d_yvar))))
  }
  // Parse the given options into the options list
  options = plot_options_parser(extra_options, options)
  if getf(options, q_d_y).truthy() {
    put(q_d_ybounds, getf(options, q_d_y))
  }
  // Remove axes labels when no box is used in gnuplot
  if memq(q_mbox, options).truthy() &&
    !getf(options, q_mbox).truthy() &&
    !eq(getf(options, q_d_plot_format), q_d_xmaxima) {
    options = plot__remf(options, q_d_xlabel).0
    options = plot__remf(options, q_d_ylabel).0
  }
  // check options given
  let xmin = first(getf(options, q_d_x))
  let xmax = second(getf(options, q_d_x))
  if getf(options, q_d_logx).truthy() && xmin.truthy() && xmax.truthy() {
    if num_gt(xmax, Fix(0L)) {
      if num_le(xmin, Fix(0L)) {
        let revised_xmin = num_div(xmax, Fix(1000L))
        mtell(
          list3(
            Str(
              "plot2d: lower bound must be positive when using 'logx'.~%plot2d: assuming lower bound = ~M instead of ~M",
            ),
            revised_xmin,
            xmin,
          ),
        )
        |> ignore
        put(q_d_x, list2(revised_xmin, xmax))
        xrange = list4(list1(q_mlist), second(xrange), revised_xmin, xmax)
      }
    } else {
      merr(
        "plot2d: upper bound must be positive when using 'logx'; found: ~M",
        [xmax],
      )
      |> ignore
    }
  }
  let ymin = first(getf(options, q_d_y))
  let ymax = second(getf(options, q_d_y))
  if getf(options, q_d_logy).truthy() && ymin.truthy() && ymax.truthy() {
    if num_gt(ymax, Fix(0L)) {
      if num_le(ymin, Fix(0L)) {
        let revised_ymin = num_div(ymax, Fix(1000L))
        mtell(
          list3(
            Str(
              "plot2d: lower bound must be positive when using 'logy'.~%plot2d: assuming lower bound = ~M instead of ~M",
            ),
            revised_ymin,
            ymin,
          ),
        )
        |> ignore
        put(q_d_y, list2(revised_ymin, ymax))
      }
    } else {
      merr(
        "plot2d: upper bound must be positive when using 'logy'; found: ~M",
        [ymax],
      )
      |> ignore
    }
  }
  set(q_ear_plot_realpart, getf(options, q_d_plot_realpart)) |> ignore
  // Creates the object that will be passed to the external graphic program
  let plot = plot__make_plot(options, "plot2d", false)
  // Parse plot object and pass it to the graphic program
  let output_file = plot__plot_preamble(plot, options)
  plot__plot2d_command(plot, fun, options, xrange)
  plot__plot_shipout(plot, options, output_file~)
}

///|
fn msymbolp(x : Value) -> Value raise {
  lbool(symbolp(x) && lstring(symval(x)).has_prefix("$"))
}

///|
fn check_range(range : Value) -> Value raise {
  let mut tem : Value = Nil
  let mut a : Value = Nil
  let mut b : Value = Nil
  let ok = d_listp(range).truthy() &&
    {
      tem = cdr(range)
      tem.truthy()
    } &&
    (symbolp(car(tem)) || d_subvarp(car(tem)).truthy()) &&
    {
      a = d_float(meval(second(tem)))
      numberp(a)
    } &&
    {
      b = d_float(meval(third(tem)))
      numberp(b)
    } &&
    num_lt(a, b)
  if !ok {
    if range.truthy() {
      merr(
        "plotting: range must be of the form [variable, min, max]; found: ~M",
        [range],
      )
      |> ignore
    } else {
      merr(
        "plotting: no range given; must supply range of the form [variable, min, max]",
        [],
      )
      |> ignore
    }
  }
  list4(list1(q_mlist), car(tem), lfloat(a), lfloat(b))
}

///|
fn d_zero_fun(x : Value, y : Value) -> Value raise {
  ignore(x)
  ignore(y)
  Flo(0.0)
}

///|
/// If m is supplied print blank line every m lines
fn output_points(points : Value, m? : Value = Nil) -> Value raise {
  let mut j = -1
  let n = length(points)
  let mut i = 0
  let pstream = symval(q_d_pstream)
  while i < n {
    print_pt(aref1(points, i)) |> ignore
    i = i + 1
    print_pt(aref1(points, i)) |> ignore
    i = i + 1
    print_pt(aref1(points, i)) |> ignore
    terpri(stream=pstream)
    if m.truthy() {
      j = j + 1
      if j == to_int(m) {
        terpri(stream=pstream)
        j = -1
      }
    }
    i = i + 1
  }
  Nil
}

///|
/// contour_plot now punts to plot2d
fn d_contour_plot(expr : Value, optional_args : Value) -> Value raise {
  let mut command : Value = Str("plot2d ([contour, ")
  command = d_sconcat(list3(command, expr, Str("]")))
  if optional_args.truthy() {
    for a in optional_args.iter() {
      command = d_sconcat(list3(command, Str(", "), a))
    }
  }
  command = d_sconcat(list2(command, Str(")")))
  mtell(list1(Str("contour_plot is now obsolete. Using plot2d instead:~%")))
  |> ignore
  mtell(list2(Str("~M~%"), command)) |> ignore
  let args = cons(list3(list1(q_mlist), q_d_contour, expr), optional_args)
  d_plot2d(car(args), xrange=cadr(args), cddr(args))
}

///|
/// plot3d
/// Examples:
///
/// plot3d (2^(-u^2 + v^2), [u, -3, 3], [v, -2, 2], nopalette);
///
/// plot3d ( log ( x^2*y^2 ), [x, -2, 2], [y, -2, 2], [grid, 29, 29]);
///
/// expr_1: cos(y)*(10.0+6*cos(x))$
/// expr_2: sin(y)*(10.0+6*cos(x))$
/// expr_3: -6*sin(x)$
/// plot3d ([expr_1, expr_2, expr_3], [x, 0, 2*%pi], [y, 0, 2*%pi],
/// ['grid, 40, 40], [z,-8,8]);
///
/// plot3d (cos (-x^2 + y^3/4), [x, -4, 4], [y, -4, 4],
/// [mesh_lines_color, false], [elevation, 0], [azimuth, 0], [grid, 150, 150]);
///
/// spherical: make_transform ([th, phi,r], r*sin(phi)*cos(th),
/// r*sin(phi)*sin(th), r*cos(phi))$
/// plot3d ( 5, [th, 0, 2*%pi], [phi, 0, %pi], [transform_xy, spherical],
/// [palette, [value, 0.65, 0.7, 0.1, 0.9]], [plot_format,xmaxima]);
///
/// V: 1 / sqrt ( (x+1)^2+y^2 ) - 1 / sqrt( (x-1)^2+y^2 )$
/// plot3d ( V, [x, -2, 2], [y, -2, 2], [z, -4, 4]);
fn d_plot3d(fun : Value, extra_options : Value) -> Value raise {
  with_special(q_ear_plot_realpart, symval(q_ear_plot_realpart), () => plot__plot3d(
    fun, extra_options,
  ))
}

///|
let plot__q_dd_gnuplot_4_0 : Value = sym("$$gnuplot_4_0")

///|
fn plot__plot3d(fun0 : Value, extra_options0 : Value) -> Value raise {
  let mut fun = fun0
  let mut extra_options = extra_options0
  let mut xrange : Value = Nil
  let mut yrange : Value = Nil
  let mut titles : Value = Nil
  let mut functions : Value = Nil
  let mut options = copy_tree(symval(q_ear_plot_options))
  let usage : Value = Str(
    "plot3d: Usage.\nTo plot a single function f of 2 variables v1 and v2:\n  plot3d (f, [v1, min, max], [v2, min, max], options)\nA parametric representation of a surface with parameters v1 and v2:\n  plot3d ([f1, f2, f3], [v1, min, max], [v2, min, max], options)\nSeveral functions depending on the two variables v1 and v2:\n  plot3d ([f1, f2, ..., fn, [v1, min, max], [v2, min, max]], options)",
  )
  let put = (k : Value, v : Value) => options = plot__putf(options, k, v)
  let pop_extra = () => {
    let v = car(extra_options)
    extra_options = cdr(extra_options)
    v
  }
  let pop_fun = () => {
    let v = car(fun)
    fun = cdr(fun)
    v
  }
  put(q_d_type, Str("plot3d"))
  // Ensure that fun is a list of expressions and maxima lists, followed by a
  // domain definition
  if d_listp(fun).truthy() {
    if length(check_list_plot3d(fun)) == 1 {
      // fun consisted of a single parametric expression
      let a = pop_extra()
      let b = pop_extra()
      fun = list3(fun, a, b)
    } else {
      // fun was a maxima list with several independent surfaces
      pop_fun() |> ignore
    }
  } else {
    // fun consisted of a single expression
    let a = pop_extra()
    let b = pop_extra()
    fun = list3(fun, a, b)
  }
  // go through all the independent surfaces creating the functions stack
  while true {
    let exprn = pop_fun()
    if d_listp(exprn).truthy() {
      let domain = check_list_plot3d(exprn)
      match length(domain) {
        1 => {
          // exprn is a parametric representation of a surface
          // list fun should have two valid ranges after exprn
          xrange = check_range(pop_fun())
          yrange = check_range(pop_fun())
          // list of the two variables for the parametric equations
          let lvars = list3(list1(q_mlist), second(xrange), second(yrange))
          // make sure that the 3 parametric equations depend only on the
          // two variables in lvars
          let vars_of = (e : Value) => d_listofvars(
            funcall(coerce_float_fun(e, list2(lvars, Str("plot3d"))), [
              second(lvars),
              third(lvars),
            ]),
          )
          let vars1 = vars_of(second(exprn))
          let vars2 = vars_of(third(exprn))
          let vars3 = vars_of(fourth(exprn))
          let lvars = d_listofvars(list4(list1(q_mlist), vars1, vars2, vars3))
          if num_le(d_length(lvars), Fix(2L)) {
            // we do have a valid parametric set. Push it into the functions
            // stack, along with their domain
            functions = cons(list3(exprn, xrange, yrange), functions)
            // add a title to the titles stack
            titles = cons(Str("Parametric function"), titles)
            // unknown variables in the parametric equations
            // ----- GNUPLOT 4.0 WORK-AROUND -----
            if d_constantp(fourth(exprn)).truthy() &&
              getf(options, q_d_gnuplot_4_0).truthy() {
              put(q_d_const_expr, d_float(meval(fourth(exprn))))
            }
          } else {
            merr("plot3d: there must be at most two variables; found: ~M", [
              lvars,
            ])
            |> ignore
          }
        }
        3 => {
          // expr is a simple function with its own domain. Push the
          // function and its domain into the functions stack
          xrange = second(domain)
          yrange = third(domain)
          functions = cons(list3(second(exprn), xrange, yrange), functions)
          // push a title for this plot into the titles stack
          if length(ensure_string(second(exprn))) < 36 {
            titles = cons(ensure_string(second(exprn)), titles)
          } else {
            titles = cons(Str("Function"), titles)
          }
        }
        _ =>
          // syntax error. exprn does not have the expected form
          merr(
            "plot3d: argument must be a list of three expressions; found: ~M",
            [exprn],
          )
          |> ignore
      }
    } else {
      // exprn is a simple function, defined in the global domain.
      if getf(options, q_d_xvar).truthy() && getf(options, q_d_yvar).truthy() {
        // the global domain has already been defined; use it.
        xrange = list4(
          list1(q_mlist),
          getf(options, q_d_xvar),
          first(getf(options, q_d_x)),
          second(getf(options, q_d_x)),
        )
        yrange = list4(
          list1(q_mlist),
          getf(options, q_d_yvar),
          first(getf(options, q_d_y)),
          second(getf(options, q_d_y)),
        )
      } else {
        // the global domain should be defined by the last two lists in fun.
        // Extract it and check whether it is valid.
        let domain = check_list_plot3d(
          append(list2(list1(q_mlist), exprn), plot__last_n(fun, 2)),
        )
        fun = butlast(fun, n=2)
        if length(domain) == 3 {
          // domain is valid. Make it the global one.
          xrange = second(domain)
          yrange = third(domain)
          put(q_d_xvar, second(xrange))
          put(q_d_x, cddr(xrange))
          put(q_d_yvar, second(yrange))
          put(q_d_y, cddr(yrange))
        } else {
          merror(usage, Nil) |> ignore
        }
      }
      // ----- GNUPLOT 4.0 WORK-AROUND -----
      if d_constantp(exprn).truthy() &&
        getf(options, plot__q_dd_gnuplot_4_0).truthy() {
        put(q_d_const_expr, d_float(meval(exprn)))
      }
      // push the function and its domain into the functions stack
      functions = cons(list3(exprn, xrange, yrange), functions)
      // push a title for this plot into the titles stack
      if length(ensure_string(exprn)) < 36 {
        titles = cons(ensure_string(exprn), titles)
      } else {
        titles = cons(Str("Function"), titles)
      }
    }
    if length(fun) == 0 {
      break
    }
  }
  // recover the original ordering for the functions and titles stacks
  functions = reverse(functions)
  titles = reverse(titles)
  // parse the options given to plot3d
  options = plot_options_parser(extra_options, options)
  let tem = getf(options, q_d_transform_xy)
  if memq(q_d_gnuplot_pm3d, options).truthy() &&
    getf(options, q_d_gnuplot_pm3d) is Nil {
    put(q_d_palette, Nil)
  }
  set(q_ear_plot_realpart, getf(options, q_d_plot_realpart)) |> ignore
  // set up the labels for the axes, unless no box is being shown
  if !(memq(q_mbox, options).truthy() && !getf(options, q_mbox).truthy()) {
    if getf(options, q_d_xvar).truthy() &&
      getf(options, q_d_yvar).truthy() &&
      tem is Nil {
      // Don't set xlabel (ylabel) if the user specified one.
      if !getf(options, q_d_xlabel).truthy() {
        put(q_d_xlabel, ensure_string(getf(options, q_d_xvar)))
      }
      if !getf(options, q_d_ylabel).truthy() {
        put(q_d_ylabel, ensure_string(getf(options, q_d_yvar)))
      }
    } else {
      put(q_d_xlabel, Str("x"))
      put(q_d_ylabel, Str("y"))
    }
    if !getf(options, q_d_zlabel).truthy() {
      put(q_d_zlabel, Str("z"))
    }
  }
  // x and y should not be bound, when an xy transformation function is used
  if tem.truthy() {
    options = plot__remf(options, q_d_x).0
    options = plot__remf(options, q_d_y).0
  }
  // Set up the plot command
  let mut legend = getf(options, q_d_legend)
  // titles will be a list. Titles given in the legend option prevail over
  // titles generated by plot3d. No legend if option [legend,false]
  if !listp(legend) {
    legend = list1(legend)
  }
  if memq(q_d_legend, options).truthy() {
    if first(legend).truthy() {
      titles = legend
    }
    titles = Nil
  }
  let plot = plot__make_plot(options, "plot3d", true)
  // Parse plot object and pass it to the graphic program
  let output_file = plot__plot_preamble(plot, options)
  plot__plot3d_command(plot, functions, options, titles)
  plot__plot_shipout(plot, options, output_file~)
}

///|
/// (last list n)
fn plot__last_n(l : Value, n : Int) -> Value {
  let len = length(l)
  if len <= n {
    l
  } else {
    nthcdr(len - n, l)
  }
}

///|
/// Given a Maxima list with 3 elements, checks whether it represents a
/// function defined in a 2-dimensional domain or a parametric
/// representation of a 3-dimensional surface, depending on two parameters.
/// The return value will be a Maxima list if the test is successful or nil
/// otherwise.  In the case of a function and a 2D domain, it returns the
/// domain, validated.  When it is a parametric representation it returns an
/// empty Maxima list.
fn check_list_plot3d(lis : Value) -> Value raise {
  // Makes sure list has the form ((mlist) $atom item1 item2)
  if !(
      d_listp(lis).truthy() &&
      num_eq(d_length(lis), Fix(3L)) &&
      !d_listp(second(lis)).truthy()
    ) {
    return Nil
  }
  // we might have a function with domain or a parametric representation
  if d_listp(third(lis)).truthy() {
    // lis is probably a function with a valid domain
    if d_listp(fourth(lis)).truthy() {
      // we do have a function and a domain. Return the domain
      let xrange = check_range(third(lis))
      let yrange = check_range(fourth(lis))
      list3(list1(q_mlist), xrange, yrange)
    } else {
      // wrong syntax: [expr1, list, expr2]
      Nil
    }
  } else if d_listp(fourth(lis)).truthy() {
    // lis is probably a parametric representation
    // wrong syntax: [expr1, expr2, list]
    Nil
  } else {
    // we do have a parametric representation. Return an empty list
    list1(list1(q_mlist))
  }
}

///|
fn init_plot() -> Unit raise {
  let string_pred = list([
    kw("setting-predicate"),
    list2(q_string_predicate, Str("must be a string")),
  ])
  defmvar(q_d_geomview_command, val=Str("geomview"), string_pred) |> ignore
  defmvar(q_d_xmaxima_plot_command, val=Str("xmaxima"), string_pred) |> ignore
  // Global plot options list; this is a property list.. It is not a Maxima
  // variable, to discourage users from changing it directly; it should be
  // changed via set_plot_option.
  d_reset_plot_options() |> ignore
  defmvar(
    q_d_plot_options,
    val=lread("((mlist) ((mlist) $plot_format $gnuplot_pipes))"),
    Nil,
  )
  |> ignore
  defmvar(q_d_gnuplot_view_args, val=Str("-persist ~a"), string_pred) |> ignore
  defmvar(q_d_gnuplot_file_args, val=Str("~a"), string_pred) |> ignore
}

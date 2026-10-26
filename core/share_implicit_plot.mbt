// Port of share/contrib/implicit_plot.lisp: implicit_plot, now a front end
// to plot2d.

///|
fn implicit_plot_fix_up_non_equations(expr : Value) -> Value raise {
  let f = fn(e : Value) -> Value raise {
    if e is Cons(_) && eq(caar(e), q_mequal) {
      e
    } else {
      list3(list1(q_mequal), e, Fix(0L))
    }
  }
  if d_listp(expr).truthy() {
    cons(list1(q_mlist), mapcar(f, cdr(expr)))
  } else {
    f(expr)
  }
}

///|
/// implicit_plot now punts to plot2d
fn d_implicit_plot(expr : Value, optional_args : Value) -> Value raise {
  let expr_eqs = implicit_plot_fix_up_non_equations(expr)
  let all_args = cons(expr_eqs, optional_args)
  mtell(
    list1(Str("implicit_plot is now obsolete. Calling plot2d instead:~%")),
  )
  |> ignore
  mtell(list2(Str("~M~%"), cons(list1(q_d_plot2d), all_args))) |> ignore
  d_plot2d(car(all_args), xrange=cadr(all_args), cddr(all_args))
}

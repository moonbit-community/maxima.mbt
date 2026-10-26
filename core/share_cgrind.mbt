// Port of share/contrib/cgrind.lisp (M. Talon, 2011): print expressions
// and matrices as C statements. Heavily lifted from grind.lisp and
// fortra.lisp; should have the same features as the fortran command.

///|
/// This function is called from Macsyma toplevel. First the argument is
/// checked to be a single expression. Then if the argument is a symbol, and
/// the symbol is bound to a matrix, the matrix is printed using an array
/// assignment notation.
fn d_cgrind(l : Value) -> Value raise {
  let l = fexprcheck(l)
  let mut value = strmeval(l)
  if msetqp(l).truthy() {
    value = list([list1(q_mequal), cadr(l), meval(l)])
  }
  if symbolp(l) && d_matrixp(value).truthy() {
    d_cgrindmx(l, value)
  } else if !atom(value) &&
    eq(caar(value), q_mequal) &&
    symbolp(cadr(value)) &&
    d_matrixp(caddr(value)).truthy() {
    d_cgrindmx(cadr(value), caddr(value))
  } else {
    c_print(value)
  }
}

///|
fn c_print(x : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  // Restructure the expression for displaying. Mainly sanitizes
  // exponentials, notably exp(2/3) becomes exp(2.0/3.0)
  let x = scanforc(x)
  // Protects the modifications to mexpt from creeping out.
  {
    defer {
      // Restore usual mexpt property etc. before exiting this frame.
      putprop(q_mexpt, q_msz_mexpt, q_grind) |> ignore
      set(q_ear_fortran_print, Nil) |> ignore
    }
    putprop(q_mexpt, q_msz_cmexpt, q_grind) |> ignore
    // This means basic printing for atoms, grind does fancy things.
    set(q_ear_fortran_print, t) |> ignore
    // Prints using the usual grind mechanisms
    mgrind(x, stream) |> ignore
    write_char(';', stream~)
    write_char('\n', stream~)
  }
  q_d_done
}

///|
/// The only modification to grind, converts a^b to pow(a,b), but taking
/// care of appropriate bracketing. The argument l to the left of (MEXPT)
/// has to be composed backwards. Finally a^-b has special treatment.
fn msz_cmexpt(x : Value, l : Value, r : Value) -> Value raise {
  let l = msize(
    cadr(x),
    revappend(list([Char('p'), Char('o'), Char('w'), Char('(')]), l),
    list1(Char(',')),
    q_mparen,
    q_mparen,
  )
  let x = nformat(caddr(x))
  let r = if mmminusp(x).truthy() {
    msize(cadr(x), list1(Char('-')), cons(Char(')'), r), q_mexpt, symval(q_rop))
  } else {
    msize(x, Nil, cons(Char(')'), r), q_mparen, q_mparen)
  }
  list([num_add(car(l), car(r)), l, r])
}

///|
/// Takes a name and a matrix and prints a sequence of C assignment
/// statements of the form
/// NAME[I][J] = <corresponding matrix element>
fn d_cgrindmx(name : Value, mat : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  with_special(q_d_loadprint, Nil, () => {
    if !symbolp(name) {
      merr("cgrindmx: first argument must be a symbol; found: ~M", [name])
      |> ignore
    } else if !d_matrixp(mat).truthy() {
      merr("cgrindmx: second argument must be a matrix; found: ~M", [mat])
      |> ignore
    }
    let mut i = 1
    for row in cdr(mat).iter() {
      let mut j = 1
      for m in cdr(row).iter() {
        format(stream, "~a[~a][~a] = ", [
          Str(string_left_trim("$", invert_case(symbol_name(name)))),
          int(i - 1),
          int(j - 1),
        ])
        |> ignore
        c_print(m, stream~) |> ignore
        j = j + 1
      }
      i = i + 1
    }
    q_d_done
  })
}

///|
/// This C scanning function is similar to fortscan. Prepare an expression
/// for printing by converting x^(1/2) to sqrt(x), etc. Since C has no
/// support for complex numbers, contrary to Fortran, ban them.
fn scanforc(e : Value) -> Value raise {
  if atom(e) {
    if eq(e, q_d__pcti) {
      // ban complex numbers
      merr("Take real and imaginary parts", [])
    } else {
      e
    }
  } else if eq(caar(e), q_mexpt) && eq(cadr(e), q_d__pcte) {
    // %e^a -> exp(a)
    list2(list2(q_p_exp, q_simp), scanforc(caddr(e)))
  } else if eq(caar(e), q_mexpt) &&
    alike1(caddr(e), list([list2(q_rat, q_simp), int(1), int(2)])).truthy() {
    // a^1/2 -> sqrt(a)
    list2(list2(q_p_sqrt, q_simp), scanforc(cadr(e)))
  } else if eq(caar(e), q_mexpt) &&
    alike1(caddr(e), list([list2(q_rat, q_simp), int(-1), int(2)])).truthy() {
    // a^-1/2 -> 1/sqrt(a)
    list([
      list2(q_mquotient, q_simp),
      int(1),
      list2(list2(q_p_sqrt, q_simp), scanforc(cadr(e))),
    ])
  } else if eq(caar(e), q_mtimes) &&
    ratnump(cadr(e)).truthy() &&
    (equal(cadr(cadr(e)), int(1)) || equal(cadr(cadr(e)), int(-1))) {
    // (1/3)*b -> b/3.0 and (-1/3)*b -> -b/3.0
    if equal(cadr(cadr(e)), int(1)) {
      scanforc_mtimes(e)
    } else {
      list2(list2(q_mminus, q_simp), scanforc_mtimes(e))
    }
  } else if eq(caar(e), q_rat) {
    // 1/3 -> 1.0/3.0
    list([list2(q_mquotient, q_simp), lfloat(cadr(e)), lfloat(caddr(e))])
  } else if eq(caar(e), q_mrat) {
    // rat(a/b) -> a/b via ratdisrep
    scanforc(ratdisrep(e))
  } else if (eq(caar(e), q_mtimes) || eq(caar(e), q_mplus)) &&
    {
      // ban complex numbers
      let a = simplify(d_bothcoef(e, q_d__pcti))
      numberp(cadr(a)) &&
      numberp(caddr(a)) &&
      !zerop1(cadr(a)).truthy() &&
      merr("Take real and imaginary parts", []).truthy()
    } {
    Nil
  } else {
    // in general do nothing, recurse
    cons(car(e), mapcar(x => scanforc(x), cdr(e)))
  }
}

///|
/// This is used above 1/3*b*c -> b*c/3.0
fn scanforc_mtimes(e : Value) -> Value raise {
  list([
    list2(q_mquotient, q_simp),
    if cdddr(e) is Nil {
      scanforc(caddr(e))
    } else {
      cons(car(e), mapcar(x => scanforc(x), cddr(e)))
    },
    lfloat(caddr(cadr(e))),
  ])
}

///|
fn init_share_cgrind() -> Unit raise {
  macsyma_module(sym("cgrind"), Nil) |> ignore
}

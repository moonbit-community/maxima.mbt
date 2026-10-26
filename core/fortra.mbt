// Port of src/fortra.lisp: fortran() -- print expressions as Fortran
// statements.

///|
/// `*read-default-float-format*` (no runtime constant): bound to
/// `single-float` while MSTRING linearizes for Fortran, so that float
/// printing always shows an exponent marker.
let fortra__q_read_default_float_format : Value = sym(
  "*read-default-float-format*",
)

///|
/// This function is called from Macsyma toplevel. If the argument is a
/// symbol, and the symbol is bound to a matrix or list, then the value is
/// printed using an array assignment notation.
fn d_fortran(l : Value) -> Value raise {
  let l = fexprcheck(l)
  let mut value = strmeval(l)
  if msetqp(l).truthy() {
    value = mk(q_mequal, [cadr(l), meval(l)])
  }
  if symbolp(l) && (d_matrixp(value).truthy() || d_listp(value).truthy()) {
    d_fortmx(l, value)
  } else if !atom(value) &&
    eq(caar(value), q_mequal) &&
    symbolp(cadr(value)) &&
    (d_matrixp(caddr(value)).truthy() || d_listp(caddr(value)).truthy()) {
    d_fortmx(cadr(value), caddr(value))
  } else {
    fortran_print(value)
  }
}

///|
/// This function is called from Lisp programs. It takes an expression and
/// a stream argument. Default stream is *STANDARD-OUTPUT*.
fn fortran_print(x : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  // Restructure the expression for displaying.
  let x0 = fortscan(x)
  // Linearize the expression using MSTRING. Some global state must be
  // modified for MSTRING to generate using Fortran syntax. This must be
  // undone so as not to modify the toplevel behavior of MSTRING.
  // (The Lisp UNWIND-PROTECT only protects the first DEFPROP; the rest are
  // its cleanup forms.)
  let mut x = x0
  putprop(q_mexpt, q_msize_infix, q_grind) |> ignore
  putprop(q_mminus, Fix(100L), q_lbp) |> ignore
  putprop(q_msetq, list1(Char(':')), q_strsym) |> ignore
  // The binding of *read-default-float-format* makes sure we get an
  // exponent marker for Fortran numbers.
  x = with_specials(
    [
      (q_ear_fortran_print, t),
      (fortra__q_read_default_float_format, sym("single-float")),
    ],
    () => mstring(x),
  )
  // Make sure this gets done before exiting this frame.
  putprop(q_mexpt, q_msz_mexpt, q_grind) |> ignore
  remprop(q_mminus, q_lbp) |> ignore

  // MSTRING returns a list of characters. Now print them.
  let fortindent = to_int(symval(q_d_fortindent))
  let mut c = char_code('0')
  let mut column = 6 + fortindent
  while x.truthy() {
    // Print five spaces, a continuation character if needed, and then more
    // spaces. COLUMN points to the last column printed in. When it equals
    // 80, we should quit.
    if c == char_code('0') {
      print_spaces(int(column), stream) |> ignore
    } else {
      print_spaces(Fix(5L), stream) |> ignore
      write_char(code_char(c), stream~)
      print_spaces(int(column - 6), stream) |> ignore
    }
    // Print the expression. Remember, Fortran ignores blanks and line
    // terminators, so we don't care where the expression is broken.
    while column != 72 {
      if x is Nil {
        if symval(q_d_fortspaces).truthy() {
          write_char(' ', stream~)
        } else {
          break
        }
      } else {
        if equal(car(x), Char('\\')) {
          x = cdr(x)
        }
        match car(x) {
          Char(ch) => write_char(ch, stream~)
          v => write_string(princ_to_string(v), stream~)
        }
        x = cdr(x)
      }
      column += 1
    }
    // Columns 73 to 80 contain spaces
    if symval(q_d_fortspaces).truthy() {
      print_spaces(Fix(8L), stream) |> ignore
    }
    terpri(stream~)
    c = 1 + (c - char_code('0')) % 16 + char_code('0')
    column = 9 + fortindent
  }
  q_d_done
}

///|
fn print_spaces(n : Value, stream : Value) -> Value raise {
  for _ in 0..<to_int(n) {
    write_char(' ', stream~)
  }
  Nil
}

///|
/// This function is similar to NFORMAT. Prepare an expression for
/// printing by converting x^(1/2) to sqrt(x), etc.
fn fortscan(e : Value) -> Value raise {
  if atom(e) {
    if eq(e, q_d__pcti) {
      mk(q_mprogn, [Flo(0.0), Flo(1.0)]) // %I is (0,1)
    } else {
      e
    }
  } else if eq(caar(e), q_mexpt) && eq(cadr(e), q_d__pcte) {
    list2(list2(q_p_exp, q_simp), fortscan(caddr(e)))
  } else if eq(caar(e), q_mexpt) && alike1(caddr(e), symval(q_n1_sl_sl2)).truthy() {
    list2(list2(q_p_sqrt, q_simp), fortscan(cadr(e)))
  } else if eq(caar(e), q_mexpt) &&
    alike1(caddr(e), symval(q_n_1_sl_sl2)).truthy() {
    list3(
      list2(q_mquotient, q_simp),
      Fix(1L),
      list2(list2(q_p_sqrt, q_simp), fortscan(cadr(e))),
    )
  } else if eq(caar(e), q_mtimes) &&
    ratnump(cadr(e)).truthy() &&
    (equal(cadadr(e), Fix(1L)) || equal(cadadr(e), Fix(-1L))) {
    if equal(cadadr(e), Fix(1L)) {
      fortscan_mtimes(e)
    } else {
      list2(list2(q_mminus, q_simp), fortscan_mtimes(e))
    }
  } else if eq(caar(e), q_rat) {
    list3(list2(q_mquotient, q_simp), lfloat(cadr(e)), lfloat(caddr(e)))
  } else if eq(caar(e), q_mrat) {
    fortscan(ratdisrep(e))
  } else {
    // complex numbers to f77 syntax a+b%i ==> (a,b)
    let cplx = if eq(caar(e), q_mtimes) || eq(caar(e), q_mplus) {
      let a = simplify(d_bothcoef(e, q_d__pcti))
      if numberp(cadr(a)) && numberp(caddr(a)) && zerop1(cadr(a)) is Nil {
        mk(q_mprogn, [caddr(a), cadr(a)])
      } else {
        Nil
      }
    } else {
      Nil
    }
    if cplx.truthy() {
      cplx
    } else {
      cons(car(e), mapcar(x => fortscan(x), cdr(e)))
    }
  }
}

///|
fn fortscan_mtimes(e : Value) -> Value raise {
  list3(
    list2(q_mquotient, q_simp),
    if cdddr(e) is Nil {
      fortscan(caddr(e))
    } else {
      cons(car(e), mapcar(x => fortscan(x), cddr(e)))
    },
    lfloat(caddr(cadr(e))),
  )
}

///|
/// Takes a name and a matrix and prints a sequence of Fortran assignment
/// statements of the form NAME(I,J) = <corresponding matrix element> or,
/// when the second argument is a list, NAME(I) = <list element>.
fn d_fortmx(name : Value, mat : Value, stream? : Value) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_output)
  }
  with_special(q_d_loadprint, Nil, () => {
    if !symbolp(name) {
      merr("fortmx: first argument must be a symbol; found: ~M", [name])
      |> ignore
    } else if d_matrixp(mat) is Nil && d_listp(mat) is Nil {
      merr("fortmx: second argument must be a list or matrix; found: ~M", [
        mat,
      ])
      |> ignore
    }
    if d_matrixp(mat).truthy() {
      let mut i = 1
      for row in cdr(mat).iter() {
        let mut j = 1
        for m in cdr(row).iter() {
          fortran_print(
            mk(q_mequal, [mk(name, [int(i), int(j)]), m]),
            stream~,
          )
          |> ignore
          j += 1
        }
        i += 1
      }
    } else if d_listp(mat).truthy() {
      let mut i = 1
      for m in cdr(mat).iter() {
        fortran_print(mk(q_mequal, [mk(name, [int(i)]), m]), stream~) |> ignore
        i += 1
      }
    }
    q_d_done
  })
}

///|
fn fortra__boolean_assign(var_ : Value, val : Value) -> Value raise {
  if eq(val, t) || val is Nil {
    Nil
  } else {
    mseterr(var_, val, reason=Str("must be one of: true, false"))
  }
}

///|
fn init_fortra() -> Unit raise {
  // (defmvar $fortspaces nil ... boolean)
  putprop(
    q_d_fortspaces,
    lfunc("fortspaces-assign", args => fortra__boolean_assign(
      arg(args, 0),
      arg(args, 1),
    )),
    q_assign,
  )
  |> ignore
  // (defmvar $fortindent 0 ... :setting-predicate ...)
  // The value must be non-negative fixnum
  putprop(
    q_d_fortindent,
    lfunc("fortindent-assign", args => {
      let var_ = arg(args, 0)
      let val = arg(args, 1)
      if fixnump(val) && num_ge(val, Fix(0L)) {
        Nil
      } else {
        mseterr(var_, val, reason=Nil)
      }
    }),
    q_assign,
  )
  |> ignore
  putprop(q_mexpt, list2(Char('*'), Char('*')), q_dissym) |> ignore
}

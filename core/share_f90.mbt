// Port of share/contrib/f90.lisp (James F. Amundson, 2004; based on
// fortra.lisp): print expressions as Fortran 90 statements.
//
// Output from f90 is "free form": no special attention to columns. Lines
// longer than *F90-OUTPUT-LINE-LENGTH-MAX* are broken with trailing
// ampersand (no additional spaces).

///|
/// (coerce (list of characters) 'string)
fn share_f90__chars_to_string(l : Value) -> String raise {
  let sb = StringBuilder::new()
  for c in l.iter() {
    match c {
      Char(ch) => sb.write_char(ch)
      v => raise type_error(v, "character")
    }
  }
  sb.to_string()
}

///|
fn f90_print(x : Value) -> Value raise {
  // This is a poor way of saying that array references are to be printed
  // with parens instead of brackets.
  with_specials([(q_ear_lb, Char('(')), (q_ear_rb, Char(')'))], () => {
    // Restructure the expression for displaying.
    let x = fortscan(x)
    // Linearize the expression using MSTRING. Some global state must be
    // modified for MSTRING to generate using Fortran syntax. This must be
    // undone so as not to modify the toplevel behavior of MSTRING. (The
    // Lisp UNWIND-PROTECT only protects the first DEFPROP; the rest are its
    // cleanup forms.)
    putprop(q_mexpt, q_msize_infix, q_grind) |> ignore
    putprop(q_mminus, int(100), q_lbp) |> ignore
    putprop(q_msetq, list1(Char(':')), q_strsym) |> ignore
    // The binding of *read-default-float-format* makes sure we get an
    // exponent marker for Fortran numbers.
    let mut s = ""
    with_specials(
      [
        (q_ear_fortran_print, t),
        (fortra__q_read_default_float_format, sym("single-float")),
      ],
      () => {
        s = share_f90__chars_to_string(mstring(x))
      },
    )
    // Make sure this gets done before exiting this frame.
    putprop(q_mexpt, q_msz_mexpt, q_grind) |> ignore
    remprop(q_mminus, q_lbp) |> ignore
    let x = s.to_array()
    let max = to_int(symval(q_ear_f90_output_line_length_max))
    let sub = (a : Array[Char], s : Int, e : Int) => String::from_array(
      a[s:e].to_array(),
    )
    if x.length() >= max {
      // Split this line and print it with trailing ampersand. Previous
      // scheme to break the lines nicely had some bugs; it's simpler to
      // break at a fixed length.
      let mut line = x
      let break_point = max
      princ(Str(sub(line, 0, break_point))) |> ignore
      princ(Str("&")) |> ignore
      terpri() |> ignore
      princ(Str("&")) |> ignore
      line = line[break_point:].to_array()
      while line.length() > break_point {
        princ(Str(sub(line, 0, break_point))) |> ignore
        princ(Str("&")) |> ignore
        terpri() |> ignore
        princ(Str("&")) |> ignore
        line = line[break_point:].to_array()
      }
      if line.length() > 0 {
        princ(Str(String::from_array(line))) |> ignore
      }
    } else {
      princ(Str(String::from_array(x))) |> ignore
    }
    terpri() |> ignore
    q_d_done
  })
}

///|
/// Takes a name and a matrix and prints a sequence of F90 assignment
/// statements of the form
///  NAME(I,J) = <corresponding matrix element>
/// or, when the second argument is a list,
///  NAME(I) = <list element>
fn d_f90mx(name : Value, mat : Value) -> Value raise {
  if !symbolp(name) {
    merr("f90mx: first argument must be a symbol; found: ~M", [name]) |> ignore
  } else if !(d_matrixp(mat).truthy() || d_listp(mat).truthy()) {
    merr("f90mx: second argument must be a list or matrix; found: ~M", [mat])
    |> ignore
  }
  if d_matrixp(mat).truthy() {
    let mut i = 1
    for row in cdr(mat).iter() {
      let mut j = 1
      for m in cdr(row).iter() {
        f90_print(
          list([list1(q_mequal), list([list1(name), int(i), int(j)]), m]),
        )
        |> ignore
        j = j + 1
      }
      i = i + 1
    }
  } else if d_listp(mat).truthy() {
    let mut i = 1
    for m in cdr(mat).iter() {
      f90_print(list([list1(q_mequal), list([list1(name), int(i)]), m]))
      |> ignore
      i = i + 1
    }
  }
  q_d_done
}

///|
fn d_f90(expr : Value) -> Value raise {
  for l in cdr(expr).iter() {
    let mut value = strmeval(l)
    if msetqp(l).truthy() {
      value = list([list1(q_mequal), cadr(l), meval(l)])
    }
    if symbolp(l) && (d_matrixp(value).truthy() || d_listp(value).truthy()) {
      d_f90mx(l, value) |> ignore
    } else if !atom(value) &&
      eq(caar(value), q_mequal) &&
      symbolp(cadr(value)) &&
      (d_matrixp(caddr(value)).truthy() || d_listp(caddr(value)).truthy()) {
      d_f90mx(cadr(value), caddr(value)) |> ignore
    } else {
      f90_print(value) |> ignore
    }
  }
  Nil
}

///|
fn init_share_f90() -> Unit raise {
  macsyma_module(sym("f90"), Nil) |> ignore
  defvar_init(
    q_d_f90_output_line_length_max,
    symval(q_ear_f90_output_line_length_max),
  )
  putprop(
    q_d_f90_output_line_length_max,
    q_ear_f90_output_line_length_max,
    q_alias,
  )
  |> ignore
  putprop(
    q_ear_f90_output_line_length_max,
    q_d_f90_output_line_length_max,
    q_reversealias,
  )
  |> ignore
}
